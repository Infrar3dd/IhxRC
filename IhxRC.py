#!/usr/bin/env python3

import argparse
import array
import base64
import curses
import json
import math
import os
import queue
import re
import shlex
import shutil
import socket
import ssl
import subprocess
import sys
import tempfile
import threading
import time
import wave
from collections import OrderedDict, deque
from datetime import datetime

VERSION = "IhxRC 1.0"
MAX_SCROLLBACK = 1000
RECONNECT_DELAY = 15.0
PING_IDLE = 120.0      # send a PING after this many seconds of silence
DEAD_AFTER = 300.0     # give up on the connection after this much silence

CTRL = {c: chr(i + 1) for i, c in enumerate("abcdefghijklmnopqrstuvwxyz")}

# mIRC formatting codes we strip before display
FORMAT_RE = re.compile(r"\x03(\d{1,2}(,\d{1,2})?)?|[\x02\x0f\x11\x16\x1d\x1e\x1f]")


# protocol helpers

class Message:
    __slots__ = ("tags", "prefix", "command", "params", "raw")

    def __init__(self, tags, prefix, command, params, raw):
        self.tags = tags
        self.prefix = prefix
        self.command = command
        self.params = params
        self.raw = raw

    @property
    def nick(self):
        return self.prefix.split("!", 1)[0] if self.prefix else ""

    def param(self, i, default=""):
        return self.params[i] if len(self.params) > i else default

    def __repr__(self):
        return "Message(%r, %r, %r)" % (self.prefix, self.command, self.params)


TAG_UNESCAPE = {r"\:": ";", r"\s": " ", r"\\": "\\", r"\r": "\r", r"\n": "\n"}


def parse_line(line):
    # Parse one raw IRC protocol line into a Message
    raw = line
    tags = {}
    line = line.strip("\r\n")
    if line.startswith("@"):
        tagpart, _, line = line[1:].partition(" ")
        for item in tagpart.split(";"):
            if not item:
                continue
            key, _, val = item.partition("=")
            for esc, real in TAG_UNESCAPE.items():
                val = val.replace(esc, real)
            tags[key] = val
        line = line.lstrip(" ")
    prefix = ""
    if line.startswith(":"):
        prefix, _, line = line[1:].partition(" ")
        line = line.lstrip(" ")
    command, _, rest = line.partition(" ")
    params = []
    rest = rest.lstrip(" ")
    while rest:
        if rest.startswith(":"):
            params.append(rest[1:])
            break
        token, _, rest = rest.partition(" ")
        if token:
            params.append(token)
        rest = rest.lstrip(" ")
    return Message(tags, prefix, command.upper(), params, raw)


def strip_formatting(text):
    return FORMAT_RE.sub("", text)


def lower(name):
    return name.lower().replace("[", "{").replace("]", "}").replace("\\", "|")



# buffers
class Buffer:
    # One window of text: the client log, a server status, a channel or a query

    def __init__(self, server, name, kind="channel"):
        self.server = server
        self.name = name
        self.kind = kind              # client | status | channel | query
        self.lines = deque(maxlen=MAX_SCROLLBACK)
        self.users = {}               # nick -> prefix chars ("@", "+", "")
        self.topic = ""
        self.scroll = 0               # wrapped lines scrolled up from the bottom
        self.unread = 0
        self.highlight = False
        self.joined = False
        self.input_history = []

    def add(self, segments, kind="text"):
        #segments: list of (text, style) tuples
        self.lines.append((time.time(), segments, kind))
        if self.scroll > 0:
            self.scroll += 1          # keep the view anchored while scrolled back

    def msg(self, text, style="text"):
        self.add([(text, style)], style)

    def rename_user(self, old, new):
        for nick in list(self.users):
            if lower(nick) == lower(old):
                self.users[new] = self.users.pop(nick)
                return True
        return False

    def has_user(self, nick):
        return any(lower(n) == lower(nick) for n in self.users)

    def remove_user(self, nick):
        for n in list(self.users):
            if lower(n) == lower(nick):
                del self.users[n]
                return True
        return False

# server connection

class Server:
    #A single IRC connection. The socket thread only reads bytes and pushes
    #events; all state mutation happens on the main thread in handle()

    def __init__(self, events, host, port=6697, tls=True, nick="IhxRC",
                 user=None, realname=None, password=None, sasl_user=None,
                 sasl_pass=None, channels=(), name=None, verify=True, app=None):
        self.events = events
        self.app = app
        self.host = host
        self.port = int(port)
        self.tls = tls
        self.verify = verify
        self.want_nick = nick
        self.nick = nick
        self.user = user or nick
        self.realname = realname or nick
        self.password = password
        self.sasl_user = sasl_user
        self.sasl_pass = sasl_pass
        self.autojoin = list(channels)
        self.name = name or host

        self.sock = None
        self.thread = None
        self.send_lock = threading.Lock()
        self.stopping = False
        self.connected = False
        self.registered = False
        self.reconnect_at = 0.0
        self.auto_reconnect = True
        self.last_rx = time.time()
        self.pinged = False
        self.nick_tries = 0

        self.isupport = {}
        self.prefix_modes = {"o": "@", "v": "+"}
        self.prefix_order = "@+"
        self.chantypes = "#&"
        self.chanmodes = ("beI", "k", "l", "imnpst")

        self.status = Buffer(self, self.name, kind="status")
        self.buffers = OrderedDict()   # lower(name) -> Buffer

    #buffer bookkeeping

    def all_buffers(self):
        return [self.status] + list(self.buffers.values())

    def buffer(self, name, kind=None, create=True):
        key = lower(name)
        buf = self.buffers.get(key)
        if buf is None and create:
            if kind is None:
                kind = "channel" if name[:1] in self.chantypes else "query"
            buf = Buffer(self, name, kind=kind)
            self.buffers[key] = buf
            if self.app:
                self.app.on_new_buffer(buf)
        return buf

    def close_buffer(self, buf):
        self.buffers.pop(lower(buf.name), None)

    def is_channel(self, name):
        return name[:1] in self.chantypes

    def is_me(self, nick):
        return lower(nick) == lower(self.nick)

    # connection

    def start(self):
        if self.thread and self.thread.is_alive():
            return
        self.stopping = False
        self.reconnect_at = 0.0
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    def _emit(self, kind, payload=None):
        self.events.put((self, kind, payload))

    def _run(self):
        sock = None
        reason = "connection closed"
        try:
            self._emit("info", "Connecting to %s:%d%s..."
                       % (self.host, self.port, " (TLS)" if self.tls else ""))
            sock = socket.create_connection((self.host, self.port), timeout=30)
            if self.tls:
                ctx = ssl.create_default_context()
                if not self.verify:
                    ctx.check_hostname = False
                    ctx.verify_mode = ssl.CERT_NONE
                sock = ctx.wrap_socket(sock, server_hostname=self.host)
            sock.settimeout(None)
            self.sock = sock
            self.connected = True
            self.last_rx = time.time()
            self._emit("connected")
            self._register()

            buf = b""
            while not self.stopping:
                data = sock.recv(8192)
                if not data:
                    break
                buf += data
                while b"\n" in buf:
                    raw, buf = buf.split(b"\n", 1)
                    text = raw.decode("utf-8", "replace").rstrip("\r")
                    if text:
                        self._emit("line", parse_line(text))
        except ssl.SSLError as exc:
            reason = "TLS error: %s" % exc
        except socket.gaierror as exc:
            reason = "cannot resolve %s (%s)" % (self.host, exc)
        except OSError as exc:
            reason = str(exc) or exc.__class__.__name__
        except Exception as exc:  # noqa: BLE001 - never kill the thread silently
            reason = "%s: %s" % (exc.__class__.__name__, exc)
        finally:
            self.connected = False
            self.registered = False
            try:
                if sock:
                    sock.close()
            except OSError:
                pass
            self.sock = None
            self._emit("disconnected", "disconnected by user" if self.stopping else reason)

    def _register(self):
        if self.sasl_user and self.sasl_pass:
            self.send("CAP LS 302")
        if self.password:
            self.send("PASS %s" % self.password)
        self.send("NICK %s" % self.want_nick)
        self.send("USER %s 0 * :%s" % (self.user, self.realname))

    def send(self, line):
        if not self.sock:
            return False
        data = line.encode("utf-8", "replace")[:510] + b"\r\n"
        try:
            with self.send_lock:
                self.sock.sendall(data)
            return True
        except OSError:
            return False

    def privmsg(self, target, text):
        self.send("PRIVMSG %s :%s" % (target, text))

    def disconnect(self, reason="Leaving", auto=False):
        self.auto_reconnect = auto
        self.stopping = True
        if self.sock:
            self.send("QUIT :%s" % reason)
            try:
                self.sock.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass

    def tick(self, now):
        #Called periodically from the main loop
        if self.connected and self.registered:
            idle = now - self.last_rx
            if idle > DEAD_AFTER:
                self.status.msg("Connection timed out.", "error")
                self.stopping = True
                if self.sock:
                    try:
                        self.sock.shutdown(socket.SHUT_RDWR)
                    except OSError:
                        pass
            elif idle > PING_IDLE and not self.pinged:
                self.pinged = True
                self.send("PING :%d" % int(now))
        elif (not self.connected and self.auto_reconnect
              and self.reconnect_at and now >= self.reconnect_at):
            self.reconnect_at = 0.0
            self.status.msg("Reconnecting...", "info")
            self.start()

    # ISUPPORT 

    def _parse_isupport(self, tokens):
        for token in tokens:
            key, _, val = token.partition("=")
            self.isupport[key.upper()] = val
            if key.upper() == "PREFIX" and val.startswith("("):
                modes, _, chars = val[1:].partition(")")
                if len(modes) == len(chars):
                    self.prefix_modes = dict(zip(modes, chars))
                    self.prefix_order = chars
            elif key.upper() == "CHANTYPES" and val:
                self.chantypes = val
            elif key.upper() == "CHANMODES":
                parts = val.split(",")
                if len(parts) >= 4:
                    self.chanmodes = tuple(parts[:4])
            elif key.upper() == "NETWORK" and val:
                self.name = val
                self.status.name = val

    def user_rank(self, prefix):
        if not prefix:
            return len(self.prefix_order)
        return self.prefix_order.index(prefix[0]) if prefix[0] in self.prefix_order \
            else len(self.prefix_order)

    def sorted_users(self, buf):
        return sorted(buf.users.items(),
                      key=lambda kv: (self.user_rank(kv[1]), lower(kv[0])))

    # inbound message handling

    def handle(self, msg):
        self.last_rx = time.time()
        self.pinged = False
        cmd = msg.command
        handler = getattr(self, "_on_" + cmd.lower(), None)
        if handler is not None:
            handler(msg)
        elif cmd.isdigit():
            self._on_numeric(msg)
        # anything else is ignored on purpose

    def channels_with(self, nick):
        return [b for b in self.buffers.values()
                if b.kind == "channel" and b.has_user(nick)]

    def _notify(self, buf, highlight=False, level=1):
        if self.app:
            self.app.notify(buf, highlight, level)

    # registration / housekeeping

    def _on_ping(self, msg):
        self.send("PONG :%s" % msg.param(0))

    def _on_pong(self, msg):
        pass

    def _on_error(self, msg):
        self.status.msg("ERROR: %s" % msg.param(0), "error")

    def _on_cap(self, msg):
        sub = msg.param(1).upper()
        caps = msg.param(2).split()
        if sub == "LS":
            if "sasl" in caps and self.sasl_user:
                self.send("CAP REQ :sasl")
            else:
                self.send("CAP END")
        elif sub == "ACK" and "sasl" in caps:
            self.send("AUTHENTICATE PLAIN")
        elif sub == "NAK":
            self.send("CAP END")

    def _on_authenticate(self, msg):
        if msg.param(0) == "+":
            payload = "\0".join([self.sasl_user, self.sasl_user, self.sasl_pass])
            blob = base64.b64encode(payload.encode("utf-8")).decode("ascii")
            self.send("AUTHENTICATE %s" % (blob or "+"))

    def _on_numeric(self, msg):
        code = msg.command
        text = " ".join(msg.params[1:]) if len(msg.params) > 1 else msg.param(0)
        if code in ("903",):
            self.status.msg("SASL authentication successful.", "info")
            self.send("CAP END")
        elif code in ("902", "904", "905", "906", "907"):
            self.status.msg("SASL failed: %s" % text, "error")
            self.send("CAP END")
        elif code == "001":
            self.registered = True
            self.nick = msg.param(0) or self.want_nick
            self.nick_tries = 0
            self.status.msg(text, "info")
            for chan in self.autojoin:
                self.send("JOIN %s" % chan)
        elif code == "005":
            self._parse_isupport(msg.params[1:-1])
        elif code == "433":                      # nickname in use
            self.nick_tries += 1
            if not self.registered and self.nick_tries < 5:
                self.want_nick = "%s_" % self.want_nick
                self.status.msg("Nick in use, trying %s" % self.want_nick, "error")
                self.send("NICK %s" % self.want_nick)
            else:
                self.status.msg(text, "error")
        elif code == "332":                      # topic
            buf = self.buffer(msg.param(1))
            buf.topic = strip_formatting(msg.param(2))
            buf.msg("Topic: %s" % buf.topic, "topic")
        elif code == "333":                      # topic set by
            buf = self.buffer(msg.param(1))
            try:
                when = datetime.fromtimestamp(int(msg.param(3))).strftime("%Y-%m-%d %H:%M")
            except (ValueError, OSError):
                when = "?"
            buf.msg("Topic set by %s on %s" % (msg.param(2).split("!")[0], when), "dim")
        elif code == "353":                      # NAMES reply
            buf = self.buffer(msg.param(2))
            for entry in msg.param(3).split():
                prefix = ""
                while entry and entry[0] in self.prefix_order:
                    prefix += entry[0]
                    entry = entry[1:]
                if "!" in entry:                 # userhost-in-names
                    entry = entry.split("!", 1)[0]
                if entry:
                    buf.users[entry] = prefix
        elif code == "366":                      # end of NAMES
            buf = self.buffer(msg.param(1))
            buf.msg("%d users in %s" % (len(buf.users), buf.name), "dim")
        elif code in ("311", "312", "313", "317", "318", "319", "330", "338", "671"):
            target = self.app.current if (self.app and self.app.current.server is self) \
                else self.status
            target.msg(text, "info")
            self._notify(target)
        elif code in ("375", "372", "376", "422"):
            self.status.msg(strip_formatting(text), "dim")
        elif code[0] in "45":
            target = self.app.current if (self.app and self.app.current.server is self) \
                else self.status
            target.msg(strip_formatting(text), "error")
            self._notify(target)
        else:
            self.status.msg(strip_formatting(text), "dim")

    # channel state

    def _on_join(self, msg):
        chan = msg.param(0)
        buf = self.buffer(chan, "channel")
        if self.is_me(msg.nick):
            buf.joined = True
            buf.users.clear()
            buf.msg("Now talking in %s" % chan, "join")
            if self.app:
                self.app.go_to(buf)
        else:
            buf.users.setdefault(msg.nick, "")
            buf.msg("%s joined %s" % (msg.nick, chan), "join")
        self._notify(buf, level=0)

    def _on_part(self, msg):
        chan = msg.param(0)
        buf = self.buffer(chan, "channel", create=False)
        if buf is None:
            return
        reason = msg.param(1)
        if self.is_me(msg.nick):
            buf.joined = False
            buf.users.clear()
            buf.msg("You left %s" % chan, "part")
        else:
            buf.remove_user(msg.nick)
            buf.msg("%s left %s%s" % (msg.nick, chan,
                                      " (%s)" % reason if reason else ""), "part")
        self._notify(buf, level=0)

    def _on_kick(self, msg):
        chan, target, reason = msg.param(0), msg.param(1), msg.param(2)
        buf = self.buffer(chan, "channel", create=False)
        if buf is None:
            return
        buf.remove_user(target)
        if self.is_me(target):
            buf.joined = False
            buf.users.clear()
        buf.msg("%s was kicked by %s%s" % (target, msg.nick,
                                           " (%s)" % reason if reason else ""), "part")
        self._notify(buf, level=0)

    def _on_quit(self, msg):
        reason = msg.param(0)
        for buf in self.channels_with(msg.nick):
            buf.remove_user(msg.nick)
            buf.msg("%s quit%s" % (msg.nick, " (%s)" % reason if reason else ""), "part")
        query = self.buffers.get(lower(msg.nick))
        if query is not None and query.kind == "query":
            query.msg("%s quit%s" % (msg.nick, " (%s)" % reason if reason else ""), "part")

    def _on_nick(self, msg):
        new = msg.param(0)
        if self.is_me(msg.nick):
            self.nick = new
            self.want_nick = new
            self.status.msg("You are now known as %s" % new, "info")
        for buf in list(self.buffers.values()):
            if buf.kind == "channel" and buf.rename_user(msg.nick, new):
                buf.msg("%s is now known as %s" % (msg.nick, new), "info")

    def _on_topic(self, msg):
        buf = self.buffer(msg.param(0), "channel")
        buf.topic = strip_formatting(msg.param(1))
        buf.msg("%s changed the topic to: %s" % (msg.nick, buf.topic), "topic")
        self._notify(buf)

    def _on_mode(self, msg):
        target = msg.param(0)
        if not self.is_channel(target):
            self.status.msg("Mode %s [%s]" % (target, " ".join(msg.params[1:])), "info")
            return
        buf = self.buffer(target, "channel", create=False)
        if buf is None:
            return
        modes = msg.param(1)
        args = list(msg.params[2:])
        adding = True
        a_modes, b_modes, c_modes = self.chanmodes[0], self.chanmodes[1], self.chanmodes[2]
        for char in modes:
            if char == "+":
                adding = True
                continue
            if char == "-":
                adding = False
                continue
            takes_arg = (char in self.prefix_modes or char in a_modes
                         or char in b_modes or (adding and char in c_modes))
            arg = args.pop(0) if (takes_arg and args) else ""
            if char in self.prefix_modes and arg:
                symbol = self.prefix_modes[char]
                for nick in list(buf.users):
                    if lower(nick) == lower(arg):
                        current = buf.users[nick]
                        if adding and symbol not in current:
                            current += symbol
                        elif not adding:
                            current = current.replace(symbol, "")
                        buf.users[nick] = "".join(
                            sorted(set(current), key=self.prefix_order.index))
        buf.msg("%s sets mode %s" % (msg.nick or self.name,
                                     " ".join(msg.params[1:])), "info")

    # conversation

    def _on_privmsg(self, msg):
        target, text = msg.param(0), msg.param(1)
        self._deliver(msg, target, text, notice=False)

    def _on_notice(self, msg):
        target, text = msg.param(0), msg.param(1)
        if not msg.nick or not self.registered:
            self.status.msg(strip_formatting(text), "notice")
            return
        self._deliver(msg, target, text, notice=True)

    def _deliver(self, msg, target, text, notice):
        sender = msg.nick or self.name
        # CTCP
        if text.startswith("\x01") and text.endswith("\x01") and len(text) > 1:
            ctcp = text[1:-1]
            verb, _, rest = ctcp.partition(" ")
            verb = verb.upper()
            if verb == "ACTION":
                self._show(msg, target, sender, rest, action=True)
                return
            if not notice:
                if verb == "VERSION":
                    self.send("NOTICE %s :\x01VERSION %s\x01" % (sender, VERSION))
                elif verb == "PING":
                    self.send("NOTICE %s :\x01PING %s\x01" % (sender, rest))
                elif verb == "TIME":
                    self.send("NOTICE %s :\x01TIME %s\x01"
                              % (sender, datetime.now().strftime("%c")))
                self.status.msg("CTCP %s from %s" % (verb, sender), "dim")
            return
        self._show(msg, target, sender, text, notice=notice)

    def _show(self, msg, target, sender, text, action=False, notice=False):
        text = strip_formatting(text)
        if self.is_channel(target):
            buf = self.buffer(target, "channel")
        elif self.is_me(target) and not self.is_me(sender):
            buf = self.buffer(sender, "query")       # incoming private message
        elif self.is_me(sender):
            buf = self.buffer(target, "query")       # our own outgoing one
        else:
            buf = self.status
        hl = self._is_highlight(text) and not self.is_me(sender)
        if action:
            buf.add([("* ", "action"), (sender, "action"), (" ", "action"),
                     (text, "highlight" if hl else "action")], "action")
        elif notice:
            buf.add([("-%s- " % sender, "notice"),
                     (text, "highlight" if hl else "text")], "notice")
        else:
            prefix = buf.users.get(sender, "")[:1]
            style = "self" if self.is_me(sender) else "nick%d" % (hash_nick(sender))
            buf.add([("<", "dim"), (prefix, "mode"), (sender, style), ("> ", "dim"),
                     (text, "highlight" if hl else "text")], "msg")
        own = self.is_me(sender)
        if buf.kind == "query" and not own:
            hl = True
        self._notify(buf, hl, level=0 if own else 1)

    def _is_highlight(self, text):
        return re.search(r"(?<![\w\[\]{}|^`\\-])%s(?![\w\[\]{}|^`\\-])"
                         % re.escape(self.nick), text, re.I) is not None


def hash_nick(nick):
    return sum(ord(c) for c in lower(nick)) % 6


# text wrapping

def wrap_segments(segments, width, indent=0):
    # Wrap styled segments into a list of lines (each a list of (text, style))
    width = max(4, width)
    indent = indent if indent < width - 4 else 0
    lines = []
    cur = []
    curlen = 0
    has_content = False

    def newline():
        nonlocal cur, curlen, has_content
        lines.append(cur)
        cur = [(" " * indent, "text")] if indent else []
        curlen = indent
        has_content = False

    for text, style in segments:
        for token in re.split(r"(\s+)", text):
            if not token:
                continue
            if token.isspace():
                if not has_content:
                    continue
                if curlen + len(token) > width:
                    newline()
                else:
                    cur.append((token, style))
                    curlen += len(token)
                continue
            while token:
                avail = width - curlen
                if avail <= 0:
                    newline()
                    continue
                if len(token) <= avail:
                    cur.append((token, style))
                    curlen += len(token)
                    has_content = True
                    token = ""
                elif has_content and len(token) <= width - indent:
                    newline()
                else:
                    cur.append((token[:avail], style))
                    token = token[avail:]
                    has_content = True
                    newline()
    lines.append(cur)
    return lines


# the application / UI


# notification sounds and desktop notifications

# tone name -> [(frequency Hz, seconds, volume)]; frequency 0 means silence
TONES = {
    "chime": [(880.00, 0.09, 0.55), (0, 0.010, 0), (1318.51, 0.20, 0.50)],
    "ping": [(1567.98, 0.06, 0.45), (0, 0.040, 0), (1567.98, 0.10, 0.45)],
    "knock": [(440.00, 0.06, 0.55), (0, 0.060, 0), (440.00, 0.09, 0.50)],
    "low": [(392.00, 0.11, 0.50), (0, 0.010, 0), (293.66, 0.22, 0.45)],
    "blip": [(1046.50, 0.05, 0.40)],
    "alert": [(1174.66, 0.07, 0.5), (0, 0.03, 0), (880.00, 0.07, 0.5),
              (0, 0.03, 0), (1174.66, 0.16, 0.5)],
}
SOUND_NAMES = sorted(TONES) + ["bell", "off"]
SOUND_EVENTS = ("highlight", "query", "message", "disconnect")
SAMPLE_RATE = 22050

# candidate command lines; {file} is replaced with the path to a wav
PLAYERS = [
    ("paplay", ["paplay", "{file}"]),
    ("pw-play", ["pw-play", "{file}"]),
    ("afplay", ["afplay", "{file}"]),
    ("aplay", ["aplay", "-q", "{file}"]),
    ("play", ["play", "-q", "{file}"]),
    ("ffplay", ["ffplay", "-nodisp", "-autoexit", "-loglevel", "quiet", "{file}"]),
    ("cvlc", ["cvlc", "--play-and-exit", "--intf", "dummy", "{file}"]),
    ("powershell.exe", ["powershell.exe", "-NoProfile", "-c",
                        "(New-Object Media.SoundPlayer '{file}').PlaySync()"]),
]

NOTIFIERS = [
    ("notify-send", ["notify-send", "-a", "IhxRC", "{title}", "{body}"]),
    ("terminal-notifier", ["terminal-notifier", "-title", "{title}",
                           "-message", "{body}"]),
    ("kdialog", ["kdialog", "--title", "{title}", "--passivepopup", "{body}", "5"]),
]


def render_tone(steps, rate=SAMPLE_RATE):
    # synthesise a short tone into 16-bit mono samples
    samples = array.array("h")
    for freq, duration, volume in steps:
        count = int(rate * duration)
        attack = max(1, int(0.006 * rate))
        release = max(1, int(0.7 * count))
        for i in range(count):
            if freq <= 0:
                samples.append(0)
                continue
            envelope = min(1.0, i / attack) * min(1.0, (count - i) / release)
            phase = 2 * math.pi * freq * (i / rate)
            value = (math.sin(phase) + 0.22 * math.sin(2 * phase)) / 1.22
            samples.append(int(max(-1.0, min(1.0, value * volume * envelope)) * 32000))
    return samples


class SoundEngine:
    #Plays short synthesised notification tones, out of the way of the UI

    def __init__(self, settings=None):
        self.enabled = True
        self.events = {"highlight": "chime", "query": "ping",
                       "message": "knock", "disconnect": "low"}
        # per-event rate limits: a busy channel must not machine-gun the speakers
        self.gaps = {"highlight": 0.35, "query": 0.5, "message": 2.5,
                     "disconnect": 1.0}
        self.min_gap = 0.35
        self.focused = False           # also sound for the buffer you are reading
        self.last_played = {}
        self.player_name = None
        self.player_cmd = None
        self.desktop_enabled = False
        self.desktop_name = None
        self.desktop_cmd = None
        self.last_error = ""
        self._cache = {}
        self._tmpdir = None
        self._queue = queue.Queue(maxsize=8)
        self._worker = None
        self.detect()
        self.configure(settings or {})

    # setup

    def detect(self):
        for name, cmd in PLAYERS:
            if shutil.which(name):
                self.player_name, self.player_cmd = name, cmd
                break
        for name, cmd in NOTIFIERS:
            if shutil.which(name):
                self.desktop_name, self.desktop_cmd = name, cmd
                break

    def configure(self, settings):
        if not isinstance(settings, dict):
            return
        self.enabled = bool(settings.get("enabled", self.enabled))
        for event in SOUND_EVENTS:
            if event in settings:
                self.events[event] = str(settings[event])
        self.focused = bool(settings.get("focused", self.focused))
        for event, gap in (settings.get("gaps") or {}).items():
            try:
                self.gaps[event] = float(gap)
            except (TypeError, ValueError):
                pass
        custom = settings.get("player")
        if custom:
            self.set_player(custom)

    def set_player(self, command):
        #command is a shell-ish string that must contain {file}
        if "{file}" not in command:
            return False
        self.player_cmd = shlex.split(command)
        self.player_name = self.player_cmd[0]
        return True

    def available(self):
        return self.player_cmd is not None

    # playing

    def play(self, event, force=False):
        tone = self.events.get(event, event)
        if not force:
            if not self.enabled or tone in ("off", "", None):
                return
            now = time.time()
            gap = self.gaps.get(event, self.min_gap)
            if now - self.last_played.get(event, 0.0) < gap:
                return
            # never let two events overlap into a jumble
            if now - max(self.last_played.values() or [0.0]) < 0.12:
                return
            self.last_played[event] = now
        if tone == "bell" or not self.available():
            self.beep()
            return
        if tone not in TONES:
            return
        self._submit(("tone", tone))

    def beep(self):
        try:
            curses.beep()
        except curses.error:
            pass

    def desktop(self, title, body):
        if not (self.desktop_enabled and self.desktop_cmd):
            return
        self._submit(("desktop", title, body))

    def _submit(self, item):
        if self._worker is None or not self._worker.is_alive():
            self._worker = threading.Thread(target=self._run, daemon=True)
            self._worker.start()
        try:
            self._queue.put_nowait(item)
        except queue.Full:
            pass

    def _wav_path(self, tone):
        path = self._cache.get(tone)
        if path:
            return path
        if self._tmpdir is None:
            self._tmpdir = tempfile.mkdtemp(prefix="IhxRC-sounds-")
        path = os.path.join(self._tmpdir, "%s.wav" % tone)
        samples = render_tone(TONES[tone])
        with wave.open(path, "wb") as fh:
            fh.setnchannels(1)
            fh.setsampwidth(2)
            fh.setframerate(SAMPLE_RATE)
            fh.writeframes(samples.tobytes())
        self._cache[tone] = path
        return path

    def _run(self):
        while True:
            try:
                item = self._queue.get(timeout=30)
            except queue.Empty:
                return
            try:
                if item[0] == "tone":
                    path = self._wav_path(item[1])
                    argv = [a.replace("{file}", path) for a in self.player_cmd]
                else:
                    argv = [a.replace("{title}", item[1]).replace("{body}", item[2])
                            for a in self.desktop_cmd]
                proc = subprocess.Popen(argv, stdin=subprocess.DEVNULL,
                                        stdout=subprocess.DEVNULL,
                                        stderr=subprocess.DEVNULL,
                                        start_new_session=True)
                try:
                    proc.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    proc.kill()
            except Exception as exc:  # a missing player must never kill the client
                self.last_error = "%s: %s" % (exc.__class__.__name__, exc)

    def close(self):
        if self._tmpdir:
            shutil.rmtree(self._tmpdir, ignore_errors=True)
            self._tmpdir = None
            self._cache.clear()

    # introspection

    def describe(self):
        out = [("Sounds: %s   player: %s"
                % ("on" if self.enabled else "off",
                   self.player_name or "none (terminal bell)"), "info")]
        for event in SOUND_EVENTS:
            out.append(("  %-11s %s" % (event, self.events.get(event, "off")), "text"))
        out.append(("Desktop notifications: %s (%s)"
                    % ("on" if self.desktop_enabled else "off",
                       self.desktop_name or "no notifier found"), "info"))
        out.append(("Active buffer also sounds: %s (/sound focus on|off)"
                    % ("yes" if self.focused else "no"), "info"))
        out.append(("Tones: %s" % ", ".join(SOUND_NAMES), "dim"))
        out.append(("/sound <event> <tone>, /sound test <tone>, "
                    "/sound player <cmd {file}>", "dim"))
        if self.last_error:
            out.append(("last player error: %s" % self.last_error, "error"))
        return out

    def as_config(self):
        cfg = {"enabled": self.enabled, "focused": self.focused}
        cfg.update(self.events)
        if self.player_cmd:
            cfg["player"] = " ".join(self.player_cmd)
        return cfg



# mouse

WHEEL_UP = curses.BUTTON4_PRESSED
WHEEL_DOWN = getattr(curses, "BUTTON5_PRESSED", 0x00200000)


def hit_region(mx, my, layout):
    #Which pane does a click at (mx, my) fall into
    h, w, side_w, nick_w, main_x, main_w = layout
    if my <= 0:
        return "title"
    if my >= h - 1:
        return "input"
    if my == h - 2:
        return "status"
    if side_w and mx < side_w:
        return "sidebar"
    if nick_w and mx >= w - nick_w:
        return "nicks"
    return "main"


HELP_SECTIONS = {
    "commands": [
        ("Commands", "info"),
        ("  /connect <host> [+port|port] [nick]   connect ('+' port = TLS, default +6697)", "text"),
        ("  /disconnect [reason] · /reconnect     drop or restart this connection", "text"),
        ("  /join #chan [key] · /part [reason]    channels", "text"),
        ("  /query <nick> · /msg <target> <text>  private messages", "text"),
        ("  /me <action> · /nick <newnick>        emote, change nick", "text"),
        ("  /topic [text] · /names · /whois <n>   channel & user info", "text"),
        ("  /close · /clear · /raw <line>         buffer & raw protocol", "text"),
        ("  /mouse · /sound · /notify · /save     preferences", "text"),
        ("  /quit [reason]", "text"),
        ("  Anything else after / is sent to the server as a raw command.", "dim"),
    ],
    "keys": [
        ("Keys", "info"),
        ("  Ctrl-N / Ctrl-P      next / previous buffer", "text"),
        ("  Alt-1 .. Alt-9       jump to buffer by number", "text"),
        ("  Alt-A                jump to next buffer with activity", "text"),
        ("  PgUp / PgDn          scroll the message pane", "text"),
        ("  Shift-PgUp / PgDn    scroll the user list", "text"),
        ("  Tab                  complete nick or command", "text"),
        ("  Up / Down            input history", "text"),
        ("  Ctrl-A/E/U/W/K       line editing (start/end/kill left/del word/kill right)", "text"),
        ("  Ctrl-L               redraw   ·   Alt-M   toggle the mouse", "text"),
    ],
    "mouse": [
        ("Mouse", "info"),
        ("  click a channel        switch to it", "text"),
        ("  right-click a channel  close it", "text"),
        ("  click a nick           put it in the input line", "text"),
        ("  right-click a nick     open a private query", "text"),
        ("  wheel                  scrolls messages, the sidebar or the user list,", "text"),
        ("                         depending on which pane the pointer is over", "dim"),
        ("  click the input line   move the cursor there", "text"),
        ("  click the status bar   jump to the next active buffer", "text"),
        ("  /mouse off (or Alt-M)  give text selection back to your terminal", "text"),
    ],
    "sound": [
        ("Notification sounds", "info"),
        ("  /sound                       show the current settings", "text"),
        ("  /sound on | off              master switch", "text"),
        ("  /sound highlight chime       set the tone for an event", "text"),
        ("  /sound test alert            hear a tone right now", "text"),
        ("  /sound focus on              also sound for the buffer you are reading", "text"),
        ("  /sound player <cmd {file}>   use a specific audio player", "text"),
        ("  /notify on                   desktop notifications on highlights", "text"),
        ("  /save                        remember these settings", "text"),
        ("  events: highlight, query, message, disconnect", "dim"),
    ],
}
HELP_TOPICS = list(HELP_SECTIONS)


class App:
    def __init__(self, screen, config):
        self.screen = screen
        self.config = config
        self.events = queue.Queue()
        self.servers = []
        self.running = True
        self.dirty = True

        self.client = Buffer(None, "IhxRC", kind="client")
        self.current = self.client
        self.client.msg("%s - type /help for commands, /connect to get started."
                        % VERSION, "info")

        self.input = ""
        self.cursor = 0
        self.history = []
        self.hist_index = None
        self.completion = None
        self.nick_offset = 0
        self.input_scroll = 0
        self.styles = {}

        self.sounds = SoundEngine(config.get("sound"))
        self.sounds.desktop_enabled = bool(config.get("desktop_notifications", False))
        self.mouse_enabled = False
        self.last_layout = (24, 80, 0, 0, 0, 80)
        self.sidebar_rows = []          # [(y, buffer)] as last drawn
        self.nick_rows = []             # [(y, nick)] as last drawn
        self.last_click = (0.0, -1, -1)

        self._setup_curses()
        self.set_mouse(config.get("mouse", True), announce=False)

    # curses plumbing

    def _setup_curses(self):
        curses.noecho()
        curses.cbreak()
        self.screen.keypad(True)
        try:
            curses.curs_set(1)
        except curses.error:
            pass
        self.screen.timeout(100)
        self.has_color = curses.has_colors()
        if self.has_color:
            curses.start_color()
            try:
                curses.use_default_colors()
                bg = -1
            except curses.error:
                bg = curses.COLOR_BLACK
            palette = [curses.COLOR_BLUE, curses.COLOR_GREEN, curses.COLOR_CYAN,
                       curses.COLOR_RED, curses.COLOR_MAGENTA, curses.COLOR_YELLOW,
                       curses.COLOR_WHITE]
            for i, color in enumerate(palette, start=1):
                try:
                    curses.init_pair(i, color, bg)
                except curses.error:
                    pass
            P = curses.color_pair
            self.styles = {
                "text": 0,
                "dim": curses.A_DIM,
                "info": P(3),
                "error": P(4) | curses.A_BOLD,
                "join": P(2),
                "part": P(4),
                "topic": P(5),
                "notice": P(6),
                "action": P(5),
                "highlight": P(6) | curses.A_BOLD,
                "self": P(7) | curses.A_BOLD,
                "mode": P(2) | curses.A_BOLD,
                "bar": curses.A_REVERSE,
                "sep": P(1),
                "active": P(3) | curses.A_BOLD,
                "unread": P(2) | curses.A_BOLD,
                "hl": P(4) | curses.A_BOLD,
                "server": P(3),
                "off": curses.A_DIM,
            }
            for i in range(6):
                self.styles["nick%d" % i] = P((i % 6) + 1)
        else:
            self.styles = {"bar": curses.A_REVERSE, "highlight": curses.A_BOLD,
                           "self": curses.A_BOLD, "error": curses.A_BOLD,
                           "dim": curses.A_DIM}

    def set_mouse(self, enable, announce=True):
        #Turn mouse reporting on or off (off gives the terminal its own
        #text selection back, which is why it is a toggle)
        try:
            if enable:
                mask = curses.ALL_MOUSE_EVENTS | WHEEL_UP | WHEEL_DOWN
                available, _ = curses.mousemask(mask)
                if not available:
                    if announce:
                        self.echo("This terminal does not report mouse events.", "error")
                    return False
                curses.mouseinterval(150)
                self._term_write("\x1b[?1006h")     # SGR mode: wide terminals + wheel
            else:
                curses.mousemask(0)
                self._term_write("\x1b[?1006l")
        except curses.error:
            if announce:
                self.echo("Mouse support is unavailable here.", "error")
            return False
        self.mouse_enabled = bool(enable)
        if announce:
            self.echo("Mouse %s." % ("enabled" if enable else "disabled"), "info")
        self.dirty = True
        return True

    @staticmethod
    def _term_write(text):
        try:
            os.write(sys.stdout.fileno(), text.encode("ascii"))
        except (OSError, ValueError):
            pass

    def style(self, name):
        return self.styles.get(name, 0)

    def addstr(self, y, x, text, attr=0, maxw=None):
        h, w = self.screen.getmaxyx()
        if y < 0 or y >= h or x >= w:
            return x
        limit = w - x if maxw is None else min(maxw, w - x)
        if limit <= 0:
            return x
        text = text[:limit]
        try:
            self.screen.addstr(y, x, text, attr)
        except curses.error:
            pass
        return x + len(text)

    # buffer navigation

    def buffer_list(self):
        out = [self.client]
        for srv in self.servers:
            out.extend(srv.all_buffers())
        return out

    def go_to(self, buf):
        if buf is None:
            return
        self.current = buf
        buf.unread = 0
        buf.highlight = False
        buf.scroll = 0
        self.nick_offset = 0
        self.dirty = True

    def cycle(self, delta):
        buffers = self.buffer_list()
        try:
            idx = buffers.index(self.current)
        except ValueError:
            idx = 0
        self.go_to(buffers[(idx + delta) % len(buffers)])

    def next_activity(self):
        buffers = self.buffer_list()
        try:
            start = buffers.index(self.current)
        except ValueError:
            start = 0
        for i in range(1, len(buffers) + 1):
            buf = buffers[(start + i) % len(buffers)]
            if buf.unread or buf.highlight:
                self.go_to(buf)
                return

    def notify(self, buf, highlight=False, level=1):
        #level 0 = joins/parts/modes: redraw, but do not mark the buffer unread
        self.dirty = True
        if buf is self.current:
            buf.unread = 0
            if highlight:
                self.sounds.play("highlight")
            elif level > 0 and self.sounds.focused:
                self.sounds.play("query" if buf.kind == "query" else "message")
            return
        if level > 0:
            buf.unread += 1
        if highlight:
            buf.highlight = True
            self.sounds.play("highlight")
            self.sounds.desktop("IhxRC: %s" % buf.name, "You were mentioned.")
        elif level > 0:
            if buf.kind == "query":
                self.sounds.play("query")
                self.sounds.desktop("IhxRC: %s" % buf.name, "New private message.")
            else:
                self.sounds.play("message")

    def on_new_buffer(self, buf):
        self.dirty = True

    # layout

    def layout(self):
        h, w = self.screen.getmaxyx()
        side_w = 0
        nick_w = 0
        if w >= 62:
            side_w = max(14, min(22, w // 5))
        if w >= 84 and self.current.kind == "channel":
            nick_w = max(12, min(18, w // 6))
        main_x = side_w + 1 if side_w else 0
        main_w = w - main_x - (nick_w + 1 if nick_w else 0)
        return h, w, side_w, nick_w, main_x, max(10, main_w)

    def draw(self):
        self.screen.erase()
        h, w, side_w, nick_w, main_x, main_w = self.layout()
        self.last_layout = (h, w, side_w, nick_w, main_x, main_w)
        top = 1
        bottom = h - 3          # last row of the panes
        if bottom < top:
            bottom = top

        self.draw_title(w)
        self.draw_sidebar(top, bottom, side_w)
        self.draw_messages(top, bottom, main_x, main_w)
        if nick_w:
            self.draw_nicklist(top, bottom, w - nick_w, nick_w)
        if side_w:
            for y in range(top, bottom + 1):
                self.addstr(y, side_w, "│", self.style("dim"))
        if nick_w:
            for y in range(top, bottom + 1):
                self.addstr(y, w - nick_w - 1, "│", self.style("dim"))
        self.draw_statusbar(h - 2, w)
        self.draw_input(h - 1, w)
        self.screen.refresh()

    def draw_title(self, w):
        buf = self.current
        if buf.kind == "channel":
            left = " %s" % buf.name
            if buf.topic:
                left += " — %s" % buf.topic
        elif buf.kind == "query":
            left = " Private message with %s" % buf.name
        elif buf.kind == "status":
            left = " %s (%s:%d)" % (buf.server.name, buf.server.host, buf.server.port)
        else:
            left = " %s" % VERSION
        self.addstr(0, 0, left.ljust(w), self.style("bar"))

    def draw_sidebar(self, top, bottom, width):
        self.sidebar_rows = []
        if not width:
            return
        rows = []
        rows.append((self.client, 0))
        for srv in self.servers:
            rows.append((srv.status, 0))
            for buf in srv.buffers.values():
                rows.append((buf, 1))
        # scroll the sidebar so the current buffer stays visible
        height = bottom - top + 1
        try:
            cur_i = [r[0] for r in rows].index(self.current)
        except ValueError:
            cur_i = 0
        start = 0
        if len(rows) > height:
            start = max(0, min(cur_i - height // 2, len(rows) - height))
        y = top
        for buf, depth in rows[start:start + height]:
            srv = buf.server
            if buf.kind == "client":
                label, attr = "IhxRC", self.style("server")
            elif buf.kind == "status":
                dot = "●" if srv.registered else ("◐" if srv.connected else "○")
                label = "%s %s" % (dot, srv.name)
                attr = self.style("server") if srv.registered else self.style("off")
            else:
                label = "  " + buf.name
                attr = 0 if buf.joined or buf.kind == "query" else self.style("off")
            if buf is self.current:
                attr = self.style("active") | curses.A_REVERSE
            elif buf.highlight:
                attr = self.style("hl")
            elif buf.unread:
                attr = self.style("unread")
            badge = ""
            if buf is not self.current and buf.unread:
                badge = " %d" % min(buf.unread, 999)
            text = label[:max(1, width - len(badge))]
            line = (text + badge).ljust(width)
            self.addstr(y, 0, line, attr, maxw=width)
            self.sidebar_rows.append((y, buf))
            y += 1

    def render_lines(self, buf, width):
        out = []
        for ts, segments, kind in buf.lines:
            stamp = time.strftime("%H:%M ", time.localtime(ts))
            head = [(stamp, "dim")]
            for line in wrap_segments(head + list(segments), width, indent=len(stamp)):
                out.append(line)
        return out

    def draw_messages(self, top, bottom, x, width):
        buf = self.current
        height = bottom - top + 1
        lines = self.render_lines(buf, width)
        max_scroll = max(0, len(lines) - height)
        buf.scroll = max(0, min(buf.scroll, max_scroll))
        end = len(lines) - buf.scroll
        view = lines[max(0, end - height):end]
        y = top + max(0, height - len(view))
        for line in view:
            cx = x
            for text, style in line:
                cx = self.addstr(y, cx, text, self.style(style), maxw=x + width - cx)
                if cx >= x + width:
                    break
            y += 1
        if buf.scroll:
            note = " -- scrolled %d lines, PgDn to return -- " % buf.scroll
            self.addstr(bottom, x + max(0, (width - len(note)) // 2), note[:width],
                        self.style("error"))

    def draw_nicklist(self, top, bottom, x, width):
        self.nick_rows = []
        buf = self.current
        srv = buf.server
        users = srv.sorted_users(buf)
        height = bottom - top + 1
        header = "Users %d" % len(users)
        self.addstr(top, x, header.ljust(width), self.style("bar"), maxw=width)
        space = max(0, height - 1)
        self.nick_offset = max(0, min(self.nick_offset, max(0, len(users) - space)))
        overflow = len(users) - self.nick_offset > space
        room = space - 1 if overflow else space
        shown = users[self.nick_offset:self.nick_offset + room]
        y = top + 1
        for nick, prefix in shown:
            sym = prefix[:1]
            attr = self.style("mode") if sym else 0
            if srv.is_me(nick):
                attr = self.style("self")
            self.addstr(y, x, sym, self.style("mode"), maxw=width)
            self.addstr(y, x + len(sym), nick[:width - len(sym)], attr,
                        maxw=width - len(sym))
            self.nick_rows.append((y, nick))
            y += 1
        if overflow:
            hidden = len(users) - self.nick_offset - room
            self.addstr(y, x, "+%d more" % hidden, self.style("dim"), maxw=width)

    def draw_statusbar(self, y, w):
        buf = self.current
        srv = buf.server
        parts = []
        if srv:
            parts.append(srv.nick)
            if not srv.connected:
                parts.append("disconnected")
        else:
            parts.append("no server")
        parts.append(buf.name)
        if buf.kind == "channel":
            parts.append("%d users" % len(buf.users))
        act = []
        for i, b in enumerate(self.buffer_list(), start=1):
            if b is not buf and (b.unread or b.highlight):
                act.append("%d:%s%s" % (i, b.name, "*" if b.highlight else ""))
        left = " " + " | ".join(parts)
        right = ("act: " + ",".join(act[:6]) + " ") if act else " "
        line = left + " " * max(1, w - len(left) - len(right)) + right
        self.addstr(y, 0, line[:w].ljust(w), self.style("bar"))

    def input_prompt(self):
        buf = self.current
        _, w = self.screen.getmaxyx()
        prompt = "[%s] " % (buf.name if buf.kind != "client" else "IhxRC")
        return prompt[:max(4, w // 3)]

    def draw_input(self, y, w):
        prompt = self.input_prompt()
        avail = w - len(prompt) - 1
        start = 0
        if self.cursor > avail:
            start = self.cursor - avail
        self.input_scroll = start
        text = self.input[start:start + avail]
        self.addstr(y, 0, prompt, self.style("info"))
        self.addstr(y, len(prompt), text.ljust(avail))
        try:
            self.screen.move(y, min(w - 1, len(prompt) + self.cursor - start))
        except curses.error:
            pass

    # input handling

    def run(self):
        while self.running:
            self.pump_events()
            now = time.time()
            for srv in self.servers:
                srv.tick(now)
            if self.dirty:
                try:
                    self.draw()
                except curses.error:
                    pass
                self.dirty = False
            self.read_key()

    def pump_events(self):
        while True:
            try:
                srv, kind, payload = self.events.get_nowait()
            except queue.Empty:
                return
            self.dirty = True
            if kind == "line":
                try:
                    srv.handle(payload)
                except Exception as exc:  # keep the client alive on odd input
                    srv.status.msg("internal error handling %s: %s"
                                   % (payload.command, exc), "error")
            elif kind == "info":
                srv.status.msg(payload, "info")
            elif kind == "connected":
                srv.status.msg("Connected. Registering...", "info")
            elif kind == "disconnected":
                srv.status.msg("Disconnected: %s" % payload, "error")
                if not srv.stopping:
                    self.sounds.play("disconnect")
                for buf in srv.buffers.values():
                    buf.joined = False
                    buf.users.clear()
                if srv.auto_reconnect and not srv.stopping:
                    srv.reconnect_at = time.time() + RECONNECT_DELAY
                    srv.status.msg("Reconnecting in %d seconds (/reconnect to hurry)."
                                   % RECONNECT_DELAY, "dim")
            elif kind == "error":
                srv.status.msg(payload, "error")

    def read_key(self):
        try:
            key = self.screen.get_wch()
        except curses.error:
            return
        except KeyboardInterrupt:
            self.quit("Interrupted")
            return
        self.dirty = True
        if key == "\x1b":                     # ESC: alt-combo or bare escape
            self.handle_escape()
            return
        if isinstance(key, int):
            self.handle_special(key)
            return
        self.handle_char(key)

    def handle_escape(self):
        self.screen.nodelay(True)
        try:
            nxt = self.screen.get_wch()
        except (curses.error, ValueError):
            nxt = None
        finally:
            self.screen.nodelay(False)
            self.screen.timeout(100)
        if isinstance(nxt, str) and nxt.isdigit() and nxt != "0":
            buffers = self.buffer_list()
            idx = int(nxt) - 1
            if idx < len(buffers):
                self.go_to(buffers[idx])
        elif isinstance(nxt, str) and nxt.lower() == "a":
            self.next_activity()
        elif isinstance(nxt, str) and nxt.lower() == "m":
            self.set_mouse(not self.mouse_enabled)
        elif nxt in (curses.KEY_LEFT, "\x1b[D"):
            self.cycle(-1)
        elif nxt == curses.KEY_RIGHT:
            self.cycle(1)

    def handle_special(self, key):
        buf = self.current
        if key in (curses.KEY_ENTER,):
            self.submit()
        elif key == curses.KEY_BACKSPACE:
            self.backspace()
        elif key == curses.KEY_DC:
            self.input = self.input[:self.cursor] + self.input[self.cursor + 1:]
        elif key == curses.KEY_LEFT:
            self.cursor = max(0, self.cursor - 1)
        elif key == curses.KEY_RIGHT:
            self.cursor = min(len(self.input), self.cursor + 1)
        elif key == curses.KEY_HOME:
            self.cursor = 0
        elif key == curses.KEY_END:
            self.cursor = len(self.input)
        elif key == curses.KEY_UP:
            self.history_move(-1)
        elif key == curses.KEY_DOWN:
            self.history_move(1)
        elif key == curses.KEY_PPAGE:
            buf.scroll += max(1, (self.screen.getmaxyx()[0] - 5) // 2)
        elif key == curses.KEY_NPAGE:
            buf.scroll = max(0, buf.scroll - max(1, (self.screen.getmaxyx()[0] - 5) // 2))
        elif key == curses.KEY_MOUSE:
            self.handle_mouse()
        elif key == curses.KEY_RESIZE:
            pass
        elif key == curses.KEY_SPREVIOUS:
            self.nick_offset = max(0, self.nick_offset - 5)
        elif key == curses.KEY_SNEXT:
            self.nick_offset += 5
        elif key == curses.KEY_SLEFT:
            self.cycle(-1)
        elif key == curses.KEY_SRIGHT:
            self.cycle(1)

    def handle_char(self, ch):
        if ch in ("\n", "\r"):
            self.submit()
        elif ch in ("\x7f", "\x08"):
            self.backspace()
        elif ch == "\t":
            self.complete()
            return
        elif ch == CTRL["n"]:
            self.cycle(1)
        elif ch == CTRL["p"]:
            self.cycle(-1)
        elif ch == CTRL["a"]:
            self.cursor = 0
        elif ch == CTRL["e"]:
            self.cursor = len(self.input)
        elif ch == CTRL["u"]:
            self.input = self.input[self.cursor:]
            self.cursor = 0
        elif ch == CTRL["k"]:
            self.input = self.input[:self.cursor]
        elif ch == CTRL["w"]:
            head = self.input[:self.cursor].rstrip()
            cut = head.rfind(" ") + 1
            self.input = self.input[:cut] + self.input[self.cursor:]
            self.cursor = cut
        elif ch == CTRL["l"]:
            self.screen.clearok(True)
        elif ch == CTRL["c"]:
            self.quit("Interrupted")
        elif ch >= " ":
            self.input = self.input[:self.cursor] + ch + self.input[self.cursor:]
            self.cursor += len(ch)
        self.completion = None

    # mouse 

    def handle_mouse(self):
        try:
            _, mx, my, _, bstate = curses.getmouse()   # drain the event either way
        except curses.error:
            return
        if not self.mouse_enabled:
            return
        region = hit_region(mx, my, self.last_layout)

        if bstate & WHEEL_UP:
            self.scroll_region(region, -1)
            return
        if bstate & WHEEL_DOWN:
            self.scroll_region(region, 1)
            return

        right = bool(bstate & (curses.BUTTON3_CLICKED | curses.BUTTON3_PRESSED))
        left = bool(bstate & (curses.BUTTON1_CLICKED | curses.BUTTON1_PRESSED))
        if not (left or right):
            return
        # ncurses can report press and click for the same physical action
        now = time.time()
        last_t, last_x, last_y = self.last_click
        if now - last_t < 0.12 and (mx, my) == (last_x, last_y):
            return
        self.last_click = (now, mx, my)

        if region == "sidebar":
            buf = dict((y, b) for y, b in self.sidebar_rows).get(my)
            if buf is None:
                return
            if right and buf.kind in ("channel", "query"):
                self.go_to(buf)
                self.cmd_close("")
            else:
                self.go_to(buf)
        elif region == "nicks":
            nick = dict((y, n) for y, n in self.nick_rows).get(my)
            if nick is None:
                return
            if right:
                self.cmd_query(nick)
            else:
                self.insert_text(nick)
        elif region == "input":
            prompt = len(self.input_prompt())
            self.cursor = max(0, min(len(self.input), mx - prompt + self.input_scroll))
        elif region == "status":
            self.next_activity()
        elif region == "title" and self.current.kind == "channel":
            self.current.scroll = 0

    def scroll_region(self, region, direction):
        if region == "sidebar":
            self.cycle(direction)
        elif region == "nicks":
            self.nick_offset = max(0, self.nick_offset + 3 * direction)
        else:
            step = 3
            if direction < 0:
                self.current.scroll += step
            else:
                self.current.scroll = max(0, self.current.scroll - step)
        self.dirty = True

    def insert_text(self, text):
        before = self.input[:self.cursor]
        if not before.strip():
            addition = text + ": "
        elif before.endswith(" "):
            addition = text + " "
        else:
            addition = " " + text + " "
        self.input = before + addition + self.input[self.cursor:]
        self.cursor += len(addition)
        self.dirty = True

    def backspace(self):
        if self.cursor > 0:
            self.input = self.input[:self.cursor - 1] + self.input[self.cursor:]
            self.cursor -= 1

    def history_move(self, delta):
        if not self.history:
            return
        if self.hist_index is None:
            if delta > 0:
                return
            self.hist_index = len(self.history)
        self.hist_index = max(0, min(len(self.history), self.hist_index + delta))
        if self.hist_index >= len(self.history):
            self.input = ""
            self.hist_index = None
        else:
            self.input = self.history[self.hist_index]
        self.cursor = len(self.input)

    def complete(self):
        head = self.input[:self.cursor]
        match = re.search(r"[^\s]*$", head)
        word = match.group(0)
        prefix_start = match.start()
        if not word:
            return
        buf = self.current
        if word.startswith("/") and prefix_start == 0:
            pool = ["/" + c for c in COMMANDS]
        elif buf.kind == "channel":
            pool = [nick for nick, _ in buf.server.sorted_users(buf)]
        elif buf.kind == "query":
            pool = [buf.name]
        else:
            pool = []
        options = [c for c in pool if lower(c).startswith(lower(word))]
        if not options:
            return
        if self.completion and self.completion[0] == (prefix_start, word):
            idx = (self.completion[1] + 1) % len(options)
        else:
            idx = 0
        choice = options[idx]
        suffix = ": " if (prefix_start == 0 and not choice.startswith("/")) else " "
        self.input = self.input[:prefix_start] + choice + suffix + self.input[self.cursor:]
        self.cursor = prefix_start + len(choice) + len(suffix)
        self.completion = ((prefix_start, word), idx)

    # commands

    def submit(self):
        text = self.input
        self.input = ""
        self.cursor = 0
        self.hist_index = None
        if not text.strip():
            return
        if not self.history or self.history[-1] != text:
            self.history.append(text)
            del self.history[:-200]
        if text.startswith("//"):
            self.say(text[1:])
        elif text.startswith("/"):
            cmd, _, args = text[1:].partition(" ")
            self.command(cmd.lower(), args.strip())
        else:
            self.say(text)

    def say(self, text):
        buf = self.current
        srv = buf.server
        if buf.kind in ("client", "status") or srv is None:
            self.echo("This buffer is not a conversation. Use /join or /query.", "error")
            return
        if not srv.registered:
            self.echo("Not connected.", "error")
            return
        srv.privmsg(buf.name, text)
        srv._show(Message({}, srv.nick, "PRIVMSG", [buf.name, text], ""),
                  buf.name, srv.nick, text)

    def echo(self, text, style="info"):
        self.current.msg(text, style)
        self.dirty = True

    def command(self, cmd, args):
        buf = self.current
        srv = buf.server
        fn = getattr(self, "cmd_" + cmd, None)
        if fn:
            fn(args)
            return
        alias = COMMAND_ALIASES.get(cmd)
        if alias:
            getattr(self, "cmd_" + alias)(args)
            return
        if srv and srv.connected:
            srv.send("%s %s" % (cmd.upper(), args) if args else cmd.upper())
        else:
            self.echo("Unknown command /%s (and no server to send it to)." % cmd, "error")

    # individual commands

    def cmd_help(self, args):
        topic = args.strip().lower()
        if topic == "all":
            sections = HELP_TOPICS
        elif topic in HELP_SECTIONS:
            sections = [topic]
        else:
            if topic:
                self.current.msg("No help topic %r." % topic, "error")
            sections = ["commands"]
        for name in sections:
            for text, style in HELP_SECTIONS[name]:
                self.current.msg(text, style)
        if sections == ["commands"]:
            self.current.msg("More: /help keys · /help mouse · /help sound · /help all",
                             "dim")
        self.dirty = True

    def cmd_connect(self, args):
        parts = args.split()
        if not parts:
            self.echo("Usage: /connect <host> [+port|port] [nick]", "error")
            return
        host = parts[0]
        port, tls = None, True
        if ":" in host and not host.startswith("["):
            host, _, maybe = host.partition(":")
            parts.insert(1, maybe)
        rest = parts[1:]
        nick = self.config.get("nick", "IhxRC")
        if rest and (rest[0].isdigit() or rest[0].startswith("+")):
            token = rest.pop(0)
            tls = token.startswith("+")
            port = int(token.lstrip("+"))
        if rest:
            nick = rest.pop(0)
        if port is None:
            port = 6697 if tls else 6667
        self.add_server({"host": host, "port": port, "tls": tls, "nick": nick})

    def add_server(self, spec):
        cfg = dict(self.config)
        cfg.update(spec)
        cfg.pop("_path", None)
        srv = Server(
            self.events, cfg["host"], cfg.get("port", 6697), cfg.get("tls", True),
            nick=cfg.get("nick", "IhxRC"), user=cfg.get("user"),
            realname=cfg.get("realname"), password=cfg.get("password"),
            sasl_user=cfg.get("sasl_user"), sasl_pass=cfg.get("sasl_pass"),
            channels=cfg.get("channels", []), name=cfg.get("name"),
            verify=cfg.get("verify", True), app=self)
        self.servers.append(srv)
        srv.start()
        self.go_to(srv.status)
        return srv

    def cmd_disconnect(self, args):
        srv = self.current.server
        if not srv:
            self.echo("No server for this buffer.", "error")
            return
        srv.disconnect(args or "Leaving", auto=False)

    def cmd_reconnect(self, args):
        srv = self.current.server
        if not srv:
            self.echo("No server for this buffer.", "error")
            return
        if srv.connected:
            srv.disconnect("Reconnecting", auto=True)
        srv.auto_reconnect = True
        srv.stopping = False
        srv.reconnect_at = time.time() + 1

    def cmd_join(self, args):
        srv = self.current.server
        if not (srv and srv.registered):
            self.echo("Not connected.", "error")
            return
        if not args:
            self.echo("Usage: /join #channel [key]", "error")
            return
        chans = args.split()
        name = chans[0]
        if name[:1] not in srv.chantypes:
            name = "#" + name
            chans[0] = name
        srv.send("JOIN " + " ".join(chans))

    def cmd_part(self, args):
        buf = self.current
        srv = buf.server
        if not srv or buf.kind not in ("channel", "query"):
            self.echo("Not in a channel.", "error")
            return
        if buf.kind == "query":
            self.cmd_close("")
            return
        srv.send("PART %s :%s" % (buf.name, args or "Leaving"))

    def cmd_close(self, args):
        buf = self.current
        srv = buf.server
        if buf.kind in ("client", "status"):
            if buf.kind == "status" and srv:
                srv.disconnect("Leaving", auto=False)
                self.servers.remove(srv)
                self.go_to(self.client)
            else:
                self.echo("Cannot close this buffer.", "error")
            return
        if buf.kind == "channel" and buf.joined and srv.connected:
            srv.send("PART %s :Leaving" % buf.name)
        self.cycle(-1)
        srv.close_buffer(buf)

    def cmd_query(self, args):
        srv = self.current.server
        if not srv:
            self.echo("No server for this buffer.", "error")
            return
        target, _, text = args.partition(" ")
        if not target:
            self.echo("Usage: /query <nick> [message]", "error")
            return
        buf = srv.buffer(target, "query")
        self.go_to(buf)
        if text.strip():
            self.say(text.strip())

    def cmd_msg(self, args):
        srv = self.current.server
        target, _, text = args.partition(" ")
        if not (srv and srv.registered) or not target or not text.strip():
            self.echo("Usage: /msg <target> <message>", "error")
            return
        srv.privmsg(target, text)
        srv._show(Message({}, srv.nick, "PRIVMSG", [target, text], ""),
                  target, srv.nick, text)

    def cmd_me(self, args):
        buf = self.current
        srv = buf.server
        if not (srv and srv.registered) or buf.kind not in ("channel", "query"):
            self.echo("Usage: /me <action> (in a channel or query)", "error")
            return
        srv.privmsg(buf.name, "\x01ACTION %s\x01" % args)
        buf.add([("* ", "action"), (srv.nick, "action"), (" ", "action"),
                 (args, "action")], "action")

    def cmd_nick(self, args):
        srv = self.current.server
        if not (srv and srv.connected) or not args:
            self.echo("Usage: /nick <newnick>", "error")
            return
        srv.send("NICK %s" % args.split()[0])

    def cmd_topic(self, args):
        buf = self.current
        srv = buf.server
        if not (srv and buf.kind == "channel"):
            self.echo("Not in a channel.", "error")
            return
        if args:
            srv.send("TOPIC %s :%s" % (buf.name, args))
        else:
            self.echo("Topic: %s" % (buf.topic or "(none)"), "topic")

    def cmd_names(self, args):
        buf = self.current
        srv = buf.server
        if srv and buf.kind == "channel":
            srv.send("NAMES %s" % buf.name)

    def cmd_whois(self, args):
        srv = self.current.server
        if srv and args:
            srv.send("WHOIS %s" % args)

    def cmd_away(self, args):
        srv = self.current.server
        if srv:
            srv.send("AWAY :%s" % args if args else "AWAY")

    def cmd_raw(self, args):
        srv = self.current.server
        if srv and srv.connected and args:
            srv.send(args)
        else:
            self.echo("Usage: /raw <raw irc line> (needs a connection)", "error")

    def cmd_clear(self, args):
        self.current.lines.clear()
        self.current.scroll = 0

    def cmd_buffer(self, args):
        buffers = self.buffer_list()
        if args.isdigit():
            idx = int(args) - 1
            if 0 <= idx < len(buffers):
                self.go_to(buffers[idx])
            return
        for buf in buffers:
            if lower(buf.name).startswith(lower(args)):
                self.go_to(buf)
                return

    def cmd_mouse(self, args):
        arg = args.strip().lower()
        if arg in ("on", "yes", "1"):
            self.set_mouse(True)
        elif arg in ("off", "no", "0"):
            self.set_mouse(False)
        elif not arg:
            self.set_mouse(not self.mouse_enabled)
        else:
            self.echo("Usage: /mouse [on|off]", "error")

    def cmd_sound(self, args):
        parts = args.split()
        if not parts:
            for text, style in self.sounds.describe():
                self.current.msg(text, style)
            self.dirty = True
            return
        word = parts[0].lower()
        rest = parts[1:]
        if word in ("on", "off"):
            self.sounds.enabled = (word == "on")
            self.echo("Notification sounds %s." % word, "info")
            return
        if word == "focus":
            if rest and rest[0].lower() in ("on", "off"):
                self.sounds.focused = rest[0].lower() == "on"
            self.echo("Sounds for the buffer you are reading: %s."
                      % ("on" if self.sounds.focused else "off"), "info")
            return
        if word == "test":
            tone = rest[0].lower() if rest else self.sounds.events["highlight"]
            if tone not in SOUND_NAMES:
                self.echo("Unknown tone %r. Try: %s" % (tone, ", ".join(SOUND_NAMES)),
                          "error")
                return
            self.sounds.play(tone, force=True)
            self.echo("Playing %s via %s." % (tone, self.sounds.player_name
                                              or "the terminal bell"), "info")
            return
        if word == "player":
            command = " ".join(rest)
            if not command:
                self.echo("Player: %s" % (self.sounds.player_name or "none"), "info")
            elif self.sounds.set_player(command):
                self.echo("Player set to: %s" % command, "info")
            else:
                self.echo("The player command must contain {file}, e.g. "
                          "/sound player aplay -q {file}", "error")
            return
        if word in SOUND_EVENTS:
            if not rest:
                self.echo("%s: %s" % (word, self.sounds.events[word]), "info")
                return
            tone = rest[0].lower()
            if tone not in SOUND_NAMES:
                self.echo("Unknown tone %r. Try: %s" % (tone, ", ".join(SOUND_NAMES)),
                          "error")
                return
            self.sounds.events[word] = tone
            self.echo("%s -> %s" % (word, tone), "info")
            if tone != "off":
                self.sounds.play(tone, force=True)
            return
        self.echo("Usage: /sound [on|off] | <%s> <tone> | focus on|off | "
                  "test <tone> | player <cmd>" % "|".join(SOUND_EVENTS), "error")

    def cmd_notify(self, args):
        arg = args.strip().lower()
        if not self.sounds.desktop_cmd:
            self.echo("No desktop notifier found (looked for %s)."
                      % ", ".join(n for n, _ in NOTIFIERS), "error")
            return
        if arg in ("on", "yes", "1"):
            self.sounds.desktop_enabled = True
        elif arg in ("off", "no", "0"):
            self.sounds.desktop_enabled = False
        elif not arg:
            self.sounds.desktop_enabled = not self.sounds.desktop_enabled
        else:
            self.echo("Usage: /notify [on|off]", "error")
            return
        state = "on" if self.sounds.desktop_enabled else "off"
        self.echo("Desktop notifications %s (%s)." % (state, self.sounds.desktop_name),
                  "info")
        if self.sounds.desktop_enabled:
            self.sounds.desktop("IhxRC", "Desktop notifications are on.")

    def cmd_save(self, args):
        #Write the current sound/mouse preferences back to the config file
        path = self.config.get("_path") or DEFAULT_CONFIG
        data = load_config(path)
        data.setdefault("nick", self.config.get("nick", "IhxRC"))
        data["mouse"] = self.mouse_enabled
        data["sound"] = self.sounds.as_config()
        data["desktop_notifications"] = self.sounds.desktop_enabled
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as fh:
                json.dump(data, fh, indent=2)
                fh.write("\n")
            self.echo("Saved settings to %s" % path, "info")
        except OSError as exc:
            self.echo("Could not save %s: %s" % (path, exc), "error")

    def cmd_next(self, args):
        self.cycle(1)

    def cmd_prev(self, args):
        self.cycle(-1)

    def cmd_quit(self, args):
        self.quit(args or "%s - bye" % VERSION)

    def quit(self, reason):
        for srv in self.servers:
            srv.disconnect(reason, auto=False)
        if self.mouse_enabled:
            self.set_mouse(False, announce=False)
        self.sounds.close()
        self.running = False


COMMANDS = ["help", "connect", "disconnect", "reconnect", "join", "part", "close",
            "query", "msg", "me", "nick", "topic", "names", "whois", "away", "raw",
            "clear", "buffer", "next", "prev", "mouse", "sound", "notify", "save",
            "quit"]
COMMAND_ALIASES = {"j": "join", "server": "connect", "q": "query", "quote": "raw",
                   "leave": "part", "wc": "close", "exit": "quit", "m": "msg"}


# entry point

DEFAULT_CONFIG = os.path.expanduser("~/.config/IhxRC/config.json")


def load_config(path=None):
    path = path or DEFAULT_CONFIG
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as fh:
                return json.load(fh)
        except (OSError, ValueError) as exc:
            print("Ignoring bad config %s: %s" % (path, exc), file=sys.stderr)
    return {}


def main(argv=None):
    ap = argparse.ArgumentParser(description="a small terminal IRC client")
    ap.add_argument("host", nargs="?", help="server to connect to on startup")
    ap.add_argument("-p", "--port", type=int, default=None)
    ap.add_argument("-n", "--nick", default=None)
    ap.add_argument("-c", "--channels", default=None,
                    help="comma separated list of channels to join")
    ap.add_argument("--no-tls", action="store_true", help="plaintext connection")
    ap.add_argument("--no-verify", action="store_true",
                    help="do not verify the TLS certificate")
    ap.add_argument("--password", default=None, help="server password (PASS)")
    ap.add_argument("--sasl-user", default=None)
    ap.add_argument("--sasl-pass", default=None)
    ap.add_argument("--config", default=None, help="path to a JSON config file")
    ap.add_argument("--no-mouse", action="store_true", help="start with the mouse off")
    ap.add_argument("--no-sound", action="store_true",
                    help="start with notification sounds off")
    args = ap.parse_args(argv)

    config = load_config(args.config)
    config["_path"] = args.config or DEFAULT_CONFIG
    config.setdefault("nick", os.environ.get("USER") or "IhxRC")
    config.setdefault("realname", config["nick"])
    if args.nick:
        config["nick"] = args.nick
    if args.no_mouse:
        config["mouse"] = False
    if args.no_sound:
        config.setdefault("sound", {})
        if isinstance(config["sound"], dict):
            config["sound"]["enabled"] = False

    startup = list(config.get("servers", []))
    if args.host:
        tls = not args.no_tls
        startup = [{
            "host": args.host,
            "port": args.port or (6667 if args.no_tls else 6697),
            "tls": tls,
            "verify": not args.no_verify,
            "nick": config["nick"],
            "password": args.password,
            "sasl_user": args.sasl_user,
            "sasl_pass": args.sasl_pass,
            "channels": [c.strip() for c in (args.channels or "").split(",") if c.strip()],
        }]

    def run(screen):
        app = App(screen, config)
        try:
            for spec in startup:
                app.add_server(spec)
            if app.servers:
                app.go_to(app.servers[0].status)
            app.run()
        finally:
            # never leave the terminal stuck in mouse-reporting mode, and never
            # leave synthesised wav files behind, however we got here
            try:
                app.set_mouse(False, announce=False)
            except Exception:
                pass
            app.sounds.close()

    try:
        curses.wrapper(run)
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
