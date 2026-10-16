# IhxRC

A small, self-contained terminal IRC client written in Python. 

It uses only the standard library — no external dependencies, no package installs, no plugin system. Just a single script that talks to IRC over TLS and gives you a usable TUI with mouse support, notification sounds, and a handful of quality-of-life features.

### Requirements

* Python 3.7 or newer (uses curses, ssl, wave, and f-strings are not used, so even older 3.x works).

* A terminal with curses support. On Windows, use Windows Terminal with WSL, or Python from python.org (which bundles curses via the windows-curses package — install it with pip install windows-curses).

Optional, for sound and desktop notifications:

* One of paplay, pw-play, afplay, aplay, play, ffplay, cvlc, or powershell.exe on your PATH.

* One of notify-send, terminal-notifier, or kdialog on your PATH. 

### Quick start

```bash
chmod +x IhxRC.py
./IhxRC.py
```

Connect to a network and join a channel:

```bash
./IhxRC.py irc.libera.chat -n yournick -c "#python,#libera"
```

Connect to a plaintext server on a non-standard port:

```bash
./IhxRC.py irc.example.net -p 6667 --no-tls -n yournick
```
