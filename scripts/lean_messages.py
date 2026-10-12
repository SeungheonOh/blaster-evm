#!/usr/bin/env python3
"""Summarise `lean --json` output: one line per message (line:col, severity, first line)."""
import json
import sys

for ln in sys.stdin:
    try:
        m = json.loads(ln)
    except ValueError:
        continue
    text = m["data"].strip().split("\n")[0][:150]
    if "blasterProven" in text:
        continue
    pos = m["pos"]
    print(f"{pos['line']}:{pos['column']}\t{m['severity']}\t{text}", flush=True)
