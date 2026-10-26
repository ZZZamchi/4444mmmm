#!/usr/bin/env python3
"""Print miniF2F formal statements by name: mf_show.py NAME..."""

import json
import sys
from pathlib import Path

sys.stdout.reconfigure(encoding="utf-8")
RAW = Path(__file__).resolve().parents[2] / "data" / "real" / "raw" / "minif2f" / "minif2f.jsonl"
names = set(sys.argv[1:])
for line in RAW.read_text(encoding="utf-8").splitlines():
    r = json.loads(line)
    if r["name"] in names:
        print("--", r["name"], r["split"])
        print(r["formal_statement"])
