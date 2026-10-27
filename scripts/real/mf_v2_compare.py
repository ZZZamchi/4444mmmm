#!/usr/bin/env python3
"""Show the miniF2F-v2s / v2c formal statements for given problem names: mf_v2_compare.py NAME..."""

import json
import sys
from pathlib import Path

sys.stdout.reconfigure(encoding="utf-8")
D = Path(__file__).resolve().parents[2] / "data" / "real" / "raw" / "minif2f_v2" / "datasets"
names = set(sys.argv[1:])
for ver in ("v2s", "v2c"):
    for line in (D / f"miniF2F_{ver}.jsonl").read_text(encoding="utf-8").splitlines():
        r = json.loads(line)
        if r["name"] in names:
            stmt = next((v for k, v in r.items() if "formal" in k and "informal" not in k), None)
            print(f"-- {ver} {r['name']}\n{stmt}\n")
