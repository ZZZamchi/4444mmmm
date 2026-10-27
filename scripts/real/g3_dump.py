#!/usr/bin/env python3
"""Dump flagged G3 probes for manual audit: g3_dump.py DATASET_SUFFIX (e.g. minif2f, putnam)."""

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2] / "data" / "real"
d = sys.argv[1]
R = json.loads((ROOT / f"g3_results_{d}.json").read_text(encoding="utf-8"))
fl = [p for p in R["probes"] if p["flag"] in ("implied", "idle")]
with open(ROOT / f"g3_flags_{d}.txt", "w", encoding="utf-8") as f:
    for p in fl:
        f.write(f"### {p['key']} [{p['flag']}]\nNL: {p['nl'][:600]}\nSTMT: {p['statement'][:700]}\n"
                f"HYP: {p['hyp_goal'][:400]}\n\n")
print(d, len(fl), len({p["stmt_id"] for p in fl}))
