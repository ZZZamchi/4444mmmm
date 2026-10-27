#!/usr/bin/env python3
"""Print flagged G3 probes present in g3_results_<NEW>.json but not in g3_results_<OLD>.json."""

import json
import sys
from pathlib import Path

sys.stdout.reconfigure(encoding="utf-8")
ROOT = Path(__file__).resolve().parents[2] / "data" / "real"
old, new = sys.argv[1], sys.argv[2]
load = lambda d: {p["key"]: p for p in json.loads((ROOT / f"g3_results_{d}.json").read_text(encoding="utf-8"))["probes"]
                  if p["flag"] in ("implied", "idle")}
O, N = load(old), load(new)
for k in sorted(set(N) - set(O)):
    p = N[k]
    print(f"### {k} [{p['flag']}]\nNL: {p['nl'][:400]}\nSTMT: {p['statement'][:600]}\nHYP: {p['hyp_goal'][:300]}\n")
print("dropped:", sorted(set(O) - set(N)))
