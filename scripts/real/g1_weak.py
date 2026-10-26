#!/usr/bin/env python3
"""G1 with a weaker proposer on both sides, for the sensitivity analysis.

Component side: the G1 pipeline with MODEL. Closed side: the F2 tiers, whose LLM tier
already used deepseek-v4.1-flash, so no closed proofs are re-run.

Usage: g1_weak.py [MODEL]          Writes data/real/g1_results_<model>.json.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import g1_full as g1
import runner

LEAN_WORKERS = 2
g1.MODEL = sys.argv[1] if len(sys.argv) > 1 else "deepseek/deepseek-v4.1-flash"
g1.OUT = runner.ROOT / "data" / "real" / f"g1_results_{g1.MODEL.split('/')[-1]}.json"
g1.check = lambda items, batch_size=10, workers=LEAN_WORKERS: runner.check(items, batch_size=batch_size, workers=LEAN_WORKERS)


def closed_from_f2(pairs, t0) -> dict:
    tiers = {p["row_id"]: set(p["t2"]) for p in json.loads(f2.OUT.read_text(encoding="utf-8"))["pairs"]}
    return {r.row_id: tiers[r.row_id] for r, _, _ in pairs}


g1.closed = closed_from_f2

if __name__ == "__main__":
    g1.main()
