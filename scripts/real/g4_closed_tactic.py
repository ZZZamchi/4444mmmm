#!/usr/bin/env python3
"""Patch `closed_tactic` (closed-side tactic tier t0/t1, no LLM) into an existing G4 results file.

Usage: g4_closed_tactic.py [RESULTS_JSON]   default data/real/g4_results.json
"""

from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

os.environ["G4_TACTIC_ONLY"] = "1"
import g4_pnv as g4  # noqa: E402

FILE = Path(sys.argv[1]) if len(sys.argv) > 1 else g4.OUT


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    rows, _ = g4.load()
    res = json.loads(FILE.read_text(encoding="utf-8"))
    keep = {p["row_id"] for p in res["pairs"]}
    pairs = [x for x in g4.usable([r for r in rows if r.row_id in keep])[0]]
    print("pairs", len(pairs), flush=True)
    proved = g4.closed(pairs, t0)
    for p in res["pairs"]:
        p["closed_tactic"] = sorted(proved.get(p["row_id"], ()))
        if "beq_plus" in p and p["beq_plus"] is None:
            del p["beq_plus"]
    res["table"] = {k: v for k, v in res["table"].items() if "|beq_" not in k or any(
        p.get("beq_plus") is not None for p in res["pairs"])}
    FILE.write_text(json.dumps(res, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print("patched", FILE.name, f"{time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
