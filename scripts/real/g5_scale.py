#!/usr/bin/env python3
"""G5: G1 on every usable pair of the ProofNetVerif test split instead of the 300-pair sample.

Step `f2` runs the closed tactic tiers (t0, t1) of F2 on all usable pairs and writes
data/real/g5/f2_full.json; the LLM tier of F2 is skipped because G1 does not use it. Each
model step then runs g1_full against that pair list and writes
data/real/g5/g1_results_<model>.json. The 300 G1 pairs are a seeded subset of the same list,
so their Lean and LLM caches are reused. Both caches make every step resumable.

Step `canon` fills the shared canonical-form cache once, so that model steps can run in parallel.

Usage: g5_scale.py f2 | g5_scale.py canon | g5_scale.py MODEL
"""

from __future__ import annotations

import functools
import json
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import g1_full as g1
import runner
from runner import ROOT

G5 = ROOT / "data" / "real" / "g5"
F2_FULL = G5 / "f2_full.json"


def short(model: str) -> str:
    return model.split("/")[-1]


def run_f2() -> None:
    t0 = time.time()
    f2.N_PER_LABEL = 10 ** 6
    f2.check = functools.partial(runner.check, workers=int(os.environ.get("G5_WORKERS", 10)))
    pairs, stats = f2.select_pairs()
    print("selection:", stats, "pairs:", len(pairs), f"{time.time() - t0:.0f}s", flush=True)
    proved: dict[str, set] = {r.row_id: set() for r, _, _ in pairs}
    by_tier: dict[str, dict[str, set]] = {}
    for tag, tactic, hb in (("t0", f2.T0, 20000), ("t1", f2.T1, 100000)):
        open_goals = {rid: set(f2.GOALS) - s for rid, s in proved.items()}
        for (rid, goal), ok in f2.run_tactic_tier(pairs, tactic, hb, tag, open_goals).items():
            if ok:
                proved[rid].add(goal)
        by_tier[tag] = {k: set(v) for k, v in proved.items()}
        print(tag, "done", f"{time.time() - t0:.0f}s", flush=True)
    summary = {
        "selection": stats,
        "n_pairs": len(pairs),
        "tiers": f2.summarize(pairs, by_tier),
        "seconds": round(time.time() - t0, 1),
        "pairs": [{"row_id": r.row_id, "stmt_id": r.stmt_id, "label": r.correct,
                   **{tier: sorted(by_tier[tier][r.row_id]) for tier in by_tier}} for r, _, _ in pairs],
    }
    G5.mkdir(parents=True, exist_ok=True)
    F2_FULL.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "pairs"}, indent=2, ensure_ascii=False), flush=True)


def run_canon() -> None:
    rows = {r.row_id: r for r in g1.proofnetverif("test")}
    pairs = [(rows[p["row_id"]], f2.normalize(g1.to_prop(rows[p["row_id"]].gold)),
              f2.normalize(g1.to_prop(rows[p["row_id"]].pred)))
             for p in json.loads(F2_FULL.read_text(encoding="utf-8"))["pairs"]]
    canon = g1.canon_all(pairs)
    print("canon", g1.Counter(canon[r.row_id]["status"] for r, _, _ in pairs), flush=True)


def run_model(model: str) -> None:
    if not F2_FULL.exists():
        raise SystemExit("run `g5_scale.py f2` first")
    f2.OUT = F2_FULL
    g1.MODEL = model
    g1.OUT = G5 / f"g1_results_{short(model)}.json"
    g1.main()


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    arg = sys.argv[1] if len(sys.argv) > 1 else "f2"
    if arg == "f2":
        run_f2()
    elif arg == "canon":
        run_canon()
    else:
        run_model(arg)


if __name__ == "__main__":
    main()
