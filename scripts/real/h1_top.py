#!/usr/bin/env python3
"""H1: the closed reward of the constant candidate `True` (Corollary hack (i)).

For each benchmark statement R the closed goal `True → R` is just R, and `R → True` is
trivial, so the constant candidate is closed-equivalent to R exactly when the prover proves
R. We run the closed pipeline on that one goal: tactic tiers T0 and T1, then one proposal and
one repair of the strong model, all kernel-checked. The same pair is a residual accept of the
three-valued criterion (the empty telescope aligns with nothing), never a local one.

Usage: h1_top.py [minif2f|proofnetsharp|putnam]     Writes data/real/h1_top_<set>.json.
"""

from __future__ import annotations

import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import f8_strong as f8
import g3_probe as g3
from runner import ROOT

MODEL = "anthropic/claude-opus-5.5"


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    g3.DATASET = sys.argv[1] if len(sys.argv) > 1 else "minif2f"
    out = ROOT / "data" / "real" / f"h1_top_{g3.DATASET}.json"
    pairs = [(r, p, "True") for r, p in g3.statements()]
    print(g3.DATASET, "statements", len(pairs), flush=True)
    proved = {r.row_id: "" for r, _, _ in pairs}
    for tag, tactic, hb in (("t0", f2.T0, 20000), ("t1", f2.T1, 100000)):
        open_goals = {rid: {"bwd"} for rid, how in proved.items() if not how}
        sub = [x for x in pairs if x[0].row_id in open_goals]
        for (rid, _), good in f2.run_tactic_tier(sub, tactic, hb, f"h1{tag}", open_goals).items():
            if good:
                proved[rid] = tag
        print(tag, sum(bool(v) for v in proved.values()), f"{time.time() - t0:.0f}s", flush=True)

    f8.MODEL = MODEL
    f2.PROPOSER = MODEL
    todo = [(r, g, p) for r, g, p in pairs if not proved[r.row_id]]

    def work(x):
        r, g, p = x
        text = f2.goal_text("bwd", g, p)
        try:
            return (r.row_id, "bwd"), (r, text, f2.propose(r, "bwd", text))
        except RuntimeError:
            return (r.row_id, "bwd"), (r, text, None)

    with ThreadPoolExecutor(max_workers=12) as pool:
        init = dict(pool.map(work, todo))
    for rid, _ in f8.propose_and_repair(init, "h1k"):
        proved[rid] = "llm"
    n = len(pairs)
    k = sum(bool(v) for v in proved.values())
    summary = {"set": g3.DATASET, "model": MODEL, "n": n, "top_rewarded": k,
               "by_tier": {t: sum(v == t for v in proved.values()) for t in ("t0", "t1", "llm")},
               "seconds": round(time.time() - t0, 1), "proved": proved}
    out.write_text(json.dumps(summary, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "proved"}), flush=True)


if __name__ == "__main__":
    main()
