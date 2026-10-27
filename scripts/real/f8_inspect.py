#!/usr/bin/env python3
"""Print goals, cached F8 proposals and Lean outcomes for chosen pairs.

Usage: f8_inspect.py MODEL ROW_ID [ROW_ID ...]
"""

from __future__ import annotations

import json
import sys

from f7_component import LLM_GOALS, OUT as F7_OUT, goal_texts
from f8_provers import lean_check, propose
from realdata import proofnetverif


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    model, ids = sys.argv[1], sys.argv[2:]
    f7 = {p["row_id"]: p for p in json.loads(F7_OUT.read_text(encoding="utf-8"))["pairs"]}
    rows = {r.row_id: r for r in proofnetverif("test")}
    jobs, props = [], {}
    for rid in ids:
        p, r = f7[rid], rows[rid]
        props[rid] = propose(model, r, p["decomposition"], [g for g in LLM_GOALS if g not in p["proved"]])
        jobs += [((rid, g), (r, p["decomposition"], pr)) for g, pr in props[rid].items()]
    res = lean_check(jobs, "inspect")
    for rid in ids:
        r, d = rows[rid], f7[rid]["decomposition"]
        print("=" * 100)
        print(rid, "label", r.correct, "\nNL:", r.nl, "\nGOLD:", r.gold, "\nPRED:", r.pred)
        print("binders:", d["binders"], "\nHr:", d["Hr"], "\nCr:", d["Cr"], "\nHs:", d["Hs"], "\nCs:", d["Cs"])
        gt = goal_texts(d)
        for g, pr in props[rid].items():
            x = res[(rid, g)]
            print(f"--- {g}  ok={x.ok and not x.uses_sorry}\n{gt[g]}\n  {pr}")
            if not x.ok:
                print("ERR:", "\n".join(x.errors)[:1200])


if __name__ == "__main__":
    main()
