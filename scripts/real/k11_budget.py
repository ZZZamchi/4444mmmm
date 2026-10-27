#!/usr/bin/env python3
"""K11: a controlled budget sweep of one model on all 1,140 G5 pairs.

Replays the G5 pipeline of `g1_full` for one model and records the budget level at which
each goal was first proved, on both the component and the closed side:

  L0  fixed tactics,
  L1  + one proposal of the model,
  L2  + one repair round (the budget of every G5 table),
  L3  + a second repair round (with EXTRA=1; new model calls).

L0-L2 reuse the Lean and LLM caches of the G5 run, item by item, so they cost nothing; the
script checks that L2 reproduces the stored G5 verdicts. The regrouping certificates
(`split_r`, `split_s`) concern each statement alone and are taken from the stored run at
every level, so the levels differ only in the comparison goals.

Usage: k11_budget.py MODEL        writes data/real/k11_budget_<model>.json
"""

from __future__ import annotations

import json
import os
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import f8_strong as f8
import g1_full as g1
from f7_component import COMP_TAC, GOALS, LLM_GOALS, SPLIT_TAC, classify
from f9_canon import repair
from k6_stats import is_local
from runner import ROOT

G5 = ROOT / "data" / "real" / "g5"
LEVELS = ["L0", "L1", "L2", "L3"]
EXTRA = os.environ.get("EXTRA") == "1"
WORKERS = int(os.environ.get("LLM_WORKERS", 12))


def short(model: str) -> str:
    return model.split("/")[-1]


def component(model, stmt, canon, good) -> dict[str, dict[str, str]]:
    """rid -> goal -> first level at which it was proved."""
    all_goals = (*GOALS, "split_r", "split_s")
    jobs = [((rid, g), (*stmt[rid], SPLIT_TAC if g.startswith("split") else COMP_TAC)) for rid in good for g in all_goals]
    tac = g1.prove_items(jobs, "g0")
    level = {rid: {g: "L0" for g in all_goals if g1.ok(tac[(rid, g)])} for rid in good}

    def proved(rid):
        return set(level[rid])

    def work(rid):
        open_goals = [g for g in LLM_GOALS if g not in level[rid]]
        if not open_goals or classify(proved(rid)) == "reject":
            return rid, {}
        return rid, g1.propose(model, stmt[rid][0], canon[rid]["goals"], open_goals)

    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        props = dict(pool.map(work, good))
    shot = g1.prove_items([((rid, g), (*stmt[rid], p)) for rid, gs in props.items() for g, p in gs.items()], "g1")
    for (rid, g), res in shot.items():
        if g1.ok(res):
            level[rid].setdefault(g, "L1")
    failed = [((rid, g), props[rid][g], res) for (rid, g), res in shot.items()
              if not g1.ok(res) and classify(proved(rid)) == "unknown"]
    for tag, lev in (("g2", "L2"), ("g3", "L3")):
        if lev == "L3" and not EXTRA:
            break

        def fix(item):
            (rid, g), proof, res = item
            return (rid, g), repair(model, stmt[rid][0], g, canon[rid]["goals"][g], proof, res.errors)

        with ThreadPoolExecutor(max_workers=WORKERS) as pool:
            fixes = dict(pool.map(fix, failed))
        res2 = g1.prove_items([((rid, g), (*stmt[rid], p)) for (rid, g), p in fixes.items() if p], tag)
        for (rid, g), res in res2.items():
            if g1.ok(res):
                level[rid].setdefault(g, lev)
        failed = [((rid, g), fixes[(rid, g)], res) for (rid, g), res in res2.items()
                  if not g1.ok(res) and classify(proved(rid)) == "unknown"]
        print("component", lev, "done", flush=True)
    return level


def closed(model, pairs) -> dict[str, dict[str, str]]:
    f8.MODEL = model
    f2.PROPOSER = model
    t1 = {p["row_id"]: set(p["t1"]) for p in json.loads(f2.OUT.read_text(encoding="utf-8"))["pairs"]}
    level = {r.row_id: {g: "L0" for g in t1[r.row_id]} for r, _, _ in pairs}
    jobs = [(r, g, p, goal) for r, g, p in pairs for goal in f2.LLM_GOALS if goal not in level[r.row_id]]

    def work(job):
        r, g, p, goal = job
        try:
            return (r.row_id, goal), (r, f2.goal_text(goal, g, p), f2.propose(r, goal, f2.goal_text(goal, g, p)))
        except RuntimeError:
            return (r.row_id, goal), (r, f2.goal_text(goal, g, p), None)

    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        init = dict(pool.map(work, jobs))
    cur = {k: v for k, v in init.items() if v[2]}
    for tag, lev in (("k8", "L1"), ("k8r", "L2"), ("k8rr", "L3")):
        if lev == "L3" and not EXTRA:
            break
        ok, fail = f8.check_round(cur, tag)
        for rid, goal in ok:
            level[rid].setdefault(goal, lev)
        if lev == "L3" or (lev == "L2" and not EXTRA):
            break
        with ThreadPoolExecutor(max_workers=WORKERS) as pool:
            fixed = dict(pool.map(f8.repair, [(k, cur[k][0], cur[k][1], cur[k][2], err) for k, err in fail.items()]))
        cur = {k: (cur[k][0], cur[k][1], p) for k, p in fixed.items() if p}
        print("closed", lev, "done", flush=True)
    return level


def upto(level: dict[str, str], lev: str) -> set[str]:
    return {g for g, l in level.items() if LEVELS.index(l) <= LEVELS.index(lev)}


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    model = sys.argv[1]
    t0 = time.time()
    f2.OUT = G5 / "f2_full.json"
    stored = {p["row_id"]: p for p in json.loads((G5 / f"g1_results_{short(model)}.json").read_text(encoding="utf-8"))["pairs"]}
    rows = {r.row_id: r for r in g1.proofnetverif("test")}
    pairs = [(rows[rid], f2.normalize(g1.to_prop(rows[rid].gold)), f2.normalize(g1.to_prop(rows[rid].pred)))
             for rid in stored]
    stmt = {r.row_id: (r, g, s) for r, g, s in pairs}
    canon = json.loads(g1.CANON_CACHE.read_text(encoding="utf-8"))
    good = [rid for rid in stored if canon.get(rid, {}).get("status") == "ok"]
    comp = component(model, stmt, canon, good)
    cl = closed(model, pairs)

    levels = LEVELS if EXTRA else LEVELS[:3]
    out_pairs, mismatch = [], Counter()
    for rid, p in stored.items():
        split = {"split_r", "split_s"} <= set(p.get("proved") or [])
        rec = {"row_id": rid, "label": p["label"], "local": is_local(p), "split": split, "comp": {}, "closed": {}}
        for lev in levels:
            goals = upto(comp.get(rid, {}), lev) - {"split_r", "split_s"}
            rec["comp"][lev] = classify(goals) if rid in comp else p["verdict"]
            rec["closed"][lev] = f2.verdict(upto(cl[rid], lev))["status"]
        mismatch["comp"] += rec["comp"]["L2"] != p["verdict"]
        mismatch["closed"] += rec["closed"]["L2"] != p["closed"]
        out_pairs.append(rec)

    table = {}
    for lev in levels:
        c = Counter()
        for rec in out_pairs:
            lab = "F" if rec["label"] else "U"
            acc = rec["comp"][lev] == "accept" and rec["split"]
            c[f"closed_acc{lab}"] += rec["closed"][lev] == "proved"
            c[f"acc{lab}"] += acc
            c[f"local{lab}"] += acc and rec["local"]
            c[f"residual{lab}"] += acc and not rec["local"]
            c[f"reject{lab}"] += rec["comp"][lev] == "reject" and rec["split"]
            c[f"unknown{lab}"] += rec["comp"][lev] == "unknown"
        table[lev] = dict(sorted(c.items()))
    summary = {"model": model, "extra": EXTRA, "mismatch_L2_vs_stored": dict(mismatch), "table": table,
               "seconds": round(time.time() - t0, 1), "pairs": out_pairs}
    out = Path(os.environ.get("K11_OUT") or ROOT / "data" / "real" / f"k11_budget_{short(model)}.json")
    tmp = out.with_suffix(f".{os.getpid()}.tmp")
    tmp.write_text(json.dumps(summary, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(tmp, out)
    print(json.dumps({k: v for k, v in summary.items() if k != "pairs"}, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
