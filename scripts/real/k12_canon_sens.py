#!/usr/bin/env python3
"""K12: how the component verdicts on the 300 G1 pairs depend on the canonicalization rules.

For each variant of `ExperimentsMathlib.CanonV2Var` that switches off one rule (or all four),
the goals of every pair are recomputed. Pairs whose goals are textually unchanged keep their
G1 verdict (the goals are the same, so are the proofs). Pairs whose goals changed are proved
again with the G1 budget: fixed tactics (both regrouping tiers), then one proposal and one
repair round of the strong model for every open goal, regrouping goals included.

Two of the rules only move a Prop between hypotheses and conclusion (`nohoist`, `nobot`);
by Proposition `prop:split` (Lean `T9.robust_reject`) they can turn a reject into an accept only
if the reject is vacuity-only. The other two change the context (`nonotex`, `noonept`).
`onept2` is not a removal but a relaxed one-point rule, to measure what a better alignment buys.

Usage: k12_canon_sens.py        writes data/real/k12_canon_sens.json
"""

from __future__ import annotations

import json
import os
import re
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import g1_full as g1
from f7_component import COMP_TAC, GOALS, SPLIT_TAC, SPLIT_TAC2, classify
from f9_canon import lean_str, repair
from k6_stats import is_local
from runner import ROOT, Item, _build, _run_file, check

D = ROOT / "data" / "real"
OUT = D / "k12_canon_sens.json"
CACHE = D / "k12_canon_cache.json"
MODULE = "ExperimentsMathlib.CanonV2Var"
MODEL = os.environ.get("K12_MODEL", "anthropic/claude-opus-5.5")
VARIANTS = ["", "nohoist", "nobot", "nonotex", "noonept", "nohoist,nobot,nonotex,noonept", "onept2"]
ALL_GOALS = (*GOALS, "split_r", "split_s")
OPEN_GOALS = ("acc", "nhyp", "ncin", "ncomp", "split_r", "split_s")
WORKERS = int(os.environ.get("LLM_WORKERS", 12))


def imports_of(r):
    imports, pre = f2.prelude(r)
    return tuple(sorted(set(imports) | {MODULE})), pre


def canon(stmt, rids, flags, cache) -> None:
    groups: dict[tuple, list] = {}
    for rid in rids:
        if f"{flags}|{rid}" in cache:
            continue
        r, g, s = stmt[rid]
        imports, pre = imports_of(r)
        groups.setdefault(imports, []).append(
            Item(f"{flags}|{rid}", imports, f"{pre}\n#canon2v_goals {lean_str(rid)} {lean_str(flags)} ({g}) ({s})"))
    batches = [g[i:i + 10] for g in groups.values() for i in range(0, len(g), 10)]

    def run(batch):
        out, _ = _run_file(_build(batch)[0], 900)
        return batch, out

    with ThreadPoolExecutor(max_workers=int(os.environ.get("LEAN_WORKERS", 6))) as pool:
        for batch, out in pool.map(run, batches):
            blocks = dict(re.findall(r"CANON_BEGIN (\S+)\n(.*?)\n?CANON_END \1", out, flags=re.DOTALL))
            for it in batch:
                b = blocks.get(it.item_id.split("|", 1)[1])
                if b is None or b.startswith("CANON_FAIL"):
                    cache[it.item_id] = {"status": "fail"}
                else:
                    info = re.search(r"CANON_INFO (.*)", b).group(1)
                    goals = dict(re.findall(r"CANON_GOAL (\w+) ::: (.*?)(?=\nCANON_GOAL |\Z)", b, flags=re.DOTALL))
                    cache[it.item_id] = {"status": "ok", "info": info, "goals": goals}
    tmp = CACHE.with_suffix(f".{os.getpid()}.tmp")
    tmp.write_text(json.dumps(cache, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(tmp, CACHE)


def prove(stmt, flags, jobs, tag) -> dict:
    """jobs: list of ((rid, goal), proof)."""
    items, keys = [], []
    for (rid, goal), proof in jobs:
        r, g, s = stmt[rid]
        imports, pre = imports_of(r)
        body = (f"{pre}\nset_option maxHeartbeats 200000 in\n"
                f"canon2v_prove {lean_str(flags)} {tag}_{goal} ({g}) ({s}) {goal} := by\n  {proof}")
        items.append(Item(f"{flags}|{rid}:{tag}:{goal}", imports, body))
        keys.append((rid, goal))
    res = check(items, batch_size=10, workers=6)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def verdict(proved: set) -> str:
    v = classify(proved - {"split_r", "split_s"})
    return v if v == "unknown" or {"split_r", "split_s"} <= proved else "unknown"


def run_variant(stmt, flags, rids, goals) -> dict[str, set]:
    proved = {rid: set() for rid in rids}
    for tag, tac in (("v0", None), ("v0b", SPLIT_TAC2)):
        jobs = []
        for rid in rids:
            for g in ALL_GOALS:
                if g in proved[rid]:
                    continue
                if tac is None:
                    jobs.append(((rid, g), SPLIT_TAC if g.startswith("split") else COMP_TAC))
                elif g.startswith("split"):
                    jobs.append(((rid, g), tac))
        for (rid, g), res in prove(stmt, flags, jobs, tag).items():
            if g1.ok(res):
                proved[rid].add(g)

    def todo(rid):
        if verdict(proved[rid]) != "unknown":
            return []
        return [g for g in OPEN_GOALS if g not in proved[rid]]

    def work(rid):
        names = todo(rid)
        return rid, (g1.propose(MODEL, stmt[rid][0], goals[rid], names) if names else {})

    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        props = dict(pool.map(work, rids))
    shot = prove(stmt, flags, [((rid, g), p) for rid, gs in props.items() for g, p in gs.items()], "v1")
    for (rid, g), res in shot.items():
        if g1.ok(res):
            proved[rid].add(g)
    failed = [((rid, g), res) for (rid, g), res in shot.items() if not g1.ok(res) and verdict(proved[rid]) == "unknown"]

    def fix(item):
        (rid, g), res = item
        return (rid, g), repair(MODEL, stmt[rid][0], g, goals[rid][g], props[rid][g], res.errors)

    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        fixes = dict(pool.map(fix, failed))
    for (rid, g), res in prove(stmt, flags, [(k, p) for k, p in fixes.items() if p], "v2").items():
        if g1.ok(res):
            proved[rid].add(g)
    return proved


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    base = {p["row_id"]: p for p in json.loads((D / "g1_results.json").read_text(encoding="utf-8"))["pairs"]}
    k3 = json.loads((D / "k3_direction.json").read_text(encoding="utf-8"))["g1"]["pairs"]
    rows = {r.row_id: r for r in g1.proofnetverif("test")}
    stmt = {rid: (rows[rid], f2.normalize(g1.to_prop(rows[rid].gold)), f2.normalize(g1.to_prop(rows[rid].pred)))
            for rid in base}
    cache = json.loads(CACHE.read_text(encoding="utf-8")) if CACHE.exists() else {}
    for flags in VARIANTS:
        canon(stmt, list(base), flags, cache)
    ref = json.loads(g1.CANON_CACHE.read_text(encoding="utf-8"))
    same = sum(cache.get(f"|{rid}", {}).get("goals") == ref.get(rid, {}).get("goals") for rid in base)
    print("canon done", f"{time.time() - t0:.0f}s", "baseline goals equal to CanonV2:", same, "/", len(base),
          flush=True)
    if os.environ.get("K12_DRY") == "1":
        for flags in VARIANTS[1:]:
            n = sum(cache.get(f"|{rid}", {}).get("goals") != cache.get(f"{flags}|{rid}", {}).get("goals")
                    for rid in base)
            print(flags, "changed", n)
        return

    def old_verdict(p):
        if p["verdict"] in ("accept", "reject", "off_domain") and not {"split_r", "split_s"} <= set(p.get("proved") or []):
            return "unknown"
        return p["verdict"]

    out = {"model": MODEL, "variants": {}}
    for flags in VARIANTS[1:]:
        changed, fail = [], []
        for rid in base:
            a, b = cache.get(f"|{rid}", {}), cache.get(f"{flags}|{rid}", {})
            if a.get("status") != "ok" or b.get("status") != "ok":
                if a.get("status") == "ok":
                    fail.append(rid)
                continue
            if a["goals"] != b["goals"]:
                changed.append(rid)
        goals = {rid: cache[f"{flags}|{rid}"]["goals"] for rid in changed}
        proved = run_variant(stmt, flags, changed, goals)
        flips = Counter()
        per_pair = []
        for rid in changed:
            p = base[rid]
            old, new = old_verdict(p), verdict(proved[rid])
            direction = k3.get(rid, {}).get("class") if old == "reject" else None
            flips[f"{'F' if p['label'] else 'U'}:{old}->{new}"] += 1
            if old == "reject" and new == "accept":
                flips[f"reject->accept:{direction}"] += 1
            per_pair.append({"row_id": rid, "label": p["label"], "old": old, "new": new, "direction": direction,
                             "old_local": is_local(p), "new_info": cache[f"{flags}|{rid}"]["info"],
                             "proved": sorted(proved[rid])})
        out["variants"][flags] = {"changed": len(changed), "canon_fail": len(fail),
                                  "flips": dict(sorted(flips.items())), "pairs": per_pair}
        print(flags, "changed", len(changed), "fail", len(fail), dict(sorted(flips.items())),
              f"{time.time() - t0:.0f}s", flush=True)
    tmp = OUT.with_suffix(f".{os.getpid()}.tmp")
    tmp.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(tmp, OUT)


if __name__ == "__main__":
    main()
