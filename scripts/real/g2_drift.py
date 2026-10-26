#!/usr/bin/env python3
"""G2: drift injection. Mutate ProofNetVerif references on their canonical telescopes.

Each sampled reference R gets four candidates built by `ExperimentsMathlib.Mutate`
(id, drop, neg, offdom), so the drift class of every pair is known by construction.
Every pair then goes through the G1 component pipeline: fixed tactics, one proposal and
one repair round, all checked against the kernel goals of `CanonV2.goals R S`.

`offdom` replaces C by C ∨ ¬Hᵢ, which R implies: whenever R is a true theorem the pair is
closed-equivalent, so any complete closed oracle accepts it.

Usage: g2_drift.py [N_REFS] [MODEL]          Writes data/real/g2_results.json.
"""

from __future__ import annotations

import json
import random
import re
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
from f7_component import COMP_TAC, GOALS, LLM_GOALS, SPLIT_TAC, classify
from f9_canon import lean_str, repair
from g1_full import propose
from realdata import proofnetverif
from runner import ROOT, Item, _build, _run_file, check
from stmt import to_prop

OUT = ROOT / "data" / "real" / "g2_results.json"
CANON_CACHE = ROOT / "data" / "real" / "g2_canon.json"
G1_CANON = ROOT / "data" / "real" / "g1_canon2.json"
IMPORT = "ExperimentsMathlib.Mutate"
KINDS = ("id", "drop", "neg", "offdom")
EXPECTED = {"id": {"accept"}, "drop": {"reject", "accept"}, "neg": {"reject"}, "offdom": {"off_domain", "accept"}}
N_REFS = int(sys.argv[1]) if len(sys.argv) > 1 else 60
MODEL = sys.argv[2] if len(sys.argv) > 2 else "anthropic/claude-opus-5.5"
if MODEL != "anthropic/claude-opus-5.5":
    OUT = OUT.with_name(f"g2_results_{MODEL.split('/')[-1]}.json")
SEED = 0
LEAN_WORKERS = 2


def imports_of(r) -> tuple[tuple[str, ...], str]:
    imports, pre = f2.prelude(r)
    return tuple(sorted(set(imports) | {IMPORT})), pre


def references():
    rows = {r.row_id: r for r in proofnetverif("test")}
    g1 = json.loads(G1_CANON.read_text(encoding="utf-8"))
    seen, refs = set(), []
    for rid in sorted(g1):
        if g1[rid]["status"] != "ok":
            continue
        r = rows[rid]
        g = f2.normalize(to_prop(r.gold))
        if g not in seen:
            seen.add(g)
            refs.append((r, g))
    random.Random(SEED).shuffle(refs)
    return refs


def canon_all(jobs) -> dict[str, dict]:
    cache = json.loads(CANON_CACHE.read_text(encoding="utf-8")) if CANON_CACHE.exists() else {}
    groups: dict[tuple, list] = {}
    for key, (r, g, kind) in jobs.items():
        if key in cache:
            continue
        imports, pre = imports_of(r)
        groups.setdefault(imports, []).append(
            Item(key, imports, f"{pre}\n#mutant_goals {lean_str(key)} {kind} ({g})"))
    batches = [g[i:i + 10] for g in groups.values() for i in range(0, len(g), 10)]

    def run(batch):
        out, _ = _run_file(_build(batch)[0], 900)
        return batch, out

    with ThreadPoolExecutor(max_workers=LEAN_WORKERS) as pool:
        for batch, out in pool.map(run, batches):
            blocks = dict(re.findall(r"CANON_BEGIN (\S+)\n(.*?)\n?CANON_END \1", out, flags=re.DOTALL))
            for it in batch:
                b = blocks.get(it.item_id)
                if b is None:
                    cache[it.item_id] = {"status": "elab_fail"}
                elif b.startswith("CANON_FAIL"):
                    cache[it.item_id] = {"status": "mutate_fail", "detail": b[:300]}
                else:
                    cache[it.item_id] = {
                        "status": "ok",
                        "info": re.search(r"CANON_INFO (.*)", b).group(1),
                        "mutant": re.search(r"CANON_MUTANT (.*?)(?=\nCANON_GOAL )", b, flags=re.DOTALL).group(1),
                        "goals": dict(re.findall(r"CANON_GOAL (\w+) ::: (.*?)(?=\nCANON_GOAL |\Z)", b, flags=re.DOTALL)),
                    }
    CANON_CACHE.write_text(json.dumps(cache, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    return cache


def prove_items(jobs, tag: str) -> dict:
    """jobs: list of ((key, goal), (row, gold, kind, proof))."""
    items, keys = [], []
    for (key, goal), (r, g, kind, proof) in jobs:
        imports, pre = imports_of(r)
        name = re.sub(r"\W", "_", f"{tag}_{key}_{goal}")
        body = (f"{pre}\nset_option maxHeartbeats 200000 in\n"
                f"mutant_prove {name} {kind} ({g}) {goal} := by\n  {proof}")
        items.append(Item(f"{key}:{tag}:{goal}", imports, body))
        keys.append((key, goal))
    res = check(items, batch_size=10, workers=LEAN_WORKERS)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def ok(res) -> bool:
    return res.ok and not res.uses_sorry


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    refs = references()
    print("distinct references", len(refs), flush=True)
    jobs = {}
    for r, g in refs[:N_REFS]:
        for kind in KINDS:
            jobs[f"{r.row_id}~{kind}"] = (r, g, kind)
    canon = canon_all(jobs)
    good = [k for k in jobs if canon[k]["status"] == "ok"]
    print("mutants", Counter(canon[k]["status"] for k in jobs), f"{time.time() - t0:.0f}s", flush=True)

    all_goals = (*GOALS, "split_r", "split_s")
    tac = prove_items([((k, g), (*jobs[k], SPLIT_TAC if g.startswith("split") else COMP_TAC))
                       for k in good for g in all_goals], "m0")
    proved = {k: {g for g in all_goals if ok(tac[(k, g)])} for k in good}
    tactic = {k: set(v) for k, v in proved.items()}
    print("tactic tier", Counter(classify(v) for v in proved.values()), f"{time.time() - t0:.0f}s", flush=True)

    def work(k):
        open_goals = [g for g in LLM_GOALS if g not in proved[k]]
        if not open_goals or classify(proved[k]) == "reject":
            return k, {}
        return k, propose(MODEL, jobs[k][0], canon[k]["goals"], open_goals)

    with ThreadPoolExecutor(max_workers=12) as pool:
        props = dict(pool.map(work, good))
    shot = prove_items([((k, g), (*jobs[k][:3], p)) for k, gs in props.items() for g, p in gs.items()], "m1")
    for (k, g), res in shot.items():
        if ok(res):
            proved[k].add(g)
    failed = [((k, g), res) for (k, g), res in shot.items() if not ok(res) and classify(proved[k]) == "unknown"]

    def fix(item):
        (k, g), res = item
        return (k, g), repair(MODEL, jobs[k][0], g, canon[k]["goals"][g], props[k][g], res.errors)

    with ThreadPoolExecutor(max_workers=12) as pool:
        fixes = dict(pool.map(fix, failed))
    for (k, g), res in prove_items([((k, g), (*jobs[k][:3], p)) for (k, g), p in fixes.items() if p], "m2").items():
        if ok(res):
            proved[k].add(g)

    table = {kind: Counter() for kind in KINDS}
    per = []
    for k, (r, g, kind) in jobs.items():
        c = canon[k]
        v = classify(proved[k]) if c["status"] == "ok" else c["status"]
        table[kind][v] += 1
        if c["status"] == "ok" and v not in EXPECTED[kind] | {"unknown"}:
            table[kind]["unexpected"] += 1
        per.append({"key": k, "row_id": r.row_id, "kind": kind, "verdict": v, "gold": g,
                    "mutant": c.get("mutant"), "proved": sorted(proved.get(k, ())),
                    "tactic": sorted(tactic.get(k, ())), "canon_info": c.get("info")})
    summary = {"model": MODEL, "n_refs": N_REFS, "table": {k: dict(v) for k, v in table.items()},
               "seconds": round(time.time() - t0, 1), "pairs": per}
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "pairs"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
