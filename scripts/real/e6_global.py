#!/usr/bin/env python3
"""E6: whole-statement probes on reference statements.

For each reference `R` with canonical telescope `(Γ, H₁…Hₖ, C)`:

    vacuous   ∀ Γ, H₁ → … → Hₖ → False     the hypotheses are jointly unsatisfiable
    trivial   ∀ Γ', C                        the conclusion holds with all free hypotheses removed

Both are positive certificates (the negations `nonvac`, `nontrivial` are also produced by
`ExperimentsMathlib.Probe` and are used here only to record non-degeneracy where a tactic
finds it). Tactic tier first, then one LLM proposal and one repair round for `vacuous` and
`trivial`, all checked by `probe_global_prove` against the kernel goal.

Usage: e6_global.py [MODEL] [proofnetsharp|minif2f|putnam]   Writes data/real/e6_results{_SUFFIX}.json.
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

import g3_probe as g3
from f7_component import COMP_TAC
from f9_canon import lean_str, repair
from g1_full import propose
from runner import ROOT, Item, _build, _run_file, check

MODEL = sys.argv[1] if len(sys.argv) > 1 else "anthropic/claude-opus-5.5"
g3.DATASET = sys.argv[2] if len(sys.argv) > 2 else "proofnetsharp"
SUFFIX = "" if g3.DATASET == "proofnetsharp" else f"_{g3.DATASET}"
OUT = ROOT / "data" / "real" / f"e6_results{SUFFIX}.json"
CANON_CACHE = ROOT / "data" / "real" / f"e6_canon{SUFFIX}.json"
LEAN_WORKERS = int(os.environ.get("LEAN_WORKERS", "2"))
POS = ("vacuous", "trivial")
NEG = ("nonvac", "nontrivial")
VAC_TAC = ("first | (intros; omega) | (intros; simp_all; done) | (intros; linarith) | (intros; nlinarith) "
           "| (intros; norm_num at *; done) | (intros; aesop) | " + COMP_TAC[len("first | "):])


def canon_all(stmts) -> dict[str, dict]:
    cache = json.loads(CANON_CACHE.read_text(encoding="utf-8")) if CANON_CACHE.exists() else {}
    groups: dict[tuple, list] = {}
    for r, g in stmts:
        if r.row_id in cache:
            continue
        imports, pre = g3.imports_of(r)
        groups.setdefault(imports, []).append(Item(r.row_id, imports, f"{pre}\n#probe_global {lean_str(r.row_id)} ({g})"))
    batches = [g[i:i + 25] for g in groups.values() for i in range(0, len(g), 25)]

    def run(batch):
        out, _ = _run_file(_build(batch)[0], 1200)
        return batch, out

    with ThreadPoolExecutor(max_workers=LEAN_WORKERS) as pool:
        for batch, out in pool.map(run, batches):
            blocks = dict(re.findall(r"CANON_BEGIN (\S+)\n(.*?)\n?CANON_END \1", out, flags=re.DOTALL))
            for it in batch:
                b = blocks.get(it.item_id)
                if b is None:
                    cache[it.item_id] = {"status": "elab_fail"}
                elif b.startswith("CANON_FAIL"):
                    cache[it.item_id] = {"status": "probe_fail", "detail": b[:300]}
                else:
                    cache[it.item_id] = {
                        "status": "ok",
                        "info": re.search(r"CANON_INFO (.*)", b).group(1),
                        "goals": dict(re.findall(r"CANON_GOAL (\w+) ::: (.*?)(?=\nCANON_GOAL |\Z)", b, flags=re.DOTALL)),
                    }
            CANON_CACHE.write_text(json.dumps(cache, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    return cache


def prove_items(jobs, tag: str) -> dict:
    items, keys = [], []
    for (rid, goal), (r, g, proof) in jobs:
        imports, pre = g3.imports_of(r)
        name = re.sub(r"\W", "_", f"{tag}_{rid}_{goal}")
        body = (f"{pre}\nset_option maxHeartbeats 200000 in\n"
                f"probe_global_prove {name} ({g}) {goal} := by\n  {proof}")
        items.append(Item(f"{rid}:{tag}:{goal}", imports, body))
        keys.append((rid, goal))
    res = check(items, batch_size=10, workers=LEAN_WORKERS)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def ok(res) -> bool:
    return res.ok and not res.uses_sorry


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    stmts = g3.statements()
    by_id = {r.row_id: (r, g) for r, g in stmts}
    print(g3.DATASET, "statements", len(stmts), flush=True)
    canon = canon_all(stmts)
    good = [rid for rid in by_id if canon[rid]["status"] == "ok"]
    print("canon", Counter(canon[rid]["status"] for rid in by_id), f"{time.time() - t0:.0f}s", flush=True)

    goals_of = {rid: [g for g in POS + NEG if g in canon[rid]["goals"]] for rid in good}
    tac = prove_items([((rid, g), (*by_id[rid], VAC_TAC)) for rid in good for g in goals_of[rid]], "e6t")
    proved = {rid: {g for g in goals_of[rid] if ok(tac[(rid, g)])} for rid in good}
    print("tactic tier", Counter(g for v in proved.values() for g in v), f"{time.time() - t0:.0f}s", flush=True)

    def work(rid):
        names = [g for g in POS if g in goals_of[rid] and g not in proved[rid]
                 and {"vacuous": "nonvac", "trivial": "nontrivial"}[g] not in proved[rid]]
        return rid, propose(MODEL, by_id[rid][0], canon[rid]["goals"], names) if names else {}

    with ThreadPoolExecutor(max_workers=12) as pool:
        props = dict(pool.map(work, good))
    shot = prove_items([((rid, g), (*by_id[rid], p)) for rid, gs in props.items() for g, p in gs.items()], "e6l")
    for (rid, g), res in shot.items():
        if ok(res):
            proved[rid].add(g)

    def fix(item):
        (rid, g), res = item
        return (rid, g), repair(MODEL, by_id[rid][0], g, canon[rid]["goals"][g], props[rid][g], res.errors)

    failed = [(k, res) for k, res in shot.items() if not ok(res)]
    with ThreadPoolExecutor(max_workers=12) as pool:
        fixes = dict(pool.map(fix, failed))
    for (rid, g), res in prove_items([((rid, g), (*by_id[rid], p)) for (rid, g), p in fixes.items() if p], "e6r").items():
        if ok(res):
            proved[rid].add(g)

    flags = Counter()
    per = []
    for rid in good:
        r, g = by_id[rid]
        f = [p for p in POS if p in proved[rid]]
        flags["+".join(f) or "none"] += 1
        per.append({"row_id": rid, "stmt_id": r.stmt_id, "split": r.split, "flags": f, "proved": sorted(proved[rid]),
                    "statement": g, "nl": r.nl, "info": canon[rid]["info"]})
    summary = {"model": MODEL, "dataset": g3.DATASET, "n_statements": len(stmts), "n_probed": len(good),
               "flags": dict(flags), "seconds": round(time.time() - t0, 1), "statements": per}
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "statements"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
