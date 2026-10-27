#!/usr/bin/env python3
"""G3: hypothesis probes on every ProofNet# reference statement (test and valid).

For each free hypothesis Hₖ of the canonical telescope (`ExperimentsMathlib.Probe`):
  implied   the other hypotheses imply Hₖ               -> flag `implied`
  idle      the conclusion holds wherever Hₖ fails       -> with `nimplied`: flag `idle`
Fixed tactics first, then one proposal and one repair round by MODEL. Every flag carries a
kernel-checked certificate; whether a flag is a faithfulness error is judged by hand
against the natural-language statement.

Usage: g3_probe.py [MODEL] [DATASET]     DATASET is proofnetsharp (default), minif2f or putnam.
Writes data/real/g3_results.json, or g3_results_<dataset>.json for other datasets.
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

import pandas as pd

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
from f7_component import COMP_TAC
from f9_canon import lean_str, repair
from g1_full import propose
from realdata import RAW, PnvRow, close_with_sorry
from runner import ROOT, Item, _build, _run_file, check
from stmt import to_prop

IMPORT = "ExperimentsMathlib.Probe"
MODEL = sys.argv[1] if len(sys.argv) > 1 else "anthropic/claude-opus-5.5"
DATASET = sys.argv[2] if len(sys.argv) > 2 else "proofnetsharp"
SUFFIX = "" if DATASET == "proofnetsharp" else f"_{DATASET}"
OUT = ROOT / "data" / "real" / f"g3_results{SUFFIX}.json"
CANON_CACHE = ROOT / "data" / "real" / f"g3_canon{SUFFIX}.json"
LEAN_WORKERS = int(os.environ.get("LEAN_WORKERS", "2"))
MAX_HYPS = 4
GOALS = ("implied", "nimplied", "idle")


def minif2f():
    out = []
    for line in (RAW / "minif2f" / "minif2f.jsonl").read_text(encoding="utf-8").splitlines():
        r = json.loads(line)
        stmt = re.sub(r":=\s*by\s*$", ":=", r["formal_statement"].rstrip())
        stmt = re.sub(r"([∑∏]\s*[^∑∏,]*?)\s+in\s+", r"\1 ∈ ", stmt)  # big-operator syntax removed from Mathlib
        nl = re.sub(r"^/--\s*|\s*-/\s*$", "", r["informal_prefix"].strip())
        row = PnvRow(f"mf-{r['split']}-{r['name']}", r["split"], r["name"], nl, r["header"],
                     close_with_sorry(stmt), "", True)
        p = to_prop(row.gold)
        if p is not None:
            out.append((row, f2.normalize(p)))
    return out


SOLUTION_RE = re.compile(r"^(?:noncomputable\s+)?abbrev\s+(\w+_solution)\s*:\s*(.*?)\s*:=\s*sorry", re.MULTILINE | re.DOTALL)
THEOREM_RE = re.compile(r"^(?:/--(.*?)-/\s*)?(theorem\s+\w+.*?:=)\s*(?:by\s*)?sorry\s*$", re.MULTILINE | re.DOTALL)


def putnam():
    """PutnamBench; answer constants `abbrev X : T := sorry` become `noncomputable opaque X : T`."""
    out = []
    for f in sorted((RAW / "putnambench" / "lean4" / "src").glob("putnam_*.lean")):
        text = f.read_text(encoding="utf-8")
        m = THEOREM_RE.search(text)
        if not m:
            continue
        header = SOLUTION_RE.sub(lambda s: f"noncomputable opaque {s.group(1)} : {s.group(2)}", text[:m.start()])
        header = re.sub(r"/--.*?-/", "", header, flags=re.DOTALL)
        row = PnvRow(f"pb-{f.stem}", "test", f.stem, (m.group(1) or "").strip(), header,
                     close_with_sorry(m.group(2)), "", True)
        p = to_prop(row.gold)
        if p is not None:
            out.append((row, f2.normalize(p)))
    return out


def statements():
    if DATASET == "minif2f":
        return minif2f()
    if DATASET == "putnam":
        return putnam()
    out = []
    for split in ("test", "valid"):
        d = pd.read_parquet(RAW / "hf" / f"ProofNetSharp-{split}.parquet")
        for _, r in d.iterrows():
            row = PnvRow(f"pns-{split}-{r['id']}", split, r["id"], r["nl_statement"], r["lean4_src_header"],
                         close_with_sorry(r["lean4_formalization"]), "", True)
            p = to_prop(row.gold)
            if p is not None:
                out.append((row, f2.normalize(p)))
    return out


def imports_of(r) -> tuple[tuple[str, ...], str]:
    imports, pre = f2.prelude(r)
    return tuple(sorted(set(imports) | {IMPORT})), pre


def canon_all(jobs) -> dict[str, dict]:
    cache = json.loads(CANON_CACHE.read_text(encoding="utf-8")) if CANON_CACHE.exists() else {}
    groups: dict[tuple, list] = {}
    for key, (r, g, k) in jobs.items():
        if key in cache:
            continue
        imports, pre = imports_of(r)
        groups.setdefault(imports, []).append(Item(key, imports, f"{pre}\n#probe_goals {lean_str(key)} {k} ({g})"))
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
                    cache[it.item_id] = {"status": "no_hyp" if "no hypothesis" in b else "probe_fail",
                                         "detail": b[:300]}
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
    for (key, goal), (r, g, k, proof) in jobs:
        imports, pre = imports_of(r)
        name = re.sub(r"\W", "_", f"{tag}_{key}_{goal}")
        body = (f"{pre}\nset_option maxHeartbeats 200000 in\n"
                f"probe_prove {name} {k} ({g}) {goal} := by\n  {proof}")
        items.append(Item(f"{key}:{tag}:{goal}", imports, body))
        keys.append((key, goal))
    res = check(items, batch_size=10, workers=LEAN_WORKERS)
    return {kk: res[it.item_id] for kk, it in zip(keys, items)}


def ok(res) -> bool:
    return res.ok and not res.uses_sorry


def flag(proved: set[str]) -> str:
    if "implied" in proved:
        return "implied"
    if "idle" in proved:
        return "idle" if "nimplied" in proved else "idle_unsure"
    return "none"


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    stmts = statements()
    print("statements", len(stmts), flush=True)
    jobs = {f"{r.row_id}~{k}": (r, g, k) for r, g in stmts for k in range(MAX_HYPS)}
    canon = canon_all(jobs)
    good = [k for k in jobs if canon[k]["status"] == "ok"]
    print("probes", Counter(canon[k]["status"] for k in jobs), f"{time.time() - t0:.0f}s", flush=True)

    tac = prove_items([((k, g), (*jobs[k], COMP_TAC)) for k in good for g in GOALS], "q0")
    proved = {k: {g for g in GOALS if ok(tac[(k, g)])} for k in good}
    print("tactic tier", Counter(flag(v) for v in proved.values()), f"{time.time() - t0:.0f}s", flush=True)

    def work(k):
        if "implied" in proved[k]:
            return k, {}
        names = [g for g in ("implied", "idle") if g not in proved[k]]
        if not names:
            names = ["nimplied"] if "nimplied" not in proved[k] else []
        return k, propose(MODEL, jobs[k][0], canon[k]["goals"], names) if names else {}

    with ThreadPoolExecutor(max_workers=12) as pool:
        props = dict(pool.map(work, good))
    shot = prove_items([((k, g), (*jobs[k], p)) for k, gs in props.items() for g, p in gs.items()], "q1")
    for (k, g), res in shot.items():
        if ok(res):
            proved[k].add(g)

    def fix(item):
        (k, g), res = item
        return (k, g), repair(MODEL, jobs[k][0], g, canon[k]["goals"][g], props[k][g], res.errors)

    failed = [((k, g), res) for (k, g), res in shot.items() if not ok(res) and flag(proved[k]) in ("none", "idle_unsure")]
    with ThreadPoolExecutor(max_workers=12) as pool:
        fixes = dict(pool.map(fix, failed))
    for (k, g), res in prove_items([((k, g), (*jobs[k], p)) for (k, g), p in fixes.items() if p], "q2").items():
        if ok(res):
            proved[k].add(g)

    # idle without a nimplied certificate: ask once for the witness
    unsure = [k for k in good if flag(proved[k]) == "idle_unsure"]
    with ThreadPoolExecutor(max_workers=12) as pool:
        wit = dict(pool.map(lambda k: (k, propose(MODEL, jobs[k][0], canon[k]["goals"], ["nimplied"])), unsure))
    for (k, g), res in prove_items([((k, g), (*jobs[k], p)) for k, gs in wit.items() for g, p in gs.items()], "q3").items():
        if ok(res):
            proved[k].add(g)

    flags = Counter()
    per = []
    for k in good:
        r, g, idx = jobs[k]
        f = flag(proved[k])
        flags[f] += 1
        per.append({"key": k, "stmt_id": r.stmt_id, "split": r.split, "k": idx, "flag": f,
                    "proved": sorted(proved[k]), "statement": g, "nl": r.nl,
                    "hyp_goal": canon[k]["goals"]["implied"]})
    summary = {"model": MODEL, "n_statements": len(stmts), "n_probes": len(good), "flags": dict(flags),
               "statements_flagged": len({p["stmt_id"] + p["split"] for p in per if p["flag"] in ("implied", "idle")}),
               "seconds": round(time.time() - t0, 1), "probes": per}
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "probes"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
