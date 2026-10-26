#!/usr/bin/env python3
"""E1: embedding alignment on the G1 pairs.

For every pair where `ExperimentsMathlib.Embed` finds a coercion from a candidate binder
into a reference binder of a type the candidate lacks, the reference is restricted along
the coercion and compared with the candidate by the G1 component pipeline (fixed tactics,
one proposal and one repair round). The extra goal `nsurj` certifies that the coercion is
not surjective. Verdict on the image: classify(proved goals); an image accept together
with `nsurj` becomes `off_image`. A G1 reject is kept (its certificate stands), and an
embedding `unknown` falls back to the G1 verdict.

Usage: e1_embed.py [MODEL]          Writes data/real/e1_results.json.
"""

from __future__ import annotations

import json
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

OUT = ROOT / "data" / "real" / "e1_results.json"
CANON_CACHE = ROOT / "data" / "real" / "e1_canon.json"
G1 = ROOT / "data" / "real" / "g1_results.json"
IMPORT = "ExperimentsMathlib.Embed"
MODEL = sys.argv[1] if len(sys.argv) > 1 else "anthropic/claude-opus-5.5"
LEAN_WORKERS = 1
ALL_GOALS = (*GOALS, "split_r", "split_s", "nsurj")
LLM = (*LLM_GOALS, "nsurj")


def imports_of(r) -> tuple[tuple[str, ...], str]:
    imports, pre = f2.prelude(r)
    return tuple(sorted(set(imports) | {IMPORT})), pre


def canon_all(stmt) -> dict[str, dict]:
    cache = json.loads(CANON_CACHE.read_text(encoding="utf-8")) if CANON_CACHE.exists() else {}
    groups: dict[tuple, list] = {}
    for rid, (r, g, s) in stmt.items():
        if rid in cache:
            continue
        imports, pre = imports_of(r)
        groups.setdefault(imports, []).append(Item(rid, imports, f"{pre}\n#embed_goals {lean_str(rid)} ({g}) ({s})"))
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
                    cache[it.item_id] = {"status": "no_embedding" if "no embedding" in b else "embed_fail",
                                         "detail": b[:300]}
                else:
                    cache[it.item_id] = {
                        "status": "ok",
                        "info": re.search(r"CANON_INFO (.*)", b).group(1),
                        "embedded": re.search(r"CANON_EMBED (.*?)(?=\nCANON_GOAL )", b, flags=re.DOTALL).group(1),
                        "goals": dict(re.findall(r"CANON_GOAL (\w+) ::: (.*?)(?=\nCANON_GOAL |\Z)", b, flags=re.DOTALL)),
                    }
    CANON_CACHE.write_text(json.dumps(cache, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    return cache


def prove_items(jobs, tag: str) -> dict:
    items, keys = [], []
    for (rid, goal), (r, g, s, proof) in jobs:
        imports, pre = imports_of(r)
        body = (f"{pre}\nset_option maxHeartbeats 200000 in\n"
                f"embed_prove {tag}_{goal} ({g}) ({s}) {goal} := by\n  {proof}")
        items.append(Item(f"{rid}:{tag}:{goal}", imports, body))
        keys.append((rid, goal))
    res = check(items, batch_size=10, workers=LEAN_WORKERS)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def ok(res) -> bool:
    return res.ok and not res.uses_sorry


def verdict(proved: set[str]) -> str:
    v = classify(proved - {"nsurj"})
    return "off_image" if v == "accept" and "nsurj" in proved else v


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    rows = {r.row_id: r for r in proofnetverif("test")}
    g1 = {p["row_id"]: p for p in json.loads(G1.read_text(encoding="utf-8"))["pairs"]}
    stmt = {rid: (rows[rid], f2.normalize(to_prop(rows[rid].gold)), f2.normalize(to_prop(rows[rid].pred))) for rid in g1}
    canon = canon_all(stmt)
    good = [rid for rid in stmt if canon[rid]["status"] == "ok"]
    print("embedding", Counter(c["status"] for c in canon.values()), f"{time.time() - t0:.0f}s", flush=True)

    tac = prove_items([((rid, g), (*stmt[rid], SPLIT_TAC if g.startswith("split") else COMP_TAC))
                       for rid in good for g in ALL_GOALS], "e0")
    proved = {rid: {g for g in ALL_GOALS if ok(tac[(rid, g)])} for rid in good}

    def work(rid):
        open_goals = [g for g in LLM if g not in proved[rid]]
        if not open_goals or classify(proved[rid] - {"nsurj"}) == "reject":
            return rid, {}
        return rid, propose(MODEL, stmt[rid][0], canon[rid]["goals"], open_goals)

    with ThreadPoolExecutor(max_workers=12) as pool:
        props = dict(pool.map(work, good))
    shot = prove_items([((rid, g), (*stmt[rid], p)) for rid, gs in props.items() for g, p in gs.items()], "e1")
    for (rid, g), res in shot.items():
        if ok(res):
            proved[rid].add(g)
    failed = [((rid, g), res) for (rid, g), res in shot.items()
              if not ok(res) and verdict(proved[rid]) in ("unknown", "accept")]

    def fix(item):
        (rid, g), res = item
        return (rid, g), repair(MODEL, stmt[rid][0], g, canon[rid]["goals"][g], props[rid][g], res.errors)

    with ThreadPoolExecutor(max_workers=12) as pool:
        fixes = dict(pool.map(fix, failed))
    for (rid, g), res in prove_items([((rid, g), (*stmt[rid], p)) for (rid, g), p in fixes.items() if p], "e2").items():
        if ok(res):
            proved[rid].add(g)

    table = {True: Counter(), False: Counter()}
    per = []
    for rid, p in g1.items():
        before = p["verdict"]
        after = verdict(proved[rid]) if rid in proved else before
        if before == "reject" or after == "unknown":
            after = before
        table[p["label"]][f"{before}->{after}"] += 1
        table[p["label"]][f"final_{after}"] += 1
        per.append({"row_id": rid, "label": p["label"], "g1": before, "embed": after,
                    "embedded": canon[rid].get("embedded"), "proved": sorted(proved.get(rid, ()))})
    out = {"model": MODEL, "label_inequivalent": dict(table[False]), "label_equivalent": dict(table[True]),
           "seconds": round(time.time() - t0, 1), "pairs": per}
    OUT.write_text(json.dumps(out, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in out.items() if k != "pairs"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
