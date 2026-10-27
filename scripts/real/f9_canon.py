#!/usr/bin/env python3
"""F9: component-level comparison with Lean-computed canonical telescopes.

Same 100 ProofNetVerif pairs as F7, but the split and the variable alignment are no longer
proposed by an LLM: `#canon_goals` (lean/ExperimentsMathlib/Canon.lean) peels every leading
binder, applies the one-point rule, and matches data binders by definitional equality of
types. Pairs with no type-consistent matching are reported as structural mismatches.

Component goals are then tried with fixed tactics and, per model, one LLM proposal plus one
repair round fed with Lean's errors. Proofs are checked against the kernel goal expressions
by `canon_prove`, so no goal text is re-parsed.

Usage: f9_canon.py [MODEL ...]     Writes data/real/f9_results.json.
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

from f2_oracle import normalize, prelude
from f7_component import COMP_TAC, GOALS, LLM_GOALS, MAX_TOKENS, OUT as F7_OUT, PROVE, SPLIT_TAC, classify
from f8_provers import REPAIR, clean
from llm import chat
from realdata import proofnetverif
from runner import ROOT, Item, _build, _run_file, check
from stmt import to_prop

OUT = ROOT / "data" / "real" / "f9_results.json"
CANON_CACHE = ROOT / "data" / "real" / "f9_canon.json"
CANON_IMPORT = "ExperimentsMathlib.Canon"
DEFAULT_MODELS = ("deepseek/deepseek-v4.1-flash", "anthropic/claude-sonnet-5.5", "openai/gpt-5.6-sol")


def lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def canon_all(pairs) -> dict[str, dict]:
    cache = json.loads(CANON_CACHE.read_text(encoding="utf-8")) if CANON_CACHE.exists() else {}
    todo = [p for p in pairs if p[0].row_id not in cache]
    groups: dict[tuple, list] = {}
    for r, g, s in todo:
        imports, pre = prelude(r)
        groups.setdefault(tuple(sorted(set(imports) | {CANON_IMPORT})), []).append(
            Item(r.row_id, tuple(sorted(set(imports) | {CANON_IMPORT})),
                 f"{pre}\n#canon_goals {lean_str(r.row_id)} ({g}) ({s})"))
    batches = [g[i:i + 10] for g in groups.values() for i in range(0, len(g), 10)]

    def run(batch):
        out, _ = _run_file(_build(batch)[0], 900)
        return batch, out

    with ThreadPoolExecutor(max_workers=6) as pool:
        for batch, out in pool.map(run, batches):
            blocks = dict(re.findall(r"CANON_BEGIN (\S+)\n(.*?)\n?CANON_END \1", out, flags=re.DOTALL))
            for it in batch:
                b = blocks.get(it.item_id)
                if b is None:
                    cache[it.item_id] = {"status": "elab_fail", "detail": out[-1500:]}
                elif b.startswith("CANON_FAIL"):
                    reason = b.split()[2] if len(b.split()) > 2 else b
                    cache[it.item_id] = {"status": reason, "detail": b[:600]}
                else:
                    info = re.search(r"CANON_INFO (.*)", b).group(1)
                    goals = dict(re.findall(r"CANON_GOAL (\w+) ::: (.*?)(?=\nCANON_GOAL |\Z)", b, flags=re.DOTALL))
                    cache[it.item_id] = {"status": "ok", "info": info, "goals": goals}
    CANON_CACHE.write_text(json.dumps(cache, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    return cache


def prove_items(jobs, tag: str) -> dict:
    """jobs: list of ((rid, goal), (row, gold, pred, proof))."""
    items, keys = [], []
    for (rid, goal), (r, g, s, proof) in jobs:
        imports, pre = prelude(r)
        imports = tuple(sorted(set(imports) | {CANON_IMPORT}))
        body = (f"{pre}\nset_option maxHeartbeats 200000 in\n"
                f"canon_prove {tag}_{goal} ({g}) ({s}) {goal} := by\n  {proof}")
        items.append(Item(f"{rid}:{tag}:{goal}", imports, body))
        keys.append((rid, goal))
    res = check(items, batch_size=10, workers=6)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def header_of(r) -> str:
    return r.header.strip() + "\nuniverse u\nset_option autoImplicit false"


def propose(model, r, goals: dict[str, str], names: list[str]) -> dict[str, str]:
    text = "\n\n".join(f"theorem {n} : {goals[n]} := by\n  sorry" for n in names)
    try:
        out = chat(model, [{"role": "user", "content": PROVE.format(header=header_of(r), goals=text)}],
                   temperature=0.2, max_tokens=MAX_TOKENS)
    except RuntimeError:
        return {}
    res = {}
    for name, body in re.findall(r"###\s*(\w+)\s*```(?:lean)?\n(.*?)```", out, flags=re.DOTALL):
        p = clean(body)
        if name in names and p:
            res[name] = p
    return res


def repair(model, r, goal_name, goal_text, proof, errors) -> str | None:
    msg = REPAIR.format(header=header_of(r), name=goal_name, goal=goal_text, proof=proof,
                        errors="\n".join(errors)[:3000])
    try:
        out = chat(model, [{"role": "user", "content": msg}], temperature=0.2, max_tokens=MAX_TOKENS)
    except RuntimeError:
        return None
    m = re.search(r"```(?:lean)?\n(.*?)```", out, flags=re.DOTALL)
    return clean(m.group(1)) if m else None


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    models = tuple(sys.argv[1:]) or DEFAULT_MODELS
    t0 = time.time()
    f7 = json.loads(F7_OUT.read_text(encoding="utf-8"))
    rows = {r.row_id: r for r in proofnetverif("test")}
    meta = {p["row_id"]: p for p in f7["pairs"]}
    pairs = [(rows[rid], normalize(to_prop(rows[rid].gold)), normalize(to_prop(rows[rid].pred))) for rid in meta]
    stmt = {r.row_id: (r, g, s) for r, g, s in pairs}

    canon = canon_all(pairs)
    print("canon", Counter((meta[rid]["label"], c["status"]) for rid, c in canon.items() if rid in meta),
          f"{time.time() - t0:.0f}s")
    ok = [rid for rid in meta if canon[rid]["status"] == "ok"]

    jobs = [((rid, g), (*stmt[rid], SPLIT_TAC if g.startswith("split") else COMP_TAC))
            for rid in ok for g in (*GOALS, "split_r", "split_s")]
    tac = prove_items(jobs, "c0")
    tactic = {rid: {g for g in (*GOALS, "split_r", "split_s") if tac[(rid, g)].ok and not tac[(rid, g)].uses_sorry}
              for rid in ok}
    print("tactic tier", Counter((meta[r]["label"], classify(tactic[r])) for r in ok),
          "split checked", sum({"split_r", "split_s"} <= tactic[r] for r in ok), f"{time.time() - t0:.0f}s")

    per_model = {}
    for model in models:
        tag = re.sub(r"\W", "_", model.split("/")[1])
        open_goals = {rid: [g for g in LLM_GOALS if g not in tactic[rid]] for rid in ok}

        def work(rid):
            if not open_goals[rid] or classify(tactic[rid]) == "reject":
                return rid, {}
            return rid, propose(model, stmt[rid][0], canon[rid]["goals"], open_goals[rid])

        with ThreadPoolExecutor(max_workers=12) as pool:
            props = dict(pool.map(work, ok))
        jobs = [((rid, g), (*stmt[rid], pr)) for rid, gs in props.items() for g, pr in gs.items()]
        shot = prove_items(jobs, tag + "_s")
        proved = {rid: set(tactic[rid]) for rid in ok}
        for (rid, g), res in shot.items():
            if res.ok and not res.uses_sorry:
                proved[rid].add(g)
        one_shot = {rid: classify(proved[rid]) for rid in ok}

        failed = [((rid, g), res) for (rid, g), res in shot.items()
                  if not res.ok and classify(proved[rid]) == "unknown"]

        def fix(item):
            (rid, g), res = item
            return (rid, g), repair(model, stmt[rid][0], g, canon[rid]["goals"][g], props[rid][g], res.errors)

        with ThreadPoolExecutor(max_workers=12) as pool:
            fixes = dict(pool.map(fix, failed))
        jobs = [((rid, g), (*stmt[rid], pr)) for (rid, g), pr in fixes.items() if pr]
        for (rid, g), res in prove_items(jobs, tag + "_r").items():
            if res.ok and not res.uses_sorry:
                proved[rid].add(g)
        per_model[model] = {"one_shot": one_shot, "repair": {rid: classify(proved[rid]) for rid in ok},
                            "proved": {rid: sorted(proved[rid]) for rid in ok}}
        print(model, "one-shot", Counter((meta[r]["label"], v) for r, v in one_shot.items()))
        print(model, "repair", Counter((meta[r]["label"], v) for r, v in per_model[model]["repair"].items()),
              f"{time.time() - t0:.0f}s")

    union = {rid: classify(set().union(*(set(per_model[m]["proved"][rid]) for m in models)) if models else tactic[rid])
             for rid in ok}
    table = {}
    for lab in (False, True):
        c = Counter()
        for rid in meta:
            if meta[rid]["label"] != lab:
                continue
            st = canon[rid]["status"]
            c[f"canon_{st}"] += 1
            c[f"f7_{meta[rid]['verdict']}"] += 1
            c[f"closed_{meta[rid]['closed']}"] += 1
            if st == "ok":
                c[f"tactic_{classify(tactic[rid])}"] += 1
                c[f"union_{union[rid]}"] += 1
                for m in models:
                    c[f"{m}_{per_model[m]['repair'][rid]}"] += 1
        table["label_equivalent" if lab else "label_inequivalent"] = dict(c)
    summary = {
        "models": list(models),
        **table,
        "seconds": round(time.time() - t0, 1),
        "pairs": [{"row_id": rid, "label": meta[rid]["label"], "closed": meta[rid]["closed"],
                   "f7": meta[rid]["verdict"], "canon": canon[rid]["status"],
                   "canon_info": canon[rid].get("info"),
                   "tactic": sorted(tactic.get(rid, ())),
                   "verdicts": {m: per_model[m]["repair"].get(rid) for m in models},
                   "proved": {m: per_model[m]["proved"].get(rid) for m in models},
                   "union": union.get(rid)} for rid in meta],
    }
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "pairs"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
