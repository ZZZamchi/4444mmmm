#!/usr/bin/env python3
"""G1: closed vs component verdicts on all 300 F2 pairs, one strong proposer for both.

Component side: canonical telescopes from `ExperimentsMathlib.CanonV2` (final negations
kept in the conclusion, independent hypotheses hoisted past the cut), fixed tactics, one
proposal and one repair round, all checked by `canon2_prove` against kernel goals.
Closed side: F2 tactic tier, then the same proposer with one repair round (as in F8).

Usage: g1_full.py [MODEL]          Writes data/real/g1_results.json.
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
import f8_strong as f8
from f7_component import COMP_TAC, GOALS, LLM_GOALS, MAX_TOKENS, PROVE, SPLIT_TAC, classify
from f8_provers import clean
from f9_canon import header_of, lean_str, repair
from llm import chat
from realdata import proofnetverif
from runner import ROOT, Item, _build, _run_file, check
from stmt import to_prop

OUT = ROOT / "data" / "real" / "g1_results.json"
CANON_CACHE = ROOT / "data" / "real" / "g1_canon2.json"
CANON_IMPORT = "ExperimentsMathlib.CanonV2"
MODEL = sys.argv[1] if len(sys.argv) > 1 else "anthropic/claude-opus-5.5"


def parse_sections(text: str, names: list[str]) -> dict[str, str]:
    """First lean block of each `### name` section; prose between header and block is allowed."""
    out = {}
    parts = re.split(r"^###\s*(\w+)\s*$", text, flags=re.MULTILINE)
    for name, body in zip(parts[1::2], parts[2::2]):
        m = re.search(r"```(?:lean4?)?\n(.*?)```", body, flags=re.DOTALL)
        p = clean(m.group(1)) if m else None
        if name in names and p and name not in out:
            out[name] = p
    return out


def propose(model, r, goals: dict[str, str], names: list[str]) -> dict[str, str]:
    text = "\n\n".join(f"theorem {n} : {goals[n]} := by\n  sorry" for n in names)
    try:
        out = chat(model, [{"role": "user", "content": PROVE.format(header=header_of(r), goals=text)}],
                   temperature=0.2, max_tokens=MAX_TOKENS)
    except RuntimeError:
        return {}
    return parse_sections(out, names)


def imports_of(r) -> tuple[tuple[str, ...], str]:
    imports, pre = f2.prelude(r)
    return tuple(sorted(set(imports) | {CANON_IMPORT})), pre


def canon_all(pairs) -> dict[str, dict]:
    cache = json.loads(CANON_CACHE.read_text(encoding="utf-8")) if CANON_CACHE.exists() else {}
    groups: dict[tuple, list] = {}
    for r, g, s in pairs:
        if r.row_id in cache:
            continue
        imports, pre = imports_of(r)
        groups.setdefault(imports, []).append(
            Item(r.row_id, imports, f"{pre}\n#canon2_goals {lean_str(r.row_id)} ({g}) ({s})"))
    batches = [g[i:i + 10] for g in groups.values() for i in range(0, len(g), 10)]

    def run(batch):
        out, _ = _run_file(_build(batch)[0], 900)
        return batch, out

    with ThreadPoolExecutor(max_workers=int(os.environ.get("LEAN_WORKERS", 6))) as pool:
        for batch, out in pool.map(run, batches):
            blocks = dict(re.findall(r"CANON_BEGIN (\S+)\n(.*?)\n?CANON_END \1", out, flags=re.DOTALL))
            for it in batch:
                b = blocks.get(it.item_id)
                if b is None:
                    cache[it.item_id] = {"status": "elab_fail"}
                elif b.startswith("CANON_FAIL"):
                    cache[it.item_id] = {"status": "canon_fail", "detail": b[:600]}
                else:
                    info = re.search(r"CANON_INFO (.*)", b).group(1)
                    goals = dict(re.findall(r"CANON_GOAL (\w+) ::: (.*?)(?=\nCANON_GOAL |\Z)", b, flags=re.DOTALL))
                    cache[it.item_id] = {"status": "ok", "info": info, "goals": goals}
    if batches:
        # Several provers share this cache; an atomic replace keeps concurrent readers from
        # seeing a partly written file.
        tmp = CANON_CACHE.with_suffix(f".{os.getpid()}.tmp")
        tmp.write_text(json.dumps(cache, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
        os.replace(tmp, CANON_CACHE)
    return cache


def prove_items(jobs, tag: str) -> dict:
    """jobs: list of ((rid, goal), (row, gold, pred, proof))."""
    items, keys = [], []
    for (rid, goal), (r, g, s, proof) in jobs:
        imports, pre = imports_of(r)
        body = (f"{pre}\nset_option maxHeartbeats 200000 in\n"
                f"canon2_prove {tag}_{goal} ({g}) ({s}) {goal} := by\n  {proof}")
        items.append(Item(f"{rid}:{tag}:{goal}", imports, body))
        keys.append((rid, goal))
    res = check(items, batch_size=10, workers=6)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def ok(res) -> bool:
    return res.ok and not res.uses_sorry


def component(pairs, stmt, canon, t0) -> tuple[dict, dict]:
    good = [r.row_id for r, _, _ in pairs if canon[r.row_id]["status"] == "ok"]
    all_goals = (*GOALS, "split_r", "split_s")
    jobs = [((rid, g), (*stmt[rid], SPLIT_TAC if g.startswith("split") else COMP_TAC)) for rid in good for g in all_goals]
    tac = prove_items(jobs, "g0")
    proved = {rid: {g for g in all_goals if ok(tac[(rid, g)])} for rid in good}
    tactic = {rid: set(v) for rid, v in proved.items()}
    print("tactic tier", Counter(classify(v) for v in proved.values()), f"{time.time() - t0:.0f}s", flush=True)

    open_goals = {rid: [g for g in LLM_GOALS if g not in proved[rid]] for rid in good}

    def work(rid):
        if not open_goals[rid] or classify(proved[rid]) == "reject":
            return rid, {}
        return rid, propose(MODEL, stmt[rid][0], canon[rid]["goals"], open_goals[rid])

    with ThreadPoolExecutor(max_workers=int(os.environ.get("LLM_WORKERS", 12))) as pool:
        props = dict(pool.map(work, good))
    shot = prove_items([((rid, g), (*stmt[rid], p)) for rid, gs in props.items() for g, p in gs.items()], "g1")
    for (rid, g), res in shot.items():
        if ok(res):
            proved[rid].add(g)
    failed = [((rid, g), res) for (rid, g), res in shot.items() if not ok(res) and classify(proved[rid]) == "unknown"]

    def fix(item):
        (rid, g), res = item
        return (rid, g), repair(MODEL, stmt[rid][0], g, canon[rid]["goals"][g], props[rid][g], res.errors)

    with ThreadPoolExecutor(max_workers=int(os.environ.get("LLM_WORKERS", 12))) as pool:
        fixes = dict(pool.map(fix, failed))
    for (rid, g), res in prove_items([((rid, g), (*stmt[rid], p)) for (rid, g), p in fixes.items() if p], "g2").items():
        if ok(res):
            proved[rid].add(g)
    print("component done", f"{time.time() - t0:.0f}s", flush=True)
    return proved, tactic


def closed(pairs, t0) -> dict:
    if OUT.exists():
        prev = json.loads(OUT.read_text(encoding="utf-8"))
        if prev.get("model") == MODEL:
            print("closed: reusing", OUT.name, flush=True)
            return {p["row_id"]: set(p["closed_proved"]) for p in prev["pairs"]}
    f8.MODEL = MODEL
    f2.PROPOSER = MODEL
    t1 = {p["row_id"]: set(p["t1"]) for p in json.loads(f2.OUT.read_text(encoding="utf-8"))["pairs"]}
    done = {r.row_id: set(t1[r.row_id]) for r, _, _ in pairs}
    jobs = [(r, g, p, goal) for r, g, p in pairs for goal in f2.LLM_GOALS if goal not in done[r.row_id]]

    def work(job):
        r, g, p, goal = job
        try:
            return (r.row_id, goal), (r, f2.goal_text(goal, g, p), f2.propose(r, goal, f2.goal_text(goal, g, p)))
        except RuntimeError:
            return (r.row_id, goal), (r, f2.goal_text(goal, g, p), None)

    with ThreadPoolExecutor(max_workers=int(os.environ.get("LLM_WORKERS", 12))) as pool:
        init = dict(pool.map(work, jobs))
    for rid, goal in f8.propose_and_repair(init, "k8"):
        done[rid].add(goal)
    print("closed done", f"{time.time() - t0:.0f}s", "jobs", len(jobs), flush=True)
    return done


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    rows = {r.row_id: r for r in proofnetverif("test")}
    f2_pairs = json.loads(f2.OUT.read_text(encoding="utf-8"))["pairs"]
    pairs = [(rows[p["row_id"]], f2.normalize(to_prop(rows[p["row_id"]].gold)), f2.normalize(to_prop(rows[p["row_id"]].pred)))
             for p in f2_pairs]
    stmt = {r.row_id: (r, g, s) for r, g, s in pairs}
    print("model", MODEL, "pairs", len(pairs), flush=True)

    canon = canon_all(pairs)
    print("canon", Counter(c["status"] for c in canon.values()), f"{time.time() - t0:.0f}s", flush=True)
    proved, tactic = component(pairs, stmt, canon, t0)
    cl = closed(pairs, t0)

    table = {True: Counter(), False: Counter()}
    per_pair = []
    for r, _, _ in pairs:
        rid = r.row_id
        cs = f2.verdict(cl[rid])["status"]
        c = canon[rid]
        if c["status"] != "ok":
            v, shared, split = c["status"], None, False
        else:
            v = classify(proved[rid])
            shared = int(re.search(r"shared=(\d+)", c["info"]).group(1))
            split = {"split_r", "split_s"} <= proved[rid]
        t = table[r.correct]
        t[f"closed_{cs}"] += 1
        t[f"comp_{v}"] += 1
        t[f"comp_{v}_{'shared0' if not shared else 'shared>0'}"] += 1
        t[f"comp_{v}_{'split' if split else 'nosplit'}"] += 1
        t[f"closed_{cs}->comp_{v}"] += 1
        if cs == "refuted" or v == "reject":
            t["union_reject"] += 1
        per_pair.append({"row_id": rid, "label": r.correct, "closed": cs, "closed_proved": sorted(cl[rid]),
                         "verdict": v, "proved": sorted(proved.get(rid, ())), "tactic": sorted(tactic.get(rid, ())),
                         "shared": shared, "split_checked": split, "canon_info": c.get("info")})
    summary = {"model": MODEL, "label_inequivalent": dict(table[False]), "label_equivalent": dict(table[True]),
               "seconds": round(time.time() - t0, 1), "pairs": per_pair}
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "pairs"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
