#!/usr/bin/env python3
"""F8: is the low F7 refutation rate a limit of the method or of the proposer?

Same 100 pairs as F7, with a strong proposer:

1. Re-decompose the pairs F7 could not split (no alignment, split failure).
2. Component goals on every pair with a checked split: F7's fixed tactics, then one
   proposal from the strong model, then one repair round with the Lean errors.
3. Closed goals (G→P, P→G, ¬(G→P), ¬P) with the same model and one repair round.

Verdicts as in F7. Writes data/real/f8_results.json.
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
import f7_component as f7
from llm import chat
from runner import ROOT, Item, check, tactic_body

OUT = ROOT / "data" / "real" / "f8_results.json"
MODEL = sys.argv[1] if len(sys.argv) > 1 else "anthropic/claude-opus-5.5"
MAX_TOKENS = 16384

REPAIR = """Your Lean 4 proof failed. Environment (already present):

{header}

theorem goal : {goal} := by
  {proof}

Lean reported:
{errors}

Give a corrected tactic proof that replaces the proof above, inside one ```lean block.
If you now believe the statement is false, reply with `skip`.
Never use sorry, admit or native_decide."""


def header_of(r) -> str:
    return r.header.strip() + "\nuniverse u\nset_option autoImplicit false"


def clean(body: str) -> str | None:
    if not body.strip() or body.strip() == "skip" or f2.FORBIDDEN.search(body):
        return None
    return tactic_body(body)


def repair(job):
    key, r, goal, proof, errors = job
    msg = REPAIR.format(header=header_of(r), goal=goal, proof=proof, errors=errors[:3000])
    try:
        text = chat(MODEL, [{"role": "user", "content": msg}], temperature=0.2, max_tokens=MAX_TOKENS)
    except RuntimeError:
        return key, None
    from llm import extract_lean
    return key, clean(extract_lean(text))


def check_round(jobs: dict, tag: str) -> tuple[set, dict]:
    """jobs: key -> (row, goal_text, proof). Returns proved keys and failures."""
    items, keys = [], []
    for key, (r, goal, proof) in jobs.items():
        imports, pre = f2.prelude(r)
        name = re.sub(r"\W", "_", f"{tag}_{key[1]}")
        items.append(Item(f"{key[0]}:{tag}:{key[1]}", imports, f"{pre}\n{f7.thm(name, goal, proof, 200000)}"))
        keys.append(key)
    res = check(items, batch_size=10, workers=6)
    ok, fail = set(), {}
    for key, it in zip(keys, items):
        rr = res[it.item_id]
        if rr.ok and not rr.uses_sorry:
            ok.add(key)
        else:
            fail[key] = "\n".join(rr.errors) or ("timeout" if rr.timeout else "failed")
    return ok, fail


def propose_and_repair(initial: dict, tag: str) -> set:
    """initial: key -> (row, goal_text, proof or None)."""
    first = {k: v for k, v in initial.items() if v[2]}
    ok, fail = check_round(first, tag)
    jobs = [(k, initial[k][0], initial[k][1], initial[k][2], err) for k, err in fail.items()]
    with ThreadPoolExecutor(max_workers=int(os.environ.get("LLM_WORKERS", 12))) as pool:
        fixed = dict(pool.map(repair, jobs))
    second = {k: (initial[k][0], initial[k][1], p) for k, p in fixed.items() if p}
    ok2, _ = check_round(second, tag + "r")
    return ok | ok2


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    f7.MODEL = MODEL
    f7.MAX_TOKENS = MAX_TOKENS
    f2.PROPOSER = MODEL
    old = {p["row_id"]: p for p in json.loads(f7.OUT.read_text(encoding="utf-8"))["pairs"]}
    pairs = f7.load_pairs()
    rows = {r.row_id: (r, g, p) for r, g, p, _ in pairs}
    print("model", MODEL, "pairs", len(pairs))

    dec = {rid: p["decomposition"] for rid, p in old.items() if p["verdict"] not in ("no_alignment", "split_fail", "decomp_fail")}
    redo = [(r, g, p, None) for r, g, p, _ in pairs if r.row_id not in dec]
    with ThreadPoolExecutor(max_workers=int(os.environ.get("LLM_WORKERS", 12))) as pool:
        new_dec = dict(pool.map(f7.decompose, redo))
    items, keys = [], []
    for rid, d in new_dec.items():
        if not d or not d.get("aligned"):
            continue
        r, g, p = rows[rid]
        imports, pre = f2.prelude(r)
        for side, orig, h, c in (("r", g, d["Hr"], d["Cr"]), ("s", p, d["Hs"], d["Cs"])):
            goal = f"({orig}) ↔ ({f7.forall(d['binders'], f'({h}) → ({c})')})"
            items.append(Item(f"{rid}:split_{side}", imports, f"{pre}\n{f7.thm('split_' + side, goal, f7.SPLIT_TAC, 100000)}"))
            keys.append((rid, side))
    res = check(items, batch_size=20, workers=6)
    split_ok: dict[str, set] = {}
    for (rid, side), it in zip(keys, items):
        if res[it.item_id].ok and not res[it.item_id].uses_sorry:
            split_ok.setdefault(rid, set()).add(side)
    redo_status = {}
    for rid, d in new_dec.items():
        if d is None:
            redo_status[rid] = "decomp_fail"
        elif not d.get("aligned"):
            redo_status[rid] = "no_alignment"
        elif split_ok.get(rid) == {"r", "s"}:
            redo_status[rid] = "split_ok"
            dec[rid] = d
        else:
            redo_status[rid] = "split_fail"
    print("re-decomposed", len(redo), Counter(redo_status.values()), f"{time.time() - t0:.0f}s")

    proved: dict[str, set] = {rid: set(old[rid]["tactic"]) if rid in old and old[rid]["verdict"] not in ("no_alignment", "split_fail") else set() for rid in dec}
    fresh = [rid for rid in dec if redo_status.get(rid) == "split_ok"]
    items, keys = [], []
    for rid in fresh:
        r = rows[rid][0]
        imports, pre = f2.prelude(r)
        gt = f7.goal_texts(dec[rid])
        for goal in f7.GOALS:
            items.append(Item(f"{rid}:c0:{goal}", imports, f"{pre}\n{f7.thm('c0_' + goal, gt[goal], f7.COMP_TAC, 100000)}"))
            keys.append((rid, goal))
    res = check(items, batch_size=20, workers=6)
    for (rid, goal), it in zip(keys, items):
        if res[it.item_id].ok and not res[it.item_id].uses_sorry:
            proved[rid].add(goal)

    jobs = [(rows[rid][0], dec[rid], [g for g in f7.LLM_GOALS if g not in proved[rid]]) for rid in dec]
    jobs = [j for j in jobs if j[2]]
    with ThreadPoolExecutor(max_workers=int(os.environ.get("LLM_WORKERS", 12))) as pool:
        props = dict(pool.map(f7.propose, jobs))
    initial = {}
    for rid, pr in props.items():
        gt = f7.goal_texts(dec[rid])
        for goal in f7.LLM_GOALS:
            if goal not in proved[rid]:
                initial[(rid, goal)] = (rows[rid][0], gt[goal], pr.get(goal))
    for rid, goal in propose_and_repair(initial, "c8"):
        proved[rid].add(goal)
    print("component done", f"{time.time() - t0:.0f}s")

    f2_t1 = {p["row_id"]: set(p["t1"]) for p in json.loads(f2.OUT.read_text(encoding="utf-8"))["pairs"]}
    closed = {rid: set(f2_t1[rid]) for rid in rows}
    cjobs = [(rows[rid][0], rows[rid][1], rows[rid][2], goal)
             for rid in rows for goal in f2.LLM_GOALS if goal not in closed[rid]]

    def cwork(job):
        r, g, p, goal = job
        try:
            return (r.row_id, goal), f2.propose(r, goal, f2.goal_text(goal, g, p))
        except RuntimeError:
            return (r.row_id, goal), None

    with ThreadPoolExecutor(max_workers=int(os.environ.get("LLM_WORKERS", 12))) as pool:
        cprops = dict(pool.map(cwork, cjobs))
    cinit = {k: (rows[k[0]][0], f2.goal_text(k[1], rows[k[0]][1], rows[k[0]][2]), v) for k, v in cprops.items()}
    for rid, goal in propose_and_repair(cinit, "k8"):
        closed[rid].add(goal)
    print("closed done", f"{time.time() - t0:.0f}s", "jobs", len(cjobs))

    table = {True: Counter(), False: Counter()}
    per_pair = []
    for rid, (r, _, _) in rows.items():
        cs = f2.verdict(closed[rid])["status"]
        if rid in dec:
            v = f7.classify(proved[rid])
        else:
            v = redo_status.get(rid, "split_fail")
        f7v = old[rid]["verdict"]
        table[r.correct][v] += 1
        table[r.correct][f"closed_{cs}"] += 1
        table[r.correct][f"f7_{f7v}->{v}"] += 1
        per_pair.append({"row_id": rid, "label": r.correct, "closed": cs, "closed_proved": sorted(closed[rid]),
                         "verdict": v, "f7_verdict": f7v, "proved": sorted(proved.get(rid, ())),
                         "decomposition": dec.get(rid) or new_dec.get(rid)})
    summary = {
        "model": MODEL,
        "label_inequivalent": dict(table[False]),
        "label_equivalent": dict(table[True]),
        "closed_llm_jobs": len(cjobs),
        "seconds": round(time.time() - t0, 1),
        "pairs": per_pair,
    }
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "pairs"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
