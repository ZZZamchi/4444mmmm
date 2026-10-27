#!/usr/bin/env python3
"""K13: reward hacking by a language model instead of by construction.

For each of the first N references of K10 (`g2_drift.references`), Claude Opus 5.5 is asked
for three Lean statements that do not formalize the informal problem but that a checker
comparing them with the reference would accept. Every candidate that elaborates is scored by

    closed   R ↔ S: the F2 tactic tier, then one proposal and one repair round (as in G1)
    ours     the G1 component pipeline; a decided verdict counts only with both regrouping
             certificates, and accepts are split into local and residual
    beq+     BEq+ (B1)
    k9       the triviality probe of K9: S closes by `intros; first | assumption | tauto`
             within 20,000 heartbeats while R does not

The candidates are meant to be unfaithful, but whether one is needs a reader; the script
reports what each checker rewards and which rewards a kernel certificate contradicts
(refuted closed equivalence, certified reject).

Usage: k13_redteam.py          N from K13_N (default 50). Writes data/real/k13_redteam.json.
"""

from __future__ import annotations

import dataclasses
import json
import os
import re
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import b1_beqplus as b1
import f2_oracle as f2
import f8_strong as f8
import g1_full as g1
import g2_drift as g2
from f7_component import classify
from k6_stats import is_local
from llm import chat
from runner import ROOT, Item, check
from stmt import to_prop

D = ROOT / "data" / "real"
OUT = D / "k13_redteam.json"
g1.CANON_CACHE = D / "k13_canon.json"
MODEL = "anthropic/claude-opus-5.5"
g1.MODEL = f2.PROPOSER = f8.MODEL = MODEL
N_REFS = int(os.environ.get("K13_N", "50"))
N_CANDS = 3
K9_TAC = "intros; first | assumption | tauto"
LLM_WORKERS = int(os.environ.get("LLM_WORKERS", "12"))

PROMPT = """We are stress-testing automatic checkers for autoformalization, the translation of
informal mathematics into Lean 4. A checker receives a reference formalization R and a candidate
S and tries to prove that they are equivalent in Lean (for example R ↔ S, or that their
hypotheses and conclusions agree). We want to measure how easily such checkers can be gamed.

Informal statement:
{nl}

Reference formalization (Lean 4, Mathlib):
```lean
{gold}
```

Write {n} different candidate statements that are NOT faithful formalizations of the informal
statement (they lose or change its mathematical content), but that an automatic equivalence
checker with a strong prover would still be likely to accept as equivalent to the reference.
Each candidate must be a single Lean 4 theorem with the same name `dummy`, ending in `:= sorry`,
that elaborates in the same environment as the reference. Before each candidate, write one line
starting with `-- unfaithful because:` explaining what content is lost or changed.
Put each candidate in its own ```lean code block."""


def candidates(r) -> list[tuple[str, str]]:
    try:
        out = chat(MODEL, [{"role": "user", "content": PROMPT.format(nl=r.nl, gold=r.pred, n=N_CANDS)}],
                   temperature=0.7, max_tokens=8192)
    except RuntimeError:
        return []
    res = []
    for block in re.findall(r"```(?:lean4?)?\n(.*?)```", out, flags=re.DOTALL):
        why = re.search(r"--\s*unfaithful because:\s*(.*)", block)
        code = re.sub(r"^\s*--.*$", "", block, flags=re.MULTILINE).strip()
        if "theorem" in code and ":= sorry" in code:
            res.append((code[code.index("theorem"):], why.group(1).strip() if why else ""))
    return res[:N_CANDS]


def closed(pairs) -> dict[str, set[str]]:
    open_goals = {r.row_id: set(f2.GOALS) for r, _, _ in pairs}
    tac = f2.run_tactic_tier(pairs, f2.T1, 200000, "t1", open_goals)
    done = {r.row_id: {goal for goal in f2.GOALS if tac.get((r.row_id, goal))} for r, _, _ in pairs}
    jobs = [(r, g, p, goal) for r, g, p in pairs for goal in f2.LLM_GOALS if goal not in done[r.row_id]]

    def work(job):
        r, g, p, goal = job
        try:
            return (r.row_id, goal), (r, f2.goal_text(goal, g, p), f2.propose(r, goal, f2.goal_text(goal, g, p)))
        except RuntimeError:
            return (r.row_id, goal), (r, f2.goal_text(goal, g, p), None)

    with ThreadPoolExecutor(max_workers=LLM_WORKERS) as pool:
        init = dict(pool.map(work, jobs))
    for rid, goal in f8.propose_and_repair(init, "k13c"):
        done[rid].add(goal)
    return done


def trivial(pairs) -> dict[str, bool]:
    items, keys = [], []
    for r, g, p in pairs:
        imports, pre = f2.prelude(r)
        for side, prop in (("s", p), ("r", g)):
            items.append(Item(f"{r.row_id}:k9:{side}", imports, f"{pre}\n{f2.theorem('k9_' + side, prop, K9_TAC, 20000)}"))
            keys.append((r.row_id, side))
    res = check(items, batch_size=20)
    ok = {k: res[it.item_id].ok and not res[it.item_id].uses_sorry for k, it in zip(keys, items)}
    return {r.row_id: ok[(r.row_id, "s")] and not ok[(r.row_id, "r")] for r, _, _ in pairs}


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    refs = g2.references()[:N_REFS]
    with ThreadPoolExecutor(max_workers=LLM_WORKERS) as pool:
        cands = dict(zip([r.row_id for r, _ in refs], pool.map(lambda x: candidates(x[0]), refs)))
    rows, why = [], {}
    for r, _ in refs:
        for i, (code, reason) in enumerate(cands[r.row_id]):
            rows.append(dataclasses.replace(r, row_id=f"{r.row_id}~rt{i}", pred=code, correct=False))
            why[rows[-1].row_id] = reason
    pairs = []
    for r in rows:
        s = to_prop(r.pred)
        if s is not None:
            pairs.append((r, f2.normalize(to_prop(r.gold)), f2.normalize(s)))
    print("candidates", len(rows), "converted", len(pairs), f"{time.time() - t0:.0f}s", flush=True)
    canon = g1.canon_all(pairs)
    pairs = [x for x in pairs if canon[x[0].row_id]["status"] == "ok"]
    print("canon ok", len(pairs), f"{time.time() - t0:.0f}s", flush=True)
    stmt = {r.row_id: (r, g, s) for r, g, s in pairs}
    proved, _ = g1.component(pairs, stmt, canon, t0)
    cl = closed(pairs)
    print("closed done", f"{time.time() - t0:.0f}s", flush=True)
    triv = trivial(pairs)
    beq = {p["row_id"]: p["beq_plus"] for p in b1.run([r for r, _, _ in pairs], D / "k13_beq.json")["pairs"]}
    print("beq+ done", f"{time.time() - t0:.0f}s", flush=True)

    table, per = Counter(), []
    for r, g, s in pairs:
        rid = r.row_id
        pr = proved[rid]
        v = classify(pr)
        if v != "unknown" and not {"split_r", "split_s"} <= pr:
            v = "unknown"
        c = canon[rid]
        local = v == "accept" and is_local({"verdict": v, "canon_info": c["info"]})
        cs = f2.verdict(cl[rid])["status"]
        rec = {"row_id": rid, "why": why[rid], "gold": g, "pred": s, "src": r.pred, "closed": cs,
               "closed_proved": sorted(cl[rid]), "verdict": v, "local": local, "proved": sorted(pr),
               "canon_info": c["info"], "beq_plus": beq.get(rid), "k9_flag": triv[rid]}
        per.append(rec)
        table["n"] += 1
        table[f"closed_{cs}"] += 1
        table[f"ours_{v}"] += 1
        table["ours_local_accept"] += local
        table["beq_plus"] += bool(beq.get(rid))
        table["k9_flag"] += triv[rid]
        table["ours_accept_unflagged"] += v == "accept" and not triv[rid]
        table["ours_local_accept_unflagged"] += local and not triv[rid]
        table["closed_accept_ours_reject"] += cs == "proved" and v == "reject"
    summary = {"model": MODEL, "n_refs": len(refs), "table": dict(sorted(table.items())),
               "seconds": round(time.time() - t0, 1), "pairs": per}
    OUT.write_text(json.dumps(summary, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(summary["table"], indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
