#!/usr/bin/env python3
"""D2: every verdict on every D1 candidate.

Each distinct elaborating candidate `S` of a ProofNet-Verified problem is paired with the
manually corrected reference `R` and judged by

  closed_tactic   closed equivalence, fixed tactics only (f2 T0/T1)
  closed          closed equivalence, tactics + one proposal and one repair round (strong prover)
  comp            ours: canonical goals, tactics + proposal + repair (strong prover), plus the
                  second regrouping tier for decided pairs without `split_r`/`split_s`
  comp_tactic     ours, fixed tactics only
  beq_plus        BEq+ (unless D2_SKIP_BEQ is set)
  judge:*         LLM judges of J1, settings `nl` and `ref`

All Lean work is cached by `runner.check`, all model calls by `llm.chat`, so the script can be
rerun after an interruption at little cost.

Usage: d2_verdicts.py [PROVER]     Writes data/real/d2_verdicts.json.
"""

from __future__ import annotations

import json
import os
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

PROVER = sys.argv[1] if len(sys.argv) > 1 else "anthropic/claude-opus-5.5"
sys.argv = sys.argv[:1] + [PROVER]

import b1_beqplus as b1
import f2_oracle as f2
import g1_full as g1
import g4_pnv as g4
import j1_judge as j1
from f7_component import SPLIT_TAC2, classify
from runner import ROOT

D = ROOT / "data" / "real"
IN = D / "d1_candidates.json"
OUT = D / "d2_verdicts.json"
BEQ_OUT = D / "d2_beqplus.json"
JUDGES = ["openai/gpt-4.1-mini", "anthropic/claude-opus-5.5"]

g1.MODEL = PROVER
g1.CANON_CACHE = D / "d2_canon2.json"
g4.MODEL = PROVER


def complete_splits(stmt, proved) -> None:
    todo = [(rid, g) for rid, ps in proved.items() if classify(ps) in ("accept", "reject")
            for g in ("split_r", "split_s") if g not in ps]
    res = g1.prove_items([((rid, g), (*stmt[rid], SPLIT_TAC2)) for rid, g in todo], "d2s")
    for (rid, g), v in res.items():
        if g1.ok(v):
            proved[rid].add(g)
    print("split tier 2", len(todo), "->", sum(g1.ok(v) for v in res.values()), flush=True)


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    rows, _ = g4.load()
    by = {r.row_id: r for r in rows}
    cands = json.loads(IN.read_text(encoding="utf-8"))["candidates"]
    pairs = [(replace(by[c["problem"]], row_id=c["cand_id"], pred=c["src"]), c["gold"], c["prop"]) for c in cands]
    stmt = {r.row_id: (r, g, s) for r, g, s in pairs}
    print("candidates", len(pairs), "prover", PROVER, flush=True)

    canon = g1.canon_all(pairs)
    print("canon", Counter(c["status"] for c in canon.values()), f"{time.time() - t0:.0f}s", flush=True)
    proved, tactic = g1.component(pairs, stmt, canon, t0)
    complete_splits(stmt, proved)

    cl = g4.closed(pairs, t0)
    cl_tac = {rid: set(s) for rid, s in g4.CLOSED_TACTIC.items()}

    if os.environ.get("D2_SKIP_BEQ"):
        beq = {}
    else:
        beq = {p["row_id"]: p["beq_plus"] for p in b1.run([r for r, _, _ in pairs], BEQ_OUT)["pairs"]}
    print("beq done", f"{time.time() - t0:.0f}s", flush=True)

    xs = [{"set": "D", "row_id": c["cand_id"], "nl": by[c["problem"]].nl, "header": by[c["problem"]].header,
           "ref": by[c["problem"]].gold, "cand": c["src"], "group": "?"} for c in cands]
    jobs = [(m, st, x) for m in JUDGES for st in j1.SETTINGS for x in xs]
    with ThreadPoolExecutor(max_workers=16) as pool:
        jr = list(pool.map(lambda j: ((j[2]["row_id"], j[0], j[1]), j1.judge(*j)["verdict"]), jobs))
    judges: dict[str, dict] = {}
    for (cid, m, st), v in jr:
        judges.setdefault(cid, {})[f"{m.split('/')[-1]}:{st}"] = v
    print("judges done", f"{time.time() - t0:.0f}s", flush=True)

    per = []
    for c in cands:
        cid = c["cand_id"]
        st = canon[cid]["status"]
        per.append({
            "cand_id": cid, "problem": c["problem"], "models": c["models"],
            "closed_tactic": f2.verdict(cl_tac.get(cid, set()))["status"],
            "closed": f2.verdict(cl[cid])["status"],
            "comp": classify(proved[cid]) if st == "ok" else st,
            "comp_tactic": classify(tactic[cid]) if st == "ok" else st,
            "split": st == "ok" and {"split_r", "split_s"} <= proved[cid],
            "proved": sorted(proved.get(cid, ())), "closed_proved": sorted(cl[cid]),
            "beq_plus": beq.get(cid), "judges": judges.get(cid, {}), "canon_info": canon[cid].get("info"),
        })
    summary = {"prover": PROVER, "n": len(per),
               "comp": dict(Counter(p["comp"] for p in per)),
               "closed": dict(Counter(p["closed"] for p in per)),
               "seconds": round(time.time() - t0, 1), "candidates": per}
    OUT.write_text(json.dumps(summary, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "candidates"}, ensure_ascii=False))


if __name__ == "__main__":
    main()
