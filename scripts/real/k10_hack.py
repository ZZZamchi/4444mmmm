#!/usr/bin/env python3
"""K10: reward hacking by construction.

Each sampled reference R = (Γ, H, C) gets three hacking candidates built by
`ExperimentsMathlib.Mutate` on its canonical telescope, plus R itself as the control:

    top     (Γ, H, True)
    absorb  (Γ, H ∧ C, C)
    vac     (Γ, H ∧ False, C)
    topsimp     (Γ, H, ∀ k : ℕ, 0 + k = k)          as `top` and `absorb`, but propositional
    absorbsimp  (Γ, H ∧ (∀ k : ℕ, k = k → C), C)    logic does not close them; one `simp` does

None of them formalizes the problem, and each is closed-equivalent to R exactly when R holds:
the direction R → S is trivial, so a checker accepts S as soon as it proves R. Every candidate
is scored by

    closed   the goal R ↔ S: fixed tactics, then one proposal and one repair round per model
    ours     the component pipeline of G1 (fixed tactics, one proposal and one repair round),
             a decided verdict counting only with both regrouping certificates
    beq+     BEq+ (B1) on the same edits applied to the source statement
    k9       the logic-level trivialization probe of K9 on S (`intros; first | assumption | tauto`)

Usage: k10_hack.py          N_REFS from K10_N (default 80). Writes data/real/k10_hack.json.
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
import g2_drift as g2
from f7_component import COMP_TAC, GOALS, LLM_GOALS, SPLIT_TAC, SPLIT_TAC2, classify
from f9_canon import repair
from g1_full import propose
from runner import ROOT, Item, check

D = ROOT / "data" / "real"
OUT = D / "k10_hack.json"
g2.CANON_CACHE = D / "k10_canon.json"
g2.LEAN_WORKERS = b1.LEAN_WORKERS = int(os.environ.get("LEAN_WORKERS", "4"))
KINDS = tuple(os.environ.get("K10_KINDS", "id,top,absorb,vac,topsimp,absorbsimp").split(","))
MODELS = ("openai/gpt-4.1-mini", "anthropic/claude-opus-5.5")
N_REFS = int(os.environ.get("K10_N", "80"))
CLOSED_TAC = f"constructor <;> ({f2.T1})"
K9_TAC = "intros; first | assumption | tauto"
K9_HEARTBEATS = 20000
LLM_WORKERS = int(os.environ.get("LLM_WORKERS", "12"))
SPLITS = ("split_r", "split_s")


def ok(res) -> bool:
    return res.ok and not res.uses_sorry


def prove(jobs, tag: str, heartbeats: int = 200000) -> dict:
    """jobs: list of ((key, goal), (row, gold, kind, proof))."""
    items, keys = [], []
    for (key, goal), (r, g, kind, proof) in jobs:
        imports, pre = g2.imports_of(r)
        name = re.sub(r"\W", "_", f"{tag}_{key}_{goal}")
        body = (f"{pre}\nset_option maxHeartbeats {heartbeats} in\n"
                f"mutant_prove {name} {kind} ({g}) {goal} := by\n  {proof}")
        items.append(Item(f"{key}:{tag}:{goal}", imports, body))
        keys.append((key, goal))
    res = check(items, batch_size=10, workers=g2.LEAN_WORKERS)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def hack_src(code: str, kind: str) -> str | None:
    idx = b1.split_conclusion(code)
    end = code.rfind(":=")
    if not idx or end <= idx:
        return None
    head, concl = code[:idx].rstrip(), code[idx + 1:end].strip()
    return {
        "id": code,
        "top": f"{head} :\n  True := sorry",
        "absorb": f"{head} (habs : {concl}) :\n  {concl} := sorry",
        "vac": f"{head} (hvac : False) :\n  {concl} := sorry",
        "topsimp": f"{head} :\n  ∀ k_hack : ℕ, 0 + k_hack = k_hack := sorry",
        "absorbsimp": f"{head} (habs : ∀ k_hack : ℕ, k_hack = k_hack → ({concl})) :\n  {concl} := sorry",
    }[kind]


def verdict(proved: set[str]) -> str:
    v = classify(proved)
    return v if v == "unknown" or set(SPLITS) <= proved else f"{v}_uncertified"


def run_model(model: str, jobs, canon, base: dict[str, set[str]]) -> dict[str, set[str]]:
    """Returns {key: proved goals}, starting from the tactic tier `base`."""
    proved = {k: set(v) for k, v in base.items()}

    def work(k):
        open_goals = [g for g in LLM_GOALS if g not in proved[k]]
        if not open_goals or classify(proved[k]) == "reject":
            return k, {}
        return k, propose(model, jobs[k][0], canon[k]["goals"], open_goals)

    def work_closed(k):
        if "closed" in proved[k]:
            return k, {}
        return k, propose(model, jobs[k][0], canon[k]["goals"], ["closed"])

    keys = list(base)
    with ThreadPoolExecutor(max_workers=LLM_WORKERS) as pool:
        props = dict(pool.map(work, keys))
        cprops = dict(pool.map(work_closed, keys))
    for k, gs in cprops.items():
        props[k] = {**props[k], **gs}
    tag = model.split("/")[-1].replace(".", "_").replace("-", "_")
    shot = prove([((k, g), (*jobs[k], p)) for k, gs in props.items() for g, p in gs.items()], f"{tag}1")
    for (k, g), res in shot.items():
        if ok(res):
            proved[k].add(g)
    failed = [((k, g), res) for (k, g), res in shot.items() if not ok(res)
              and (g == "closed" or classify(proved[k]) == "unknown")]

    def fix(item):
        (k, g), res = item
        return (k, g), repair(model, jobs[k][0], g, canon[k]["goals"][g], props[k][g], res.errors)

    with ThreadPoolExecutor(max_workers=LLM_WORKERS) as pool:
        fixes = dict(pool.map(fix, failed))
    for (k, g), res in prove([((k, g), (*jobs[k], p)) for (k, g), p in fixes.items() if p], f"{tag}2").items():
        if ok(res):
            proved[k].add(g)
    return proved


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    refs = g2.references()[:N_REFS]
    jobs = {f"{r.row_id}~{kind}": (r, g, kind) for r, g in refs for kind in KINDS}
    canon = g2.canon_all(jobs)
    good = [k for k in jobs if canon[k]["status"] == "ok"]
    print("canon", Counter((jobs[k][2], canon[k]["status"]) for k in jobs), f"{time.time() - t0:.0f}s", flush=True)

    comp = (*GOALS, *SPLITS)
    tac = prove([((k, g), (*jobs[k], SPLIT_TAC if g in SPLITS else COMP_TAC)) for k in good for g in comp], "t0")
    tac.update(prove([((k, "closed"), (*jobs[k], CLOSED_TAC)) for k in good], "t0"))
    base = {k: {g for g in (*comp, "closed") if ok(tac[(k, g)])} for k in good}
    retry = [(k, g) for k in good for g in SPLITS if g not in base[k]]
    for (k, g), res in prove([((k, g), (*jobs[k], SPLIT_TAC2)) for k, g in retry], "t0b").items():
        if ok(res):
            base[k].add(g)
    k9 = prove([((k, "cand"), (*jobs[k], K9_TAC)) for k in good], "k9", K9_HEARTBEATS)
    triv = {k: ok(k9[(k, "cand")]) for k in good}
    print("tactic tier", Counter((jobs[k][2], verdict(base[k])) for k in good), f"{time.time() - t0:.0f}s", flush=True)

    rows, src_of = [], {}
    for k in good:
        r, _, kind = jobs[k]
        s = hack_src(f2.normalize(r.gold), kind)
        if s is not None:
            src_of[k] = s
            rows.append(dataclasses.replace(r, row_id=k, pred=s, correct=kind == "id"))
    beq = {p["row_id"]: p["beq_plus"] for p in b1.run(rows, D / "k10_beq.json")["pairs"]}
    print("beq+ done", f"{time.time() - t0:.0f}s", flush=True)

    tiers = {"tactics": base}
    for m in MODELS:
        tiers[m] = run_model(m, jobs, canon, base)
        print("model", m, Counter((jobs[k][2], verdict(tiers[m][k])) for k in good), f"{time.time() - t0:.0f}s", flush=True)

    per, table = [], {}
    for k in good:
        r, g, kind = jobs[k]
        rid = r.row_id
        r_triv = triv.get(f"{rid}~id", False)
        flag = triv[k] and not r_triv
        p = {"key": k, "row_id": rid, "kind": kind, "beq_plus": beq.get(k), "k9_s": triv[k], "k9_r": r_triv,
             "k9_flag": flag, "mutant": canon[k].get("mutant"), "canon_info": canon[k].get("info"),
             "src": src_of.get(k), "tiers": {}}
        t = table.setdefault(kind, Counter())
        t["n"] += 1
        t["beq_plus"] += bool(beq.get(k))
        t["k9_flag"] += flag
        for name, proved in tiers.items():
            v = verdict(proved[k])
            p["tiers"][name] = {"verdict": v, "closed": "closed" in proved[k], "proved": sorted(proved[k])}
            t[f"{name}:closed"] += "closed" in proved[k]
            t[f"{name}:{v}"] += 1
            if v == "accept":
                t[f"{name}:accept_unflagged"] += not flag
        per.append(p)
    summary = {"n_refs": N_REFS, "models": MODELS, "kinds": KINDS, "table": {k: dict(v) for k, v in table.items()},
               "seconds": round(time.time() - t0, 1), "pairs": per}
    OUT.write_text(json.dumps(summary, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(summary["table"], indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
