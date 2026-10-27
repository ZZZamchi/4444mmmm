#!/usr/bin/env python3
"""F2: tiered three-valued oracle on ProofNetVerif pairs.

For each (gold G, prediction P) the goals are

  fwd    G → P          nfwd   ¬ (G → P)
  bwd    P → G          nbwd   ¬ (P → G)
  pfalse ¬ P            gfalse ¬ G   (gold sanity: must never be proved)

Tiers are cumulative:
  t0 simple tactics, t1 + aesop / exact?, t2 + one LLM-proposed proof per open goal.
Every accepted proof is checked by the Lean kernel through runner.check; proofs
containing sorry, admit or native_decide are rejected before checking.

Writes data/real/f2_results.json.
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

from llm import chat, extract_lean
from realdata import PnvRow, proofnetverif
from runner import ROOT, Item, check, split_imports, tactic_body
from stmt import to_prop

OUT = ROOT / "data" / "real" / "f2_results.json"
PROPOSER = "deepseek/deepseek-v4.1-flash"
N_PER_LABEL = 150
SEED = 0

T0 = (
    "first | (intro h; exact h) | (intro h; intros; apply h <;> assumption) "
    "| (intro h; intros; simp_all; done) | (simp; done) | decide"
)
T1 = (
    "first | (intro h; exact h) | (intro h; intros; apply h <;> assumption) "
    "| (intro h; intros; simp_all; done) | (simp; done) | decide "
    "| (intro h; intros; aesop) | (intro h; intros; exact?)"
)
GOALS = ("fwd", "bwd", "nfwd", "nbwd", "pfalse", "gfalse")
LLM_GOALS = ("fwd", "bwd", "nfwd", "pfalse")
FORBIDDEN = re.compile(r"\b(sorry|admit|native_decide|axiom|implemented_by|extern)\b")


def normalize(prop: str) -> str:
    return prop.replace("Type*", "Type u").replace("Sort*", "Sort u")


def goal_text(g: str, gold: str, pred: str) -> str:
    G, P = f"({gold})", f"({pred})"
    return {
        "fwd": f"{G} → {P}",
        "bwd": f"{P} → {G}",
        "nfwd": f"¬ ({G} → {P})",
        "nbwd": f"¬ ({P} → {G})",
        "pfalse": f"¬ {P}",
        "gfalse": f"¬ {G}",
    }[g]


def prelude(row: PnvRow) -> tuple[tuple[str, ...], str]:
    imports, opens = split_imports(row.header)
    return imports, f"{opens}\nuniverse u\nset_option autoImplicit false"


def theorem(name: str, goal: str, proof: str, heartbeats: int) -> str:
    return f"set_option maxHeartbeats {heartbeats} in\ntheorem {name} : {goal} := by\n  {proof}"


def select_pairs() -> tuple[list[tuple[PnvRow, str, str]], dict]:
    rows = proofnetverif("test")
    conv = []
    stats = Counter()
    for r in rows:
        g, p = to_prop(r.gold), to_prop(r.pred)
        if g is None or p is None:
            stats["no_conversion"] += 1
            continue
        conv.append((r, normalize(g), normalize(p)))
    items = []
    for r, g, p in conv:
        imports, pre = prelude(r)
        items.append(Item(f"{r.row_id}:elab", imports, f"{pre}\nexample : ({g}) ∧ ({p}) → True := fun _ => trivial"))
    res = check(items, batch_size=25)
    usable = []
    for (r, g, p), it in zip(conv, items):
        if res[it.item_id].ok:
            usable.append((r, g, p))
        else:
            msg = " ".join(res[it.item_id].errors)[:4000]
            stats["elab_fail_autoimplicit" if "unknown identifier" in msg or "unknown constant" in msg else "elab_fail_other"] += 1
    stats["usable"] = len(usable)
    stats["usable_true"] = sum(r.correct for r, _, _ in usable)
    rng = random.Random(SEED)
    pos = [x for x in usable if x[0].correct]
    neg = [x for x in usable if not x[0].correct]
    rng.shuffle(pos)
    rng.shuffle(neg)
    chosen = pos[:N_PER_LABEL] + neg[:N_PER_LABEL]
    return chosen, dict(stats)


def run_tactic_tier(pairs, tactic: str, heartbeats: int, tag: str, open_goals: dict) -> dict:
    items, keys = [], []
    for r, g, p in pairs:
        imports, pre = prelude(r)
        for goal in GOALS:
            if goal not in open_goals[r.row_id]:
                continue
            name = f"{tag}_{goal}"
            items.append(Item(f"{r.row_id}:{tag}:{goal}", imports, f"{pre}\n{theorem(name, goal_text(goal, g, p), tactic, heartbeats)}"))
            keys.append((r.row_id, goal))
    res = check(items, batch_size=10 if tag == "t1" else 20)
    return {k: res[it.item_id].ok and not res[it.item_id].uses_sorry for k, it in zip(keys, items)}


PROMPT = """You are an expert in Lean 4 and Mathlib. Prove the following theorem.
Lean environment (already present above the theorem):

{header}

Theorem:

theorem goal : {goal} := by
  sorry

Reply with ONLY the tactic proof that replaces `sorry`, inside one ```lean code block.
Do not restate the theorem. Do not use sorry, admit or native_decide.
If the statement is false, still try your best; an invalid proof is simply rejected."""


def propose(row: PnvRow, goal: str, text: str) -> str | None:
    header = row.header.strip() + "\nuniverse u\nset_option autoImplicit false"
    out = chat(PROPOSER, [{"role": "user", "content": PROMPT.format(header=header, goal=text)}], temperature=0.2)
    proof = extract_lean(out)
    if not proof.strip() or FORBIDDEN.search(proof):
        return None
    return tactic_body(proof)


def run_llm_tier(pairs, open_goals: dict) -> tuple[dict, int]:
    jobs = []
    for r, g, p in pairs:
        for goal in LLM_GOALS:
            if goal in open_goals[r.row_id]:
                jobs.append((r, g, p, goal))

    def work(job):
        r, g, p, goal = job
        try:
            return job, propose(r, goal, goal_text(goal, g, p))
        except RuntimeError:
            return job, None

    with ThreadPoolExecutor(max_workers=8) as pool:
        proposals = list(pool.map(work, jobs))
    items, keys = [], []
    for (r, g, p, goal), proof in proposals:
        if proof is None:
            continue
        imports, pre = prelude(r)
        items.append(Item(f"{r.row_id}:t2:{goal}", imports, f"{pre}\n{theorem('t2_' + goal, goal_text(goal, g, p), proof, 200000)}"))
        keys.append((r.row_id, goal))
    res = check(items, batch_size=10)
    return {k: res[it.item_id].ok and not res[it.item_id].uses_sorry for k, it in zip(keys, items)}, len(jobs)


def verdict(proved: set[str]) -> dict:
    fwd = "proved" if "fwd" in proved else "refuted" if "nfwd" in proved else "unknown"
    bwd = "proved" if "bwd" in proved else "refuted" if "nbwd" in proved else "unknown"
    if "refuted" in (fwd, bwd):
        status = "refuted"
    elif fwd == bwd == "proved":
        status = "proved"
    else:
        status = "unknown"
    return {
        "fwd": fwd,
        "bwd": bwd,
        "status": status,
        "pred_false": "pfalse" in proved,
        "gold_false": "gfalse" in proved,
    }


def summarize(pairs, proved_by_tier: dict[str, dict[str, set]]) -> dict:
    out = {}
    for tier, proved in proved_by_tier.items():
        table = {True: Counter(), False: Counter()}
        for r, _, _ in pairs:
            v = verdict(proved[r.row_id])
            label = r.correct
            table[label][v["status"]] += 1
            if v["pred_false"]:
                table[label]["pred_false"] += 1
            if v["status"] == "unknown" and not v["pred_false"]:
                table[label]["unknown_no_cert"] += 1
            if v["gold_false"]:
                table[label]["gold_false"] += 1
        neg = table[False]
        n_neg = sum(neg[s] for s in ("proved", "refuted", "unknown"))
        pos = table[True]
        out[tier] = {
            "label_equivalent": dict(pos),
            "label_inequivalent": dict(neg),
            "inequivalent_unknown_share": round(neg["unknown_no_cert"] / n_neg, 3) if n_neg else None,
            "inequivalent_certified_share": round((n_neg - neg["unknown_no_cert"]) / n_neg, 3) if n_neg else None,
            "inequivalent_refuted_share": round(neg["refuted"] / n_neg, 3) if n_neg else None,
            "proved_precision": round(pos["proved"] / (pos["proved"] + neg["proved"]), 3) if pos["proved"] + neg["proved"] else None,
            "refuted_precision": round(neg["refuted"] / (pos["refuted"] + neg["refuted"]), 3) if pos["refuted"] + neg["refuted"] else None,
            "pred_false_precision": round(neg["pred_false"] / (pos["pred_false"] + neg["pred_false"]), 3) if pos["pred_false"] + neg["pred_false"] else None,
        }
    return out


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    pairs, stats = select_pairs()
    print("selection:", stats, "chosen:", len(pairs), f"{time.time() - t0:.0f}s")
    proved: dict[str, set] = {r.row_id: set() for r, _, _ in pairs}
    by_tier: dict[str, dict[str, set]] = {}

    def open_goals():
        return {rid: set(GOALS) - s for rid, s in proved.items()}

    for tag, tactic, hb in (("t0", T0, 20000), ("t1", T1, 100000)):
        res = run_tactic_tier(pairs, tactic, hb, tag, open_goals())
        for (rid, goal), ok in res.items():
            if ok:
                proved[rid].add(goal)
        by_tier[tag] = {k: set(v) for k, v in proved.items()}
        print(tag, "done", f"{time.time() - t0:.0f}s")

    res, n_jobs = run_llm_tier(pairs, open_goals())
    for (rid, goal), ok in res.items():
        if ok:
            proved[rid].add(goal)
    by_tier["t2"] = {k: set(v) for k, v in proved.items()}
    print("t2 done", f"{time.time() - t0:.0f}s", "llm jobs", n_jobs)

    summary = {
        "selection": stats,
        "n_pairs": len(pairs),
        "proposer": PROPOSER,
        "tiers": summarize(pairs, by_tier),
        "llm_jobs": n_jobs,
        "seconds": round(time.time() - t0, 1),
        "pairs": [
            {
                "row_id": r.row_id,
                "stmt_id": r.stmt_id,
                "label": r.correct,
                **{tier: sorted(by_tier[tier][r.row_id]) for tier in by_tier},
            }
            for r, _, _ in pairs
        ],
    }
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "pairs"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
