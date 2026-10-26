#!/usr/bin/env python3
"""F7: component-level comparison on a subset of the F2 ProofNetVerif pairs.

For each (gold G, prediction P):

1. An LLM proposes a shared telescope B and components Hg, Cg, Hp, Cp.
2. Lean checks the split: G ↔ ∀ B, Hg → Cg and P ↔ ∀ B, Hp → Cp.
   Pairs whose split fails are reported as such and get no component verdict.
3. Component goals, tried with fixed tactics and then one LLM proposal each:
     acc    ∀ B, (Hg ↔ Hp) ∧ (Cg ↔ Cp)
     cond   ∀ B, (Hg ↔ Hp) ∧ (Hg → (Cg ↔ Cp))
     nhyp   ¬ ∀ B, (Hg ↔ Hp)
     ncin   ¬ ∀ B, Hg → (Cg ↔ Cp)
     ncomp  ¬ ∀ B, (Cg ↔ Cp)
4. Verdict: reject if nhyp or ncin; accept if acc; off-domain if cond and ncomp;
   unknown otherwise.

The telescope (which variable of P corresponds to which of G) is chosen by the LLM
and is not checked, so a reject means "refuted under the proposed alignment";
false rejects on label-equivalent pairs measure how often that alignment is wrong.

Writes data/real/f7_results.json.
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

from f2_oracle import FORBIDDEN, GOALS as CLOSED_GOALS, OUT as F2_OUT, normalize, prelude, run_llm_tier
from f2_oracle import verdict as f2_verdict
from llm import chat
from realdata import proofnetverif
from runner import ROOT, Item, check, tactic_body
from stmt import to_prop

OUT = ROOT / "data" / "real" / "f7_results.json"
MODEL = "deepseek/deepseek-v4.1-flash"
N_NEG, N_POS = 60, 40
MAX_TOKENS = 16384

SPLIT_TAC = (
    "first | exact Iff.rfl | (simp only [and_imp]; done) | (simp only [and_imp, and_assoc]; done) "
    "| (constructor <;> intro h <;> intros <;> simp_all) "
    "| (constructor <;> intro h <;> intros <;> aesop) | tauto"
)
# Stronger second tier for the regrouping goals (E2): instantiate the other side directly,
# with `subst_vars` for one-point eliminations and `rfl` for equations the canonical form
# eliminated. The last alternative covers `→ false = true` conclusions turned into `¬`.
SPLIT_TAC2 = (
    "first | (simp only [true_implies, and_imp, and_assoc, forall_const]; done) "
    "| (constructor <;> intro h <;> intros <;> (first | (apply h <;> assumption) "
    "| solve_by_elim (config := {maxDepth := 30}) [h] "
    "| (apply h <;> solve_by_elim (config := {maxDepth := 30})) | (aesop (add safe forward h)) | (simp_all; done))) "
    "| (constructor <;> intro h <;> intros <;> subst_vars <;> (first | (apply h <;> assumption) "
    "| solve_by_elim (config := {maxDepth := 30}) [h, rfl] "
    "| (apply h <;> solve_by_elim (config := {maxDepth := 30}) [rfl]) "
    "| (exfalso; simpa using h ‹_› ‹_› ‹_› ‹_›) | (simp_all; done)))"
)
COMP_TAC = (
    "first | (intros; simp_all; done) | (simp; done) | decide | (intros; aesop) "
    "| (constructor <;> intros <;> simp_all) | tauto"
)
GOALS = ("acc", "cond", "nhyp", "ncin", "ncomp")
LLM_GOALS = ("acc", "nhyp", "ncin", "ncomp")

DECOMP = """You are an expert in Lean 4 and Mathlib. Two Lean propositions formalize the same
natural-language problem:

Problem: {nl}

Reference R:
{gold}

Candidate S:
{pred}

Rewrite both over ONE shared telescope of binders, matching each variable of S with the
variable of R that plays the same role in the problem. Give:

- binders: the shared Lean binder list as it would appear after `∀`, e.g.
  `{{G : Type u}} [Group G] (a b : G)`; use "" if there are no variables;
- Hr, Cr: hypotheses (conjunction, `True` if none) and conclusion of R over these binders;
- Hs, Cs: the same for S.

They must satisfy, provably and with no other change,
  R ↔ ∀ binders, Hr → Cr     and     S ↔ ∀ binders, Hs → Cs.
Do not move hypotheses into conclusions or vice versa beyond what the statements say.
If corresponding variables have different types so no shared telescope exists,
return {{"binders": null}}.

Reply with ONLY one JSON object with keys binders, Hr, Cr, Hs, Cs."""

PROVE = """You are an expert in Lean 4 and Mathlib. Environment (already present):

{header}

For each theorem below, give a tactic proof if you believe it is true; otherwise
write `skip`. Exactly one is relevant per pair of opposites; false ones are simply rejected.
Never use sorry, admit or native_decide.

{goals}

Reply with one section per theorem, in this exact format:

### <name>
```lean
<tactic proof>
```"""


def parse_json(text: str) -> dict | None:
    m = re.search(r"\{.*\}", text, flags=re.DOTALL)
    if not m:
        return None
    try:
        return json.loads(m.group(0))
    except json.JSONDecodeError:
        return None


def forall(binders: str, body: str) -> str:
    return f"∀ {binders}, {body}" if binders.strip() else body


def goal_texts(d: dict) -> dict[str, str]:
    b = d["binders"]
    hr, cr, hs, cs = (f"({d[k]})" for k in ("Hr", "Cr", "Hs", "Cs"))
    return {
        "acc": forall(b, f"({hr} ↔ {hs}) ∧ ({cr} ↔ {cs})"),
        "cond": forall(b, f"({hr} ↔ {hs}) ∧ ({hr} → ({cr} ↔ {cs}))"),
        "nhyp": f"¬ ({forall(b, f'{hr} ↔ {hs}')})",
        "ncin": f"¬ ({forall(b, f'{hr} → ({cr} ↔ {cs})')})",
        "ncomp": f"¬ ({forall(b, f'{cr} ↔ {cs}')})",
    }


def thm(name: str, goal: str, proof: str, hb: int) -> str:
    return f"set_option maxHeartbeats {hb} in\ntheorem {name} : {goal} := by\n  {proof}"


def load_pairs():
    f2 = json.loads(F2_OUT.read_text(encoding="utf-8"))
    by_id = {r.row_id: r for r in proofnetverif("test")}
    neg = [p for p in f2["pairs"] if not p["label"]][:N_NEG]
    pos = [p for p in f2["pairs"] if p["label"]][:N_POS]
    out = []
    for p in neg + pos:
        r = by_id[p["row_id"]]
        out.append((r, normalize(to_prop(r.gold)), normalize(to_prop(r.pred)), set(p["t1"])))
    return out


def decompose(job):
    r, g, p, _ = job
    try:
        text = chat(MODEL, [{"role": "user", "content": DECOMP.format(nl=r.nl, gold=g, pred=p)}],
                    temperature=0.0, max_tokens=MAX_TOKENS)
    except RuntimeError:
        return r.row_id, None
    d = parse_json(text)
    if not d or d.get("binders") is None:
        return r.row_id, {"aligned": False}
    if not all(isinstance(d.get(k), str) for k in ("binders", "Hr", "Cr", "Hs", "Cs")):
        return r.row_id, None
    if any(FORBIDDEN.search(d[k]) for k in ("binders", "Hr", "Cr", "Hs", "Cs")):
        return r.row_id, None
    d["aligned"] = True
    return r.row_id, d


def propose(job):
    r, d, open_goals = job
    gt = goal_texts(d)
    goals = "\n\n".join(f"theorem {g} : {gt[g]} := by\n  sorry" for g in open_goals)
    header = r.header.strip() + "\nuniverse u\nset_option autoImplicit false"
    try:
        text = chat(MODEL, [{"role": "user", "content": PROVE.format(header=header, goals=goals)}],
                    temperature=0.2, max_tokens=MAX_TOKENS)
    except RuntimeError:
        return r.row_id, {}
    out = {}
    for name, body in re.findall(r"###\s*(\w+)\s*```(?:lean)?\n(.*?)```", text, flags=re.DOTALL):
        if name in open_goals and body.strip() not in ("", "skip") and not FORBIDDEN.search(body):
            out[name] = tactic_body(body)
    return r.row_id, out


def classify(proved: set[str]) -> str:
    if "nhyp" in proved or "ncin" in proved:
        return "reject"
    if "acc" in proved:
        return "accept"
    if "cond" in proved and "ncomp" in proved:
        return "off_domain"
    return "unknown"


def main() -> None:
    global N_NEG, N_POS
    sys.stdout.reconfigure(encoding="utf-8")
    if len(sys.argv) > 2:
        N_NEG, N_POS = int(sys.argv[1]), int(sys.argv[2])
    t0 = time.time()
    pairs = load_pairs()
    rows = {r.row_id: (r, g, p, s) for r, g, p, s in pairs}
    print("pairs", len(pairs))

    open_closed = {r.row_id: set(CLOSED_GOALS) - t1 for r, _, _, t1 in pairs}
    closed_new, n_closed_jobs = run_llm_tier([(r, g, p) for r, g, p, _ in pairs], open_closed)
    closed_proved = {r.row_id: set(t1) for r, _, _, t1 in pairs}
    for (rid, goal), ok in closed_new.items():
        if ok:
            closed_proved[rid].add(goal)
    print("closed llm tier", f"{time.time() - t0:.0f}s", "jobs", n_closed_jobs)

    with ThreadPoolExecutor(max_workers=16) as pool:
        dec = dict(pool.map(decompose, pairs))
    print("decomposed", f"{time.time() - t0:.0f}s")

    items, keys = [], []
    for rid, d in dec.items():
        if not d or not d.get("aligned"):
            continue
        r, g, p, _ = rows[rid]
        imports, pre = prelude(r)
        for side, orig, h, c in (("r", g, d["Hr"], d["Cr"]), ("s", p, d["Hs"], d["Cs"])):
            goal = f"({orig}) ↔ ({forall(d['binders'], f'({h}) → ({c})')})"
            items.append(Item(f"{rid}:split_{side}", imports, f"{pre}\n{thm('split_' + side, goal, SPLIT_TAC, 100000)}"))
            keys.append((rid, side))
    res = check(items, batch_size=20, workers=6)
    split_ok: dict[str, set] = {}
    for (rid, side), it in zip(keys, items):
        if res[it.item_id].ok and not res[it.item_id].uses_sorry:
            split_ok.setdefault(rid, set()).add(side)
    good = [rid for rid in dec if split_ok.get(rid) == {"r", "s"}]
    print("split ok", len(good), f"{time.time() - t0:.0f}s")

    proved: dict[str, set] = {rid: set() for rid in good}
    items, keys = [], []
    for rid in good:
        r = rows[rid][0]
        imports, pre = prelude(r)
        gt = goal_texts(dec[rid])
        for goal in GOALS:
            items.append(Item(f"{rid}:c0:{goal}", imports, f"{pre}\n{thm('c0_' + goal, gt[goal], COMP_TAC, 100000)}"))
            keys.append((rid, goal))
    res = check(items, batch_size=20, workers=6)
    for (rid, goal), it in zip(keys, items):
        if res[it.item_id].ok and not res[it.item_id].uses_sorry:
            proved[rid].add(goal)
    tactic_proved = {rid: set(v) for rid, v in proved.items()}
    print("tactic tier", f"{time.time() - t0:.0f}s")

    jobs = []
    for rid in good:
        open_goals = [g for g in LLM_GOALS if g not in proved[rid]]
        if open_goals:
            jobs.append((rows[rid][0], dec[rid], open_goals))
    with ThreadPoolExecutor(max_workers=16) as pool:
        props = dict(pool.map(propose, jobs))
    items, keys = [], []
    for rid, pr in props.items():
        r = rows[rid][0]
        imports, pre = prelude(r)
        gt = goal_texts(dec[rid])
        for goal, proof in pr.items():
            items.append(Item(f"{rid}:c2:{goal}", imports, f"{pre}\n{thm('c2_' + goal, gt[goal], proof, 200000)}"))
            keys.append((rid, goal))
    res = check(items, batch_size=10, workers=6)
    for (rid, goal), it in zip(keys, items):
        if res[it.item_id].ok and not res[it.item_id].uses_sorry:
            proved[rid].add(goal)
    print("llm tier", f"{time.time() - t0:.0f}s", "jobs", len(jobs))

    table = {True: Counter(), False: Counter()}
    per_pair = []
    for rid, (r, _, _, _) in rows.items():
        f2s = f2_verdict(closed_proved[rid])["status"]
        d = dec.get(rid)
        if d is None:
            v = "decomp_fail"
        elif not d.get("aligned"):
            v = "no_alignment"
        elif rid not in proved:
            v = "split_fail"
        else:
            v = classify(proved[rid])
        table[r.correct][v] += 1
        table[r.correct][f"closed_{f2s}"] += 1
        table[r.correct][f"closed_{f2s}->{v}"] += 1
        per_pair.append({
            "row_id": rid, "label": r.correct, "closed": f2s, "closed_proved": sorted(closed_proved[rid]),
            "verdict": v,
            "tactic": sorted(tactic_proved.get(rid, ())), "proved": sorted(proved.get(rid, ())),
            "decomposition": d,
        })
    summary = {
        "model": MODEL,
        "n_neg": N_NEG, "n_pos": N_POS, "max_tokens": MAX_TOKENS, "closed_llm_jobs": n_closed_jobs,
        "label_inequivalent": dict(table[False]),
        "label_equivalent": dict(table[True]),
        "seconds": round(time.time() - t0, 1),
        "pairs": per_pair,
    }
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "pairs"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
