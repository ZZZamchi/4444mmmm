#!/usr/bin/env python3
"""F3: do autoformalization rankings depend on oracle strength?

Six systems formalize the same ProofNetVerif test statements (RLM25 needs six
pinned research repositories, so ProofNetVerif is the documented substitute).
Each system is scored under four oracles of increasing strength:

  compile  prediction type-checks (the usual compile-rate metric)
  t0/t1/t2 equivalence to the gold certified by the F2 tiers

Rankings are compared with Kendall tau-b against the strongest tier, with a
bootstrap over problems. Writes data/real/f3_results.json.
"""

from __future__ import annotations

import itertools
import json
import random
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from f2_oracle import GOALS, T0, T1, normalize, prelude, run_llm_tier, run_tactic_tier, verdict
from llm import chat, extract_lean
from realdata import PnvRow, proofnetverif
from runner import ROOT, Item, check
from stmt import to_prop

OUT = ROOT / "data" / "real" / "f3_results.json"
SYSTEMS = (
    "anthropic/claude-sonnet-5.5",
    "deepseek/deepseek-v4.1-flash",
    "qwen/qwen3.5-27b",
    "openai/gpt-4.1-mini",
    "openai/gpt-4o-mini",
    "google/gemini-2.5-flash-lite",
)
N_PROBLEMS = 60
SEED = 1
TIERS = ("compile", "t0", "t1", "t2")

PROMPT = """Translate the following mathematical statement into a Lean 4 theorem statement using Mathlib.

The file starts with:

{header}

Statement:
{nl}

Reply with ONLY one Lean 4 theorem declaration in a ```lean code block, named `{name}`,
ending with `:= by sorry`. Do not add imports. Do not prove it."""


def problems() -> list[PnvRow]:
    rows = proofnetverif("test")
    by_stmt: dict[str, PnvRow] = {}
    for r in rows:
        by_stmt.setdefault(r.stmt_id, r)
    golds = []
    for r in by_stmt.values():
        g = to_prop(r.gold)
        if g is not None:
            golds.append(r)
    items = []
    for r in golds:
        imports, pre = prelude(r)
        items.append(Item(f"{r.stmt_id}:gold", imports, f"{pre}\nexample : ({normalize(to_prop(r.gold))}) → True := fun _ => trivial"))
    res = check(items, batch_size=25)
    ok = [r for r, it in zip(golds, items) if res[it.item_id].ok]
    random.Random(SEED).shuffle(ok)
    return ok[:N_PROBLEMS]


def formalize(model: str, r: PnvRow) -> str:
    name = "stmt_" + "".join(ch if ch.isalnum() else "_" for ch in r.stmt_id)
    try:
        out = chat(model, [{"role": "user", "content": PROMPT.format(header=r.header.strip(), nl=r.nl.strip(), name=name)}])
    except RuntimeError:
        return ""
    return extract_lean(out).strip()


def kendall_tau_b(x: list[float], y: list[float]) -> float:
    conc = disc = tx = ty = 0
    for i, j in itertools.combinations(range(len(x)), 2):
        dx, dy = x[i] - x[j], y[i] - y[j]
        if dx == 0 and dy == 0:
            continue
        if dx == 0:
            tx += 1
        elif dy == 0:
            ty += 1
        elif dx * dy > 0:
            conc += 1
        else:
            disc += 1
    denom = ((conc + disc + tx) * (conc + disc + ty)) ** 0.5
    return (conc - disc) / denom if denom else 1.0


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    probs = problems()
    print("problems", len(probs), f"{time.time() - t0:.0f}s")

    jobs = [(m, r) for m in SYSTEMS for r in probs]
    with ThreadPoolExecutor(max_workers=8) as pool:
        preds = dict(zip(jobs, pool.map(lambda j: formalize(*j), jobs)))
    print("formalized", f"{time.time() - t0:.0f}s")

    compile_items = []
    for (m, r), p in preds.items():
        imports, pre = prelude(r)
        body = p if p and "theorem" in p else "example : False := by exact?"
        compile_items.append(Item(f"{m}|{r.stmt_id}", imports, f"{pre}\n{body}"))
    cres = check(compile_items, batch_size=20)

    pairs = []
    compiled: dict[tuple[str, str], bool] = {}
    for (m, r), p in preds.items():
        ok = cres[f"{m}|{r.stmt_id}"].ok
        compiled[(m, r.stmt_id)] = ok
        prop = to_prop(p) if ok else None
        if prop is None:
            continue
        row = PnvRow(f"{m}|{r.stmt_id}", "test", r.stmt_id, r.nl, r.header, r.gold, p, None)
        pairs.append((row, normalize(to_prop(r.gold)), normalize(prop)))
    print("pairs", len(pairs), f"{time.time() - t0:.0f}s")

    proved: dict[str, set] = {row.row_id: set() for row, _, _ in pairs}
    by_tier: dict[str, dict[str, set]] = {}

    def open_goals():
        return {rid: set(GOALS) - s for rid, s in proved.items()}

    for tag, tactic, hb in (("t0", T0, 20000), ("t1", T1, 100000)):
        for k, ok in run_tactic_tier(pairs, tactic, hb, tag, open_goals()).items():
            if ok:
                proved[k[0]].add(k[1])
        by_tier[tag] = {k: set(v) for k, v in proved.items()}
        print(tag, f"{time.time() - t0:.0f}s")
    res, n_jobs = run_llm_tier(pairs, open_goals())
    for k, ok in res.items():
        if ok:
            proved[k[0]].add(k[1])
    by_tier["t2"] = {k: set(v) for k, v in proved.items()}
    print("t2", f"{time.time() - t0:.0f}s", n_jobs)

    def score_matrix(subset: list[PnvRow]) -> dict[str, dict[str, float]]:
        out = {}
        for m in SYSTEMS:
            s = {"compile": sum(compiled[(m, r.stmt_id)] for r in subset) / len(subset)}
            for tier in ("t0", "t1", "t2"):
                s[tier] = sum(
                    verdict(by_tier[tier].get(f"{m}|{r.stmt_id}", set()))["status"] == "proved" for r in subset
                ) / len(subset)
                s[tier + "_refuted"] = sum(
                    verdict(by_tier[tier].get(f"{m}|{r.stmt_id}", set()))["status"] == "refuted"
                    or "pfalse" in by_tier[tier].get(f"{m}|{r.stmt_id}", set())
                    for r in subset
                ) / len(subset)
            out[m] = s
        return out

    scores = score_matrix(probs)
    taus = {tier: round(kendall_tau_b([scores[m][tier] for m in SYSTEMS], [scores[m]["t2"] for m in SYSTEMS]), 3) for tier in TIERS}
    rng = random.Random(0)
    boot = {tier: [] for tier in TIERS}
    for _ in range(500):
        sub = [rng.choice(probs) for _ in probs]
        sm = score_matrix(sub)
        for tier in TIERS:
            boot[tier].append(kendall_tau_b([sm[m][tier] for m in SYSTEMS], [sm[m]["t2"] for m in SYSTEMS]))
    rankings = {tier: sorted(SYSTEMS, key=lambda m: -scores[m][tier]) for tier in TIERS}
    out = {
        "n_problems": len(probs),
        "systems": SYSTEMS,
        "scores": {m: {k: round(v, 3) for k, v in s.items()} for m, s in scores.items()},
        "rankings": rankings,
        "tau_vs_t2": taus,
        "bootstrap_tau_vs_t2_mean": {t: round(sum(v) / len(v), 3) for t, v in boot.items()},
        "bootstrap_tau_vs_t2_p_le_0.6": {t: round(sum(x <= 0.6 for x in v) / len(v), 3) for t, v in boot.items()},
        "llm_jobs": n_jobs,
        "seconds": round(time.time() - t0, 1),
        "predictions": {f"{m}|{r.stmt_id}": preds[(m, r)] for m, r in jobs},
    }
    OUT.write_text(json.dumps(out, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in out.items() if k != "predictions"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
