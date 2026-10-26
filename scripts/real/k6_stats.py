#!/usr/bin/env python3
"""K6: confidence intervals, paired tests and the total-alignment ablation on G1 (and G4 BEq+).

For every G1 prover tier: exact (Clopper-Pearson) 95% intervals for false accepts on the 150
labelled-inequivalent and recall on the 150 labelled-equivalent pairs, for
  closed        closed equivalence with that prover,
  closed_total  closed equivalence, accepted only when the canonical alignment is total
                (the ablation: does total alignment alone remove the collapse?),
  ours          all accepts of the three-valued criterion,
  local         local accepts only;
and exact McNemar tests (same pairs) of ours/local against BEq+ and against closed_total.

Usage: k6_stats.py        writes data/real/k6_stats.json and prints a table
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from scipy.stats import beta, binomtest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from a1_local import label, local
from runner import ROOT

D = ROOT / "data" / "real"
OUT = D / "k6_stats.json"
TIERS = {"opus": "g1_results.json", "deepseek": "g1_results_deepseek-v4.1-flash.json",
         "gpt-4.1-mini": "g1_results_gpt-4.1-mini.json", "qwen": "g1_results_qwen3.8-27b-nothink.json",
         "gpt-6-astra": "g1_results_gpt-6-astra.json", "gemini-4-argon": "g1_results_gemini-4-argon.json"}
G4 = {"opus": "g4_results.json", "deepseek": "g4_results_deepseek-v4.1-flash.json",
      "gpt-4.1-mini": "g4_results_gpt-4.1-mini.json", "qwen": "g4_results_qwen3.8-27b-nothink.json",
      "gpt-6-astra": "g4_results_gpt-6-astra.json", "gemini-4-argon": "g4_results_gemini-4-argon.json"}
G5 = {"opus": "g1_results_claude-opus-5.5.json", "deepseek": "g1_results_deepseek-v4.1-flash.json",
      "gpt-4.1-mini": "g1_results_gpt-4.1-mini.json", "qwen": "g1_results_qwen3.8-27b-nothink.json"}


def cp(k: int, n: int) -> list[float]:
    lo = 0.0 if k == 0 else float(beta.ppf(0.025, k, n - k + 1))
    hi = 1.0 if k == n else float(beta.ppf(0.975, k + 1, n - k))
    return [round(lo, 4), round(hi, 4)]


def mcnemar(a: dict[str, bool], b: dict[str, bool], ids: list[str]) -> dict:
    only_a = sum(a[i] and not b[i] for i in ids)
    only_b = sum(b[i] and not a[i] for i in ids)
    p = float(binomtest(only_a, only_a + only_b).pvalue) if only_a + only_b else 1.0
    return {"only_first": only_a, "only_second": only_b, "p_exact": p}


def is_local(p: dict) -> bool:
    return local(p.get("canon_info"))


def accepted(p: dict) -> bool:
    """A decided verdict counts only with both regrouping certificates."""
    return p["verdict"] == "accept" and {"split_r", "split_s"} <= set(p.get("proved") or [])


def runs():
    beq1 = {p["row_id"]: p["beq_plus"] for p in json.loads((D / "b1_results.json").read_text(encoding="utf-8"))["pairs"]}
    for tier, f in TIERS.items():
        yield "g1", tier, D / f, beq1
    beq4 = {p["row_id"]: p["beq_plus"] for p in json.loads((D / "g4_beqplus.json").read_text(encoding="utf-8"))["pairs"]}
    for tier, f in G4.items():
        yield "g4", tier, D / f, beq4
    b5 = D / "g5" / "b1_results.json"
    if b5.exists():
        beq5 = {p["row_id"]: p["beq_plus"] for p in json.loads(b5.read_text(encoding="utf-8"))["pairs"]}
        for tier, f in G5.items():
            yield "g5", tier, D / "g5" / f, beq5


def main() -> None:
    out = {}
    for ds, tier, path, beq in runs():
        if not path.exists():
            continue
        pairs = json.loads(path.read_text(encoding="utf-8"))["pairs"]
        for p in pairs:
            p["label"] = label(p)
        acc = {
            "closed": {p["row_id"]: p["closed"] == "proved" for p in pairs},
            "closed_total": {p["row_id"]: p["closed"] == "proved" and is_local(p) for p in pairs},
            "ours": {p["row_id"]: accepted(p) for p in pairs},
            "local": {p["row_id"]: accepted(p) and is_local(p) for p in pairs},
            "beq_plus": {p["row_id"]: beq[p["row_id"]] for p in pairs},
            "local_or_restricted": {p["row_id"]: accepted(p) and (is_local(p) or beq[p["row_id"]])
                                    for p in pairs},
        }
        eq = [p["row_id"] for p in pairs if p["label"]]
        neq = [p["row_id"] for p in pairs if not p["label"]]
        row = {}
        for name, a in acc.items():
            fa, rc = sum(a[i] for i in neq), sum(a[i] for i in eq)
            row[name] = {"fa": fa, "fa_ci": cp(fa, len(neq)), "recall": rc, "recall_ci": cp(rc, len(eq))}
        tests = {}
        for x, y in [("ours", "beq_plus"), ("local", "beq_plus"), ("local", "closed_total"), ("ours", "closed"),
                     ("local_or_restricted", "beq_plus")]:
            tests[f"{x}_vs_{y}"] = {"recall": mcnemar(acc[x], acc[y], eq), "fa": mcnemar(acc[x], acc[y], neq)}
        out[f"{ds}:{tier}"] = {"n_eq": len(eq), "n_neq": len(neq), "rates": row, "mcnemar": tests}
        print(f"\n== {ds} {tier}  (eq {len(eq)}, neq {len(neq)})")
        for name, r in row.items():
            print(f"  {name:13s} FA {r['fa']:3d} {r['fa_ci']}   recall {r['recall']:3d} {r['recall_ci']}")
        for k, t in tests.items():
            print(f"  {k:24s} recall {t['recall']}  fa {t['fa']}")
    OUT.write_text(json.dumps(out, indent=1), encoding="utf-8")


if __name__ == "__main__":
    main()
