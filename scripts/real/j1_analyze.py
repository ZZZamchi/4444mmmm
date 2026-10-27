#!/usr/bin/env python3
"""J1 analysis: LLM judges against the certified criterion.

For every (set, judge model, setting):
  fa / acc_f          false accepts on unfaithful pairs, accepts on faithful pairs (as in j1_judge)
  prov_wrong_acc      judge says FAITHFUL on a pair our criterion certified `reject`
                      (kernel proof that hypotheses or in-domain conclusions differ)
  prov_wrong_rej      judge says UNFAITHFUL on a pair our criterion certified `accept`
                      (kernel proof of component equivalence with the reference)
Combined selectors (judge J, ours O):
  veto      accept iff J accepts and O does not reject
  ours+j    accept iff O accepts, or O is unknown and J accepts
Stability: pairwise agreement and Fleiss' kappa of the six judge configurations per set.

Usage: j1_analyze.py      Writes data/real/j1_analysis.json.
"""

from __future__ import annotations

import json
import sys
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from runner import ROOT

D = ROOT / "data" / "real"
OUT = D / "j1_analysis.json"


def ours() -> tuple[dict, dict]:
    out, cl = {}, {}
    for s, f in (("G1", "g1_results.json"), ("G4", "g4_results.json")):
        for p in json.loads((D / f).read_text(encoding="utf-8"))["pairs"]:
            out[(s, p["row_id"])] = p["verdict"]
            cl[(s, p["row_id"])] = p["closed"]
    return out, cl


def fleiss(table: list[list[int]]) -> float:
    n = sum(table[0])
    N = len(table)
    k = len(table[0])
    p = [sum(row[j] for row in table) / (N * n) for j in range(k)]
    P = [(sum(c * c for c in row) - n) / (n * (n - 1)) for row in table]
    Pbar, Pe = sum(P) / N, sum(x * x for x in p)
    return (Pbar - Pe) / (1 - Pe) if Pe < 1 else 1.0


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    res = json.loads((D / "j1_results.json").read_text(encoding="utf-8"))["results"]
    ov, cv = ours()
    by = defaultdict(dict)
    group = {}
    for r in res:
        by[(r["set"], r["model"].split("/")[-1], r["setting"])][r["row_id"]] = r["verdict"]
        group[(r["set"], r["row_id"])] = r["group"]

    rows = []
    for (s, m, st), v in sorted(by.items()):
        c = Counter()
        for rid, jv in v.items():
            g = group[(s, rid)]
            unf = g.startswith("unfaithful")
            o = ov.get((s, rid), "missing")
            ja = jv == "faithful"
            c["n_unf" if unf else "n_f"] += 1
            if ja:
                c["fa" if unf else "acc_f"] += 1
            if ja and o == "reject":
                c["prov_wrong_acc"] += 1
                c["prov_wrong_acc_" + ("unf" if unf else "f")] += 1
            if (ja and ((unf and o == "reject") or cv.get((s, rid)) == "refuted")) or \
                    (jv == "unfaithful" and not unf and o == "accept"):
                c["conservative_wrong"] += 1
            if ja and cv.get((s, rid)) == "refuted":
                c["wrong_acc_closed_refuted"] += 1
            if jv == "unfaithful" and o == "accept":
                c["prov_wrong_rej"] += 1
                c["prov_wrong_rej_" + ("unf" if unf else "f")] += 1
            if o == "reject":
                c["ours_reject"] += 1
            if o == "accept":
                c["ours_accept"] += 1
            veto = ja and o != "reject"
            comb = o == "accept" or (o not in ("accept", "reject") and ja)
            if veto:
                c["veto_fa" if unf else "veto_acc_f"] += 1
            if comb:
                c["comb_fa" if unf else "comb_acc_f"] += 1
            if g == "unfaithful_true" and ja:
                c["unf_true_acc"] += 1
        rows.append({"set": s, "model": m, "setting": st, **dict(c)})

    stab = {}
    for s in ("G1", "G4"):
        confs = [k for k in by if k[0] == s]
        ids = sorted(set.intersection(*(set(by[k]) for k in confs)))
        table = [[sum(by[k][i] == "faithful" for k in confs), sum(by[k][i] != "faithful" for k in confs)]
                 for i in ids]
        agree = {f"{a[1]}:{a[2]}~{b[1]}:{b[2]}": round(sum(by[a][i] == by[b][i] for i in ids) / len(ids), 3)
                 for a, b in combinations(sorted(confs), 2)}
        split = sum(0 < t[0] < len(confs) for t in table)
        def cons(k, i):
            unf = group[(s, i)].startswith("unfaithful")
            o = ov.get((s, i))
            return (by[k][i] == "faithful" and ((unf and o == "reject") or cv.get((s, i)) == "refuted")) or \
                (by[k][i] == "unfaithful" and not unf and o == "accept")

        wrong = [i for i in ids if any(cons(k, i) for k in confs)]
        flips = {m: sum(by[(s, m, "nl")][i] != by[(s, m, "ref")][i] for i in ids)
                 for m in sorted({k[1] for k in confs})}
        stab[s] = {"n": len(ids), "configs": len(confs), "fleiss_kappa": round(fleiss(table), 3),
                   "pairs_with_disagreement": split, "pairs_some_judge_provably_wrong": len(wrong),
                   "nl_ref_flips": flips, "pairwise_agreement": agree}

    OUT.write_text(json.dumps({"rows": rows, "stability": stab}, indent=1) + "\n", encoding="utf-8")
    keys = ["n_unf", "fa", "n_f", "acc_f", "prov_wrong_acc", "prov_wrong_acc_f", "wrong_acc_closed_refuted",
            "prov_wrong_rej", "prov_wrong_rej_f",
            "conservative_wrong", "veto_fa", "veto_acc_f", "comb_fa", "comb_acc_f", "unf_true_acc"]
    print("set model setting " + " ".join(keys))
    for r in rows:
        print(r["set"], r["model"], r["setting"], " ".join(str(r.get(k, 0)) for k in keys))
    for s, v in stab.items():
        print(s, {k: v for k, v in v.items() if k != "pairwise_agreement"})


if __name__ == "__main__":
    main()
