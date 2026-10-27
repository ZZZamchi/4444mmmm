#!/usr/bin/env python3
"""D2 analysis: rewards and best-of-n selection over the D1 draws.

Each draw (problem, model, k) yields a candidate or nothing (no elaboration). A reward is a
predicate on candidates:
  closed       closed equivalence proved
  judge:<cfg>  the judge answers FAITHFUL
  ours         accept (component equivalence)
  ours_local   local accept (Proposition residue)
  veto:<cfg>   judge accepts and ours does not reject
  ours+<cfg>   local accept, else (no reject and judge accepts)
Each candidate is classified by certificates that do not depend on the reward:
  wrong   ours rejects (kernel proof that hypotheses or in-domain conclusions differ) or the
          closed equivalence is refuted (the two statements differ in truth value)
  right   local accept
  open    otherwise
Reported: per-draw reward precision (share of rewarded draws that are wrong / right / open)
and best-of-n selection (first rewarded draw among n, averaged over random draw orders).

Usage: [D2_GT=loose|strict|refuted] d2_analyze.py
       Writes data/real/d2_analysis.json (loose) or d2_analysis_<GT>.json.
"""

from __future__ import annotations

import json
import os
import random
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from a1_local import local
from runner import ROOT

D = ROOT / "data" / "real"
NS = (1, 2, 4, 8, 16, 24)
ORDERS = 50


GT = os.environ.get("D2_GT", "loose")
# Direction classes of the rejects (K3); `robust` keeps only rejects that survive every regrouping.
DIRECTION = json.loads((D / "k3_direction.json").read_text(encoding="utf-8"))["d2"]["pairs"] if GT == "robust" else {}


def classify(p: dict, cid: str | None = None) -> str:
    """`loose`: as above. `strict`: a reject counts only with both regrouping certificates and a
    total alignment, a local accept only with both certificates. `robust`: as `strict`, and a
    reject counts only with a kernel proof that the pointwise claims differ (`npimp`), the
    rejects that survive every regrouping (Proposition prop:split).
    `refuted`: wrong only by a refuted closed equivalence, which does not depend on our criterion."""
    certs = {"split_r", "split_s"} <= set(p.get("proved") or [])
    full = "full=true" in (p.get("canon_info") or "")
    if p["closed"] == "refuted":
        return "wrong"
    strict = GT in ("strict", "robust") and certs and full
    if GT == "robust":
        strict = strict and "npimp" in DIRECTION.get(cid, {}).get("proved", [])
    if p["verdict"] == "reject" and (GT == "loose" or strict):
        return "wrong"
    if p["verdict"] == "accept" and local(p.get("canon_info")) and (GT == "loose" or certs):
        return "right"
    return "open"


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    d1 = json.loads((D / "d1_candidates.json").read_text(encoding="utf-8"))
    pv = json.loads((D / "d2_prove.json").read_text(encoding="utf-8"))["candidates"]
    jv = json.loads((D / "d2_judge.json").read_text(encoding="utf-8"))["candidates"] \
        if (D / "d2_judge.json").exists() else {}
    cfgs = sorted({k for v in jv.values() for k in v})
    done = set(pv)
    print("missing judge verdicts", {k: sum(k not in jv.get(c, {}) for c in done) for k in cfgs}, flush=True)
    probs = defaultdict(list)
    for x in d1["draws"]:
        probs[x["problem"]].append(x["cand"])
    probs = {p: ds for p, ds in probs.items() if all(c is None or c in done for c in ds)}
    print("problems", len(probs), "candidates", len(done), "judge configs", cfgs, flush=True)

    rewards = {
        "closed": lambda c: pv[c]["closed"] == "proved",
        "ours": lambda c: pv[c]["verdict"] == "accept",
        "ours_local": lambda c: classify(pv[c], c) == "right",
    }
    for k in cfgs:
        rewards[f"judge:{k}"] = lambda c, k=k: jv.get(c, {}).get(k) == "faithful"
        rewards[f"veto:{k}"] = lambda c, k=k: jv.get(c, {}).get(k) == "faithful" and pv[c]["verdict"] != "reject"
        rewards[f"ours+{k}"] = lambda c, k=k: classify(pv[c], c) == "right" or (
            jv.get(c, {}).get(k) == "faithful" and classify(pv[c], c) != "wrong")

    cls = {c: classify(pv[c], c) for c in done}
    if GT == "robust":
        strict_rejects = [c for c in done if pv[c]["verdict"] == "reject"
                          and {"split_r", "split_s"} <= set(pv[c].get("proved") or [])
                          and "full=true" in (pv[c].get("canon_info") or "")]
        print("strict rejects", len(strict_rejects), "with direction", sum(c in DIRECTION for c in strict_rejects),
              Counter(DIRECTION.get(c, {}).get("class") for c in strict_rejects),
              "npimp", sum("npimp" in DIRECTION.get(c, {}).get("proved", []) for c in strict_rejects), flush=True)
    draws = [c for ds in probs.values() for c in ds if c is not None]
    print("draw classes", dict(Counter(cls[c] for c in draws)), "no candidate",
          sum(c is None for ds in probs.values() for c in ds), flush=True)

    precision = {}
    for name, f in rewards.items():
        got = Counter(cls[c] for c in draws if f(c))
        n = sum(got.values())
        precision[name] = {"rewarded": n, **{k: got[k] for k in ("wrong", "right", "open")},
                           "wrong_rate": round(got["wrong"] / n, 4) if n else None}

    rng = random.Random(0)
    orders = {p: [rng.sample(ds, len(ds)) for _ in range(ORDERS)] for p, ds in probs.items()}
    bon = {}
    for name, f in rewards.items():
        row = {}
        for n in NS:
            c = Counter()
            for p, os_ in orders.items():
                for o in os_:
                    pick = next((x for x in o[:n] if x is not None and f(x)), None)
                    c["none" if pick is None else cls[pick]] += 1
            tot = sum(c.values())
            row[n] = {k: round(c[k] / tot, 4) for k in ("right", "open", "wrong", "none")}
        bon[name] = row

    out = {"problems": len(probs), "candidates": len(done), "configs": cfgs,
           "draw_classes": dict(Counter(cls[c] for c in draws)), "precision": precision, "best_of_n": bon}
    out["ground_truth"] = GT
    (D / ("d2_analysis.json" if GT == "loose" else f"d2_analysis_{GT}.json")).write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    print("\nreward precision (per draw)")
    for k, v in precision.items():
        print(f"  {k:28s} {v}")
    print("\nbest-of-n: selected wrong / right / none")
    for k, row in bon.items():
        print(f"  {k:28s} " + "  ".join(f"n={n}: {r['wrong']:.3f}/{r['right']:.3f}/{r['none']:.3f}" for n, r in row.items()))


if __name__ == "__main__":
    main()
