#!/usr/bin/env python3
"""D3: best-of-n selection with each verdict as the selector.

Ground truth per candidate (certificates only, no model opinion):
  faithful     `comp == accept`: kernel-checked comp-equivalence to the corrected reference
  unfaithful   `comp == reject` or closed refutation: kernel-checked difference
  uncertified  everything else (off-domain or unknown); left to human annotation (H1)

For a pool of draws and a budget n, the first n draws of a random permutation are taken; the
selector keeps the candidates it accepts and picks the most frequent one (ties: earliest).
If nothing is accepted the selector abstains. Averaged over R permutations per problem.

Usage: d3_select.py [R]     Writes data/real/d3_select.json.
"""

from __future__ import annotations

import json
import random
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from runner import ROOT

D = ROOT / "data" / "real"
R = int(sys.argv[1]) if len(sys.argv) > 1 else 50


def truth(c: dict) -> str:
    if c["comp"] == "accept":
        return "faithful"
    if c["comp"] == "reject" or c["closed"] == "refuted":
        return "unfaithful"
    return "uncertified"


def selectors(cands: list[dict]) -> dict:
    judge_keys = sorted({k for c in cands for k in c["judges"]})
    sel = {
        "none": lambda c: True,
        "closed_tactic": lambda c: c["closed_tactic"] == "proved",
        "closed": lambda c: c["closed"] == "proved",
        "beq_plus": lambda c: c["beq_plus"] is True,
        "ours_tactic": lambda c: c["comp_tactic"] == "accept",
        "ours": lambda c: c["comp"] == "accept",
    }
    for k in judge_keys:
        sel[f"judge:{k}"] = (lambda kk: lambda c: c["judges"].get(kk) == "faithful")(k)
    return sel


def pick(seq: list, acc: dict) -> str | None:
    good = [x for x in seq if x is not None and acc[x]]
    if not good:
        return None
    cnt = Counter(good)
    best = max(cnt.values())
    return next(x for x in good if cnt[x] == best)


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    d1 = json.loads((D / "d1_candidates.json").read_text(encoding="utf-8"))
    cands = json.loads((D / "d2_verdicts.json").read_text(encoding="utf-8"))["candidates"]
    by = {c["cand_id"]: c for c in cands}
    gt = {cid: truth(c) for cid, c in by.items()}
    sel = selectors(cands)
    acc = {s: {cid: f(c) for cid, c in by.items()} for s, f in sel.items()}

    pools: dict[tuple, list] = defaultdict(list)
    for d in d1["draws"]:
        cid = d["cand"] if d["cand"] in by else None
        pools[(d["model"].split("/")[-1], d["problem"])].append(cid)
        pools[("all", d["problem"])].append(cid)
    problems = sorted({p for _, p in pools})
    names = sorted({m for m, _ in pools})

    rng = random.Random(0)
    curves = []
    for m in names:
        size = max(len(pools[(m, p)]) for p in problems)
        ns = [n for n in (1, 2, 3, 4, 6, 8, 12, 16, 24) if n <= size]
        perms = {p: [rng.sample(pools[(m, p)], len(pools[(m, p)])) for _ in range(R)] for p in problems}
        for s in sel:
            for n in ns:
                c = Counter()
                for p in problems:
                    for perm in perms[p]:
                        x = pick(perm[:n], acc[s])
                        c["abstain" if x is None else gt[x]] += 1
                tot = len(problems) * R
                chosen = tot - c["abstain"]
                curves.append({
                    "pool": m, "selector": s, "n": n,
                    "coverage": round(chosen / tot, 4),
                    "faithful": round(c["faithful"] / tot, 4),
                    "unfaithful": round(c["unfaithful"] / tot, 4),
                    "uncertified": round(c["uncertified"] / tot, 4),
                    "unfaithful_share": round(c["unfaithful"] / chosen, 4) if chosen else None,
                })

    pool_stats = {m: dict(Counter(gt[x] if x else "failed" for p in problems for x in pools[(m, p)])) for m in names}
    cand_stats = dict(Counter(gt.values()))
    sel_stats = {s: dict(Counter(gt[cid] for cid in by if acc[s][cid])) for s in sel}
    out = {"R": R, "problems": len(problems), "draws_by_truth": pool_stats, "candidates_by_truth": cand_stats,
           "accepted_by_truth": sel_stats, "curves": curves}
    (D / "d3_select.json").write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    print("candidates", cand_stats)
    print("draws", pool_stats)
    for s, v in sel_stats.items():
        print(f"{s:28s}", v)
    for row in curves:
        if row["pool"] == "all" and row["n"] in (1, 4, 24):
            print(row)


if __name__ == "__main__":
    main()
