#!/usr/bin/env python3
"""K18: our full-set verdicts (G5, Opus) combined with SemantEq-Eval on the ProofNetVerif test split.

SemantEq restricts the proofs an accept may use and does not certify differences; we certify
differences with an unrestricted prover. This scores, on the pairs both cover, SemantEq-Eval alone,
our criterion alone, a two-sided evaluator that takes SemantEq's accepts and our certified rejects,
and accepting only what both accept, under the published and the adjudicated labels.

Data: `data/real/ext/semanteq_pnv_test_verdicts.jsonl` is `test/results/pnv_test_verdicts.jsonl` of
github.com/hlxr89/SemantEq at commit f92767000e14d11744580946980cf874324f5d19 (Apache-2.0,
`data/real/ext/SEMANTEQ_LICENSE`); its id `pnv:test:NNNN:...` is our `pnv-test-N`.

Usage: k18_combine.py      -> data/real/k18_combine.json
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from h2_audit import direction
from paper_check import D, load, located, verdict

VERDICTS = D / "ext" / "semanteq_pnv_test_verdicts.jsonl"
OUT = D / "k18_combine.json"


def semanteq() -> dict[str, dict]:
    out = {}
    for line in VERDICTS.read_text(encoding="utf-8").splitlines():
        r = json.loads(line)
        n = int(re.match(r"pnv:test:(\d+):", r["id"]).group(1))
        out[f"pnv-test-{n}"] = r
    return out


def score(decisions: dict[str, str], truth: dict[str, bool]) -> dict:
    """decisions: accept / reject / undecided per pair; truth: True for equivalent."""
    c = Counter((d, truth[k]) for k, d in decisions.items())
    acc, rej = c[("accept", True)] + c[("accept", False)], c[("reject", True)] + c[("reject", False)]
    eq, ne = sum(truth.values()), sum(not v for v in truth.values())
    return {"accept": acc, "false_accept": c[("accept", False)], "reject": rej, "false_reject": c[("reject", True)],
            "undecided": len(decisions) - acc - rej,
            "accept_precision": round(c[("accept", True)] / acc, 4) if acc else None,
            "accept_recall": round(c[("accept", True)] / eq, 4),
            "reject_precision": round(c[("reject", False)] / rej, 4) if rej else None,
            "reject_recall": round(c[("reject", False)] / ne, 4),
            "decided": round((acc + rej) / len(decisions), 4), "equivalent": eq, "inequivalent": ne}


def compute() -> dict:
    se = semanteq()
    ours = {p["row_id"]: p for p in load(D / "g5" / "g1_results_claude-opus-5.5.json")}
    shared = sorted(set(se) & set(ours), key=lambda k: int(k.split("-")[-1]))
    k3 = json.loads((D / "k3_direction.json").read_text(encoding="utf-8"))["g5"]["pairs"]
    v = {k: verdict(ours[k]) for k in shared}
    s_acc = {k: bool(se[k]["semanteq_accept"]) for k in shared}
    systems = {
        "semanteq": {k: "accept" if s_acc[k] else "undecided" for k in shared},
        "ours": {k: v[k] if v[k] in ("accept", "reject") else "undecided" for k in shared},
        "semanteq_accept_ours_reject": {k: "conflict" if s_acc[k] and v[k] == "reject" else
                                        "accept" if s_acc[k] else "reject" if v[k] == "reject" else "undecided"
                                        for k in shared},
        "both_accept": {k: "accept" if s_acc[k] and v[k] == "accept" else "reject" if v[k] == "reject" else "undecided"
                        for k in shared},
        "beqplus": {k: "accept" if se[k]["beqplus_v430_accept"] else "undecided" for k in shared},
    }
    labels = {"published": {k: bool(se[k]["published_equivalent"]) for k in shared},
              "adjudicated": {k: bool(se[k]["adjudicated_equivalent"]) for k in shared}}
    ours_label = {k: bool(ours[k]["label"]) for k in shared}
    res: dict = {"semanteq_pairs": len(se), "ours_pairs": len(ours), "shared": len(shared),
                 "label_agreement_published": sum(labels["published"][k] == ours_label[k] for k in shared),
                 "scores": {}}
    for lab, truth in labels.items():
        for name, dec in systems.items():
            # a conflict counts as neither an accept nor a reject of the combined evaluator
            res["scores"][f"{name}|{lab}"] = score({k: (d if d != "conflict" else "undecided") for k, d in dec.items()},
                                                   truth)
    conflicts = [k for k in shared if s_acc[k] and v[k] == "reject"]
    res["conflicts"] = [{"row_id": k, "label": labels["published"][k], "adjudicated": labels["adjudicated"][k],
                         "located": located(ours[k]) or "closed", "direction": direction(k3.get(k), ours[k].get("closed"))}
                        for k in conflicts]
    res["our_false_accepts_semanteq_accepts"] = sum(s_acc[k] for k in shared if v[k] == "accept" and not ours_label[k])
    res["our_false_accepts"] = sum(1 for k in shared if v[k] == "accept" and not ours_label[k])
    res["accept_overlap"] = Counter(f"{'S' if s_acc[k] else '-'}{'O' if v[k] == 'accept' else '-'}" for k in shared)
    return res


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    res = compute()
    OUT.write_text(json.dumps(res, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
