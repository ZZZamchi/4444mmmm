#!/usr/bin/env python3
"""K17: our full-set verdicts (G5, Opus) against the adjudicated labels of SemantEq.

SemantEq (arXiv 2610.32919) re-adjudicates the ProofNetVerif test pairs labelled equivalent under
the criterion that the candidate makes the same claim as the reference, and runs its proof audit
on them. `data/real/ext/semanteq_manifest.jsonl` is `test/campaign/manifest.jsonl` of
github.com/hlxr89/SemantEq at commit f92767000e14d11744580946980cf874324f5d19 (Apache-2.0,
`data/real/ext/SEMANTEQ_LICENSE`); its pair `pnv_test_NNNN_...` is our `pnv-test-N`.

For each of our outcomes on the labelled-equivalent pairs it counts their label and whether their
audit certifies both directions under some prompt style. Runs no prover and calls no model.

Usage: k17_semanteq.py      -> data/real/k17_semanteq.json
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from a1_local import local
from h2_audit import direction
from paper_check import D, load, located, verdict

MANIFEST = D / "ext" / "semanteq_manifest.jsonl"
OUT = D / "k17_semanteq.json"
STYLES = ("expedient", "unrestricted", "faithful", "rewrite")


def manifest() -> dict[str, dict]:
    out = {}
    for line in MANIFEST.read_text(encoding="utf-8").splitlines():
        r = json.loads(line)
        m = re.match(r"pnv_test_(\d+)_(.*)", r["pair"])
        if not m:
            continue
        both = any(all(r[s].get(d, {}).get("status") == "accepted" for d in ("ref_imp_cand", "cand_imp_ref"))
                   for s in STYLES if s in r)
        out[f"pnv-test-{int(m.group(1))}"] = {"label": r["label"], "audit_both": both, "exercise": m.group(2)}
    return out


def outcome(p: dict) -> str:
    v = verdict(p)
    if v == "reject":
        return "reject:component" if p["verdict"] == "reject" else "reject:closed"
    return v


def compute() -> dict:
    man = manifest()
    k3 = json.loads((D / "k3_direction.json").read_text(encoding="utf-8"))["g5"]["pairs"]
    F = {p["row_id"]: p for p in load(D / "g5" / "g1_results_claude-opus-5.5.json") if p["label"]}
    res: dict = {"manifest_pairs": len(man), "manifest_labels": Counter(v["label"] for v in man.values()),
                 "ours_equivalent": len(F), "shared": sum(k in man for k in F), "by_outcome": {}}
    for k, p in F.items():
        if k not in man:
            continue
        o = res["by_outcome"].setdefault(outcome(p), Counter())
        o[man[k]["label"]] += 1
        o["audit_both"] += man[k]["audit_both"]
    kept = []
    for k, p in sorted(F.items(), key=lambda kv: int(kv[0].split("-")[-1])):
        if k in man and verdict(p) == "reject" and man[k]["label"] == "equivalent":
            kept.append({"row_id": k, "exercise": man[k]["exercise"], "audit_both": man[k]["audit_both"],
                         "component": p["verdict"] == "reject", "located": located(p) or "closed",
                         "alignment": "total" if local(p.get("canon_info")) else "not total",
                         "direction": direction(k3.get(k), p.get("closed"))})
    comp = [k for k, p in F.items() if k in man and verdict(p) == "reject" and p["verdict"] == "reject"]
    nonvac = [k for k in comp if direction(k3.get(k), F[k].get("closed")) != "vacuity"]
    res["rejects_kept_equivalent"] = kept
    res["component_not_vacuity"] = {"n": len(nonvac),
                                    "relabelled": sum(man[k]["label"] != "equivalent" for k in nonvac)}
    res["accepts_relabelled"] = [{"row_id": k, "exercise": man[k]["exercise"]} for k, p in F.items()
                                 if k in man and verdict(p) == "accept" and man[k]["label"] != "equivalent"]
    return res


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    res = compute()
    OUT.write_text(json.dumps(res, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
