#!/usr/bin/env python3
"""K14: where the strong prover's `unknown` verdicts on the 300-pair subset come from.

Final verdicts are those after embedding alignment (`e1_results.json`); per-pair goals and
alignment come from `g1_results.json`. Each unknown pair falls in exactly one class:

* `no_split`     a regrouping certificate (`split_r` or `split_s`) is missing;
* `no_shared`    both certificates hold but no binder is aligned, so every component
                 goal is a closed comparison of the residual statements;
* `partial`      some but not all binders are aligned;
* `full`         every binder is aligned and no component goal was decided.

Within each class it reports the closed outcome and whether `ncomp` (the conclusions differ
somewhere) was proved while the hypothesis goals stayed open.

Writes data/real/k14_unknown.json.
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
G1 = ROOT / "data" / "real" / "g1_results.json"
E1 = ROOT / "data" / "real" / "e1_results.json"
OUT = ROOT / "data" / "real" / "k14_unknown.json"


def klass(p: dict) -> str:
    if not {"split_r", "split_s"} <= set(p["proved"]):
        return "no_split"
    if int(p.get("shared") or 0) == 0:
        return "no_shared"
    return "full" if "full=true" in (p.get("canon_info") or "") else "partial"


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    g1 = {p["row_id"]: p for p in json.loads(G1.read_text(encoding="utf-8"))["pairs"]}
    final = {p["row_id"]: p["embed"] for p in json.loads(E1.read_text(encoding="utf-8"))["pairs"]}
    unk = [g1[r] for r, v in final.items() if v == "unknown"]
    out: dict = {"n": len(final), "unknown": len(unk), "classes": {}}
    for k in ("no_split", "no_shared", "partial", "full"):
        ps = [p for p in unk if klass(p) == k]
        out["classes"][k] = {
            "n": len(ps),
            "label_equivalent": sum(p["label"] for p in ps),
            "closed": dict(Counter(p["closed"] for p in ps)),
            "ncomp_only": sum("ncomp" in p["proved"] for p in ps),
            "row_ids": sorted(p["row_id"] for p in ps),
        }
    OUT.write_text(json.dumps(out, indent=1), encoding="utf-8")
    print(json.dumps({k: {a: b for a, b in v.items() if a != "row_ids"} for k, v in out["classes"].items()}, indent=1))
    print("unknown", out["unknown"], "of", out["n"])


if __name__ == "__main__":
    main()
