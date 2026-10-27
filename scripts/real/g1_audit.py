#!/usr/bin/env python3
"""Dump G1 cases that need a manual check, and compare with F9 on the shared pairs.

Writes data/real/g1_audit.txt.
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from realdata import proofnetverif
from runner import ROOT
from stmt import to_prop

D = ROOT / "data" / "real"


def main() -> None:
    g1 = {p["row_id"]: p for p in json.loads((D / "g1_results.json").read_text(encoding="utf-8"))["pairs"]}
    f9 = {p["row_id"]: p for p in json.loads((D / "f9_results.json").read_text(encoding="utf-8"))["pairs"]}
    canon = json.loads((D / "g1_canon2.json").read_text(encoding="utf-8"))
    rows = {r.row_id: r for r in proofnetverif("test")}
    out = ["overlap with F9 (label, F9 union, G1 verdict) -> count"]
    for k, v in sorted(Counter((p["label"], f9[rid]["union"], g1[rid]["verdict"]) for rid, p in g1.items() if rid in f9).items(), key=str):
        out.append(f"  {k}: {v}")
    sus = [p for p in g1.values() if (p["label"] and (p["verdict"] == "reject" or p["closed"] == "refuted"))
           or (not p["label"] and p["verdict"] == "accept")]
    for p in sus:
        r = rows[p["row_id"]]
        g = canon[p["row_id"]]["goals"]
        out.append(f"\n===== {p['row_id']} label={p['label']} comp={p['verdict']} closed={p['closed']} {p['closed_proved']}")
        out.append(f"proved={p['proved']} {p['canon_info']}")
        out.append("NL: " + r.nl[:300].replace("\n", " "))
        out.append("G: " + to_prop(r.gold)[:400].replace("\n", " "))
        out.append("P: " + to_prop(r.pred)[:400].replace("\n", " "))
        for k in ("nhyp", "ncin", "ncomp") if p["verdict"] == "reject" else ("acc",):
            if k in p["proved"]:
                out.append(f"{k}: " + g[k][:600].replace("\n", " "))
    (D / "g1_audit.txt").write_text("\n".join(out) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
