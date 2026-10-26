#!/usr/bin/env python3
"""Audit F9 verdicts: shared-prefix size, split checks, and the suspicious cases.

Reads data/real/f9_results.json and data/real/f9_canon.json (read only).
Writes data/real/g1_audit_f9.txt.
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from realdata import proofnetverif
from runner import ROOT
from stmt import to_prop

D = ROOT / "data" / "real"
OUT = D / "g1_audit_f9.txt"


def info(s: str | None) -> dict:
    return dict(re.findall(r"(\w+)=(\S+)", s or ""))


def main() -> None:
    res = json.loads((D / "f9_results.json").read_text(encoding="utf-8"))
    canon = json.loads((D / "f9_canon.json").read_text(encoding="utf-8"))
    rows = {r.row_id: r for r in proofnetverif("test")}
    out = []
    tab = Counter()
    for p in res["pairs"]:
        inf = info(p["canon_info"])
        shared = int(inf.get("shared", 0))
        split = {"split_r", "split_s"} <= set(p["tactic"])
        tab[(p["label"], p["union"], "shared0" if shared == 0 else "shared>0", "split" if split else "nosplit")] += 1
    out.append("label, union verdict, shared prefix, split checked -> count")
    for k, v in sorted(tab.items(), key=str):
        out.append(f"  {k}: {v}")
    for p in res["pairs"]:
        sus = (not p["label"] and p["union"] in ("accept", "reject")) or (p["label"] and p["union"] == "reject")
        if not sus:
            continue
        r = rows[p["row_id"]]
        g = canon[p["row_id"]].get("goals", {})
        proved = sorted(set().union(*(set(v or ()) for v in p["proved"].values())))
        out.append(f"\n===== {p['row_id']} label={p['label']} union={p['union']} closed={p['closed']} {p['canon_info']}")
        out.append(f"proved: {proved}  tactic: {p['tactic']}")
        out.append("NL: " + r.nl[:300].replace("\n", " "))
        out.append("G: " + to_prop(r.gold)[:400].replace("\n", " "))
        out.append("P: " + to_prop(r.pred)[:400].replace("\n", " "))
        for k in ("nhyp", "ncin", "acc"):
            if k in g:
                out.append(f"{k}: " + g[k][:500].replace("\n", " "))
    OUT.write_text("\n".join(out) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
