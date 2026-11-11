#!/usr/bin/env python3
"""The accepts that rule L adds to v4 on a split, for reading (notes/protocol-v4.md §9).

Lists every pair that v4 (`univ0m,align` with L and NF) accepts and the same flags with NF alone do
not, with its label, both statements, the alignment info and the canonical `acc` goal. Analysis
only: nothing here feeds a verdict. With `--split valid` it needs the v4 unlock (`K22_VALID_UNLOCK`).

Usage: k22_l_audit.py [--split valid]   -> data/real/k22_l_audit_{split}.json
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import k22_align as k


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    base, post, stmt, cache = k.load()
    store = json.loads(k.PROVED.read_text(encoding="utf-8"))
    v4 = k.verdicts(base, post, cache, store, k.V4_FLAGS, k.V4_RULES, "full")
    no_l = k.verdicts(base, post, cache, store, k.V4_FLAGS, "NF", "full")
    rows = []
    for rid in sorted(base, key=lambda r: int(r.split("-")[-1])):
        if v4[rid] != "accept" or no_l[rid] == "accept":
            continue
        r, gold, pred = stmt[rid]
        c = cache.get(f"{k.V4_FLAGS}|{rid}", {})
        rows.append({"row_id": rid, "label": bool(base[rid]["label"]), "without_L": no_l[rid],
                     "info": c.get("info") or base[rid].get("canon_info"), "reference": gold, "candidate": pred,
                     "acc_goal": (c.get("goals") or {}).get("acc")})
    out = D / f"k22_l_audit_{k.SPLIT}.json"
    k.save(out, rows)
    for x in rows:
        print("=" * 100)
        print(x["row_id"], "equivalent" if x["label"] else "INEQUIVALENT", "| without L:", x["without_L"])
        print("info:", x["info"])
        print("R:", x["reference"])
        print("S:", x["candidate"])
        print("acc:", (x["acc_goal"] or "")[:600])
    print(f"{len(rows)} accepts added by L:", sum(x["label"] for x in rows), "equivalent,",
          sum(not x["label"] for x in rows), "inequivalent ->", out)


D = k.D

if __name__ == "__main__":
    main()
