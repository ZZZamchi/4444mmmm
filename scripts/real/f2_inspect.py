#!/usr/bin/env python3
"""Per-goal breakdown of F2, label conflicts, and elaboration failure causes."""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from f2_oracle import OUT, normalize, prelude
from realdata import proofnetverif
from runner import Item, check
from stmt import to_prop


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    d = json.loads(OUT.read_text(encoding="utf-8"))
    for tier in ("t0", "t1", "t2"):
        c = Counter((p["label"], g) for p in d["pairs"] for g in p[tier])
        print(tier, dict(sorted(c.items())))
    rows = {r.row_id: r for r in proofnetverif("test")}
    for p in d["pairs"]:
        if not p["label"] and {"fwd", "bwd"} <= set(p["t2"]):
            r = rows[p["row_id"]]
            print("=== label inequivalent, proved equivalent:", r.row_id, r.stmt_id)
            print("NL:", r.nl.strip()[:300])
            print("GOLD:", r.gold.strip())
            print("PRED:", r.pred.strip())

    causes = Counter()
    items = []
    for r in rows.values():
        g, pr = to_prop(r.gold), to_prop(r.pred)
        if g is None or pr is None:
            continue
        imports, pre = prelude(r)
        items.append(Item(f"{r.row_id}:elab", imports, f"{pre}\nexample : ({normalize(g)}) ∧ ({normalize(pr)}) → True := fun _ => trivial"))
    res = check(items, batch_size=25)
    for it in items:
        rr = res[it.item_id]
        if rr.ok:
            continue
        msg = " ".join(rr.errors)
        if "nknown identifier" in msg or "nknown constant" in msg:
            causes["unknown_identifier (autoImplicit off or renamed)"] += 1
        elif "universe" in msg.lower():
            causes["universe"] += 1
        elif "synthesize" in msg:
            causes["instance"] += 1
        elif "unexpected token" in msg or "expected" in msg:
            causes["parse"] += 1
        else:
            causes["other"] += 1
    print("elab failures:", dict(causes))


if __name__ == "__main__":
    main()
