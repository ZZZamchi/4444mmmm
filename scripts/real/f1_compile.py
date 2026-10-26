#!/usr/bin/env python3
"""F1: compile rates of real-data sources under lean/ (Mathlib v4.27.0-rc1).

Writes data/real/f1_compile.json and prints an availability table.
"""

from __future__ import annotations

import json
import sys
import time
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from realdata import formaltcs, pnv_item, proofnetverif
from runner import ROOT, check

OUT = ROOT / "data" / "real" / "f1_compile.json"


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    rows = proofnetverif("test")
    golds = {}
    for r in rows:
        golds.setdefault(r.stmt_id, r)
    gold_items = [pnv_item(r, "gold") for r in golds.values()]
    pred_items = [pnv_item(r, "pred") for r in rows]
    tcs_items = formaltcs()

    res = check(gold_items + pred_items + tcs_items)

    def rate(items):
        ok = sum(res[i.item_id].ok for i in items)
        return ok, len(items)

    gold_ok = {r.stmt_id for r in golds.values() if res[f"{r.row_id}:gold"].ok}
    pred_ok_rows = [r for r in rows if res[f"{r.row_id}:pred"].ok]
    usable = [r for r in pred_ok_rows if r.stmt_id in gold_ok]
    err_kinds = Counter()
    for it in gold_items + tcs_items:
        for e in res[it.item_id].errors[:1]:
            err_kinds[e.split("\n")[0][:60]] += 1

    summary = {
        "lean_env": "lean/ Mathlib v4.27.0-rc1",
        "proofnetverif_test": {
            "gold_ok": rate(gold_items),
            "pred_ok": rate(pred_items),
            "usable_pairs": len(usable),
            "usable_equivalent": sum(r.correct for r in usable),
            "usable_inequivalent": sum(not r.correct for r in usable),
        },
        "formaltcs": {"ok": rate(tcs_items)},
        "top_first_errors": err_kinds.most_common(12),
        "seconds": round(time.time() - t0, 1),
    }
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
