#!/usr/bin/env python3
"""v3 development (test split only): intensional accept for residual pairs (rule R3).

A `residual` accept proves the component equivalences on an alignment that ends early, so the
remainder is compared closed and inherits the closed collapse. If the `acc` goal is closed by
`Iff.rfl` at reducible transparency, the two sides are the same proposition up to reducible
unfolding, which no collapse can produce; such a pair can be accepted. Lean only, no API.
Writes data/real/v3/ident.json.

Usage: v3_ident.py
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import g1_full as g1
from paper_check import D, load, verdict
from realdata import proofnetverif
from stmt import to_prop

OUT = D / "v3" / "ident.json"
IDENT_TAC = "intros; with_reducible exact ⟨Iff.rfl, Iff.rfl⟩"


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    ps = load(D / "g5" / "g1_results_claude-opus-5.5.json")
    rows = {r.row_id: r for r in proofnetverif("test")}
    res_pairs = [p for p in ps if verdict(p) == "residual"]
    stmt = {p["row_id"]: (rows[p["row_id"]], f2.normalize(to_prop(rows[p["row_id"]].gold)),
                          f2.normalize(to_prop(rows[p["row_id"]].pred))) for p in res_pairs}
    res = g1.prove_items([((p["row_id"], "acc"), (*stmt[p["row_id"]], IDENT_TAC)) for p in res_pairs], "v3id")
    out = [{"row_id": p["row_id"], "label": p["label"], "identical": res[(p["row_id"], "acc")].ok
            and not res[(p["row_id"], "acc")].uses_sorry, "canon_info": p.get("canon_info")} for p in res_pairs]
    summary = {"residual": len(res_pairs),
               "identical": dict(Counter(f"{'F' if o['label'] else 'U'}" for o in out if o["identical"])),
               "identical_U": [o["row_id"] for o in out if o["identical"] and not o["label"]]}
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps({"summary": summary, "pairs": out}, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
