#!/usr/bin/env python3
"""K9: trivialization probe.

A component accept certifies ∀ x̄, H_R ↔ H_S and the conclusions pointwise. When the content of
the exercise is itself such a hypothesis equivalence (R: "a ∣ b in ℤ[i] → a ∣ b in ℤ",
S: "a ∣ b → a ∣ b"), the accept is correct relative to the theory but S has lost the problem.
K7 does not see this, since the conclusion is not constant. The probe asks whether each
statement closes under a fixed tactic within a small heartbeat budget, at two levels:

  logic    intros, assumption, tauto: the statement holds by propositional logic alone
  shallow  logic plus rfl and simp_all: it holds by definitional unfolding or one simp call

A pair is flagged at a level when S closes there and R does not. A flag is a kernel proof that
S is trivial at that level, not a verdict. At the shallow level a reference that is itself a
Mathlib simp lemma (R above is `Zsqrtd.intCast_dvd_intCast`) masks the flag.

Usage: k9_trivial.py [g1|g4|g5 ...]   writes data/real/k9_trivial.json
"""

from __future__ import annotations

import json
import os
import sys
import time
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
from a1_local import label, local
from k6_stats import accepted
from realdata import proofnetverif
from runner import ROOT, Item, check
from stmt import to_prop

D = ROOT / "data" / "real"
OUT = D / "k9_trivial.json"
LEVELS = {
    "logic": "intros; first | assumption | tauto",
    "shallow": "intros; first | assumption | rfl | tauto | (simp_all; done)",
}
HEARTBEATS = 20000
WORKERS = int(os.environ.get("K9_WORKERS", "4"))
RESULTS = {"g1": "g1_results.json", "g4": "g4_results.json", "g5": "g5/g1_results_claude-opus-5.5.json"}


def rows_of(which: str) -> dict:
    if which in ("g1", "g5"):
        return {r.row_id: r for r in proofnetverif("test")}
    import g4_pnv as g4
    return {r.row_id: r for r in g4.load()[0]}


def run(which: str) -> dict:
    t0 = time.time()
    rows = rows_of(which)
    pairs = json.loads((D / RESULTS[which]).read_text(encoding="utf-8"))["pairs"]
    items, keys = [], []
    for p in pairs:
        r = rows[p["row_id"]]
        imports, pre = f2.prelude(r)
        for side, src in (("R", r.gold), ("S", r.pred)):
            prop = to_prop(src)
            if prop is None:
                continue
            for lvl, tac in LEVELS.items():
                items.append(Item(f"{r.row_id}:k9{lvl}:{side}", imports,
                                  f"{pre}\n{f2.theorem(f'k9_{lvl}_{side}', f2.normalize(prop), tac, HEARTBEATS)}"))
                keys.append((r.row_id, lvl, side))
    res = check(items, batch_size=20, workers=WORKERS)
    triv = {k: res[it.item_id].ok and not res[it.item_id].uses_sorry for k, it in zip(keys, items)}
    out = {}
    for p in pairs:
        rid = p["row_id"]
        v = {"label": label(p), "accepted": accepted(p), "local": local(p.get("canon_info"))}
        for lvl in LEVELS:
            s, r_ = triv.get((rid, lvl, "S"), False), triv.get((rid, lvl, "R"), False)
            v[lvl] = {"s": s, "r": r_, "flag": s and not r_}
        out[rid] = v
    summary = Counter()
    for v in out.values():
        lab = "faithful" if v["label"] else "unfaithful"
        summary[f"{lab}:n"] += 1
        kind = ("local" if v["local"] else "residual") + "_accept" if v["accepted"] else None
        if kind:
            summary[f"{lab}:{kind}"] += 1
        for lvl in LEVELS:
            summary[f"{lab}:{lvl}_flag"] += v[lvl]["flag"]
            if kind:
                summary[f"{lab}:{kind}_{lvl}_flag"] += v[lvl]["flag"]
    print(which, dict(sorted(summary.items())), f"{time.time() - t0:.0f}s", flush=True)
    return {"levels": LEVELS, "heartbeats": HEARTBEATS, "summary": dict(summary), "pairs": out}


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    out = json.loads(OUT.read_text(encoding="utf-8")) if OUT.exists() else {}
    for which in sys.argv[1:] or ["g1", "g4", "g5"]:
        out[which] = run(which)
        OUT.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
