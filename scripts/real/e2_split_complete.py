#!/usr/bin/env python3
"""E2: complete the regrouping certificates `split_r`, `split_s` of decided pairs.

A decided pair (accept or reject) whose canonical goals were proved but whose regrouping
goals `R ↔ ∀ x̄, H_R → C_R` and `S ↔ ∀ x̄, H_S → C_S` were not, is a verdict whose meaning
still depends on the canonicalization code. This script tries, for every missing regrouping
goal, the second tactic tier `SPLIT_TAC2`, then one LLM proposal with one repair round, all
checked by `canon2_prove` against the kernel goal. Results are written back into the results
file (`split_checked`, `split_source`) and the proofs to `data/real/e2_split_proofs.json`.

Usage: e2_split_complete.py g1|g4|d2 [MODEL [RESULTS_FILE]]
RESULTS_FILE (g1/g4 only) selects another prover tier's results; its proofs are keyed by the
file stem so that each tier's certificates come from its own model.
"""

from __future__ import annotations

import json
import os
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import g1_full as g1
from f7_component import SPLIT_TAC2
from f9_canon import repair
from runner import ROOT
from stmt import to_prop

WHICH = sys.argv[1] if len(sys.argv) > 1 else "g1"
MODEL = sys.argv[2] if len(sys.argv) > 2 else "anthropic/claude-opus-5.5"
RESULTS = Path(sys.argv[3]) if len(sys.argv) > 3 else None
g1.MODEL = MODEL
PROOFS = ROOT / "data" / "real" / "e2_split_proofs.json"
KEY = RESULTS.stem if RESULTS else WHICH


def load():
    if WHICH == "d2":
        import d2_select as d2
        res_file = ROOT / "data" / "real" / "d2_prove.json"
        g1.CANON_CACHE = ROOT / "data" / "real" / f"d2_canon_{d2.d1_digest()}.json"
        raw = json.loads(res_file.read_text(encoding="utf-8"))
        res = {"raw": raw, "pairs": [{"row_id": k, **v} for k, v in raw["candidates"].items()]}
        canon = json.loads(g1.CANON_CACHE.read_text(encoding="utf-8"))
        stmt = {r.row_id: (r, g, s) for r, g, s in d2.load()[0] if r.row_id in raw["candidates"]}
        return res_file, res, canon, stmt
    if WHICH == "g1":
        from realdata import proofnetverif
        res_file = RESULTS or ROOT / "data" / "real" / "g1_results.json"
        rows = {r.row_id: r for r in proofnetverif("test")}
    else:
        import g4_pnv as g4
        g4.OUT = ROOT / "data" / "real" / "g4_results.json"
        g4.MODEL = MODEL
        g1.MODEL = MODEL
        g1.CANON_CACHE = ROOT / "data" / "real" / "g4_canon2.json"
        res_file = RESULTS or g4.OUT
        rows = {r.row_id: r for r in g4.load()[0]}
    res = json.loads(res_file.read_text(encoding="utf-8"))
    canon = json.loads(g1.CANON_CACHE.read_text(encoding="utf-8"))
    stmt = {}
    for p in res["pairs"]:
        r = rows[p["row_id"]]
        g, s = to_prop(r.gold), to_prop(r.pred)
        if g is not None and s is not None:
            stmt[r.row_id] = (r, f2.normalize(g), f2.normalize(s))
    return res_file, res, canon, stmt


def ok(v) -> bool:
    return v.ok and not v.uses_sorry


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    res_file, res, canon, stmt = load()
    todo = [(p["row_id"], g) for p in res["pairs"] if p["verdict"] in ("accept", "reject") and not p.get("split_checked")
            for g in ("split_r", "split_s") if g not in (p.get("proved") or []) and p["row_id"] in stmt]
    print(WHICH, "open regrouping goals", len(todo), flush=True)
    done: dict[tuple, str] = {}

    tac = g1.prove_items([((rid, g), (*stmt[rid], SPLIT_TAC2)) for rid, g in todo], "e2t")
    for k, v in tac.items():
        if ok(v):
            done[k] = "tactic2"
    todo = [k for k in todo if k not in done]
    print("after tactic tier 2: open", len(todo), flush=True)

    props = {}
    for rid, g in todo:
        p = g1.propose(MODEL, stmt[rid][0], canon[rid]["goals"], [g])
        if g in p:
            props[(rid, g)] = p[g]
    shot = g1.prove_items([((rid, g), (*stmt[rid], p)) for (rid, g), p in props.items()], "e2l")
    fixes = {}
    for k, v in shot.items():
        if ok(v):
            done[k] = "llm"
        else:
            rid, g = k
            fixes[k] = repair(MODEL, stmt[rid][0], g, canon[rid]["goals"][g], props[k], v.errors)
    rep = g1.prove_items([((rid, g), (*stmt[rid], p)) for (rid, g), p in fixes.items() if p], "e2r")
    for k, v in rep.items():
        if ok(v):
            done[k] = "llm_repair"
    # Other tiers may have written PROOFS since it was read; merge into the current file.
    proofs = json.loads(PROOFS.read_text(encoding="utf-8")) if PROOFS.exists() else {}
    for k, src in done.items():
        proofs[f"{KEY}:{k[0]}:{k[1]}"] = {"source": src, "proof": SPLIT_TAC2 if src == "tactic2" else
                                             (props[k] if src == "llm" else fixes[k])}
    tmp = PROOFS.with_suffix(f".{os.getpid()}.tmp")
    tmp.write_text(json.dumps(proofs, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(tmp, PROOFS)

    for p in res["pairs"]:
        for g in ("split_r", "split_s"):
            if (p["row_id"], g) in done:
                p["proved"] = sorted(set(p["proved"]) | {g})
                p.setdefault("split_source", {})[g] = done[(p["row_id"], g)]
        p["split_checked"] = {"split_r", "split_s"} <= set(p["proved"])
    if "raw" in res:
        for p in res["pairs"]:
            res["raw"]["candidates"][p["row_id"]] = {k: v for k, v in p.items() if k != "row_id"}
        res_file.write_text(json.dumps(res["raw"], indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    else:
        res_file.write_text(json.dumps(res, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    dec = [p for p in res["pairs"] if p["verdict"] in ("accept", "reject")]
    print("sources", Counter(done.values()))
    print("decided", len(dec), "with both regrouping certificates", sum(p["split_checked"] for p in dec),
          "still missing", [(p["row_id"], p["verdict"]) for p in dec if not p["split_checked"]])


if __name__ == "__main__":
    main()
