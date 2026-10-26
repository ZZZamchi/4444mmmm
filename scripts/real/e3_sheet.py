#!/usr/bin/env python3
"""E3: blind annotation sheet for a second annotator, and Cohen's kappa against the first.

Three item sets from G1 (ProofNetVerif test, strong prover):

  A  rejects on labelled-equivalent pairs      question: are G and P equivalent formalizations
                                               of NL? If not, which is wrong / what differs?
  B  accepts on labelled-inequivalent pairs    same question.
  C  the 20 unknown pairs sampled in L1        question: is the label "not equivalent" right?

The sheet contains only NL, G, P and the questions; our own answers are kept in
`data/real/e3_first_annotator.json` and are not shown. Items are shuffled with a fixed seed.

Usage: e3_sheet.py export            -> data/real/e3_blind_sheet.md, e3_items.json
       e3_sheet.py kappa second.json -> kappa per set and overall
         second.json: {item_id: {"equivalent": true|false, "label_correct": true|false, ...}}
"""

from __future__ import annotations

import json
import random
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from realdata import proofnetverif
from runner import ROOT

D = ROOT / "data" / "real"
RES = D / "g1_results.json"
SHEET = D / "e3_blind_sheet.md"
ITEMS = D / "e3_items.json"
FIRST = D / "e3_first_annotator.json"

# First annotator (from notes/feasibility-2026-10.md, G1 audit and L1).
A_LABEL_ERROR = {695, 738, 1026, 311}            # one side provably false: reject correct, label wrong
A_HYP_DIFF = {253, 992, 1114, 365, 576, 693, 913}  # certified hypothesis difference tolerated by label
A_CANON = {1135, 358}                              # canonicalization artefact: reject wrong
B_RESIDUAL = {1098, 836, 1355, 796, 532, 1441, 406, 892, 1042, 866, 453, 754, 72, 769}
C_DISPUTED = {518}
C_LABEL_WRONG = set()


def export() -> None:
    rows = {r.row_id: r for r in proofnetverif("test")}
    res = json.loads(RES.read_text(encoding="utf-8"))
    items, first = [], {}
    for p in res["pairs"]:
        n = int(p["row_id"].rsplit("-", 1)[1])
        if p["label"] and p["verdict"] == "reject":
            items.append(("A", p["row_id"]))
            first[p["row_id"]] = {"equivalent": False if n in A_LABEL_ERROR | A_HYP_DIFF else True,
                                  "kind": "label_error" if n in A_LABEL_ERROR else
                                          "hyp_diff" if n in A_HYP_DIFF else "canon_artifact"}
        elif not p["label"] and p["verdict"] == "accept":
            items.append(("B", p["row_id"]))
            first[p["row_id"]] = {"equivalent": False, "kind": "residual_collapse"}
    sample = re.findall(r"^===== (pnv-test-\d+)", (D / "l1_sample.txt").read_bytes().decode("utf-16" if (D / "l1_sample.txt").read_bytes()[:2] in (b"\xff\xfe", b"\xfe\xff") else "utf-8"), flags=re.M)
    for rid in sample:
        n = int(rid.rsplit("-", 1)[1])
        items.append(("C", rid))
        first[rid] = {"label_correct": n not in C_LABEL_WRONG, "disputed": n in C_DISPUTED}
    random.Random(2026).shuffle(items)
    lines = ["# Blind annotation sheet (E3)", "",
             "For every item: read NL, G (reference) and P (candidate). Answer the questions for the item's set.",
             "Do not consult any tool output. Record answers as JSON `{item_id: {...}}`.", "",
             "Set A/B question: `equivalent` (true/false): are G and P equivalent formalizations of NL?",
             "If false, `kind`: `label_error` (one side is wrong w.r.t. NL), `hyp_diff` (hypotheses differ, both",
             "defensible), `conclusion_diff`, `type_drift` (same statement on a different type), `other`.",
             "Set C question: `label_correct` (true/false): the dataset label says G and P are NOT equivalent; is that right?", ""]
    out_items = []
    for i, (st, rid) in enumerate(items, 1):
        r = rows[rid]
        lines += [f"## item {i:02d}  [{rid}]  set {st}", "", f"**NL.** {r.nl}", "", "```lean", r.gold.strip(), "```", "",
                  "```lean", r.pred.strip(), "```", ""]
        out_items.append({"item": i, "row_id": rid, "set": st})
    SHEET.write_text("\n".join(lines), encoding="utf-8")
    ITEMS.write_text(json.dumps(out_items, indent=1) + "\n", encoding="utf-8")
    FIRST.write_text(json.dumps(first, indent=1) + "\n", encoding="utf-8")
    from collections import Counter
    print("items", Counter(st for st, _ in items), "->", SHEET.name)


def kappa(a: list, b: list) -> float:
    n = len(a)
    po = sum(x == y for x, y in zip(a, b)) / n
    cats = set(a) | set(b)
    pe = sum((a.count(c) / n) * (b.count(c) / n) for c in cats)
    return (po - pe) / (1 - pe) if pe < 1 else 1.0


def compare(second_path: str) -> None:
    first = json.loads(FIRST.read_text(encoding="utf-8"))
    second = json.loads(Path(second_path).read_text(encoding="utf-8"))
    items = json.loads(ITEMS.read_text(encoding="utf-8"))
    for st, key in (("A", "equivalent"), ("B", "equivalent"), ("C", "label_correct")):
        ids = [it["row_id"] for it in items if it["set"] == st and it["row_id"] in second]
        a = [bool(first[i][key]) for i in ids]
        b = [bool(second[i][key]) for i in ids]
        if ids:
            print(f"set {st}: n={len(ids)} agreement={sum(x == y for x, y in zip(a, b))}/{len(ids)} kappa={kappa(a, b):.3f}")
    ids = [it["row_id"] for it in items if it["row_id"] in second]
    a = [bool(first[i].get("equivalent", first[i].get("label_correct"))) for i in ids]
    b = [bool(second[i].get("equivalent", second[i].get("label_correct"))) for i in ids]
    print(f"overall: n={len(ids)} kappa={kappa(a, b):.3f}")


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    if len(sys.argv) > 1 and sys.argv[1] == "kappa":
        compare(sys.argv[2])
    else:
        export()
