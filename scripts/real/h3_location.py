#!/usr/bin/env python3
"""H3: a blind audit of where the mechanically located rejects say the difference is.

The faithfulness audit (H2) asks whether a candidate is faithful; it cannot tell whether the
component a reject names is where reference and candidate differ. This sheet asks that, for a
stratified sample of the located rejects of labelled-inequivalent pairs on the full set (G5,
Opus): 30 on a total alignment and 30 on an alignment that is not total, at most one per problem
and none already in H2. Each item shows the namespaces its benchmark opens, and nothing about our
verdict or its location.

Answers: `hypotheses`, `conclusion`, `both`, `types` (the variables differ in type), `same` (no
difference in what they say), `unsure`. A located reject names H (hypotheses), C (conclusion) or
both; `types`, `same` and `unsure` are not comparable with a location.

Usage: h3_location.py export              -> data/real/h3_sheet.md, h3_sheet.csv, h3_items.json
       h3_location.py score a.csv [b.csv]  -> data/real/h3_scores.json
"""

from __future__ import annotations

import csv
import json
import random
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from a1_local import local
from h2_audit import kappa, wilson
from paper_check import D, load, located, verdict
from realdata import proofnetverif

SHEET_MD, SHEET_CSV, ITEMS, SCORES = (D / n for n in ("h3_sheet.md", "h3_sheet.csv", "h3_items.json", "h3_scores.json"))
PER_STRATUM = 30
SEED = 2027
ANSWERS = ("hypotheses", "conclusion", "both", "types", "same", "unsure")
COMPONENT = {"H": "hypotheses", "C": "conclusion", "HC": "both"}

INSTRUCTIONS = """# Where do the two formal statements differ? (H3)

Each item shows an informal statement (for context), a reference formalization R, a candidate P,
and the namespaces that the Lean file opens before both (so `log` is `Real.log` when `Real` is
open). R and P are known to differ. Question: where do they differ in what they say?

- `hypotheses`: the assumptions differ (the binders before the colon, and leading implications
  `A → B → ...` before the final claim): one is added, dropped, weakened or strengthened.
- `conclusion`: what is finally asserted differs, under the same assumptions.
- `both`: both differ.
- `types`: the variables themselves have different types or structures (e.g. `ℕ` against `ℤ`,
  `Ring` against `CommRing`), so the comparison above does not apply.
- `same`: you see no difference in what they say.
- `unsure`.

Judge R against P, not against the informal statement. Do not use Lean, a language model or any
other tool; you may look up Mathlib definitions. Fill the column `location` in h3_sheet.csv;
`note` is optional.
"""


def opens(header: str) -> str:
    return "\n".join(l for l in header.splitlines() if l.strip().startswith(("open", "namespace", "variable")))


def export() -> None:
    rows = {r.row_id: r for r in proofnetverif("test")}
    seen = {it["key"] for it in json.loads((D / "h2_items.json").read_text(encoding="utf-8"))}
    pool = {"total": [], "not_total": []}
    for p in load(D / "g5" / "g1_results_claude-opus-5.5.json"):
        if p["label"] or verdict(p) != "reject" or not located(p) or p["row_id"] in seen:
            continue
        pool["total" if local(p.get("canon_info")) else "not_total"].append(p)
    rng = random.Random(SEED)
    items = []
    for stratum, ps in pool.items():
        by_problem: dict[str, list] = {}
        for p in sorted(ps, key=lambda p: p["row_id"]):
            by_problem.setdefault(rows[p["row_id"]].nl, []).append(p)
        for nl in rng.sample(sorted(by_problem), min(PER_STRATUM, len(by_problem))):
            p = rng.choice(by_problem[nl])
            r = rows[p["row_id"]]
            items.append({"key": p["row_id"], "stratum": stratum, "located": located(p), "closed": p.get("closed"),
                          "nl": r.nl, "ref": r.gold, "cand": r.pred, "opens": opens(r.header)})
    rng.shuffle(items)
    for i, it in enumerate(items, 1):
        it["item"] = i
    ITEMS.write_text(json.dumps(items, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    body = [INSTRUCTIONS]
    for it in items:
        body += [f"## item {it['item']:03d}", "", f"**NL.** {it['nl']}", "", "**Opened namespaces**", "", "```lean",
                 it["opens"] or "(none)", "```", "", "**R (reference)**", "", "```lean", it["ref"].strip(), "```", "",
                 "**P (candidate)**", "", "```lean", it["cand"].strip(), "```", ""]
    SHEET_MD.write_text("\n".join(body), encoding="utf-8")
    with SHEET_CSV.open("w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f)
        w.writerow(["item", "NL", "opens", "R (reference)", "P (candidate)", "location", "note"])
        for it in items:
            w.writerow([it["item"], it["nl"], it["opens"], it["ref"].strip(), it["cand"].strip(), "", ""])
    print(len(items), "items", Counter(it["stratum"] for it in items), Counter(it["located"] for it in items),
          "pool", {k: len(v) for k, v in pool.items()})


def read(path: str) -> dict[int, str]:
    with open(path, encoding="utf-8-sig", newline="") as f:
        out = {}
        for r in csv.DictReader(f):
            v = (r.get("location") or "").strip().lower()
            if v in ANSWERS:
                out[int(r["item"])] = v
        return out


def score(paths: list[str]) -> None:
    items = {it["item"]: it for it in json.loads(ITEMS.read_text(encoding="utf-8"))}
    ann = [read(p) for p in paths]
    res: dict = {"annotators": len(ann), "answered": [len(a) for a in ann]}

    def tally(ks: list[int], answer) -> dict:
        exact = overlap = comparable = 0
        other = Counter()
        for k in ks:
            a = answer(k)
            if a in COMPONENT.values():
                comparable += 1
                mech = COMPONENT[items[k]["located"]]
                exact += a == mech
                overlap += a == mech or "both" in (a, mech)
            else:
                other[a] += 1
        return {"items": len(ks), "comparable": comparable, "exact": exact, "overlap": overlap,
                "exact_ci95": wilson(exact, comparable), **{f"n_{k}": v for k, v in other.items()}}

    for stratum in ("total", "not_total", "all"):
        ks = [k for k, it in items.items() if stratum == "all" or it["stratum"] == stratum]
        for i, a in enumerate(ann):
            res[f"{stratum}_{'AB'[i]}"] = tally([k for k in ks if k in a], lambda k, a=a: a[k])
        if len(ann) == 2:
            both = [k for k in ks if k in ann[0] and k in ann[1] and ann[0][k] == ann[1][k]]
            res[f"{stratum}_agreed"] = tally(both, lambda k: ann[0][k])
    if len(ann) == 2:
        ks = sorted(set(ann[0]) & set(ann[1]))
        res["kappa_between"] = {"n": len(ks), "kappa": kappa([ann[0][k] for k in ks], [ann[1][k] for k in ks]),
                                "agree": sum(ann[0][k] == ann[1][k] for k in ks)}
    SCORES.write_text(json.dumps(res, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    if len(sys.argv) > 1 and sys.argv[1] == "score":
        score(sys.argv[2:])
    else:
        export()
