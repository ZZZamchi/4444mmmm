#!/usr/bin/env python3
"""H2: one blind human audit that serves the selection experiment and the second annotator.

Items (shuffled together, the sheet shows no set, verdict or selector):

  G  the E3 items from G1 (ProofNetVerif): rejects on labelled-equivalent pairs, accepts on
     labelled-inequivalent pairs, and the 20 L1 unknowns. Our first-annotator answers are in
     `e3_first_annotator.json`; the second annotator's answers give Cohen's kappa against them.
  S  open candidates from D2 rewarded by a selector (closed equivalence, Opus judge with
     reference, our accept): PER_SEL per selector, one per problem, problems drawn uniformly among
     those where the selector rewards an open draw and the candidate in proportion to its draws,
     which is how a best-of-n pick lands on the open class.
  J  strict rejects (both regrouping certificates, total alignment, closed equivalence not
     refuted) that closed equivalence or the Opus judge rewards: PER_REJ, drawn the same way. They
     carry the Goodhart claim of the selection section; the question is how many are unfaithful.
  K  controls from D2: certified equivalent (local accept with both certificates), rejects that
     are not strict (partial alignment or a missing certificate), refuted closed equivalence.
  F  the full ProofNetVerif set (G5, Opus): certified rejects of labelled-equivalent pairs and
     local accepts of labelled-inequivalent pairs, with controls from the opposite cells. Pairs
     already in G are not repeated; their G item carries `f_cell`.

Classes follow the strict ground truth of `d2_analyze.py` (D2_GT=strict).

Every item asks one question: is the candidate a faithful formalization of the informal
statement (the reference is a faithful one)? Answer `yes` / `no` / `unsure`; for `no`, a kind.

Items that state the same proposition (`SAME_AS`) share one sheet row (`sheet_item`); the answer is
copied to every item of the group, and the scores also report how many distinct rows a cell has.

Usage: h2_audit.py export                 -> data/real/h2_sheet.md, h2_sheet.csv, h2_items.json
       h2_audit.py sheet                  rewrite the sheet from the existing h2_items.json
       h2_audit.py score a.csv [b.csv]    -> data/real/h2_scores.json
"""

from __future__ import annotations

import csv
import json
import math
import os
import random
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
os.environ["D2_GT"] = "strict"

from a1_local import local
from d2_analyze import classify
from realdata import proofnetverif
from runner import ROOT

D = ROOT / "data" / "real"
SHEET_MD, SHEET_CSV, ITEMS, SCORES = (D / n for n in ("h2_sheet.md", "h2_sheet.csv", "h2_items.json", "h2_scores.json"))
PER_SEL = 30
PER_REJ = 40
CONTROLS = {"equivalent": 10, "reject_nonstrict": 5, "different_closed": 3}
SELECTORS = {
    "closed": lambda p, j: p["closed"] == "proved",
    "judge_opus_ref": lambda p, j: j.get("claude-opus-5.5:ref") == "faithful",
    "ours": lambda p, j: p["verdict"] == "accept",
}
# Items that state the same Lean proposition up to names, notation, bracket kind or hypothesis order,
# checked by hand (same NL, candidates compared after renaming bound variables). The sheet shows one item per group; the others inherit the
# answer. Pairs whose surface difference can change the meaning (`k` vs `↑k`, `Finite` vs
# `Fintype`, `Type _` vs `Type`, `→` vs `↔`) are kept apart.
SAME_AS = [
    ["pnv-test-340", "pnv-test-142", "pnv-test-91", "pnv-test-254"],
    ["pnv-test-404", "pnv-test-507", "pnv-test-1112", "pnv-test-1040", "pnv-test-672", "pnv-test-569",
     "pnv-test-1201", "pnv-test-311"],
    ["d1-357-4494", "pnv-test-809"],
    ["pnv-test-1026", "pnv-test-1054", "pnv-test-338"],
    ["pnv-test-1441", "d1-276-3506", "pnv-test-532", "pnv-test-406"],
    ["pnv-test-992", "pnv-test-1114", "pnv-test-528", "pnv-test-253"],
    ["pnv-test-576", "pnv-test-1370"],
    ["d1-330-4215", "d1-330-4217"],
    ["d1-145-1861", "d1-145-1859"],
    ["pnv-test-1355", "pnv-test-796"],
]
KINDS = ("hyp_missing", "hyp_extra", "conclusion_diff", "type_drift", "vacuous", "false_statement", "other")
SEED = 2026


def g_items() -> list[dict]:
    rows = {r.row_id: r for r in proofnetverif("test")}
    out = []
    for it in json.loads((D / "e3_items.json").read_text(encoding="utf-8")):
        r = rows[it["row_id"]]
        out.append({"key": it["row_id"], "part": "G", "set": it["set"], "nl": r.nl, "ref": r.gold, "cand": r.pred})
    return out


def d2_items(rng: random.Random) -> list[dict]:
    import g4_pnv as g4
    d1 = json.loads((D / "d1_candidates.json").read_text(encoding="utf-8"))
    pv = json.loads((D / "d2_prove.json").read_text(encoding="utf-8"))["candidates"]
    jv = json.loads((D / "d2_judge.json").read_text(encoding="utf-8"))["candidates"]
    rows = {r.row_id: r for r in g4.load()[0]}
    cands = {c["cand_id"]: c for c in d1["candidates"]}
    draws = Counter(x["cand"] for x in d1["draws"] if x["cand"] in pv)
    by_prob = defaultdict(list)
    for c in draws:
        by_prob[cands[c]["problem"]].append(c)

    def item(c: str, part: str, **kw) -> dict:
        r = rows[cands[c]["problem"]]
        return {"key": c, "part": part, "nl": r.nl, "ref": r.gold, "cand": cands[c]["src"], **kw}

    def pick(pool: dict, n: int) -> list[str]:
        probs = [p for p, cs in pool.items() if cs]
        return [rng.choices(pool[p], weights=[draws[x] for x in pool[p]])[0]
                for p in rng.sample(probs, min(n, len(probs)))]

    def rewarded(c: str) -> list[str]:
        return [s for s, rew in SELECTORS.items() if rew(pv[c], jv.get(c, {}))]

    chosen: dict[str, dict] = {}
    for sel, rew in SELECTORS.items():
        pool = {p: [c for c in cs if classify(pv[c]) == "open" and rew(pv[c], jv.get(c, {}))]
                for p, cs in sorted(by_prob.items())}
        for c in pick(pool, PER_SEL):
            chosen.setdefault(c, item(c, "S", selectors=[]))["selectors"].append(sel)
    pool = {p: [c for c in cs if classify(pv[c]) == "wrong" and pv[c]["closed"] != "refuted"
                and set(rewarded(c)) & {"closed", "judge_opus_ref"} and c not in chosen]
            for p, cs in sorted(by_prob.items())}
    for c in pick(pool, PER_REJ):
        chosen[c] = item(c, "J")
    for c, it in chosen.items():
        it["rewarded_by"] = rewarded(c)
    klass = {
        "equivalent": [c for c in draws if classify(pv[c]) == "right"],
        "reject_nonstrict": [c for c in draws if pv[c]["verdict"] == "reject" and classify(pv[c]) == "open"],
        "different_closed": [c for c in draws if pv[c]["closed"] == "refuted"],
    }
    ctrl = []
    for k, n in CONTROLS.items():
        for c in rng.sample(sorted(set(klass[k]) - set(chosen)), n):
            ctrl.append(item(c, "K", control=k))
    return list(chosen.values()) + ctrl


G5_RESULTS = D / "g5" / "g1_results_claude-opus-5.5.json"
F_CONTROLS = {"faithful_local_accept": 10, "unfaithful_reject": 10}


def f_items(rng: random.Random, skip: dict[str, dict]) -> list[dict]:
    """Full-set (G5, Opus) items: certified rejects of labelled-equivalent pairs, local accepts of
    labelled-inequivalent pairs, and controls drawn from the opposite cells."""
    from k6_stats import accepted, is_local
    rows = {r.row_id: r for r in proofnetverif("test")}
    k7 = json.loads((D / "k7_pointwise.json").read_text(encoding="utf-8"))["g5"]
    k7 = k7.get("pairs", k7)
    pairs = json.loads(G5_RESULTS.read_text(encoding="utf-8"))["pairs"]
    cert = lambda p: {"split_r", "split_s"} <= set(p.get("proved") or [])
    cells = {
        "faithful_reject": [p for p in pairs if p["label"] and p["verdict"] == "reject" and cert(p)],
        "unfaithful_local_accept": [p for p in pairs if not p["label"] and accepted(p) and is_local(p)],
    }
    ctrl = {
        "faithful_local_accept": [p for p in pairs if p["label"] and accepted(p) and is_local(p)
                                  and k7.get(p["row_id"], {}).get("class") == "informative"],
        "unfaithful_reject": [p for p in pairs if not p["label"] and p["verdict"] == "reject" and cert(p)],
    }
    out = []

    def item(p, **kw):
        r = rows[p["row_id"]]
        return {"key": p["row_id"], "part": "F", "nl": r.nl, "ref": r.gold, "cand": r.pred, **kw}

    for cell, ps in cells.items():
        out += [item(p, cell=cell) for p in ps if p["row_id"] not in skip]
        for it in skip.values():
            if any(p["row_id"] == it["key"] for p in ps):
                it["f_cell"] = cell
    for cell, n in F_CONTROLS.items():
        pool = sorted((p for p in ctrl[cell] if p["row_id"] not in skip), key=lambda p: p["row_id"])
        out += [item(p, cell=cell, control=True) for p in rng.sample(pool, n)]
    return out


def export() -> None:
    rng = random.Random(SEED)
    g = g_items()
    items = g + d2_items(rng)
    items += f_items(rng, {it["key"]: it for it in g})
    rng.shuffle(items)
    for i, it in enumerate(items, 1):
        it["item"] = i
    write_sheet(items)


def write_sheet(items: list[dict]) -> None:
    """One sheet row per group of `SAME_AS`, numbered 1.. in item order; every item records its row."""
    group = {k: g[0] for g in SAME_AS for k in g}
    row_of: dict[str, int] = {}
    shown = []
    for it in sorted(items, key=lambda x: x["item"]):
        g = group.get(it["key"], it["key"])
        if g not in row_of:
            row_of[g] = len(shown) + 1
            shown.append(it)
        it["sheet_item"] = row_of[g]
    ITEMS.write_text(json.dumps(items, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    head = ["# Blind faithfulness annotation (H2)", "",
            "For every item read the informal statement (NL), a reference formalization R and the candidate",
            "formalization P. Question: is P a faithful formalization of NL? Judge P against NL. R is meant",
            "as a help and is usually faithful, but not always; if R is wrong, P can still be faithful.",
            "Faithful means P says the same thing as NL: same objects and types, same hypotheses (none",
            "missing, none added), same conclusion. Differences in naming, binder order, implicit vs",
            "explicit arguments or an equivalent rephrasing are fine. Mind Lean's type inference: an",
            "unannotated variable or numeral (e.g. `fun k => ...`, `Icc 0 1`) gets a type from context,",
            "which may not be the intended one. Do not use Lean, an LLM or any tool; you may look up",
            "Mathlib definitions. Fill the columns `faithful` (yes / no / unsure) and, for `no`, `kind`",
            f"(one of: {', '.join(KINDS)}) in h2_sheet.csv; `note` is optional.", ""]
    body = []
    for it in shown:
        body += [f"## item {it['sheet_item']:03d}", "", f"**NL.** {it['nl']}", "", "**R (reference)**", "", "```lean",
                 it["ref"].strip(), "```", "", "**P (candidate)**", "", "```lean", it["cand"].strip(), "```", ""]
    SHEET_MD.write_text("\n".join(head + body), encoding="utf-8")
    with SHEET_CSV.open("w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f)
        w.writerow(["item", "NL", "R (reference)", "P (candidate)", "faithful", "kind", "note"])
        for it in shown:
            w.writerow([it["sheet_item"], it["nl"], it["ref"].strip(), it["cand"].strip(), "", "", ""])
    print("items", len(items), "sheet rows", len(shown), Counter(it["part"] for it in items),
          "S per selector", Counter(s for it in items for s in it.get("selectors", [])), "->", SHEET_CSV.name)


def read(path: str) -> dict[int, dict]:
    with open(path, encoding="utf-8-sig", newline="") as f:
        out = {}
        for r in csv.DictReader(f):
            v = (r.get("faithful") or "").strip().lower()
            if v in ("yes", "no", "unsure"):
                out[int(r["item"])] = {"faithful": v, "kind": (r.get("kind") or "").strip()}
        return out


def kappa(a: list, b: list) -> float | None:
    n = len(a)
    if not n:
        return None
    po = sum(x == y for x, y in zip(a, b)) / n
    pe = sum((a.count(c) / n) * (b.count(c) / n) for c in set(a) | set(b))
    return (po - pe) / (1 - pe) if pe < 1 else 1.0


def wilson(k: int, n: int, z: float = 1.96) -> list:
    if not n:
        return [None, None]
    p, d = k / n, 1 + z * z / n
    c, h = (p + z * z / (2 * n)) / d, z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return [round(c - h, 3), round(c + h, 3)]


# the component an annotator's kind of difference names, for comparison with the located one
KIND_COMPONENT = {"hyp_missing": "H", "hyp_extra": "H", "vacuous": "H", "conclusion_diff": "C"}
REJECT_GROUPS = {
    "align": ("total", "early"),
    "loc": ("H", "C", "HC", "closed"),
    "dir": ("ref_false", "cand_false", "one_false", "vacuity", "direction_only", "open"),
}
ACCEPT_GROUPS = {"fa": ("constant", "trivial", "neither")}


def direction(v: dict | None, closed: str | None) -> str:
    """What the direction goals of `k3_direction.py` certify about a reject (Appendix A): a side is
    false once the pointwise claims (`npimp`) or the closed statements (a refuted closed
    equivalence) differ, and a proved direction says which."""
    if not v:
        return "open"
    if v["class"] == "vacuity_only":
        return "vacuity"
    false = "npimp" in v.get("proved", []) or closed == "refuted"
    if v["class"] in ("weaker", "stronger"):
        return ("ref_false" if v["class"] == "weaker" else "cand_false") if false else "direction_only"
    return "one_false" if false else "open"


def mechanical(items: dict, ann: list, verdict, distinct, one_per_row) -> dict:
    """The audit against the kernel facts behind each audited reject and false accept of the full
    set: alignment, located component and direction certificate of the 43 component-goal rejects of
    labelled-equivalent pairs, constancy and triviality of the 14 false accepts, and whether the kind
    of difference an annotator names matches the located component of a rejected candidate. Fixed
    before the answers return, so that confirmed locations and alignment artefacts are told apart
    by a rule chosen in advance."""
    from paper_check import located
    g5 = {p["row_id"]: p for p in json.loads(G5_RESULTS.read_text(encoding="utf-8"))["pairs"]}
    pv = json.loads((D / "d2_prove.json").read_text(encoding="utf-8"))["candidates"]
    k3 = json.loads((D / "k3_direction.json").read_text(encoding="utf-8"))["g5"]["pairs"]
    k7 = json.loads((D / "k7_pointwise.json").read_text(encoding="utf-8"))["g5"]
    k7 = k7.get("pairs", k7)
    k9 = json.loads((D / "k9_trivial.json").read_text(encoding="utf-8"))["g5"]["pairs"]
    in_cell = lambda it, cell: it.get("cell") == cell or it.get("f_cell") == cell

    def tab(groups: dict, cat_of) -> dict:
        out = {}
        for g, cats in groups.items():
            by = {c: [k for k, it in items.items() if cat_of(g, it) == c] for c in cats}
            out[g] = {c: {"items": len(ks), "statements": distinct(ks),
                          **Counter(str(verdict(k)) for k in ks)} for c, ks in by.items()}
        return out

    def reject_cat(g: str, it: dict) -> str | None:
        if not in_cell(it, "faithful_reject"):
            return None
        p = g5[it["key"]]
        return {"align": lambda: "total" if local(p.get("canon_info")) else "early",
                "loc": lambda: located(p) or "closed",
                "dir": lambda: direction(k3.get(it["key"]), p.get("closed"))}[g]()

    def accept_cat(g: str, it: dict) -> str | None:
        if not in_cell(it, "unfaithful_local_accept"):
            return None
        if k7.get(it["key"], {}).get("class") == "collapsed":
            return "constant"
        return "trivial" if k9.get(it["key"], {}).get("logic", {}).get("flag") else "neither"

    rejected = {k: located(p) for k, it in items.items()
                if (p := g5.get(it["key"]) or pv.get(it["key"])) and p["verdict"] == "reject" and located(p)
                and {"split_r", "split_s"} <= set(p.get("proved") or [])}
    agree = []
    for a in ann:
        pairs = [(KIND_COMPONENT[a[k]["kind"]], rejected[k]) for k in one_per_row([k for k in rejected if k in a])
                 if a[k]["faithful"] == "no" and a[k]["kind"] in KIND_COMPONENT]
        agree.append({"n": len(pairs), "agree": sum(c in loc for c, loc in pairs)})
    return {"map_rejects": tab(REJECT_GROUPS, reject_cat), "map_accepts": tab(ACCEPT_GROUPS, accept_cat),
            "location_vs_kind": agree, "located_reject_rows": distinct(list(rejected))}


def score(paths: list[str]) -> None:
    items = {it["item"]: it for it in json.loads(ITEMS.read_text(encoding="utf-8"))}
    row = {k: it.get("sheet_item", k) for k, it in items.items()}
    ann = [{k: a[row[k]] for k in items if row[k] in a} for a in (read(p) for p in paths)]
    first = json.loads((D / "e3_first_annotator.json").read_text(encoding="utf-8"))
    res: dict = {"annotators": len(ann), "answered": [len({row[k] for k in a}) for a in ann],
                 "items_covered": [len(a) for a in ann]}
    distinct = lambda ks: len({row[k] for k in ks})
    # rates count each distinct statement once, so that copies do not narrow the intervals
    one_per_row = lambda ks: list({row[k]: k for k in ks}.values())

    def g_first(it: dict) -> str:
        f = first[it["key"]]
        eq = f["equivalent"] if "equivalent" in f else not f["label_correct"]
        return "yes" if eq else "no"

    for i, a in enumerate(ann):
        ids = sorted({row[k]: k for k, it in items.items()
                      if it["part"] == "G" and k in a and a[k]["faithful"] != "unsure"}.values())
        res[f"g_kappa_vs_first_{i}"] = {"n": len(ids), "kappa": kappa([g_first(items[k]) for k in ids], [a[k]["faithful"] for k in ids])}
        # the first annotation asks whether R and P agree; where R itself is wrong the answers flip
        ids = [k for k in ids if first[items[k]["key"]].get("kind") != "label_error"]
        res[f"g_kappa_vs_first_{i}_ref_ok"] = {"n": len(ids), "kappa": kappa([g_first(items[k]) for k in ids], [a[k]["faithful"] for k in ids])}
    if len(ann) == 2:
        ids = sorted({row[k]: k for k in items if k in ann[0] and k in ann[1]}.values())
        res["kappa_between"] = {"n": len(ids), "kappa": kappa([ann[0][k]["faithful"] for k in ids], [ann[1][k]["faithful"] for k in ids]),
                                "agree": sum(ann[0][k]["faithful"] == ann[1][k]["faithful"] for k in ids)}

    def verdict(k: int) -> str | None:
        vs = [a[k]["faithful"] for a in ann if k in a]
        if not vs:
            return None
        return vs[0] if all(v == vs[0] for v in vs) else "disagree"

    for sel in SELECTORS:
        ks = [k for k, it in items.items() if sel in it.get("selectors", [])]
        c = Counter(verdict(k) for k in one_per_row(ks))
        n = c["yes"] + c["no"]
        res[f"open_picks_{sel}"] = {"sampled": len(ks), "distinct": distinct(ks), **{str(x): y for x, y in c.items()},
                                    "unfaithful_rate": round(c["no"] / n, 4) if n else None, "ci95": wilson(c["no"], n)}
    for sel in ("all", "closed", "judge_opus_ref"):
        ks = [k for k, it in items.items() if it["part"] == "J" and (sel == "all" or sel in it["rewarded_by"])]
        c = Counter(verdict(k) for k in one_per_row(ks))
        n = c["yes"] + c["no"]
        res[f"strict_rejects_rewarded_{sel}"] = {"sampled": len(ks), "distinct": distinct(ks), **{str(x): y for x, y in c.items()},
                                                 "unfaithful_rate": round(c["no"] / n, 4) if n else None,
                                                 "ci95": wilson(c["no"], n)}
    for k in CONTROLS:
        ks = [i for i, it in items.items() if it.get("control") == k]
        res[f"control_{k}"] = {str(x): y for x, y in Counter(verdict(i) for i in one_per_row(ks)).items()}
    for cell in ("faithful_reject", "unfaithful_local_accept", "faithful_local_accept", "unfaithful_reject"):
        ks = [k for k, it in items.items() if it.get("cell") == cell or it.get("f_cell") == cell]
        c = Counter(verdict(k) for k in one_per_row(ks))
        n = c["yes"] + c["no"]
        res[f"full_{cell}"] = {"sampled": len(ks), "distinct": distinct(ks), **{str(x): y for x, y in c.items()},
                               "faithful_rate": round(c["yes"] / n, 4) if n else None, "ci95": wilson(c["yes"], n)}
    res["kinds"] = Counter(a[k]["kind"] for a in ann for k in {row[i]: i for i in a}.values() if a[k]["faithful"] == "no")
    res.update(mechanical(items, ann, verdict, distinct, one_per_row))
    SCORES.write_text(json.dumps(res, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    if len(sys.argv) > 1 and sys.argv[1] == "score":
        score(sys.argv[2:])
    elif len(sys.argv) > 1 and sys.argv[1] == "sheet":
        write_sheet(json.loads(ITEMS.read_text(encoding="utf-8")))
    else:
        export()
