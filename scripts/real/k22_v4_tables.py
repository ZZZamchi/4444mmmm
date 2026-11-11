#!/usr/bin/env python3
"""Numbers and LaTeX for the v4 appendix of the paper (notes/protocol-v4.md).

`compute` recomputes, for one split, the arms v2.1, U+A (`univ0m,align`), U+A+NF and v4 (U+A with L
and NF) next to closed equivalence, under the published labels and, on test, SemantEq's adjudicated
ones; the step from each arm to the next; the accepts that L adds; the labelled-equivalent pairs
that closed equivalence accepts and v4 does not, by cause; on test also the renaming and shuffling
robustness of the alignment and the comparison with SemantEq on the shared set. Results are merged
into data/real/k22_v4_tables.json. `tex` renders paper/v4_results.tex: macros only, loaded in the
preamble, with `tab:v4rules` wrapped in \\VfRulesTable; `paper_check.py` fails if that file is stale.
Nothing here changes a verdict of the frozen protocol.

Usage: k22_v4_tables.py compute [--split valid]    (valid needs the v4 unlock, K22_VALID_UNLOCK)
       k22_v4_tables.py tex
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "data" / "real" / "k22_v4_tables.json"
TEX = ROOT / "paper" / "v4_results.tex"
ARMS = ("v2.1", "U+A", "U+A+NF", "v4")
STEPS = (("UA", "v2.1", "U+A"), ("NF", "U+A", "U+A+NF"), ("L", "U+A+NF", "v4"))


def stats(v: dict[str, str], lab: dict[str, bool]) -> dict:
    from paper_check import wilson
    F = [r for r in lab if lab[r]]
    U = [r for r in lab if not lab[r]]
    acc, fa = sum(v[r] == "accept" for r in F), sum(v[r] == "accept" for r in U)
    pct = lambda a, n: round(100 * a / n, 2)
    ci = lambda a, n: [round(100 * x, 2) for x in wilson(a, n)]
    return {"accept": acc, "accept_pct": pct(acc, len(F)), "accept_ci": ci(acc, len(F)),
            "false_accept": fa, "false_accept_pct": pct(fa, len(U)), "false_accept_ci": ci(fa, len(U)),
            "precision_pct": pct(acc, acc + fa) if acc + fa else None}


def cause(k, base, cache, v4, r) -> str:
    c = cache.get(f"{k.V4_FLAGS}|{r}", {})
    if c.get("status") != "ok" or base[r]["verdict"] == "canon_fail":
        return "canon_fail"
    m = re.search(r"full=(\w+) prefix_r=(\d+)/(\d+) prefix_s=(\d+)/(\d+)", c.get("info") or "")
    full = bool(m) and m.group(1) == "true"
    if v4[r] == "residual":
        if m and m.group(3) == m.group(5) == "0":
            return "residual_closed"
        if m and m.group(2) == m.group(4) == "0":
            return "residual_first_binder"
        return "residual_partial"
    if v4[r] == "unknown":
        return "unknown_total" if full else "unknown_partial"
    return v4[r]


def robustness(k, base, cache, v21) -> dict:
    """Renaming every candidate binder, and reversing runs of adjacent same-type binders after renaming."""
    lab = {r: bool(p["label"]) for r, p in base.items()}
    comp = ("acc", "cond", "nhyp", "ncin", "ncomp")
    info = lambda f, r: cache.get(f"{f}|{r}", {}).get("info", "")
    goals = lambda f, r: cache.get(f"{f}|{r}", {}).get("goals", {})
    out = {}
    for name, plain in (("greedy", ""), ("align", "align")):
        named = plain
        anon = f"{plain},anon".lstrip(",")
        shuf = f"{anon},shuffle"
        renamed = [r for r in base if k.field(info(anon, r), "map") != k.field(info(named, r), "map")]
        runs = [r for r in base if goals(shuf, r).get("split_s") != goals(anon, r).get("split_s")]
        diff = [r for r in runs if any(goals(shuf, r).get(g) != goals(anon, r).get(g) for g in comp)]
        full = lambda f: dict(Counter("F" if lab[r] else "U" for r in base if "full=true" in info(f, r)))
        out[name] = {"renamed_map_changes": len(renamed), "shuffled_candidates": len(runs),
                     "shuffled_goal_changes": len(diff),
                     "shuffled_goal_changes_on_v21_equivalent_accepts": sum(lab[r] and v21[r] == "accept" for r in diff),
                     "full_before_shuffle": full(anon), "full_after_shuffle": full(shuf)}
    return out


def shared(base, v4) -> dict:
    import k18_combine as k18
    se = k18.semanteq()
    ids = sorted(set(se) & set(base))
    s_acc = {r: bool(se[r]["semanteq_accept"]) for r in ids}
    out = {"pairs": len(ids)}
    for lab_name, key in (("published", "published_equivalent"), ("adjudicated", "adjudicated_equivalent")):
        truth = {r: bool(se[r][key]) for r in ids}
        dec = {r: v4[r] if v4[r] in ("accept", "reject") else "undecided" for r in ids}
        sem = {r: "accept" if s_acc[r] else "undecided" for r in ids}
        out[lab_name] = {"v4": k18.score(dec, truth), "semanteq": k18.score(sem, truth)}
    out["semanteq_accepts_v4_accepts"] = sum(s_acc[r] and v4[r] == "accept" for r in ids)
    out["v4_only_accepts"] = sum(v4[r] == "accept" and not s_acc[r] for r in ids)
    return out


def compute() -> None:
    import k22_align as k
    base, post, stmt, cache = k.load()
    store = json.loads(k.PROVED.read_text(encoding="utf-8"))
    V = lambda flags, rules: k.verdicts(base, post, cache, store, flags, rules, "full")
    arms = {"v2.1": V("", ""), "U+A": V(k.V4_FLAGS, ""), "U+A+NF": V(k.V4_FLAGS, "NF"), "v4": V(k.V4_FLAGS, "L,NF")}
    closed = {r: "accept" if p.get("closed") == "proved" else "other" for r, p in base.items()}
    labels = {"published": {r: bool(p["label"]) for r, p in base.items()}}
    if k.SPLIT == "test":
        labels["adjudicated"] = k.semanteq_labels(base)
    res: dict = {"pairs": len(base), "labels": {}}
    for name, lab in labels.items():
        res["labels"][name] = {"equivalent": sum(lab.values()), "inequivalent": sum(not x for x in lab.values()),
                               "arms": {**{a: stats(arms[a], lab) for a in ARMS}, "closed": stats(closed, lab)}}
        added = [r for r in base if arms["v4"][r] == "accept" and arms["U+A+NF"][r] != "accept"]
        fa_refs = Counter(stmt[r][1] for r in added if not lab[r])
        new_fa = {r for r in base if not lab[r] and arms["v4"][r] == "accept" and arms["v2.1"][r] != "accept"}
        res["labels"][name]["L_added"] = {"equivalent": sum(lab[r] for r in added),
                                          "inequivalent": sum(not lab[r] for r in added),
                                          "inequivalent_references": len(fa_refs),
                                          "largest_reference_group": max(fa_refs.values(), default=0),
                                          "all_new_false_accepts": new_fa == {r for r in added if not lab[r]}}
        gap = [r for r in base if lab[r] and closed[r] == "accept" and arms["v4"][r] != "accept"]
        res["labels"][name]["closed_not_v4"] = {"pairs": len(gap),
                                                **dict(Counter(cause(k, base, cache, arms["v4"], r) for r in gap))}
    pub = res["labels"]["published"]["arms"]
    score = json.loads((k.OUT if k.SPLIT == "valid" else k.D / "k22_score_test.json").read_text(encoding="utf-8"))
    for a, s in (("v2.1", "v2.1"), ("v4", "v4"), ("U+A", f"{k.V4_FLAGS} only")):
        m = score["metrics"][s]
        if (m["accept"], m["false_accept"]) != (pub[a]["accept"], pub[a]["false_accept"]):
            raise SystemExit(f"{a}: does not match the frozen scorer ({m['accept']}, {m['false_accept']})")
    res["H5"] = score["H5_v4_vs_v21_accepts"]
    if k.SPLIT == "test":
        res["robustness"] = robustness(k, base, cache, arms["v2.1"])
        res["shared"] = shared(base, arms["v4"])
    allres = json.loads(OUT.read_text(encoding="utf-8")) if OUT.exists() else {}
    allres[k.SPLIT] = res
    k.save(OUT, allres)
    print(json.dumps(res, indent=1, ensure_ascii=False))


def macro(name: str, value) -> str:
    return f"\\newcommand{{\\Vf{name}}}{{{value}}}"


def render(t: dict) -> str:
    out = ["% generated by scripts/real/k22_v4_tables.py from data/real/k22_v4_tables.json; do not edit"]
    cols = [("Test", "Pub", t["test"]["labels"]["published"]), ("Test", "Adj", t["test"]["labels"]["adjudicated"]),
            ("Valid", "Pub", t["valid"]["labels"]["published"])]
    names = {"v2.1": "VtwoOne", "U+A": "UA", "U+A+NF": "UANF", "v4": "Vfour", "closed": "Closed"}
    for split, lab, d in cols:
        out += [macro(f"{split}{lab}F", d["equivalent"]), macro(f"{split}{lab}U", d["inequivalent"])]
        for arm, nm in names.items():
            m = d["arms"][arm]
            out += [macro(f"{split}{lab}{nm}Acc", m["accept"]), macro(f"{split}{lab}{nm}AccPct", f"{m['accept_pct']:.1f}"),
                    macro(f"{split}{lab}{nm}AccCI", "--".join(f"{x:.1f}" for x in m["accept_ci"])),
                    macro(f"{split}{lab}{nm}FA", m["false_accept"]),
                    macro(f"{split}{lab}{nm}FAPct", f"{m['false_accept_pct']:.1f}"),
                    macro(f"{split}{lab}{nm}Prec", f"{m['precision_pct']:.1f}")]
        for step, a, b in STEPS:
            da = d["arms"][b]["accept"] - d["arms"][a]["accept"]
            df = d["arms"][b]["false_accept"] - d["arms"][a]["false_accept"]
            out += [macro(f"{split}{lab}Step{step}F", da), macro(f"{split}{lab}Step{step}U", df)]
        la = d["L_added"]
        out += [macro(f"{split}{lab}LAddF", la["equivalent"]), macro(f"{split}{lab}LAddU", la["inequivalent"]),
                macro(f"{split}{lab}LAdd", la["equivalent"] + la["inequivalent"]),
                macro(f"{split}{lab}LFARefs", la["inequivalent_references"]),
                macro(f"{split}{lab}LFATop", la["largest_reference_group"])]
        g = d["closed_not_v4"]
        res = sum(g.get(x, 0) for x in ("residual_first_binder", "residual_closed", "residual_partial"))
        unk = g.get("unknown_total", 0) + g.get("unknown_partial", 0)
        out += [macro(f"{split}{lab}Gap", g["pairs"]), macro(f"{split}{lab}GapReject", g.get("reject", 0)),
                macro(f"{split}{lab}GapResidual", res), macro(f"{split}{lab}GapUnknown", unk),
                macro(f"{split}{lab}GapUnknownTotal", g.get("unknown_total", 0)),
                macro(f"{split}{lab}GapCanonFail", g.get("canon_fail", 0))]
    for split in ("Test", "Valid"):
        h = t[split.lower()]["H5"]
        b, c = h["discordant"]
        p = h["p_one_sided"]
        out += [macro(f"{split}HfiveB", b), macro(f"{split}HfiveC", c),
                macro(f"{split}HfiveFAIncrease", f"{h['false_accept_increase_pp']:.2f}"),
                macro(f"{split}HfiveP", "<10^{-3}" if p < 1e-3 else f"={p:.3f}")]
    rb = t["test"]["robustness"]
    for nm, key in (("Greedy", "greedy"), ("Align", "align")):
        r = rb[key]
        out += [macro(f"Rename{nm}", r["renamed_map_changes"]), macro(f"Shuffle{nm}Goals", r["shuffled_goal_changes"]),
                macro(f"Shuffle{nm}Acc", r["shuffled_goal_changes_on_v21_equivalent_accepts"]),
                macro(f"Full{nm}BeforeF", r["full_before_shuffle"].get("F", 0)),
                macro(f"Full{nm}BeforeU", r["full_before_shuffle"].get("U", 0)),
                macro(f"Full{nm}AfterF", r["full_after_shuffle"].get("F", 0)),
                macro(f"Full{nm}AfterU", r["full_after_shuffle"].get("U", 0))]
    out.append(macro("ShuffleCandidates", rb["align"]["shuffled_candidates"]))
    sh = t["test"]["shared"]
    a, s = sh["adjudicated"]["v4"], sh["adjudicated"]["semanteq"]
    out += [macro("SharedPairs", f"{sh['pairs']:,}"), macro("SharedVfourAcc", a["accept"]),
            macro("SharedVfourFA", a["false_accept"]), macro("SharedVfourRecall", f"{100 * a['accept_recall']:.1f}"),
            macro("SharedVfourPrec", f"{100 * a['accept_precision']:.1f}"), macro("SharedVfourRej", a["reject"]),
            macro("SharedVfourFalseRej", a["false_reject"]), macro("SharedSemAcc", s["accept"]),
            macro("SharedSemRecall", f"{100 * s['accept_recall']:.1f}"),
            macro("SharedBothAcc", sh["semanteq_accepts_v4_accepts"]), macro("SharedVfourOnly", sh["v4_only_accepts"])]

    def cell(d, arm):
        m = d["arms"][arm]
        return f"{m['accept']} ({m['accept_pct']:.1f}) & {m['false_accept']} ({m['false_accept_pct']:.1f})"

    rows = [("v2.1", "v2.1"), ("+ U, A", "U+A"), ("+ NF", "U+A+NF"), ("+ L (v4)", "v4"), ("closed $\\Ecl$", "closed")]
    body = [f"{label} & " + " & ".join(cell(d, arm) for _, _, d in cols) + "\\\\"
            + ("\\midrule" if arm == "v4" else "") for label, arm in rows]
    out += ["\\newcommand{\\VfRulesTable}{%", "\\begin{table}[t]", "\\centering\\small\\setlength{\\tabcolsep}{4pt}",
            "\\begin{tabular}{lrrrrrr}",
            "\\toprule",
            "& \\multicolumn{2}{c}{development, published} & \\multicolumn{2}{c}{development, adjudicated} "
            "& \\multicolumn{2}{c}{held out, published}\\\\",
            "\\cmidrule(lr){2-3}\\cmidrule(lr){4-5}\\cmidrule(lr){6-7}",
            "check & acc. (\\%) & FA (\\%) & acc. (\\%) & FA (\\%) & acc. (\\%) & FA (\\%)\\\\", "\\midrule", *body,
            "\\bottomrule", "\\end{tabular}",
            "\\caption{The rules of protocol v4 added one at a time, with Claude Opus~5.5 at the budget of "
            "Table~\\ref{tab:full}. Development: the 1,140 test pairs on which the rules were developed, under "
            f"ProofNetVerif's labels ({cols[0][2]['equivalent']} equivalent, {cols[0][2]['inequivalent']} not) and "
            f"SemantEq's adjudicated ones ({cols[1][2]['equivalent']}, {cols[1][2]['inequivalent']}). Held out: the "
            f"{t['valid']['pairs']:,} valid pairs ({cols[2][2]['equivalent']}, {cols[2][2]['inequivalent']}), read "
            "after the freeze. acc.: accepts of equivalent pairs; FA: accepts of inequivalent pairs. The order of "
            "the steps is the order of the protocol; only v2.1, U+A and v4 were arms fixed in advance "
            "(\\texttt{k22\\_v4\\_tables.py}).}",
            "\\label{tab:v4rules}", "\\end{table}}", ""]
    return "\n".join(out)


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    mode = sys.argv[1] if len(sys.argv) > 1 else ""
    if mode == "compute":
        compute()
    elif mode == "tex":
        TEX.write_text(render(json.loads(OUT.read_text(encoding="utf-8"))), encoding="utf-8")
        print("wrote", TEX)
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
