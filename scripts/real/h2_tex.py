#!/usr/bin/env python3
"""Render the blind audit scores (data/real/h2_scores.json) as LaTeX for the paper.

Writes paper/h2_results.tex: macros for the numbers used in the prose (\\HtwoKappa, ...) and the
table `tab:h2`. The paper inputs the file only if it exists, and `paper_check.py` fails if the file
differs from what this script renders from the current scores.

Usage: h2_tex.py        (run after `h2_audit.py score A.csv B.csv`)
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCORES = ROOT / "data" / "real" / "h2_scores.json"
OUT = ROOT / "paper" / "h2_results.tex"

ROWS = [
    ("full_faithful_reject", "rejects of labelled-equivalent pairs", "yes"),
    ("full_unfaithful_local_accept", "accepts of labelled-inequivalent pairs", "yes"),
    ("full_faithful_local_accept", "\\quad control: accepts of equivalent pairs", "yes"),
    ("full_unfaithful_reject", "\\quad control: rejects of inequivalent pairs", "yes"),
    ("strict_rejects_rewarded_all", "strict rejects rewarded by a selector", "no"),
    ("strict_rejects_rewarded_closed", "\\quad rewarded by closed equivalence", "no"),
    ("strict_rejects_rewarded_judge_opus_ref", "\\quad rewarded by the judge", "no"),
    ("open_picks_closed", "open picks of closed equivalence", "no"),
    ("open_picks_judge_opus_ref", "open picks of the judge", "no"),
    ("open_picks_ours", "open picks of our accept", "no"),
]


MAP_ROWS = [
    ("map_rejects", None, "\\emph{43 component-goal rejects of labelled-equivalent pairs}"),
    ("map_rejects", ("align", "total"), "alignment total"),
    ("map_rejects", ("align", "early"), "alignment not total"),
    ("map_rejects", ("loc", "H"), "located in the hypotheses"),
    ("map_rejects", ("loc", "C"), "located in the conclusion"),
    ("map_rejects", ("loc", "HC"), "located in both"),
    ("map_rejects", ("loc", "closed"), "closed statements only"),
    ("map_rejects", ("dir", "ref_false"), "reference certified false"),
    ("map_rejects", ("dir", "cand_false"), "candidate certified false"),
    ("map_rejects", ("dir", "one_false"), "one side certified false"),
    ("map_rejects", ("dir", "vacuity"), "vacuity-only"),
    ("map_rejects", ("dir", "direction_only"), "direction proved, no side certified false"),
    ("map_rejects", ("dir", "open"), "no direction proved"),
    ("map_accepts", None, "\\emph{14 accepts of labelled-inequivalent pairs}"),
    ("map_accepts", ("fa", "constant"), "conclusion certified constant"),
    ("map_accepts", ("fa", "trivial"), "candidate flagged trivial"),
    ("map_accepts", ("fa", "neither"), "neither"),
]


def pct(x) -> str:
    return "--" if x is None else f"{100 * x:.0f}"


def camel(*parts: str) -> str:
    return "".join(w.capitalize() for p in parts for w in p.replace("_", " ").split())


def mapping(s: dict) -> list[str]:
    """Macros and table `tab:h2map`: the audit against the mechanical facts of each item."""
    out = []
    for i, a in enumerate(s.get("location_vs_kind", [])):
        out += [macro(f"LocKindN{'AB'[i]}", a["n"]), macro(f"LocKindAgree{'AB'[i]}", a["agree"])]
    body = []
    for top, key, label in MAP_ROWS:
        if key is None:
            body.append(f"\\multicolumn{{7}}{{l}}{{{label}}}\\\\")
            continue
        r = s.get(top, {}).get(key[0], {}).get(key[1], {})
        if key == ("dir", "open") and not r.get("items"):
            continue
        cells = [r.get("items", 0), r.get("statements", 0), r.get("yes", 0), r.get("no", 0), r.get("unsure", 0),
                 r.get("disagree", 0)]
        out += [macro(f"Map{camel(*key)}{col}", v) for col, v in zip(("N", "Rows", "Yes", "No"), cells)]
        body.append(f"\\quad {label} & " + " & ".join(map(str, cells)) + "\\\\")
    agree = "; ".join(f"annotator {'AB'[i]}: {a['agree']} of {a['n']}" for i, a in enumerate(s.get("location_vs_kind", [])))
    return out + ["\\begin{table}[t]", "\\centering\\small", "\\begin{tabular}{lrrrrrr}", "\\toprule",
                  "mechanical facts & items & statements & yes & no & unsure & disagree\\\\", "\\midrule", *body,
                  "\\bottomrule", "\\end{tabular}",
                  "\\caption{The blind audit against the kernel facts behind each reject and false accept of "
                  "Table~\\ref{tab:dist}, by a mapping fixed before the answers returned. The three blocks of the "
                  "rejects classify the same 43 items; copies of one proposition share its answer. Yes: both "
                  "annotators judge the candidate faithful. For a reject this means that the located difference "
                  "does not make the candidate unfaithful: the reference is wrong, the difference is waivable, or "
                  "the alignment paired the wrong binders; for an accept, that the label is wrong. Where an "
                  "annotator calls a rejected candidate unfaithful and names a missing, extra or vacuous "
                  "hypothesis or a different conclusion, the located component agrees in " + (agree or "--") + ".}",
                  "\\label{tab:h2map}", "\\end{table}", ""]


def macro(name: str, value) -> str:
    return f"\\newcommand{{\\Htwo{name}}}{{{value}}}"


def render(s: dict) -> str:
    kb = s.get("kappa_between", {})
    out = ["% generated by scripts/real/h2_tex.py from data/real/h2_scores.json; do not edit",
           macro("Kappa", "--" if kb.get("kappa") is None else f"{kb['kappa']:.2f}"),
           macro("KappaN", kb.get("n", 0)),
           macro("Agree", kb.get("agree", 0))]
    for i in range(s.get("annotators", 0)):
        g = s.get(f"g_kappa_vs_first_{i}", {})
        out.append(macro(f"KappaFirst{'AB'[i]}", "--" if g.get("kappa") is None else f"{g['kappa']:.2f}"))
    for key, _, side in ROWS:
        r = s.get(key, {})
        name = "".join(w.capitalize() for w in key.replace("_opus_ref", "").split("_"))
        rate = r.get("faithful_rate" if side == "yes" else "unfaithful_rate")
        out.append(macro(name + "Rate", pct(rate)))
        out.append(macro(name + "N", r.get("sampled", 0)))
    out += ["\\begin{table}[t]", "\\centering\\small\\setlength{\\tabcolsep}{4pt}", "\\begin{tabular}{lrrrrrrl}", "\\toprule",
            "set & items & statements & yes & no & unsure & disagree & rate [95\\% CI]\\\\", "\\midrule"]
    for key, label, side in ROWS:
        r = s.get(key, {})
        rate = r.get("faithful_rate" if side == "yes" else "unfaithful_rate")
        ci = r.get("ci95") or [None, None]
        cis = "--" if ci[0] is None else f"{pct(ci[0])}--{pct(ci[1])}"
        what = "faithful" if side == "yes" else "unfaithful"
        out.append(f"{label} & {r.get('sampled', 0)} & {r.get('distinct', r.get('sampled', 0))} & "
                   f"{r.get('yes', 0)} & {r.get('no', 0)} & {r.get('unsure', 0)} & {r.get('disagree', 0)} & "
                   f"{pct(rate)}\\% {what} [{cis}]\\\\")
    out += ["\\bottomrule", "\\end{tabular}",
            f"\\caption{{Blind two-annotator audit. ``Statements'': distinct propositions (items that state the "
            f"same proposition share one answer); the answer columns and rates count statements. A verdict "
            f"counts only when both annotators agree; "
            f"inter-annotator $\\kappa={kb.get('kappa', 0) or 0:.2f}$ on {kb.get('n', 0)} statements.}}",
            "\\label{tab:h2}", "\\end{table}", ""]
    return "\n".join(out + mapping(s))


def main() -> None:
    if not SCORES.exists():
        raise SystemExit("no data/real/h2_scores.json; run h2_audit.py score first")
    OUT.write_text(render(json.loads(SCORES.read_text(encoding="utf-8"))), encoding="utf-8")
    print("wrote", OUT)


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    main()
