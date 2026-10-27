#!/usr/bin/env python3
"""Recompute the numbers of the paper's main tables from the stored results and compare them
with paper/main.tex, cell by cell; also checks a list of numbers stated in the prose.

Verdicts are counted the same way everywhere: a decided verdict needs both regrouping
certificates (`split_r`, `split_s`), otherwise it is `unknown`; a certified accept whose
alignment is not total, or whose prefix is empty, is `residual`.

Runs no prover and calls no model. Writes data/real/paper_numbers.json (all recomputed rows and
the verdict distribution of tab:dist).

Usage: paper_check.py           exit status 1 if any cell or prose number differs
"""

from __future__ import annotations

import csv
import json
import math
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from a1_local import local
from f7_component import classify

ROOT = Path(__file__).resolve().parents[2]
D = ROOT / "data" / "real"
TEX = ROOT / "paper" / "main.tex"
SPLITS = {"split_r", "split_s"}
SUBSET_TIERS = [("tactics", None), ("qwen", "qwen3.8-27b-nothink"), ("mini", "gpt-4.1-mini"),
                ("deepseek", "deepseek-v4.1-flash"), ("gemini", "gemini-4-argon"), ("astra", "gpt-6-astra"),
                ("opus", None)]
FULL_TIERS = [("qwen", "qwen3.8-27b-nothink"), ("mini", "gpt-4.1-mini"), ("deepseek", "deepseek-v4.1-flash"),
              ("opus", "claude-opus-5.5")]


def load(path: Path) -> list[dict]:
    return json.loads(path.read_text(encoding="utf-8"))["pairs"]


def verdict(p: dict, proved: set[str] | None = None, v: str | None = None,
            closed: str | None = None) -> str:
    """accept / residual / reject / off_domain / unknown, with the certificate rule.

    A refuted closed equivalence with both regrouping certificates is a reject
    (Proposition cert, `T9.cert_closed_refute`)."""
    proved = set(p.get("proved") or []) if proved is None else proved
    v = p["verdict"] if v is None else v
    closed = p.get("closed") if closed is None else closed
    if v == "canon_fail":
        return "unknown"
    if not SPLITS <= proved:
        return "unknown"
    if v == "unknown" and closed == "refuted":
        return "reject"
    if v == "accept" and not local(p.get("canon_info")):
        return "residual"
    return v


def closed_of(goals: set[str]) -> str:
    """Closed outcome from the proved closed goals (as `f2_oracle.verdict`)."""
    if goals & {"nfwd", "nbwd"}:
        return "refuted"
    return "proved" if {"fwd", "bwd"} <= goals else "unknown"


def unknown_cause(p: dict, proved: set[str] | None = None, v: str | None = None) -> str:
    proved = set(p.get("proved") or []) if proved is None else proved
    v = p["verdict"] if v is None else v
    if v == "canon_fail" or not p.get("canon_info"):
        return "canon_fail"
    if not SPLITS <= proved:
        return "no_certificate"
    info = p["canon_info"]
    if int(p.get("shared") or re.search(r"shared=(\d+)", info).group(1)) == 0:
        return "no_alignment"
    return "budget" if "full=true" in info else "partial_alignment"


def located(p: dict) -> str:
    """The component a reject certifies: H (nhyp), C (ncin), HC, or "" when it certifies only
    that the closed statements differ: no component goal is decided, or neither telescope has a
    prefix binder or a hoisted hypothesis, so that the conclusion goal compares the closed statements."""
    pr = set(p.get("proved") or [])
    info = p.get("canon_info") or ""
    m = re.search(r"prefix_r=(\d+)/\d+ prefix_s=(\d+)/\d+", info)
    if m and m.group(1) == m.group(2) == "0" and not any(int(x) for x in re.findall(r"hoist_[rs]=(\d+)", info)):
        return ""
    return ("H" if "nhyp" in pr else "") + ("C" if "ncin" in pr else "")


def outcome(p: dict) -> str:
    """The row of tab:dist: the verdict, with rejects split by the evidence behind them."""
    v = verdict(p)
    if v == "reject":
        if not located(p):
            return "reject:closed:refuted" if p["verdict"] == "unknown" else "reject:closed:empty"
        return "reject:total" if local(p.get("canon_info")) else "reject:early"
    if v == "unknown":
        return f"unknown:{unknown_cause(p)}"
    return v


def tally(rows, faithful) -> dict:
    """rows: (pair, verdict, closed_proved); counts per label (U unfaithful, F faithful)."""
    c = Counter()
    for p, v, closed in rows:
        lab = "F" if faithful(p) else "U"
        c[f"n{lab}"] += 1
        c[f"closed{lab}"] += closed
        c[f"{v}{lab}"] += 1
    return c


def g5_rows() -> dict[str, Counter]:
    f2 = {p["row_id"]: set(p["t1"]) for p in load(D / "g5" / "f2_full.json")}
    base = load(D / "g5" / "g1_results_claude-opus-5.5.json")
    out = {"tactics": tally([(p, verdict(p, set(p.get("tactic") or []), classify(set(p.get("tactic") or [])),
                                         closed_of(f2[p["row_id"]]))
                              if p["verdict"] != "canon_fail" else "unknown",
                              {"fwd", "bwd"} <= f2[p["row_id"]]) for p in base], lambda p: p["label"])}
    for name, f in FULL_TIERS:
        ps = load(D / "g5" / f"g1_results_{f}.json")
        out[name] = tally([(p, verdict(p), p["closed"] == "proved") for p in ps], lambda p: p["label"])
    return out


def subset_rows(ds: str) -> dict[str, Counter]:
    prefix = "g1" if ds == "g1" else "g4"
    faithful = (lambda p: p["label"]) if ds == "g1" else (lambda p: p["relation"] == "faithful")
    opus = load(D / f"{prefix}_results.json")
    f2 = {p["row_id"]: set(p["t1"]) for p in load(D / "f2_results.json")} if ds == "g1" else None
    out = {}
    for name, f in SUBSET_TIERS:
        if name == "tactics":
            rows = []
            for p in opus:
                tac = set(p.get("tactic") or [])
                closed_tac = f2[p["row_id"]] if f2 is not None else set(p.get("closed_tactic") or [])
                v = verdict(p, tac, classify(tac), closed_of(closed_tac)) if p["verdict"] != "canon_fail" else "unknown"
                rows.append((p, v, {"fwd", "bwd"} <= closed_tac))
        else:
            ps = opus if name == "opus" else load(D / f"{prefix}_results_{f}.json")
            rows = [(p, verdict(p), p["closed"] == "proved") for p in ps]
        out[name] = tally(rows, faithful)
    return out


def g1_strong_final() -> Counter:
    """Opus on the subset after embedding alignment (Table g1): off-image is not an accept."""
    g1 = {p["row_id"]: p for p in load(D / "g1_results.json")}
    rows = []
    for e in load(D / "e1_results.json"):
        p = g1[e["row_id"]]
        v = e["embed"]
        v = v if v == "off_image" else verdict(p, set(e.get("proved") or p["proved"]), v)
        rows.append((p, v, p["closed"] == "proved"))
    return tally(rows, lambda p: p["label"])


def g4_groups() -> dict[str, Counter]:
    out = {}
    for p in load(D / "g4_results.json"):
        grp = "faithful" if p["relation"] == "faithful" else ("true" if p.get("candidate_true") else "other")
        c = out.setdefault(grp, Counter())
        c["n"] += 1
        c[f"closed_{p['closed']}"] += 1
        c[verdict(p)] += 1
    return out


def budget_rows() -> dict[str, dict]:
    out = {}
    for model in ("claude-opus-5.5", "deepseek-v4.1-flash"):
        f = D / f"k11_budget_{model}.json"
        if not f.exists():
            continue
        d = json.loads(f.read_text(encoding="utf-8"))
        table = {lev: dict(t) for lev, t in d["table"].items()}
        for rec in d["pairs"]:
            lab = "F" if rec["label"] else "U"
            for lev, t in table.items():
                if rec["split"] and rec["comp"][lev] == "unknown" and rec["closed"][lev] == "refuted":
                    t[f"reject{lab}"] += 1
                    t[f"unknown{lab}"] -= 1
        out[model] = table
    return out


def cost_rows() -> list[list[float]]:
    """tab:cost: cumulative model calls, tokens (millions) and Lean checks per K11 level (K15)."""
    rows = []
    for model in ("claude-opus-5.5", "deepseek-v4.1-flash"):
        d = json.loads((D / f"k15_cost_{model}.json").read_text(encoding="utf-8"))
        assert d["table_matches_k11"], model
        run = {"closed": Counter(), "comp": Counter()}
        for lev in ("L1", "L2", "L3"):
            t = d["table"][lev]
            row = []
            for side, fa, acc in (("closed", "closed_accU", "closed_accF"), ("comp", "localU", "localF")):
                run[side].update(d["cost"].get(f"{side}/{lev}", {}))
                c = run[side]
                row += [c["calls"], round((c["prompt_tokens"] + c["completion_tokens"]) / 1e6, 1),
                        c["lean_checks"], t[fa], t[acc]]
            rows.append(row)
    return rows


def wilson(k: int, n: int, z: float = 1.959964) -> tuple[float, float]:
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return max(0.0, c - h), min(1.0, c + h)


def distribution() -> dict:
    """tab:dist: every outcome of the strongest configuration on the full set, per label."""
    ps = load(D / "g5" / "g1_results_claude-opus-5.5.json")
    out = {}
    for lab, name in ((False, "U"), (True, "F")):
        sel = [p for p in ps if p["label"] == lab]
        n = len(sel)
        c, closed = Counter(), Counter()
        for p in sel:
            o = outcome(p)
            keys = {verdict(p), o, *(["reject:closed"] if o.startswith("reject:closed") else [])}
            c.update(keys)
            closed.update(k for k in keys if p["closed"] == "proved")
        out[name] = {"n": n, "closed_proved": sum(p["closed"] == "proved" for p in sel),
                     **{k: {"k": v, "pct": round(100 * v / n, 1), "closed_proved": closed[k],
                            "wilson95": [round(100 * x, 1) for x in wilson(v, n)]}
                        for k, v in sorted(c.items())}}
    return out


# ---------------------------------------------------------------- expected table cells

def expected() -> dict[str, list[list[float | None]]]:
    full, sub, pnv = g5_rows(), subset_rows("g1"), subset_rows("g4")
    beq_full = {p["row_id"]: bool(p["beq_plus"]) for p in load(D / "g5" / "b1_results.json")}
    exp: dict[str, list] = {}
    exp["tab:full"] = [[c["closedU"], c["closedF"], c["acceptU"], c["acceptF"], c["residualU"], c["residualF"],
                        c["rejectU"], c["rejectF"]] for c in (full[t] for t in ("tactics", "qwen", "mini",
                                                                                   "deepseek", "opus"))]
    base = {p["row_id"]: p["label"] for p in load(D / "g5" / "g1_results_claude-opus-5.5.json")}
    exp["beq_full"] = [sum(beq_full[r] and not l for r, l in base.items()), sum(beq_full[r] and l for r, l in base.items())]
    exp["tab:sweep"] = [[c["closedU"], c["closedF"], c["acceptU"], c["acceptF"], c["residualU"], c["residualF"]]
                        for rows in (sub, pnv) for c in (rows[t] for t, _ in SUBSET_TIERS)]
    exp["tab:budget"] = [[t[l]["closed_accU"], t[l]["closed_accF"], t[l]["localU"], t[l]["localF"],
                          t[l]["residualU"], t[l]["residualF"], t[l]["rejectU"]]
                         for t in budget_rows().values() for l in ("L0", "L1", "L2", "L3") if l in t]
    exp["tab:cost"] = cost_rows()
    weak, strong = sub["deepseek"], g1_strong_final()
    beq_sub = {p["row_id"]: bool(p["beq_plus"]) for p in load(D / "b1_results.json")}
    lab_sub = {p["row_id"]: p["label"] for p in load(D / "g1_results.json")}
    exp["tab:g1"] = [
        [weak["closedU"], weak["closedF"]], [strong["closedU"], strong["closedF"]],
        [sum(beq_sub[r] and not l for r, l in lab_sub.items()), sum(beq_sub[r] and l for r, l in lab_sub.items())],
        [weak["acceptU"], weak["rejectU"], weak["acceptF"], weak["rejectF"], None],
        [strong["acceptU"], strong["rejectU"], strong["acceptF"], strong["rejectF"], None],
        [weak["residualU"], weak["residualF"]], [strong["residualU"], strong["residualF"]],
    ]
    g = g4_groups()
    exp["tab:g4"] = [
        [g["true"]["closed_proved"], g["true"]["n"] - g["true"]["closed_proved"] - g["true"]["closed_refuted"],
         g["other"]["closed_proved"], g["other"]["closed_refuted"], g["faithful"]["closed_proved"]],
        [g["true"]["accept"], g["true"]["reject"], g["true"]["unknown"], g["other"]["accept"],
         g["other"]["reject"], g["faithful"]["accept"]],
        [g["true"]["residual"], g["other"]["residual"], g["faithful"]["residual"]],
    ]
    t = json.loads((D / "g5_tables.json").read_text(encoding="utf-8"))
    lv = t["levels"]
    exp["tab:levels"] = [[lv[r]["FA"]["k"], *(round(100 * x, 1) for x in lv[r]["FA"]["wilson95"]), lv[r]["acc"]["k"]]
                         for r in ("closed", "ours_all", "ours_local", "ours_local_not_trivial",
                                   "ours_local_not_trivial_not_constant", "beq_plus", "beq_or_local_not_trivial",
                                   "beq_or_local_not_trivial_not_constant")]
    hk = t["hack"]
    exp["tab:hack"] = [[h["closed:tactics"], h["closed:openai/gpt-4.1-mini"], h["closed:anthropic/claude-opus-5.5"],
                        h["beq_plus"], h.get("ours:accept", 0), h.get("ours:residual", 0), h.get("ours:reject", 0),
                        h.get("ours:off_domain", 0), h.get("ours:unknown", 0), h["ours+triviality:rewarded"]]
                       for h in (hk[k] for k in ("id", "top", "absorb", "vac", "topsimp", "absorbsimp"))]
    dist = distribution()
    rows = []
    for key in ("accept", "reject:total", "residual", "reject:early", "reject:closed", "reject:closed:refuted",
                "reject:closed:empty", "unknown", "unknown:canon_fail", "unknown:no_certificate",
                "unknown:no_alignment", "unknown:partial_alignment", "unknown:budget"):
        row = []
        for lab in ("U", "F"):
            x = dist[lab].get(key, {"k": 0, "pct": 0.0, "wilson95": [0.0, 0.0], "closed_proved": 0})
            row += [x["k"], x["pct"], *x["wilson95"], x["closed_proved"]]
        rows.append(row)
    rows.append([dist["U"]["n"], dist["U"]["closed_proved"], dist["F"]["n"], dist["F"]["closed_proved"]])
    exp["tab:dist"] = rows
    e5 = json.loads((D / "e5_results.json").read_text(encoding="utf-8"))["per_kind"]
    outcomes = ("identical", "reordered", "logical", "open")
    exp["tab:repr"] = []
    for kinds in (("swap0", "swap1", "swap2"), ("conj0", "conj1"), ("negpeel",), ("unconj0",)):
        c = Counter()
        for k in kinds:
            c.update({o: n for o, n in e5[k].items() if o != "not_applicable"})
        exp["tab:repr"].append([sum(c.values()), *(c[o] for o in outcomes)])
    import k18_combine
    sc = k18_combine.compute()["scores"]
    pct = lambda x: round(100 * x, 1)
    exp["tab:common"] = [[s["accept"], s["false_accept"], pct(s["accept_precision"]), pct(s["accept_recall"]),
                          *([s["reject"], s["false_reject"], pct(s["reject_precision"])] if s["reject"] else []),
                          pct(s["decided"])]
                         for lab in ("published", "adjudicated")
                         for s in (sc[f"{n}|{lab}"] for n in ("beqplus", "semanteq", "ours",
                                                               "semanteq_accept_ours_reject", "both_accept"))]
    return exp


# ---------------------------------------------------------------- parsing main.tex

NUM = re.compile(r"\d+(?:\.\d+)?")


def table_rows(tex: str, label: str) -> list[list[float]] | None:
    i = tex.find(f"\\label{{{label}}}")
    if i < 0:
        return None
    start = tex.rfind("\\begin{table", 0, i)
    body = tex[start:i]
    body = body[body.find("\\midrule"):body.rfind("\\bottomrule")]
    out = []
    for raw in body.split("\\\\"):
        raw = re.sub(r"\\(c?midrule)(\([^)]*\))?(\{[^}]*\})?", "", raw).strip()
        if "&" not in raw:
            continue
        cells = raw.split("&")
        nums = []
        for cell in cells[1:]:
            cell = re.sub(r"\([^)]*\)", "", cell)
            cell = re.sub(r"\\(textbf|V|emph)\{([^}]*)\}", r"\2", cell)
            if re.search(r"[A-Za-z]{3,}", cell):
                continue
            nums += [float(x) for x in NUM.findall(cell)]
        out.append(nums)
    return out


def flat(row) -> list[float]:
    return [x for x in row if x is not None]


def compare_tables(tex: str, exp: dict) -> list[str]:
    errs = []
    for label, rows in exp.items():
        if not label.startswith("tab:"):
            continue
        got = table_rows(tex, label)
        if got is None:
            errs.append(f"{label}: not in main.tex")
            continue
        got = [r for r in got if r]
        if len(got) != len(rows):
            errs.append(f"{label}: {len(got)} numeric rows in the paper, {len(rows)} expected")
        for k, (g, e) in enumerate(zip(got, rows)):
            if None in e:
                g = g[:len(e)]
                pairs = [(a, b) for a, b in zip(g, e) if b is not None]
            else:
                pairs = list(zip(g, e))
                if len(g) != len(e):
                    errs.append(f"{label} row {k + 1}: paper {g} expected {e}")
                    continue
            if any(abs(a - b) > 0.051 for a, b in pairs):
                errs.append(f"{label} row {k + 1}: paper {g} expected {flat(e)}")
    return errs


# ---------------------------------------------------------------- prose numbers

def thousands(n: int) -> str:
    return f"{n // 1000}\\{{,\\}}{n % 1000:03d}" if n >= 1000 else str(n)


def where(model: str) -> dict[str, dict[str, int]]:
    """Certified rejects of inequivalent pairs by the component a certificate names, with the
    closed outcome: H = nhyp only, C = ncin only, HC = both; not located: R = closed refutation
    only, C0 = a component goal on two empty prefixes."""
    out = {k: {"n": 0, "proved": 0, "refuted": 0} for k in ("H", "C", "HC", "R", "C0")}
    for p in load(D / "g5" / f"g1_results_{model}.json"):
        if p["label"] or verdict(p) != "reject":
            continue
        loc = located(p) or ("R" if p["verdict"] == "unknown" else "C0")
        out[loc]["n"] += 1
        if p["closed"] in ("proved", "refuted"):
            out[loc][p["closed"]] += 1
    return out


def prose_claims(exp: dict) -> list[tuple[str, str]]:
    """(regex that must occur in main.tex, description). Numbers come from the recomputed rows."""
    full = exp["tab:full"]
    opus, tac = full[4], full[0]
    bud = exp["tab:budget"]
    t = json.loads((D / "g5_tables.json").read_text(encoding="utf-8"))["paired_tests_opus"]
    cl = t["closed vs ours_local [FA]"]
    ca = t["closed vs ours_local [acc]"]
    bq = t["beq_plus vs ours_local [acc]"]
    beq = exp["beq_full"]
    dist = distribution()
    dec = {lab: dist[lab]["n"] - dist[lab]["unknown"]["k"] for lab in ("U", "F")}
    strict = {lab: dec[lab] - dist[lab]["residual"]["k"] for lab in ("U", "F")}
    pct = lambda k, lab: round(100 * k / dist[lab]["n"])
    early = sum(dist["U"][f"unknown:{k}"]["k"] for k in ("canon_fail", "no_certificate", "no_alignment",
                                                          "partial_alignment"))
    us = [p for p in load(D / "g5" / "g1_results_claude-opus-5.5.json") if not p["label"]]
    sep = (sum(verdict(p) == "reject" and p["closed"] == "unknown" for p in us),
           sum(verdict(p) == "unknown" and p["closed"] == "refuted" for p in us))
    fs = [p for p in load(D / "g5" / "g1_results_claude-opus-5.5.json") if p["label"]]
    loc_u = [p for p in us if verdict(p) == "reject" and located(p)]
    part = [p for p in loc_u if not local(p.get("canon_info"))]
    part_open = sum(p["closed"] != "refuted" for p in part)
    part_f = sum(verdict(p) == "reject" and bool(located(p)) and not local(p.get("canon_info")) for p in fs)
    comp_f = sum(verdict(p) == "reject" and p["verdict"] != "unknown" for p in fs)
    # where the closed accepts go that ours does not share: the cost on F, the gain on U
    cost = Counter(verdict(p) for p in fs if p["closed"] == "proved" and verdict(p) != "accept")
    gain = Counter(verdict(p) for p in us if p["closed"] == "proved" and verdict(p) != "accept")
    gain_loc = sum(p["closed"] == "proved" and bool(located(p)) for p in loc_u)
    gain_total = sum(p["closed"] == "proved" and local(p.get("canon_info")) for p in loc_u)
    ws = lambda s: s.replace(" ", r"\s+")
    wo, wd = where("claude-opus-5.5"), where("deepseek-v4.1-flash")
    import k17_semanteq
    import k18_combine
    se = k17_semanteq.compute()
    kc = k18_combine.compute()
    sc = kc["scores"]
    two, two_adj = sc["semanteq_accept_ours_reject|published"], sc["semanteq_accept_ours_reject|adjudicated"]
    s_only, o_only = sc["semanteq|published"], sc["ours|published"]
    both, ct = sc["both_accept|published"], kc["crosstab"]
    bo = se["by_outcome"]
    se_rej = {k: bo[f"reject:{k}"] for k in ("component", "closed")}
    se_rel = {k: v.get("non_equivalent", 0) for k, v in bo.items()}
    kept = se["rejects_kept_equivalent"]
    k13 = load(D / "k13_redteam.json")
    red = Counter(verdict(p) for p in k13)
    red_rew = sum(verdict(p) == "reject" and p["closed"] == "proved" for p in k13)
    share = lambda c: round(100 * c["proved"] / c["n"])
    return [
        (ws(rf"the hypotheses differ in {wo['H']['n']}, the conclusions inside the hypotheses in "
            rf"{wo['C']['n']}, and both in {wo['HC']['n']}"), "where, Opus counts"),
        (ws(rf"Closed equivalence proves {wo['H']['proved']} of the {wo['H']['n']} \({share(wo['H'])}\\%\) and "
            rf"{wo['HC']['proved']} of the {wo['HC']['n']}, but only {wo['C']['proved']} of the {wo['C']['n']} "
            rf"\({share(wo['C'])}\\%\), and it refutes {wo['C']['refuted']} of the {wo['C']['n']}"), "where, Opus closed"),
        (rf"{wd['H']['proved']} of {wd['H']['n']}, {wd['HC']['proved']} of {wd['HC']['n']}\s+and "
         rf"{wd['C']['proved']} of {wd['C']['n']}", "where, DeepSeek"),
        (rf"we decide {pct(dec['U'], 'U')}\\% of the inequivalent\s+and {pct(dec['F'], 'F')}\\% of the equivalent",
         "coverage with residual"),
        (rf"{pct(strict['U'], 'U')}\\% and {pct(strict['F'], 'F')}\\% without\s+it", "coverage without residual"),
        (rf"Of the {dist['U']['unknown']['k']} \\V\{{unknown\}} inequivalent pairs only "
         rf"{dist['U']['unknown:budget']['k']} have", "unknown causes"),
        (rf"the other {early} fail earlier", "unknown causes, front end"),
        (ws(rf"{len(part)} of the {len(loc_u)} located rejects have an alignment that is not total, and in the "
            rf"{part_open} of them"), "located rejects on an alignment that is not total"),
        (ws(rf"The other {wo['R']['n'] + wo['C0']['n']} certify a difference of the closed statements without "
            rf"locating it: for {wo['R']['n']} no component goal is decided"), "not located"),
        (ws(rf"for {wo['C0']['n']} neither telescope has a binder or a hypothesis in its prefix"), "not located, empty"),
        (ws(rf"Of the {sum(cost.values())} equivalent pairs that only closed equivalence accepts, {cost['residual']} "
            rf"are \\V\{{residual\}}, {cost['unknown']} \\V\{{unknown\}} and {cost['reject']} rejected"), "coverage cost"),
        (ws(rf"of the {sum(gain.values())} closed false accepts that we do not accept, {gain['residual']} are "
            rf"\\V\{{residual\}}, {gain['unknown']} \\V\{{unknown\}} and "
            rf"{gain['reject'] if gain['reject'] == gain_loc else -1} rejects that locate the difference, "
            rf"{gain_total} of them on a total alignment"), "what the cost buys"),
        (ws(rf"{pct(dist['F']['accept']['k'], 'F')}\\% of the faithful pairs are accepted, against "
            rf"{pct(opus[1], 'F')}\\% by closed equivalence"), "abstract, coverage"),
        (ws(rf"{sum(cost.values())} faithful pairs are accepted only by closed equivalence, "
            rf"{cost['residual']} of them returned as \\V\{{residual\}}"), "contributions, cost"),
        (ws(rf"location: {len(loc_u)} of the {opus[6]} rejects of unfaithful pairs name the aligned component"),
         "contributions, location"),
        (ws(rf"no reader has checked the {len(loc_u)} locations"), "locations unchecked"),
        (ws(rf"and {part_f} of them locate the difference on an alignment that is not total"), "F rejects, early"),
        (ws(rf"\({part_f} of the {opus[7]} rejects of labelled-equivalent pairs locate a difference on one\)"),
         "tab:layers, F rejects"),
        (ws(rf"{part_f} of the {comp_f} rejects of labelled-equivalent pairs that rest on component goals locate"),
         "limitations, F rejects"),
        (ws(rf"{se['shared']} of our {se['ours_equivalent']} equivalent pairs are among them"), "SemantEq coverage"),
        (ws(rf"On the {kc['shared']:,} test pairs that both cover, SemantEq-Eval accepts {s_only['accept']} and "
            rf"never a pair labelled inequivalent") if s_only["false_accept"] == 0 else r"(?!)", "K18 SemantEq alone"),
        (ws(rf"our criterion decides {o_only['accept'] + o_only['reject']} \({o_only['accept']} accepts, "
            rf"{o_only['false_accept']} of them false, and {o_only['reject']} certified rejects\)"), "K18 ours alone"),
        (ws(rf"decides {two['accept'] + two['reject']} pairs \({round(100 * two['decided'])}\\%, against "
            rf"{round(100 * s_only['decided'])}\\% for SemantEq alone\) with no false accept observed under either "
            rf"label set \(at most {100 * wilson(0, two['accept'])[1]:.1f}\\% of its {two['accept']} accepts at 95\\% "
            rf"confidence\); of its {two['reject']} "
            rf"rejects, {two['false_reject']} are of pairs labelled equivalent by ProofNetVerif and "
            rf"{two_adj['false_reject']} under SemantEq's adjudicated labels \({100 * two_adj['reject_precision']:.1f}\\% "
            rf"precision\)") if two["false_accept"] == two_adj["false_accept"] == 0 else r"(?!)", "K18 two-sided"),
        (ws(rf"of its {s_only['accept']} accepts we accept {ct['accept|accept']['n']}, leave "
            rf"{ct['accept|residual']['n']} \\V\{{residual\}} and {ct['accept|unknown']['n']} \\V\{{unknown\}} and reject "
            rf"{ct['accept|reject']['n']},")
         if sum(c["n"] for k, c in ct.items() if k.startswith("accept|")) == s_only["accept"] else r"(?!)",
         "K18 crosstab"),
        (ws(rf"Accepting what either accepts would take on all {kc['our_false_accepts']}; accepting only what both "
            rf"accept gives up {two['accept'] - both['accept']} accepts and no false one")
         if ct["other|accept"]["ineq_published"] == kc["our_false_accepts"] and both["false_accept"] == 0
         else r"(?!)", "K18 union and intersection"),
        (ws(r"The two disagree on one pair, the artefact 358") if [c["row_id"] for c in kc["conflicts"]] == ["pnv-test-358"]
         else r"(?!)", "K18 conflicts"),
        (ws(rf"SemantEq accepts none of our {kc['our_false_accepts']} false accepts, and our accepts add "
            rf"{kc['accept_overlap']['-O']} pairs that SemantEq does not accept, "
            rf"{kc['accept_overlap']['-O'] - kc['our_false_accepts']} of them labelled equivalent")
         if kc["our_false_accepts_semanteq_accepts"] == 0 else r"(?!)", "K18 accept overlap"),
        (ws(rf"decides {round(100 * two['decided'])}\\% of the shared test pairs with no false accept observed under "
            rf"either label set, though with false rejects") if two["false_accept"] == two_adj["false_accept"] == 0
         and two["false_reject"] > 0 and two_adj["false_reject"] > 0 else r"(?!)", "contributions: K18"),
        (ws(rf"\(ours: {100 * opus[3] / (opus[3] + opus[2]):.1f}\\% and {100 * opus[3] / 446:.1f}\\% under the "
            rf"published labels"), "precision and recall vs SemantEq"),
        (ws(rf"They relabel {se_rel['reject:component'] + se_rel['reject:closed']} of our {opus[7]} rejects as "
            rf"non-equivalent: all {sum(se_rej['closed'].get(x, 0) for x in ('equivalent', 'non_equivalent'))} rejects "
            rf"through a refuted closed equivalence and {se_rel['reject:component']} of the "
            rf"{sum(se_rej['component'].get(x, 0) for x in ('equivalent', 'non_equivalent'))} that rest on component goals"),
         "SemantEq rejects"),
        (ws(rf"Of the {len(kept)} they keep equivalent, {sum(k['direction'] == 'vacuity' for k in kept)} are "
            rf"vacuity-only"), "SemantEq kept"),
        (ws(rf"Of the {se['component_not_vacuity']['n']} component rejects that are not vacuity-only, "
            rf"{se['component_not_vacuity']['relabelled']} are relabelled"), "SemantEq non-vacuity"),
        (ws(rf"Of our {opus[3]} accepts they relabel {len(se['accepts_relabelled'])}, all Artin 2.8.6")
         if {a["exercise"] for a in se["accepts_relabelled"]} == {"Artin_exercise_2_8_6"} else r"(?!)", "SemantEq accepts"),
        (ws(rf"of the {sum(se_rel.values())} pairs they relabel that we cover, we reject "
            rf"{se_rel['reject:component'] + se_rel['reject:closed']}, accept {se_rel['accept']} and leave "
            rf"{se_rel['residual']} \\V\{{residual\}} and {se_rel['unknown']} \\V\{{unknown\}}"), "SemantEq reverse"),
        (ws(rf"relabels {se_rel['reject:component'] + se_rel['reject:closed']} of our {opus[7]} rejects there as "
            rf"non-equivalent"), "contributions, SemantEq"),
        (ws(r"\(1135 and 358; their proof audit certifies 358 in both directions") if
         [k["row_id"] for k in kept if k["audit_both"]] == ["pnv-test-358"]
         and {"pnv-test-1135", "pnv-test-358"} <= {k["row_id"] for k in kept} else r"(?!)", "SemantEq artefacts"),
        (r"no pair is\s+\\V\{off-domain\}" if not (dist["U"].get("off_domain") or dist["F"].get("off_domain"))
         else r"(?!)", "no off-domain on the full set"),
        (rf"closed equivalence accepts {round(100 * tac[0] / 694)}\\% of the unfaithful pairs with\s+fixed tactics "
         rf"and {round(100 * opus[0] / 694)}\\%", "abstract, closed FA"),
        (rf"from {round(100 * bud[0][0] / 694)}\\% to {round(100 * bud[3][0] / 694)}\\%", "abstract, budget"),
        (rf"FA {beq[0]}, acc {beq[1]}", "BEq+ row of tab:full"),
        (rf"false accepts are 108 with DeepSeek and {opus[0]}\s+\({round(100 * opus[0] / 694)}\\%\) with Opus",
         "closed FA, Opus, full set"),
        (rf"accepted equivalent pairs are {tac[1]} with tactics and {opus[1]} with Opus", "closed acc"),
        (rf"from 12\s+to {bud[1][0]}, {bud[2][0]} and {bud[3][0]} of 694 \({round(100 * bud[3][0] / 694)}\\%\)",
         "budget, closed FA"),
        (rf"Our false accepts go from {bud[0][2]} to {bud[3][2]}", "budget, our FA"),
        (rf"from 1 to {bud[3][4]}\.", "budget, residual FA"),
        (rf"{cl['only_first']} inequivalent pairs are accepted only by closed equivalence\s+and none only",
         "McNemar FA"),
        (rf"cost of {ca['only_first']} against {ca['only_second']}\s+equivalent", "McNemar acc"),
        (rf"{bq['only_second']} accepted only by\s+us and {bq['only_first']} only by BEq\+", "vs BEq+"),
        (rf"\({opus[5]} faithful against {opus[4]}\s+unfaithful pairs with Opus, against {opus[1]} and {opus[0]}",
         "residual precision"),
        (rf"stay at {tac[2]}--{opus[2]} of 694", "our FA range"),
        (rf"rejects {opus[7]} of 446", "faithful rejects, Opus"),
        (rf"from {tac[6]} to {opus[6]} on\s+inequivalent", "certified rejects U"),
        *((rf"{thousands(o[5])}\s+calls\s+and\s+{o[6]}M\s+tokens\s+against\s+{thousands(c[0])}\s+and\s+{c[1]}M,"
           rf"\s+with\s+{o[8]}\s+against\s+{c[3]}", f"cost, {name}")
          for name, o, c in (("Opus", exp["tab:cost"][2], exp["tab:cost"][0]),
                             ("DeepSeek", exp["tab:cost"][5], exp["tab:cost"][3]))),
        (rf"We accept {red['accept']}, reject {red['reject']} with certificates \({red_rew} of them rewarded by closed "
         rf"equivalence\), and\s+return \\V\{{residual\}} for {red['residual']} and \\V\{{unknown\}} for {red['unknown']}",
         "K13 red team"),
        (rf"{sep[0]} inequivalent pairs rejected with closed equivalence undecided, {sep[1]} the other way",
         "separation, tab:theory"),
    ]


def main_claims(exp: dict) -> list[tuple[str, str]]:
    """Numbers of the main-result paragraphs of sec:measure that are functions of the checked tables."""
    from h2_audit import direction
    ws = lambda t: t.replace(" ", r"\s+")
    full, sw, bud, cost = exp["tab:full"], exp["tab:sweep"], exp["tab:budget"], exp["tab:cost"]
    rp = exp["tab:repr"]
    tac, qwen, mini, ds, opus = full
    nU = sum(not p["label"] for p in load(D / "g5" / "g1_results_claude-opus-5.5.json"))
    sub_fa = [sw[i][0] for i in (3, 4, 5, 6)]
    pnv_fa = [sw[i][0] for i in (10, 11, 12, 13)]
    ours = [r[2] for r in full]
    res_u, res_f = [r[4] for r in full], [r[5] for r in full]
    g5 = load(D / "g5" / "g1_results_claude-opus-5.5.json")
    k3 = json.loads((D / "k3_direction.json").read_text(encoding="utf-8"))["g5"]["pairs"]
    frej = [p for p in g5 if p["label"] and verdict(p) == "reject"]
    dirs = Counter("closed_only" if p["verdict"] == "unknown" else direction(k3.get(p["row_id"]), p.get("closed"))
                   for p in frej)
    cand_false = dirs["cand_false"] + dirs["closed_only"]
    false_side = cand_false + dirs["ref_false"] + dirs["one_false"]
    return [
        (ws(rf"{tac[0]} false accepts of {nU} with tactics alone and with GPT-4.1-mini, {qwen[0]} with Qwen")
         if mini[0] == tac[0] else r"(?!)", "paradox: weak provers"),
        (ws(rf"{round(opus[0] / tac[0])} times the false accepts at {opus[1] / tac[1]:.1f} times the recall"),
         "paradox: ratio"),
        (ws(rf"closed false accepts are {sub_fa[0]}, {sub_fa[1]}, {sub_fa[2]} and {sub_fa[3]} of 150, and {pnv_fa[0]}, "
            rf"{pnv_fa[1]}, {pnv_fa[2]} and {pnv_fa[3]} of 75"), "paradox: sweep"),
        (ws(rf"stay at {min(ours)}--{max(ours)} of {nU} \({100 * min(ours) / nU:.1f}--{100 * max(ours) / nU:.1f}\\%\)"),
         "paradox: our FA across models"),
        (ws(rf"{min(res_u)} to {max(res_u)} false against {min(res_f)} to {max(res_f)} faithful"), "paradox: residual"),
        (ws(rf"into \${false_side}\+{dirs['vacuity']}\+{dirs['direction_only']}\$\. In {false_side} of them one of the "
            rf"two statements is certified false: in \${cand_false}\+{dirs['ref_false']}\$ of these also which one, in the "
            rf"other {dirs['one_false']} not\. For {cand_false}, closed equivalence is refuted"),
         "paradox: directions of the equivalent rejects"),
        (ws(rf"{dirs['closed_only']} of them are rejects only through this refutation"), "paradox: closed-only rejects"),
        (ws(rf"For {dirs['ref_false']}, \\texttt\{{npimp\}} and \\texttt\{{rs\}} certify"), "paradox: reference false"),
        (ws(rf"{dirs['vacuity']} rejects are vacuity-only"), "paradox: vacuity-only"),
        (ws(rf"The remaining {dirs['direction_only']} have a proved direction but no"), "paradox: direction only"),
        (ws(rf"The second repair round adds {bud[3][0] - bud[2][0]} closed false accepts against {bud[3][1] - bud[2][1]} "
            rf"closed accepts of equivalent pairs"), "budget: second repair"),
        (ws(rf"\({bud[2][0]} here, {opus[0]} in Table"), "budget: replay vs full"),
        (ws(rf"closed false accepts {bud[4][0]}, {bud[5][0]}, {bud[6][0]} and {bud[7][0]}, ours {bud[4][2]}, {bud[5][2]}, "
            rf"{bud[6][2]} and {bud[7][2]}"), "budget: DeepSeek"),
        (ws(rf"the false accepts are {bud[0][2]} against {bud[0][0]}"), "cost: tactics"),
        (ws(rf"the closed check at {cost[0][1]}M tokens accepts {cost[0][4]} equivalent pairs, ours at {cost[2][6]}M "
            rf"accepts {cost[2][9]} and returns \\V\{{residual\}} on {bud[3][5]} more"), "cost: coverage"),
        (ws(rf"no false accept under either prover \(at most {100 * wilson(0, 150)[1]:.1f}\\% of the 150 at 95\\% "
            rf"confidence\)") if exp["tab:g1"][3][0] == exp["tab:g1"][4][0] == 0 else r"(?!)", "subset: zero FA bound"),
        (ws(rf"leaves the canonical form unchanged in {rp[0][1]} of {rp[0][0]} cases, while conjoined hypotheses "
            rf"need conjunct reordering in {rp[1][2]} of {rp[1][0]} and account for {rp[1][4]} of the "
            rf"{sum(r[4] for r in rp)} open ones"), "tab:repr prose"),
    ]


def front_claims(exp: dict) -> list[tuple[str, str]]:
    """Sizes of the data sets wherever they occur, and the numbers of the abstract and introduction."""
    ws = lambda t: t.replace(" ", r"\s+")
    g5 = load(D / "g5" / "g1_results_claude-opus-5.5.json")
    nU, nF = sum(not p["label"] for p in g5), sum(p["label"] for p in g5)
    sub = load(D / "g1_results.json")
    pnv = load(D / "g4_results.json")
    se = [json.loads(l) for l in (D / "ext" / "semanteq_pnv_test_verdicts.jsonl").read_text(encoding="utf-8").splitlines()]
    full, bud = exp["tab:full"], exp["tab:budget"]
    tac, opus = full[0], full[4]
    ours_fa = [row[2] for row in bud[:4]]
    lo, hi = wilson(opus[0], nU)
    pub_eq = [r for r in se if r["published_equivalent"]]
    adj_eq = [r for r in se if r["adjudicated_equivalent"]]
    s_acc = [r for r in se if r["semanteq_accept"]]
    s_prec = sum(r["adjudicated_equivalent"] for r in s_acc) / len(s_acc)
    return [
        (rf"(?<![\d.]){len(g5):,}(?![\d])", "size: full set"),
        (rf"(?<![\d.]){nU}(?![\d])", "size: inequivalent pairs of the full set"),
        (rf"(?<![\d.]){nF}(?![\d])", "size: equivalent pairs of the full set"),
        (rf"(?<![\d.,]){len(sub)}-pair", "size: subset"),
        (rf"(?<![\d.]){len(pnv)}(?=\s+ProofNet-Verified|\s+ProofNet\\#\s+statements)", "size: ProofNet-Verified"),
        (ws(rf"false accepts stay at {min(ours_fa)}--{max(ours_fa)} of {nU}"), "abstract: our FA across budgets"),
        (ws(rf"ours stay at {min(ours_fa)}--{max(ours_fa)}, at fewer model calls"), "contributions: our FA across budgets"),
        (ws(rf"closed false accepts rise from {100 * tac[0] / nU:.1f}\\% with tactics to {round(100 * opus[0] / nU)}\\% "
            rf"\(95\\% interval {100 * lo:.0f}--{100 * hi:.0f}\\%\)"), "contributions: closed FA"),
        (ws(rf"from {bud[0][0]} to {bud[3][0]} \({round(100 * bud[3][0] / nU)}\\%\) within one model"),
         "contributions: closed FA within one model"),
        (ws(rf"reports {100 * s_prec:.0f}\\% precision on the ProofNetVerif test split with "
            rf"{100 * sum(r['published_equivalent'] for r in s_acc) / len(pub_eq):.1f}\\% recall under the published "
            rf"labels and {100 * sum(r['adjudicated_equivalent'] for r in s_acc) / len(adj_eq):.1f}\\% under"),
         "contributions: SemantEq precision and recall"),
    ]


def audit_claims() -> list[tuple[str, str]]:
    """Numbers of the blind audit (sec:blind), from data/real/h2_scores.json and the two answer files."""
    import h2_audit
    import h2_tex
    if not h2_tex.SCORES.exists():
        return []
    s = json.loads(h2_tex.SCORES.read_text(encoding="utf-8"))
    ws = lambda t: t.replace(" ", r"\s+")
    agreed = lambda r: r.get("yes", 0) + r.get("no", 0)
    kb, fr, fa = s["kappa_between"], s["full_faithful_reject"], s["full_unfaithful_local_accept"]
    k1 = [f"{s[f'g_kappa_vs_first_{i}']['kappa']:.2f}" for i in (0, 1)]
    k2 = [f"{s[f'g_kappa_vs_first_{i}_ref_ok']['kappa']:.2f}" for i in (0, 1)]
    cand = s["map_rejects"]["dir"]["cand_false"]
    fa_no = sum(r.get("no", 0) for r in s["map_accepts"]["fa"].values())
    lk = s["location_vs_kind"]
    j = s["strict_rejects_rewarded_all"]
    op = {k: s[f"open_picks_{k}"] for k in ("closed", "judge_opus_ref", "ours")}
    fl, fu, ce = s["full_faithful_local_accept"], s["full_unfaithful_reject"], s["control_equivalent"]
    items = json.loads(h2_audit.ITEMS.read_text(encoding="utf-8"))
    rows = {it["key"]: it["sheet_item"] for it in items}
    ann = [h2_audit.read(str(D / f"h2_annot_{x}.csv")) for x in "AB"]
    # the canonicalization artefacts named in sec:blind: both annotators must judge each candidate faithful
    artefacts = sum(all(a[rows[k]]["faithful"] == "yes" for a in ann)
                    for k in ("pnv-test-1135", "pnv-test-358", "pnv-test-310"))
    word = lambda n: ["no", "one", "two", "three", "four", "five", "six", "seven"][n]
    kappa = f"{kb['kappa']:.2f}"
    pct = lambda r: (f"{100 * r.get('no', 0) / agreed(r):.0f}\\\\%, 95\\\\% interval {100 * r['ci95'][0]:.0f}--"
                     f"{100 * r['ci95'][1]:.0f}\\\\%")
    ci = lambda r: f"{100 * r['ci95'][0]:.0f}--{100 * r['ci95'][1]:.0f}\\\\%"
    notes = [{int(r["item"]): r["note"] for r in csv.DictReader(open(D / f"h2_annot_{x}.csv", encoding="utf-8-sig"))}
             for x in "AB"]
    unqualified = re.compile(r"未限定|未知|写法无效|类型推断错误")
    names = sum(ann[0][r]["faithful"] == "no" and bool(unqualified.search(notes[0][r])) and ann[1][r]["faithful"] == "yes"
                for r in ann[0])
    share = [100 * x["agree"] / x["n"] for x in lk]
    import k19_rules
    k19 = k19_rules.compute()
    tg = k19["targets"]
    k19_ok = (tg["pnv-test-310"]["new"] == tg["pnv-test-1135"]["new"] == "accept"
              and [tg[k]["new_loc"] for k in ("pnv-test-167", "pnv-test-595")] == ["H", "H"]
              and tg["pnv-test-365"]["new"] == "unknown" and not k19["new_false_accepts"]
              and k19["flips"].get("U:accept->reject", 0) + k19["flips"].get("U:accept->unknown", 0) == 2
              and set(k19["equivalent_rejects"]["no_longer_reject"]) <= {"accept|yes", "unknown|yes"}
              and sum(k19["equivalent_rejects"]["no_longer_reject"].values()) == 3
              and len(k19["lost_faithful_accepts"]) == 3)
    return [
        (ws(rf"They change the goals of {k19['changed']} of the 1,140 pairs") if k19_ok else r"(?!)",
         "K19 rules from the audit"),
        (ws(rf"agree on {kb['agree']} of the {kb['n']} statements \(\$\\kappa={kappa}\$\)"), "audit: kappa"),
        (ws(rf"at \$\\kappa={k1[0]}\$ and \${k1[1]}\$, and at \${k2[0]}\$ and \${k2[1]}\$ without"),
         "audit: kappa against the first classification"),
        (ws(rf"It concerns {names} statements, on all of which the other annotator answered ``faithful''"),
         "audit: unqualified names"),
        (ws(rf"matches it in {min(share):.0f}--{max(share):.0f}\\% of the cases"), "measure: location against kind"),
        (ws(rf"finds {j.get('no', 0)} of the {agreed(j)} rewarded strict rejects it can judge unfaithful"),
         "select: audit"),
        (ws(rf"and by this rate an unfaithful one for about {2.8 * j.get('no', 0) / agreed(j):.1f}\\%"),
         "select: unfaithful picks at n=24"),
        (ws(rf"agree on {agreed(fr)} of the {fr['distinct']} statements behind the {fr['sampled']} component-goal "
            rf"rejects. {fr.get('no', 0)} candidates are unfaithful"), "audit: rejects"),
        (ws(rf"Of the {fr.get('yes', 0)} faithful ones"), "audit: faithful rejects"),
        (ws(rf"{cand.get('no', 0)} of the {cand['items']} candidates certified false are judged unfaithful"),
         "audit: candidates certified false"),
        (ws(rf"matches it in {lk[0]['agree']} of {lk[0]['n']} cases for the first annotator and {lk[1]['agree']} of "
            rf"{lk[1]['n']} for the second"), "audit: location against kind"),
        (ws(rf"Of the {fa['distinct']} statements behind the {fa['sampled']} false accepts, the annotators agree on "
            rf"{'all ' + str(agreed(fa)) if agreed(fa) == fa['distinct'] else agreed(fa)}\. "
            rf"{word(fa.get('no', 0)).capitalize()} are unfaithful"), "audit: false accepts"),
        (ws(rf"{word(fa.get('yes', 0)).capitalize()} are faithful, so their label is wrong"),
         "audit: label errors among false accepts"),
        (ws(rf"A reader thus confirms {fa_no} of the {fa['sampled']} false accepts"), "audit: confirmed false accepts"),
        (ws(rf"{fl['sampled']} sampled accepts of equivalent pairs with an informative conclusion, all "
            rf"{fl.get('yes', 0)} are judged faithful; of {fu['sampled']} sampled rejects of inequivalent pairs, "
            rf"{fu.get('no', 0)} are judged unfaithful and {fu.get('disagree', 0)} is split")
         if fl.get("yes") == fl["sampled"] and not fu.get("yes") else r"(?!)", "audit: controls"),
        (ws(rf"{ce.get('yes', 0)} of the {sum(ce.values())} candidates certified equivalent to the corrected reference "
            rf"are judged faithful and {ce.get('disagree', 0)} are split") if not ce.get("no") else r"(?!)",
         "audit: certified-equivalent controls"),
        (ws(rf"Of the {j['distinct']} rewarded strict rejects, the annotators agree on {agreed(j)} and judge "
            rf"{j.get('no', 0)} unfaithful \({pct(j)}\)"), "audit: rewarded strict rejects"),
        (ws(rf"{op['closed'].get('no', 0)} of the {agreed(op['closed'])} agreed picks of closed equivalence are "
            rf"unfaithful \({pct(op['closed'])}\), {op['judge_opus_ref'].get('no', 0)} of the "
            rf"{agreed(op['judge_opus_ref'])} of the Opus judge with the reference, and {op['ours'].get('no', 0)} of the "
            rf"{agreed(op['ours'])} of our accept \({100 * op['ours'].get('no', 0) / agreed(op['ours']):.0f}\\%, "
            rf"{ci(op['ours'])}\)"),
         "audit: open picks"),
        (ws(rf"the {fr['sampled']} component-goal rejects among them rest on {fr['distinct']} distinct statements; of "
            rf"the {agreed(fr)} distinct statements on which the annotators agree, {fr.get('no', 0)} are unfaithful "
            rf"candidates, {fr.get('yes', 0) - artefacts} faithful candidates whose reference says something else and "
            rf"{artefacts} canonicalization artefacts, and a reader confirms {fa_no} of our {fa['sampled']} false "
            rf"accepts \({fa.get('no', 0)} of {fa['distinct']} distinct statements\)"), "contributions: audit"),
        (ws(rf"agree on {round(100 * kb['agree'] / kb['n'])}\\% of the statements \(\$\\kappa={kappa}\$\)"),
         "limitations: audit"),
        (ws(rf"which judges {fr.get('no', 0)} of the {agreed(fr)} statements it agrees on unfaithful and finds "
            rf"{word(artefacts)} canonicalization artefacts"), "measure: audit"),
    ]


# Spans that hold names or code, not results: masked before numbers are inventoried.
NOT_RESULTS = [r"(?<!\\)%.*", r"\\(?:ref|label|cite|eqref|url|input|IfFileExists)\{[^}]*\}", r"\\texttt\{(?:[^{}]|\{[^{}]*\})*\}",
               r"\$[^$]*\$", r"\\\[.*?\\\]", r"\\begin\{(tabular|lstlisting|verbatim)\}.*?\\end\{\1\}",
               r"(?:Dummit--Foote|Herstein|Artin|Rudin|Pugh|Munkres|Axler|Ireland--Rosen|Shakarchi|Putnam)"
               r"(?:~|\s)+(?:\d{4}\s+[AB]\d|\d+(?:\.\d+)+[a-z]?)",
               r"(?:pairs?|candidates?|items?|row)\s+\d+(?:(?:,\s*|\s+and\s+)\d+)*",
               r"(?:Opus|GPT|Qwen|DeepSeek|Gemini|Astra|Lean|Mathlib|ProofNet|miniF2F|PutnamBench|T\$\^2\$)[-~\s]?"
               r"(?:[A-Za-z]*[-.]?\d[\w.\-]*)?",
               r"\b(?:T|E|K|G|D|H|F)\d+(?:--[A-Z]?\d+)?\b", r"\b(?:19|20)\d\d(?:-\d\d-\d\d)?\b", r"\\section\{[^}]*\}"]


def coverage(tex: str, claims: list[tuple[str, str]], exp: dict) -> dict:
    """Numbers in the body of main.tex that no checked table and no prose claim covers."""
    end = tex.find("\\begin{thebibliography}")
    body = tex[:end]
    masked = body
    for pat in NOT_RESULTS:
        multiline = pat.startswith((r"\\\[", r"\\begin"))
        masked = re.sub(pat, lambda m: re.sub(r"[^\n]", " ", m.group(0)), masked, flags=re.S if multiline else 0)
    spans = [(m.start(), m.end()) for pat, _ in claims for m in re.finditer(pat, body)]
    for label in exp:
        if label.startswith("tab:") and (i := body.find(f"\\label{{{label}}}")) >= 0:
            spans.append((body.rfind("\\begin{table", 0, i), i))
    covered = lambda a, b: any(s <= a and b <= e for s, e in spans)
    sections = [(m.start(), m.group(1)) for m in re.finditer(r"\\(?:section|paragraph)\{([^}]*)\}", body)]
    out: dict[str, list] = {}
    n = 0
    for m in re.finditer(r"(?<![\w.\-])\d+(?:\{,\}\d{3}|,\d{3})*(?:\.\d+)?(?![\w])", masked):
        n += 1
        if covered(m.start(), m.end()):
            continue
        sec = next((name for pos, name in reversed(sections) if pos < m.start()), "front")
        line = body.count("\n", 0, m.start()) + 1
        ctx = re.sub(r"\s+", " ", body[max(0, m.start() - 50):m.end() + 30])
        out.setdefault(sec, []).append({"line": line, "number": m.group(0), "context": ctx})
    return {"numbers": n, "uncovered": sum(len(v) for v in out.values()), "by_section": out}


# One definition per quantity: what is counted, its denominator, and which labels decide right and wrong.
DEFINITIONS = {
    "full set": "the 1,140 labelled ProofNetVerif test pairs whose statements elaborate in our Mathlib; 694 "
                "labelled inequivalent (U), 446 labelled equivalent (F); published ProofNetVerif labels",
    "subset": "300 pairs of the full set stratified 150 / 150 (published labels); experiments too costly for the full set",
    "ProofNet-Verified": "317 ProofNet# problems with the corrected references of ProofNet-Verified; 75 originals "
                         "unfaithful, 242 faithful by its own labels",
    "shared SemantEq set": "the 1,135 full-set pairs that SemantEq-Eval also scores; published labels and SemantEq's "
                           "adjudicated labels (102 originally equivalent pairs relabelled inequivalent)",
    "false accept (FA)": "an accept of a pair labelled inequivalent under the label set named with it; published "
                         "labels unless stated",
    "false reject": "a reject of a pair labelled equivalent under the named labels; a certified formal difference, "
                    "not a proof of unfaithfulness",
    "decided": "accept, reject or off-domain with both regrouping certificates; residual is reported separately "
               "and counted as decided only where stated",
    "residual": "a proof of component equivalence on an alignment that ends early; never an accept",
    "located reject": "a reject whose certificate is a component goal (nhyp or ncin) on telescopes with a nonempty "
                      "prefix or a hoisted hypothesis; a mechanical location, counted per pair",
    "component-goal reject": "a reject decided by a component goal rather than by a refuted closed equivalence; "
                             "counted per pair (43 on labelled-equivalent pairs, resting on 30 distinct statements)",
    "blind audit": "249 items shown as 226 distinct statements; a verdict counts only when both annotators agree; "
                   "rates count distinct statements",
    "selection": "317 problems, 7,608 draws, 2,879 distinct candidates; classes from kernel facts against the "
                 "corrected reference",
    "reference error": "a benchmark statement that the probes flag and that is unfaithful to its informal text "
                       "after review; counted per statement",
}


UNITS = ROOT / "paper" / "units.tex"


def definition_errors() -> list[str]:
    """The sizes stated in DEFINITIONS, recomputed from the data."""
    g5 = load(D / "g5" / "g1_results_claude-opus-5.5.json")
    sub = load(D / "g1_results.json")
    pnv = load(D / "g4_results.json")
    se = [json.loads(l) for l in (D / "ext" / "semanteq_pnv_test_verdicts.jsonl").read_text(encoding="utf-8").splitlines()]
    shared = {f"pnv-test-{int(re.match(r'pnv:test:(\d+):', r['id']).group(1))}" for r in se} & {p["row_id"] for p in g5}
    relab = sum(r["published_equivalent"] and not r["adjudicated_equivalent"] for r in se)
    items = json.loads((D / "h2_items.json").read_text(encoding="utf-8"))
    fr = json.loads((D / "h2_scores.json").read_text(encoding="utf-8"))["full_faithful_reject"]
    d1 = json.loads((D / "d1_candidates.json").read_text(encoding="utf-8"))
    facts = {"1,140": len(g5), "694": sum(not p["label"] for p in g5), "446": sum(p["label"] for p in g5),
             "300": len(sub), "150 / 150": (sum(p["label"] for p in sub), sum(not p["label"] for p in sub)),
             "317": len(pnv), "75": sum(p["relation"] != "faithful" for p in pnv),
             "242": sum(p["relation"] == "faithful" for p in pnv), "1,135": len(shared), "102": relab,
             "249": len(items), "226": len({it["sheet_item"] for it in items}), "43": fr["sampled"],
             "30": fr["distinct"], "7,608": len(d1["draws"]), "2,879": len(d1["candidates"])}
    want = {"1,140": 1140, "694": 694, "446": 446, "300": 300, "150 / 150": (150, 150), "317": 317, "75": 75,
            "242": 242, "1,135": 1135, "102": 102, "249": 249, "226": 226, "43": 43, "30": 30, "7,608": 7608,
            "2,879": 2879}
    text = " ".join(DEFINITIONS.values())
    errs = [f"definitions: {k} is {facts[k]} in the data" for k in want if facts[k] != want[k]]
    errs += [f"definitions: '{k}' does not occur" for k in want if k not in text]
    return errs


def render_units() -> str:
    esc = lambda s: s.replace("#", "\\#").replace("%", "\\%")
    rows = [f"{esc(k)} & {esc(v)}\\\\" for k, v in DEFINITIONS.items()]
    return "\n".join(["% generated by scripts/real/paper_check.py from DEFINITIONS; do not edit",
                      "\\begin{table}[h]", "\\centering\\footnotesize",
                      "\\begin{tabular}{p{0.2\\linewidth}p{0.74\\linewidth}}", "\\toprule", "quantity & definition\\\\",
                      "\\midrule", *rows, "\\bottomrule", "\\end{tabular}",
                      "\\caption{Units, denominators and label versions. Every number in the main tables and in the "
                      "checked prose is computed from the stored results under these definitions by "
                      "\\texttt{paper\\_check.py}, which also writes a machine-readable list of the checked numbers "
                      "(\\texttt{paper\\_manifest.json}) and of the numbers it does not yet check "
                      "(\\texttt{paper\\_coverage.json}).}", "\\label{tab:units}", "\\end{table}", ""])


def manifest(tex: str, exp: dict, claims: list[tuple[str, str]], cov: dict) -> dict:
    """Machine-readable list of every checked number: table cells and prose claims with their lines."""
    line = lambda pos: tex.count("\n", 0, pos) + 1
    prose = []
    for pat, what in claims:
        hits = [{"line": line(m.start()), "text": re.sub(r"\s+", " ", m.group(0))[:200]} for m in re.finditer(pat, tex)]
        prose.append({"claim": what, "occurrences": hits})
    return {"definitions": DEFINITIONS,
            "tables": {k: v for k, v in exp.items() if k.startswith("tab:")},
            "prose": prose,
            "coverage": {"numbers": cov["numbers"], "uncovered": cov["uncovered"],
                         "uncovered_by_section": {s: len(v) for s, v in cov["by_section"].items()}}}


def bench_claims() -> list[tuple[str, str]]:
    """The benchmark reference errors of sec:audit, from data/real/bench_errors.csv (one row per error)."""
    import csv
    ws = lambda t: t.replace(" ", r"\s+")
    rows = list(csv.DictReader((D / "bench_errors.csv").open(encoding="utf-8")))
    hard = [r for r in rows if r["evidence"] in ("proved_false", "proved_vacuous")]
    by = lambda bench, rs: sum(r["benchmark"] == bench for r in rs)
    pn = [r for r in rows if r["benchmark"] == "ProofNet#"]
    pn_neg = sum(r["evidence"] == "proved_false" for r in pn)
    pn_vac = sum(r["evidence"] == "proved_vacuous" for r in pn)
    in_pnv = sum("unfaithful" in r["independent_record"] for r in pn)
    putnam_hard = [r["statement"] for r in hard if r["benchmark"] == "PutnamBench"]
    return [
        (ws(rf"evidence for {len(rows)} errors in ProofNet\\#, miniF2F and PutnamBench, {len(hard)} of them proved "
            rf"false or vacuous"), "abstract: benchmark errors"),
        (ws(rf"The {len(rows)} errors rest on evidence of two strengths\. For {len(hard)}, Lean"), "audit: evidence strengths"),
        (ws(rf"{pn_neg} ProofNet\\# negations"), "audit: ProofNet# negations"),
        (ws(rf"the {pn_vac} ProofNet\\# statements whose\s+hypotheses the \\texttt\{{vacuous\}} probe refutes, "
            rf"{by('miniF2F', hard)} miniF2F statements and") if putnam_hard == ["putnam_1991_a6"] else r"(?!)",
         "audit: vacuous and competition"),
        (ws(rf"For the other {len(rows) - len(hard)} the kernel"), "audit: degeneracies"),
        (ws(rf"{in_pnv} of our {len(pn)} ProofNet\\# errors are also in ProofNet-Verified"), "audit: in ProofNet-Verified"),
        (ws(rf"The {len(pn)} ProofNet\\# reference errors"), "tab:refs caption"),
        (ws(rf"Table~\\ref\{{tab:refs\}} lists the {len(pn)} errors"), "app:refs count"),
    ]


def recheck_claims() -> list[tuple[str, str]]:
    """The standalone recheck and the replay of app:repro (k5_standalone_audit.py, k20_dump.py)."""
    import gzip
    ws = lambda t: t.replace(" ", r"\s+")
    k5 = lambda f: json.loads((D / f).read_text(encoding="utf-8"))["summary"]
    first, post = k5("k5_standalone_audit.json"), k5("k5_standalone_post.json")
    n = lambda c: sum(c.values())
    exported = sum(1 for _ in gzip.open(D / "accepted_proofs.jsonl.gz", "rt", encoding="utf-8"))
    k20 = json.loads((D / "k20_dump.json").read_text(encoding="utf-8"))
    replay_ok = (all(r["exit"] == 0 for r in k20.values())
                 and k20["k11:claude-opus-5.5"]["tables_equal"] and k20["k11:deepseek-v4.1-flash"]["tables_equal"]
                 and all(k20[k]["same_verdicts"] == k20[k]["pairs"] for k in ("g5:qwen3.8-27b-nothink", "g5:gpt-4.1-mini")))
    first_ok = n(first["population"]) == n(first["checked"]) == n(first["passed"]) and not first["failures"]
    post_ok = n(post["checked"]) == n(post["passed"]) and not post["failures"]
    later = (rf"and the {n(post['checked'])} checked at the time of writing passed as well" if not post["complete"]
             else r"and all of them passed")
    return [
        (ws(rf"tables are {exported:,} distinct proofs") if exported == n(first["population"]) + n(post["population"])
         else r"(?!)", "recheck: exported proofs"),
        (ws(rf"All {n(first['passed']):,} of the first recheck passed") if first_ok else r"(?!)", "recheck: first"),
        (ws(rf"The {n(post['population']):,} that later runs added") + r"[\s\S]{0,260}?" + ws(later)
         if post_ok else r"(?!)", "recheck: later runs"),
        (ws(r"reproduced Table~\\ref\{tab:budget\} for both models and all 1,140 verdicts of Qwen and GPT-4.1-mini")
         if replay_ok else r"(?!)", "replay"),
    ]


def main() -> int:
    sys.stdout.reconfigure(encoding="utf-8")
    tex = TEX.read_text(encoding="utf-8")
    exp = expected()
    errs = compare_tables(tex, exp)
    claims = (prose_claims(exp) + audit_claims() + front_claims(exp) + main_claims(exp) + bench_claims()
              + recheck_claims())
    for pat, what in claims:
        if not re.search(pat, tex):
            errs.append(f"prose: {what}: /{pat}/ not found")
    import h2_tex
    if h2_tex.OUT.exists() != h2_tex.SCORES.exists():
        errs.append("h2: paper/h2_results.tex and data/real/h2_scores.json must exist together")
    elif h2_tex.OUT.exists() and h2_tex.OUT.read_text(encoding="utf-8") != h2_tex.render(
            json.loads(h2_tex.SCORES.read_text(encoding="utf-8"))):
        errs.append("h2: paper/h2_results.tex is stale; run h2_tex.py")
    errs += definition_errors()
    if "--write-units" in sys.argv[1:]:
        UNITS.write_text(render_units(), encoding="utf-8")
    elif not UNITS.exists() or UNITS.read_text(encoding="utf-8") != render_units():
        errs.append("units: paper/units.tex is missing or stale; run paper_check.py --write-units")
    out = {"tables": exp, "distribution_opus_full": distribution()}
    (D / "paper_numbers.json").write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    cov = coverage(tex, claims, exp)
    (D / "paper_coverage.json").write_text(json.dumps(cov, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    (D / "paper_manifest.json").write_text(json.dumps(manifest(tex, exp, claims, cov), indent=1, ensure_ascii=False)
                                           + "\n", encoding="utf-8")
    print(f"{cov['numbers']} result numbers in the body, {cov['uncovered']} not covered by a check "
          f"(data/real/paper_coverage.json)")
    for e in errs:
        print("MISMATCH", e)
    tabs = {k: v for k, v in exp.items() if k.startswith("tab:")}
    print(f"{len(tabs)} tables, {sum(len(r) for r in tabs.values())} rows and {len(claims)} prose "
          f"numbers checked; {len(errs)} mismatches")
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main())
