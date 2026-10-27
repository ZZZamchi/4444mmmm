"""Numbers of the full-set tables: tab:full, tab:levels (G5) and tab:hack (K10).

Reads the G5 results (data/real/g5/), the BEq+ run on the same pairs, the constancy (K7) and
triviality (K9) certificates and the K10 hacking run; runs no prover.

Usage: g5_tables.py        prints the tables and writes data/real/g5_tables.json
"""
import json
import math
import os
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from f7_component import classify
from k6_stats import accepted, is_local, local

D = Path("data/real")
G5 = D / "g5"
TIERS = ["qwen3.8-27b-nothink", "gpt-4.1-mini", "deepseek-v4.1-flash", "claude-opus-5.5"]
HACK_TIERS = ["tactics", "openai/gpt-4.1-mini", "anthropic/claude-opus-5.5"]
SPLITS = {"split_r", "split_s"}


def load(path):
    return json.load(open(path, encoding="utf-8"))


def certified(p):
    return SPLITS <= set(p.get("proved") or [])


def full_row(pairs):
    c = Counter()
    for p in pairs:
        lab = "F" if p["label"] else "U"
        a = accepted(p)
        c[f"n{lab}"] += 1
        c[f"closed{lab}"] += p["closed_acc"]
        c[f"acc{lab}"] += a
        c[f"local{lab}"] += a and is_local(p)
        c[f"reject{lab}"] += p["verdict"] == "reject" and certified(p)
    return dict(c)


def tab_full():
    f2 = {p["row_id"]: p for p in load(G5 / "f2_full.json")["pairs"]}
    base = load(G5 / "g1_results_claude-opus-5.5.json")["pairs"]
    rows = {"tactics": full_row([
        {**p, "verdict": classify(set(p.get("tactic") or [])), "proved": sorted(p.get("tactic") or []),
         "closed_acc": {"fwd", "bwd"} <= set(f2[p["row_id"]]["t1"])} for p in base])}
    for m in TIERS:
        f = G5 / f"g1_results_{m}.json"
        if f.exists():
            rows[m] = full_row([{**p, "closed_acc": p["closed"] == "proved"} for p in load(f)["pairs"]])
    return rows, base


def tab_levels(base):
    beq = {p["row_id"]: bool(p["beq_plus"]) for p in load(G5 / "b1_results.json")["pairs"]}
    k7 = load(D / "k7_pointwise.json")["g5"]
    k7 = k7.get("pairs", k7)
    k9 = load(D / "k9_trivial.json")["g5"]["pairs"]
    rules = {
        "closed": lambda p, x: p["closed"] == "proved",
        "ours_all": lambda p, x: x["acc"],
        "ours_local": lambda p, x: x["loc"],
        "ours_local_not_trivial": lambda p, x: x["loc"] and not x["triv"],
        "ours_local_not_trivial_not_constant": lambda p, x: x["loc"] and not x["triv"] and not x["const"],
        "beq_plus": lambda p, x: x["beq"],
        "beq_or_local_not_trivial": lambda p, x: x["beq"] or (x["loc"] and not x["triv"]),
        "beq_or_local_not_trivial_not_constant":
            lambda p, x: x["beq"] or (x["loc"] and not x["triv"] and not x["const"]),
    }
    dec = {r: {"FA": [], "acc": []} for r in rules}
    for p in base:
        x = {"acc": accepted(p), "loc": accepted(p) and is_local(p), "beq": beq.get(p["row_id"], False),
             "triv": bool(k9.get(p["row_id"], {}).get("logic", {}).get("flag")),
             "const": k7.get(p["row_id"], {}).get("class") == "collapsed"}
        lab = "acc" if p["label"] else "FA"
        for r, f in rules.items():
            dec[r][lab].append(bool(f(p, x)))
    out = {r: {lab: {"k": sum(v), "n": len(v), "wilson95": wilson(sum(v), len(v))} for lab, v in d.items()}
           for r, d in dec.items()}
    tests = {}
    for a, b in PAIRED:
        for lab in ("FA", "acc"):
            only_a = sum(x and not y for x, y in zip(dec[a][lab], dec[b][lab]))
            only_b = sum(y and not x for x, y in zip(dec[a][lab], dec[b][lab]))
            tests[f"{a} vs {b} [{lab}]"] = {"only_first": only_a, "only_second": only_b,
                                            "p_exact_mcnemar": mcnemar(only_a, only_b)}
    return out, tests


PAIRED = [("closed", "ours_all"), ("closed", "ours_local"), ("beq_plus", "ours_local"),
          ("ours_local", "ours_local_not_trivial"),
          ("ours_local_not_trivial", "ours_local_not_trivial_not_constant"),
          ("beq_plus", "ours_local_not_trivial_not_constant"), ("beq_plus", "beq_or_local_not_trivial_not_constant")]


def wilson(k, n, z=1.959964):
    if n == 0:
        return None
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return [round(max(0.0, c - h), 4), round(min(1.0, c + h), 4)]


def mcnemar(b, c):
    """Exact two-sided McNemar p-value on b and c discordant pairs."""
    n = b + c
    if n == 0:
        return 1.0
    tail = sum(math.comb(n, i) for i in range(min(b, c) + 1))
    return float(min(1, Fraction(2 * tail, 2 ** n)))


def tab_hack():
    d = load(D / "k10_hack.json")
    out = {}
    for kind in d["kinds"]:
        c = Counter()
        for p in (p for p in d["pairs"] if p["kind"] == kind):
            c["n"] += 1
            c["beq_plus"] += bool(p["beq_plus"])
            for t in HACK_TIERS:
                c[f"closed:{t}"] += p["tiers"][t]["closed"]
            v = p["tiers"][HACK_TIERS[-1]]["verdict"]
            v = "unknown" if v.endswith("_uncertified") else v
            if v == "accept" and not local(p["canon_info"]):
                v = "residual"
            c[f"ours:{v}"] += 1
            c["ours+triviality:rewarded"] += v == "accept" and not p["k9_flag"]
        out[kind] = dict(sorted(c.items()))
    return out


def main():
    full, base = tab_full()
    for row in full.values():
        for k in ("closed", "acc", "local"):
            row[f"{k}U_wilson95"] = wilson(row[f"{k}U"], row["nU"])
            row[f"{k}F_wilson95"] = wilson(row[f"{k}F"], row["nF"])
    levels, tests = tab_levels(base)
    res = {"full": full, "levels": levels, "paired_tests_opus": tests}
    if (D / "k10_hack.json").exists():
        res["hack"] = tab_hack()
    for name, t in res.items():
        print(f"== {name}")
        for k, v in t.items():
            print(f"  {k:40s} {v}")
    tmp = D / f"g5_tables.{os.getpid()}.tmp"
    tmp.write_text(json.dumps(res, indent=1), encoding="utf-8")
    os.replace(tmp, D / "g5_tables.json")


if __name__ == "__main__":
    main()
