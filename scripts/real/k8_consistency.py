#!/usr/bin/env python3
"""K8: contradiction audit of proved goal sets.

The kernel is sound and Lean + Mathlib is assumed consistent, so no pair can have both a goal
and its negation proved. A pair that does is evidence of a checker bug (a false `ok`). Checked
pairs of mutually exclusive goals:

    closed      fwd / nfwd, bwd / nbwd
    components  acc / nhyp, acc / ncin, acc / ncomp, cond / nhyp, cond / ncin
    direction   pimp / npimp            (k3_direction.json)
    pointwise   ptr / nptr, pts / npts, pfr / npfr, pfs / npfs   (k7_pointwise.json)

Usage: k8_consistency.py [DIR ...]   default: data/real and the round snapshots
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from runner import ROOT

D = ROOT / "data" / "real"
CLOSED = [("fwd", "nfwd"), ("bwd", "nbwd")]
COMP = [("acc", "nhyp"), ("acc", "ncin"), ("acc", "ncomp"), ("cond", "nhyp"), ("cond", "ncin")]
DIR = [("pimp", "npimp")]
PT = [("ptr", "nptr"), ("pts", "npts"), ("pfr", "npfr"), ("pfs", "npfs")]


def clashes(proved, pairs) -> list[tuple[str, str]]:
    s = set(proved or [])
    return [(a, b) for a, b in pairs if a in s and b in s]


def audit(d: Path) -> dict:
    out = {}
    for f in sorted(d.glob("g[14]_results*.json")):
        try:
            pairs = json.loads(f.read_text(encoding="utf-8"))["pairs"]
        except (KeyError, json.JSONDecodeError):
            continue
        bad = []
        for p in pairs:
            c = clashes(p.get("closed_proved"), CLOSED) + clashes(p.get("proved"), COMP)
            if c:
                bad.append((p["row_id"], c))
        out[f.name] = {"pairs": len(pairs), "contradictions": bad}
    for name, key, pairs_of in (("k3_direction.json", DIR, lambda v: v["proved"]),
                                ("k7_pointwise.json", PT, lambda v: v["proved"])):
        f = d / name
        if not f.exists():
            continue
        data = json.loads(f.read_text(encoding="utf-8"))
        for which, block in data.items():
            bad = [(rid, clashes(pairs_of(v), key)) for rid, v in block["pairs"].items() if clashes(pairs_of(v), key)]
            out[f"{name}:{which}"] = {"pairs": len(block["pairs"]), "contradictions": bad}
    return out


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    dirs = [Path(a) for a in sys.argv[1:]] or [D / "k2_round1", D / "k2_round2", D]
    for d in dirs:
        print(f"== {d.relative_to(ROOT) if d.is_relative_to(ROOT) else d}")
        for name, r in audit(d).items():
            n = len(r["contradictions"])
            print(f"  {name:45s} pairs {r['pairs']:4d}  contradictions {n}" + (f"  {r['contradictions'][:4]}" if n else ""))


if __name__ == "__main__":
    main()
