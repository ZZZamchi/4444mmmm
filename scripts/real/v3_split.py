#!/usr/bin/env python3
"""v3 development (test split only): regrouping certificates for the pairs that lack them.

The full-set run (G5, Opus) leaves 97 pairs `unknown` because `split_r` or `split_s` is unproved; E2
only completed certificates of decided pairs, so these were never given the second tactic tier.
This tries, on every missing regrouping goal, `SPLIT_TAC2` and then `SPLIT_TAC3`, which first
destructures a conjunction of hypotheses so that Prop-valued instances moved into it by
canonicalization become local instances again, then applies the other side. Lean only, no API.
Nothing in the G5 results is modified; the outcome is `data/real/v3/split.json`.

Usage: v3_split.py
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import g1_full as g1
from f7_component import SPLIT_TAC2
from paper_check import D, load, unknown_cause, verdict
from realdata import proofnetverif
from stmt import to_prop

OUT = D / "v3" / "split.json"
SPLIT_TAC3 = ("first | (constructor <;> intro h <;> intros <;> (try casesm* _ ∧ _) <;> "
              "(try simp only [true_implies, forall_const] at *) <;> apply h <;> "
              "repeat' (first | assumption | exact trivial | apply And.intro))")


def ok(v) -> bool:
    return v.ok and not v.uses_sorry


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    ps = load(D / "g5" / "g1_results_claude-opus-5.5.json")
    rows = {r.row_id: r for r in proofnetverif("test")}
    bad = [p for p in ps if verdict(p) == "unknown" and unknown_cause(p) == "no_certificate"]
    stmt = {}
    for p in bad:
        r = rows[p["row_id"]]
        stmt[r.row_id] = (r, f2.normalize(to_prop(r.gold)), f2.normalize(to_prop(r.pred)))
    todo = [(p["row_id"], g) for p in bad for g in ("split_r", "split_s") if g not in (p.get("proved") or [])]
    print("pairs", len(bad), "open regrouping goals", len(todo), flush=True)
    found: dict[tuple, str] = {}
    for tag, tac in (("v3s2", SPLIT_TAC2), ("v3s3", SPLIT_TAC3)):
        res = g1.prove_items([((rid, g), (*stmt[rid], tac)) for rid, g in todo if (rid, g) not in found], tag)
        for k, v in res.items():
            if ok(v):
                found[k] = tag
        print(tag, "proved so far", len(found), flush=True)
    out = []
    for p in bad:
        proved = set(p.get("proved") or []) | {g for (rid, g) in found if rid == p["row_id"]}
        out.append({"row_id": p["row_id"], "label": p["label"], "closed": p.get("closed"),
                    "found": {g: found[(p["row_id"], g)] for g in ("split_r", "split_s") if (p["row_id"], g) in found},
                    "both": {"split_r", "split_s"} <= proved,
                    "new_verdict": verdict(p, proved=proved)})
    summary = {"pairs": len(bad), "open_goals": len(todo), "proved_goals": dict(Counter(found.values())),
               "pairs_with_both": sum(o["both"] for o in out),
               "new_verdicts": dict(Counter(f"{'F' if o['label'] else 'U'}:{o['new_verdict']}" for o in out))}
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps({"summary": summary, "pairs": out}, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
