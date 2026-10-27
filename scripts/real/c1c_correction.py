#!/usr/bin/env python3
"""C1c: certified correctness of FormalRx-CC model corrections.

In the `full` setting a FormalRx-CC model also writes `corrected_statement`, its own
`Intended`. We compare it with the gold intended definition using the C1 goals, with the gold
definition in the candidate slot, and only the tactic and bounded-search tiers (no LLM), so
the check is the same for every model:

    certified_correct   the two definitions are proved equivalent (ci and ic, or eq);
    certified_wrong     some separating goal is proved (nci, nic, neq or vac);
    unparseable         no single `def Intended…` with the gold argument types;
    unknown             otherwise.

Usage: c1c_correction.py            Writes data/real/c1c_results.json.
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from c1_formalrx import DEF_RE, SEARCH_GOALS, TAC, ok, pair_of, prove, relation, search_tac
from runner import ROOT

CCF = ROOT / "data" / "real" / "raw" / "papers" / "ccf"
DATA = CCF / "data" / "formalrx_cc_eval204.jsonl"
OUTPUTS = CCF / "results" / "model_outputs"
OUT = ROOT / "data" / "real" / "c1c_results.json"
SEPARATING = {"nci", "nic", "neq", "vac"}


def corrected(text: str, gold_head: str) -> str | None:
    text = re.sub(r"```(?:lean4?)?", "", str(text or "")).strip()
    defs = [d.strip() for d in re.split(r"(?m)^(?=def\s)", text) if d.strip().startswith("def ")]
    mine = [d for d in defs if re.match(rf"def\s+{gold_head}\b", d)]
    return mine[0] if len(mine) == 1 and DEF_RE.match(mine[0]) else None


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    rows = {json.loads(l)["idx"]: json.loads(l) for l in DATA.read_text(encoding="utf-8").splitlines() if l.strip()}
    stems = sorted(p.stem for p in OUTPUTS.glob("*_full_*.jsonl") if not p.stem.startswith("copy_gold"))
    jobs, verdict = {}, {}
    for stem in stems:
        for line in (OUTPUTS / f"{stem}.jsonl").read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            p = json.loads(line)
            x = rows[p["idx"]]
            ghead = re.match(r"\s*def\s+(\w+)", x["intended_statement"]).group(1)
            chead = ghead.replace("Intended", "Candidate")
            mine = corrected(p.get("corrected_statement"), ghead)
            key = (stem, p["idx"])
            if mine is None:
                verdict[key] = "unparseable"
                continue
            y = dict(x, candidate_statement=re.sub(rf"^(\s*def\s+){ghead}\b", rf"\g<1>{chead}",
                                                    x["intended_statement"].strip()),
                     intended_statement=mine)
            try:
                jobs[key] = pair_of(y)
            except (AssertionError, AttributeError):
                verdict[key] = "unparseable"

    uniq = {}
    for key, pr in jobs.items():
        uniq.setdefault((pr["pre"], tuple(pr["imports"])), (f"q{len(uniq):04d}", pr))
    print("model outputs", len(verdict) + len(jobs), "parsed", len(jobs), "distinct", len(uniq), flush=True)

    todo = []
    for k, pr in uniq.values():
        for g in pr["goals"]:
            todo.append(((k, g), pr, TAC.format(defs=", ".join(pr["names"]))))
            if g in SEARCH_GOALS and search_tac(pr, g):
                todo.append(((k, g + "_s"), pr | {"goals": pr["goals"] | {g + "_s": pr["goals"][g]}}, search_tac(pr, g)))
    res = prove(todo, "c")
    proved = {}
    for (k, g), r in res.items():
        if ok(r):
            proved.setdefault(k, set()).add(g.removesuffix("_s"))

    for key, pr in jobs.items():
        k, _ = uniq[(pr["pre"], tuple(pr["imports"]))]
        got = proved.get(k, set())
        rel = relation(pr["kind"], got)
        verdict[key] = ("certified_correct" if rel == "equivalent" else
                        "certified_wrong" if got & SEPARATING else "unknown")

    summary, per = {}, []
    for stem in stems:
        t = Counter(v for (s, _), v in verdict.items() if s == stem)
        summary[stem] = dict(t)
        print(stem, json.dumps(dict(t)), flush=True)
    for (s, idx), v in sorted(verdict.items()):
        per.append({"run": s, "idx": idx, "verdict": v})
    OUT.write_text(json.dumps({"summary": summary, "items": per}, indent=2, ensure_ascii=False) + "\n",
                   encoding="utf-8")


if __name__ == "__main__":
    main()
