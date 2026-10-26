#!/usr/bin/env python3
"""J1: LLM-judge baselines for formalization faithfulness.

Same pairs as the main experiments: G1 (ProofNetVerif test, 300 pairs, equivalence labels)
and G4 (ProofNet-Verified, 317 usable pairs, relation labels from the manual audit).

Two settings per judge model:
  nl    informal statement + candidate              (reference-free, as in FormalAlign-style judges)
  ref   informal statement + reference + candidate  (reference-based, comparable to BEq+ / ours)

The judge answers with a final line `VERDICT: FAITHFUL` or `VERDICT: UNFAITHFUL`; anything
else counts as `none`. Temperature 0, one sample, cached by `llm.chat`.

Usage: j1_judge.py [g1|g4|all] [MODEL ...]     Writes data/real/j1_results.json (merged).
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
from llm import chat
from realdata import proofnetverif
from runner import ROOT

OUT = ROOT / "data" / "real" / "j1_results.json"
MODELS = ["deepseek/deepseek-v4.1-flash", "openai/gpt-4.1-mini", "anthropic/claude-opus-5.5"]
SETTINGS = ("nl", "ref")

SYSTEM = ("You are an expert in Lean 4, Mathlib and mathematics. You judge whether a Lean 4 "
          "formalization faithfully captures a mathematical statement: same objects, same "
          "hypotheses, same conclusion, no extra or missing assumptions, no change of domain "
          "or type that changes the meaning. Minor differences in notation or in how a "
          "hypothesis is packaged are acceptable.")

NL_PROMPT = """Informal statement:
{nl}

Lean 4 formalization (header omitted except `open` lines):
```lean
{header}
{cand}
```

Is the formalization faithful to the informal statement? Think briefly, then end your answer
with exactly one line: `VERDICT: FAITHFUL` or `VERDICT: UNFAITHFUL`."""

REF_PROMPT = """Informal statement:
{nl}

Trusted reference formalization:
```lean
{header}
{ref}
```

Candidate formalization:
```lean
{cand}
```

Is the candidate a faithful formalization of the informal statement, i.e. does it say the
same thing as the reference (up to harmless differences)? Think briefly, then end your
answer with exactly one line: `VERDICT: FAITHFUL` or `VERDICT: UNFAITHFUL`."""


def opens(header: str) -> str:
    return "\n".join(l for l in header.splitlines() if l.strip().startswith(("open ", "variable ")))


def parse(text: str) -> str:
    m = re.findall(r"VERDICT:\s*\**\s*(FAITHFUL|UNFAITHFUL)", text.upper())
    return m[-1].lower() if m else "none"


def g1_rows() -> list[dict]:
    rows = {r.row_id: r for r in proofnetverif("test")}
    ids = [p["row_id"] for p in json.loads(f2.OUT.read_text(encoding="utf-8"))["pairs"]]
    return [{"set": "G1", "row_id": i, "nl": rows[i].nl, "header": rows[i].header,
             "ref": rows[i].gold, "cand": rows[i].pred, "label": rows[i].correct, "group":
             "faithful" if rows[i].correct else "unfaithful"} for i in ids]


def g4_rows() -> list[dict]:
    import g4_pnv as g4
    rows, meta = g4.load()
    by = {r.row_id: r for r in rows}
    res = json.loads((ROOT / "data" / "real" / "g4_results.json").read_text(encoding="utf-8"))["pairs"]
    out = []
    for p in res:
        r, m = by[p["row_id"]], meta[p["row_id"]]
        group = "faithful" if m["relation"] == "faithful" else \
            f"unfaithful_{'true' if m['candidate_true'] else 'other'}"
        out.append({"set": "G4", "row_id": r.row_id, "nl": r.nl, "header": r.header, "ref": r.gold,
                    "cand": r.pred, "label": m["relation"] == "faithful", "group": group})
    return out


def judge(model: str, setting: str, x: dict) -> dict:
    tmpl = NL_PROMPT if setting == "nl" else REF_PROMPT
    msg = tmpl.format(nl=x["nl"].strip(), header=opens(x["header"]), ref=x["ref"].strip(), cand=x["cand"].strip())
    try:
        text = chat(model, [{"role": "system", "content": SYSTEM}, {"role": "user", "content": msg}],
                    temperature=0.0, max_tokens=4096)
    except RuntimeError:
        text = ""
    return {"verdict": parse(text), "reply_tail": text[-300:]}


def table(results: list[dict]) -> list[dict]:
    rows = []
    keys = sorted({(r["set"], r["model"], r["setting"]) for r in results})
    for s, m, st in keys:
        sub = [r for r in results if (r["set"], r["model"], r["setting"]) == (s, m, st)]
        c = Counter()
        for r in sub:
            c[(r["group"], r["verdict"])] += 1
            c[(r["group"], "n")] += 1
        unf = [g for g in {r["group"] for r in sub} if g.startswith("unfaithful")]
        n_unf = sum(c[(g, "n")] for g in unf)
        fa = sum(c[(g, "faithful")] for g in unf)
        row = {"set": s, "model": m.split("/")[-1], "setting": st,
               "n_unfaithful": n_unf, "false_accept": fa,
               "n_faithful": c[("faithful", "n")], "accept_faithful": c[("faithful", "faithful")],
               "none": sum(v for (g, k), v in c.items() if k == "none")}
        if s == "G4":
            row["unf_true_n"] = c[("unfaithful_true", "n")]
            row["unf_true_accept"] = c[("unfaithful_true", "faithful")]
        rows.append(row)
    return rows


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    models = sys.argv[2:] or MODELS
    data = (g1_rows() if which in ("g1", "all") else []) + (g4_rows() if which in ("g4", "all") else [])
    print("pairs", Counter(x["set"] for x in data), flush=True)
    old = json.loads(OUT.read_text(encoding="utf-8"))["results"] if OUT.exists() else []
    old = [r for r in old if r["reply_tail"]]
    done = {(r["set"], r["row_id"], r["model"], r["setting"]) for r in old}
    jobs = [(m, st, x) for m in models for st in SETTINGS for x in data
            if (x["set"], x["row_id"], m, st) not in done]
    print("jobs", len(jobs), flush=True)

    def work(job):
        m, st, x = job
        return {"set": x["set"], "row_id": x["row_id"], "group": x["group"], "model": m, "setting": st,
                **judge(m, st, x)}

    new = []
    with ThreadPoolExecutor(max_workers=16) as pool:
        for i, r in enumerate(pool.map(work, jobs)):
            new.append(r)
            if (i + 1) % 200 == 0:
                print("done", i + 1, flush=True)
    results = old + new
    summary = {"table": table(results), "results": results}
    OUT.write_text(json.dumps(summary, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    for row in summary["table"]:
        print(json.dumps(row, ensure_ascii=False))


if __name__ == "__main__":
    main()
