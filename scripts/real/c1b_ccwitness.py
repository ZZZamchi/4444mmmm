#!/usr/bin/env python3
"""C1b: re-check FormalRx-CC model witnesses under our Lean, with a collapse test.

For each archived FormalRx-CC output (one JSON line per eval204 item) we compile the
model's `witness_lean` after the gold candidate and intended definitions, three times:

    orig     the gold definitions;
    c_is_i   Candidate redefined with the intended body (the two objects coincide);
    i_is_c   Intended redefined with the candidate body.

A witness can only demonstrate that the two objects differ if it fails to compile once they
coincide. We call a witness discriminating when it compiles on `orig` and fails on both
collapsed variants; a witness that still compiles after a collapse proves nothing about the
difference, whatever its explanation says.

Usage: c1b_ccwitness.py [OUTPUT_STEM ... | eval51]     Writes data/real/c1b_results[_eval51].json.
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from runner import ROOT, Item, check, split_imports

CCF = ROOT / "data" / "real" / "raw" / "papers" / "ccf"
DATA = CCF / "data" / "formalrx_cc_eval204.jsonl"
OUTPUTS = CCF / "results" / "model_outputs"
OUT = ROOT / "data" / "real" / "c1b_results.json"
DEFAULT = ("gold", "openai_gpt41mini_gold_witness_eval204", "openai_gpt41mini_full_eval204",
           "openai_gpt41mini_full_repair1_nogold_eval204")
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b")
VARIANTS = ("orig", "c_is_i", "i_is_c")


def head(stmt: str) -> str:
    return re.match(r"\s*def\s+(\w+)", stmt).group(1)


def rename(stmt: str, new: str) -> str:
    return re.sub(r"^(\s*def\s+)\w+", rf"\g<1>{new}", stmt, count=1)


def body(x: dict, witness: str, variant: str) -> tuple[tuple[str, ...], str]:
    c, i = x["candidate_statement"].strip(), x["intended_statement"].strip()
    if variant == "c_is_i":
        c = rename(i, head(c))
    elif variant == "i_is_c":
        i = rename(c, head(i))
    imports, rest = split_imports(x["header"])
    close = "\nend" if "noncomputable section" in rest else ""
    return imports, f"{rest}\n{c}\n{i}\n\n{witness.strip()}{close}"


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    global OUT
    stems = tuple(sys.argv[1:]) or DEFAULT
    if stems == ("eval51",):
        stems = tuple(sorted(p.stem for p in OUTPUTS.glob("*eval51*.jsonl") if not p.stem.startswith("copy_gold")))
        OUT = OUT.with_name("c1b_results_eval51.json")
    rows = {json.loads(l)["idx"]: json.loads(l) for l in DATA.read_text(encoding="utf-8").splitlines() if l.strip()}
    summary = {}
    for stem in stems:
        if stem == "gold":
            preds = [{"idx": k, "semantic_relation": x["semantic_relation"], "witness_lean": x["gold_witness_lean"]}
                     for k, x in rows.items()]
        else:
            preds = [json.loads(l) for l in (OUTPUTS / f"{stem}.jsonl").read_text(encoding="utf-8").splitlines()
                     if l.strip()]
        items, meta = [], {}
        for p in preds:
            x, w = rows[p["idx"]], p.get("witness_lean") or ""
            meta[p["idx"]] = {"gold": x["semantic_relation"], "pred": p.get("semantic_relation"),
                              "forbidden": bool(FORBIDDEN.search(w)), "empty": not w.strip()}
            if meta[p["idx"]]["forbidden"] or meta[p["idx"]]["empty"]:
                continue
            for v in VARIANTS:
                imports, b = body(x, w, v)
                items.append(Item(f"{stem}:{p['idx']}:{v}", imports, b))
        res = check(items, batch_size=10, workers=1)
        per, tally = [], Counter()
        for idx, m in meta.items():
            comp = {v: (lambda r: r is not None and r.ok and not r.uses_sorry)(res.get(f"{stem}:{idx}:{v}"))
                    for v in VARIANTS}
            compiles = comp["orig"]
            disc = compiles and not comp["c_is_i"] and not comp["i_is_c"]
            rel_ok = m["pred"] == m["gold"]
            tally["items"] += 1
            tally["relation_correct"] += rel_ok
            tally["compiles"] += compiles
            tally["compiles_after_collapse"] += compiles and not disc
            tally["discriminating"] += disc
            tally["relation_correct_and_discriminating"] += rel_ok and disc
            tally["forbidden"] += m["forbidden"]
            per.append({"idx": idx, **m, **{f"compiles_{v}": comp[v] for v in VARIANTS},
                        "discriminating": disc})
        summary[stem] = {"tally": dict(tally), "pairs": per}
        print(stem, json.dumps(dict(tally)), flush=True)
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
