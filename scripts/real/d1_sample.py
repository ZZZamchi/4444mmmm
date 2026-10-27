#!/usr/bin/env python3
"""D1: sample autoformalizations for the downstream experiments.

Problems: the 317 ProofNet-Verified problems of G4. The reference is the manually corrected
statement (`PnvRow.gold`), which the audit marks faithful. Each autoformalizer receives the
informal statement, the `open` lines of the header and the theorem name, and returns one Lean
4 statement ending in `:= by sorry`. K samples per model at temperature 0.8 (sample index
distinguishes cache entries).

A candidate is kept if it converts to a Prop and elaborates together with the reference
(the G4 `usable` check). Exact duplicates per problem (after whitespace normalization) are
merged and their multiplicity recorded, so best-of-n can still be simulated over the raw
draws.

Usage: d1_sample.py [K] [MODEL ...]     Writes data/real/d1_candidates.json.
"""

from __future__ import annotations

import json
import re
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import g4_pnv as g4
from llm import chat, extract_lean
from runner import ROOT, Item, check
from stmt import to_prop

OUT = ROOT / "data" / "real" / "d1_candidates.json"
K = int(sys.argv[1]) if len(sys.argv) > 1 else 8
MODELS = sys.argv[2:] or ["deepseek/deepseek-v4.1-flash", "openai/gpt-4.1-mini", "anthropic/claude-opus-5.5"]

PROMPT = """Formalize the following statement in Lean 4 with Mathlib. Write a single theorem named
`{name}` whose proof is `by sorry`. Do not define auxiliary definitions; do not write a proof.
The file already contains:
```lean
import Mathlib
{opens}
```

Statement:
{nl}

Answer with one ```lean code block containing only the theorem."""


def opens(header: str) -> str:
    return "\n".join(l for l in header.splitlines() if l.strip().startswith(("open ", "variable ")))


def thm_name(r) -> str:
    return re.sub(r"\W", "_", r.stmt_id)


def draw(model: str, r, k: int) -> str | None:
    msg = PROMPT.format(name=thm_name(r), opens=opens(r.header), nl=r.nl.strip())
    try:
        out = chat(model, [{"role": "user", "content": msg}], temperature=0.8, sample=k, max_tokens=4096)
    except RuntimeError:
        return None
    src = extract_lean(out).strip()
    return src if "theorem" in src or "lemma" in src else None


def key(prop: str) -> str:
    return re.sub(r"\s+", " ", prop).strip()


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    rows, meta = g4.load()
    ids = {p["row_id"] for p in json.loads((ROOT / "data" / "real" / "g4_results.json").read_text(encoding="utf-8"))["pairs"]}
    probs = [r for r in rows if r.row_id in ids]
    print("problems", len(probs), "models", MODELS, "K", K, flush=True)

    jobs = [(m, r, k) for r in probs for m in MODELS for k in range(K)]
    with ThreadPoolExecutor(max_workers=16) as pool:
        raw = list(pool.map(lambda j: (j, draw(*j)), jobs))
    print("drawn", sum(s is not None for _, s in raw), "/", len(raw), f"{time.time() - t0:.0f}s", flush=True)

    gold = {r.row_id: f2.normalize(to_prop(r.gold)) for r in probs}
    cands: dict[tuple, dict] = {}
    draws = []
    stats = Counter()
    for (m, r, k), src in raw:
        p = to_prop(src) if src else None
        if p is None:
            stats["no_conversion"] += 1
            draws.append({"problem": r.row_id, "model": m, "k": k, "cand": None})
            continue
        p = f2.normalize(p)
        ck = (r.row_id, key(p))
        if ck not in cands:
            cands[ck] = {"cand_id": f"d1-{r.row_id[3:]}-{len(cands)}", "problem": r.row_id, "prop": p,
                         "src": src, "models": Counter()}
        cands[ck]["models"][m] += 1
        draws.append({"problem": r.row_id, "model": m, "k": k, "cand": cands[ck]["cand_id"]})

    by_id = {r.row_id: r for r in probs}
    items = []
    for c in cands.values():
        r = by_id[c["problem"]]
        imports, pre = f2.prelude(r)
        items.append(Item(f"{c['cand_id']}:elab", imports,
                          f"{pre}\nexample : ({gold[r.row_id]}) ∧ ({c['prop']}) → True := fun _ => trivial"))
    res = check(items, batch_size=25)
    ok = set()
    for c, it in zip(cands.values(), items):
        if res[it.item_id].ok:
            ok.add(c["cand_id"])
    stats["distinct"] = len(cands)
    stats["distinct_elab"] = len(ok)
    for d in draws:
        if d["cand"] is not None and d["cand"] not in ok:
            stats["elab_fail_draws"] += 1
            d["cand"] = None
    stats["usable_draws"] = sum(d["cand"] is not None for d in draws)
    out = {"K": K, "models": MODELS, "stats": dict(stats),
           "candidates": [{**c, "models": dict(c["models"]), "gold": gold[c["problem"]]}
                          for c in cands.values() if c["cand_id"] in ok],
           "draws": draws, "seconds": round(time.time() - t0, 1)}
    OUT.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(out["stats"]), f"{time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
