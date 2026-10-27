#!/usr/bin/env python3
"""E5: metamorphic tests of the canonicalizer.

Each ProofNetVerif reference `R` (the distinct references of G1 whose canonicalization
succeeds) is re-presented on the surface by `ExperimentsMathlib.CanonMeta.represent`:
adjacent independent binders swapped (`swap0`, `swap1`, `swap2`), adjacent free hypotheses
conjoined (`conj0`, `conj1`), a final negation written as `C → False` (`negpeel`), a
conjunctive hypothesis split (`unconj0`). The pair `(R, represent R)` is canonicalized and the
`acc` goal is attacked with three tiers:

  identical   `intros; exact ⟨Iff.rfl, Iff.rfl⟩`         canonical forms are syntactically equal
  reordered   conjunct reordering (`and_comm`, `and_assoc`) canonical forms equal up to ∧ order
  logical     `tauto` / `simp_all`                         equal up to propositional logic

Anything left is reported with the canonicalization information of both sides.
Writes data/real/e5_results.json. Usage: e5_meta.py [N_REFS]
"""

from __future__ import annotations

import json
import os
import re
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
from f9_canon import lean_str
from realdata import proofnetverif
from runner import ROOT, Item, _build, _run_file, check
from stmt import to_prop

OUT = ROOT / "data" / "real" / "e5_results.json"
CANON_CACHE = ROOT / "data" / "real" / "e5_canon.json"
G1_CANON = ROOT / "data" / "real" / "g1_canon2.json"
IMPORT = "ExperimentsMathlib.CanonMeta"
KINDS = ("swap0", "swap1", "swap2", "conj0", "conj1", "negpeel", "unconj0")
N_REFS = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
LEAN_WORKERS = int(os.environ.get("LEAN_WORKERS", "2"))
TIERS = (
    ("identical", "intros; exact ⟨Iff.rfl, Iff.rfl⟩"),
    ("reordered", "intros; constructor <;> first | rfl | (simp only [and_comm, and_assoc, and_left_comm]; done)"),
    ("logical", "intros; constructor <;> first | rfl | tauto | (simp_all; done) | (constructor <;> intro h <;> aesop)"),
)


def imports_of(r) -> tuple[tuple[str, ...], str]:
    imports, pre = f2.prelude(r)
    return tuple(sorted(set(imports) | {IMPORT})), pre


def references():
    rows = {r.row_id: r for r in proofnetverif("test")}
    g1 = json.loads(G1_CANON.read_text(encoding="utf-8"))
    seen, refs = set(), []
    for rid in sorted(g1):
        if g1[rid]["status"] != "ok":
            continue
        r = rows[rid]
        g = f2.normalize(to_prop(r.gold))
        if g not in seen:
            seen.add(g)
            refs.append((r, g))
    return refs[:N_REFS]


def canon_all(jobs) -> dict[str, dict]:
    cache = json.loads(CANON_CACHE.read_text(encoding="utf-8")) if CANON_CACHE.exists() else {}
    groups: dict[tuple, list] = {}
    for key, (r, g, kind) in jobs.items():
        if key in cache:
            continue
        imports, pre = imports_of(r)
        groups.setdefault(imports, []).append(Item(key, imports, f"{pre}\n#canon2_meta {lean_str(key)} {kind} ({g})"))
    batches = [g[i:i + 10] for g in groups.values() for i in range(0, len(g), 10)]

    def run(batch):
        out, _ = _run_file(_build(batch)[0], 900)
        return batch, out

    with ThreadPoolExecutor(max_workers=LEAN_WORKERS) as pool:
        for batch, out in pool.map(run, batches):
            blocks = dict(re.findall(r"CANON_BEGIN (\S+)\n(.*?)\n?CANON_END \1", out, flags=re.DOTALL))
            for it in batch:
                b = blocks.get(it.item_id)
                if b is None:
                    cache[it.item_id] = {"status": "elab_fail"}
                elif b.startswith("CANON_FAIL"):
                    na = any(s in b for s in ("no swappable", "no conjoinable", "no splittable", "not a negation"))
                    cache[it.item_id] = {"status": "not_applicable" if na else "canon_fail", "detail": b[:300]}
                else:
                    cache[it.item_id] = {
                        "status": "ok",
                        "info": re.search(r"CANON_INFO (.*)", b).group(1),
                        "mutant": re.search(r"CANON_MUTANT (.*?)(?=\nCANON_GOAL )", b, flags=re.DOTALL).group(1),
                        "goals": dict(re.findall(r"CANON_GOAL (\w+) ::: (.*?)(?=\nCANON_GOAL |\Z)", b, flags=re.DOTALL)),
                    }
    CANON_CACHE.write_text(json.dumps(cache, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    return cache


def prove(jobs, tag: str) -> dict:
    items, keys = [], []
    for key, (r, g, kind, proof) in jobs:
        imports, pre = imports_of(r)
        name = re.sub(r"\W", "_", f"{tag}_{key}")
        body = (f"{pre}\nset_option maxHeartbeats 200000 in\n"
                f"canon2_meta_prove {name} {kind} ({g}) acc := by\n  {proof}")
        items.append(Item(f"{key}:{tag}", imports, body))
        keys.append(key)
    res = check(items, batch_size=10, workers=LEAN_WORKERS)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    refs = references()
    print("references", len(refs), flush=True)
    jobs = {f"{r.row_id}~{k}": (r, g, k) for r, g in refs for k in KINDS}
    canon = canon_all(jobs)
    status = Counter(canon[k]["status"] for k in jobs)
    print("re-presentations", dict(status), f"{time.time() - t0:.0f}s", flush=True)
    good = [k for k in jobs if canon[k]["status"] == "ok"]
    result = {}
    todo = list(good)
    for tier, tac in TIERS:
        res = prove([(k, (*jobs[k], tac)) for k in todo], f"e5{tier[:3]}")
        for k, v in res.items():
            if v.ok and not v.uses_sorry:
                result[k] = tier
        todo = [k for k in todo if k not in result]
        print(tier, sum(v == tier for v in result.values()), "open", len(todo), f"{time.time() - t0:.0f}s", flush=True)
    per_kind = {}
    for kind in KINDS:
        c = Counter()
        for k in jobs:
            if not k.endswith(f"~{kind}"):
                continue
            s = canon[k]["status"]
            c[result.get(k, "open") if s == "ok" else s] += 1
        per_kind[kind] = dict(c)
    open_items = [{"key": k, "info": canon[k]["info"], "mutant": canon[k]["mutant"][:300],
                   "acc": canon[k]["goals"]["acc"][:400]} for k in todo]
    logical_items = [{"key": k, "info": canon[k]["info"], "mutant": canon[k]["mutant"][:300],
                      "acc": canon[k]["goals"]["acc"][:400]} for k, v in result.items() if v == "logical"]
    summary = {"n_references": len(refs), "n_applicable": len(good), "by_tier": dict(Counter(result.values())),
               "per_kind": per_kind, "tiers": result, "logical": logical_items, "open": open_items,
               "seconds": round(time.time() - t0, 1)}
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "open"}, indent=2, ensure_ascii=False))
    for o in open_items[:20]:
        print("OPEN", o["key"], o["info"])


if __name__ == "__main__":
    main()
