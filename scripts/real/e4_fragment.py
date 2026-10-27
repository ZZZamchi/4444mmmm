#!/usr/bin/env python3
"""E4: syntactic fragment of every statement in G1, G4, ProofNet#, miniF2F and PutnamBench.

`ExperimentsMathlib.Fragment` canonicalizes a statement and reports the data-binder types,
instance binders, constants and nonlinearity flags of its components. The classes used by
the complexity transfer theorem are decided here:

  presburger   data in {Nat, Int}, linear arithmetic only              (decidable, no unknown)
  rcf          data in {Real, Rat}, polynomial arithmetic only          (decidable, no unknown)
  arith        data in {Nat, Int}, with nonlinear multiplication etc.   (Sigma_1 / Pi_1)
  arith+       Nat/Int/Real with other arithmetic functions (prime, factorial, exp, sums, ...)
  structural   functions, sets, structures, type classes, abstract types

Usage: e4_fragment.py [SET ...]   SET in g1 g4 pns mf pb; default all. Writes data/real/e4_fragments.json.
"""

from __future__ import annotations

import json
import os
import re
import sys
import time
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
from f9_canon import lean_str
from realdata import proofnetverif
from runner import ROOT, Item, _build, _run_file
from stmt import to_prop

OUT = ROOT / "data" / "real" / "e4_fragments.json"
IMPORT = "ExperimentsMathlib.Fragment"
LEAN_WORKERS = int(os.environ.get("LEAN_WORKERS", "3"))

NUM = {"Nat", "Int"}
REAL = {"Real", "Rat", "NNReal"}
LOGIC = {"Eq", "Ne", "Not", "And", "Or", "Iff", "Exists", "True", "False", "LE.le", "LT.lt", "GE.ge", "GT.gt",
         "HAdd.hAdd", "HSub.hSub", "HMul.hMul", "HPow.hPow", "HDiv.hDiv", "HMod.hMod", "Dvd.dvd", "OfNat.ofNat",
         "Neg.neg", "Nat.cast", "Int.cast", "NatCast.natCast", "IntCast.intCast", "Nat.succ", "Nat", "Int", "Real",
         "Rat", "abs", "Max.max", "Min.min", "Monoid.npow", "Nat.pow", "Int.pow", "Real.sqrt", "Inv.inv", "Nat.pred",
         "Int.natAbs", "Int.toNat", "Int.ofNat", "Subtype.val", "Membership.mem", "Set.Icc", "Set.Ico", "Set.Ioc",
         "Set.Ioo", "Set.Ici", "Set.Iic", "Set.Ioi", "Set.Iio", "Nat.ModEq", "Int.ModEq", "Even", "Odd", "Nat.succ",
         "DecidableEq", "Decidable", "ite", "dite", "instDecidableEqNat", "Classical.propDecidable", "Int.emod",
         "Int.ediv", "Nat.div", "Nat.mod", "HSMul.hSMul", "SMul.smul", "Finset.Icc", "Finset.range", "Finset.Ico"}
NONLIN = {"mul_nonlit", "pow_nonlit", "div_nonlit", "mod_nonlit", "dvd_nonlit"}
ORDER = ["presburger", "rcf", "arith", "arith+", "structural", "fail"]


def is_inst(name: str) -> bool:
    last = name.rsplit(".", 1)[-1]
    return last.startswith("inst") or ".inst" in name or re.match(r"to[A-Z]", last) is not None


def classify(d: dict) -> str:
    if d.get("status") != "ok":
        return "fail"
    data, inst, flags = set(d["data"]), set(d["inst"]), set(d["flags"])
    consts = {c for c in d["consts"] if not is_inst(c)}
    if inst or data - (NUM | REAL):
        return "structural"
    extra = consts - LOGIC
    if any(c.startswith(("Set.", "Finset.", "Function.", "Polynomial.", "Matrix.", "Filter.")) or c in
           ("Set", "Finset", "Function", "Polynomial", "Matrix") for c in extra):
        return "structural"
    if extra:
        return "arith+"
    if data <= NUM:
        return "presburger" if not (flags & NONLIN) else "arith"
    if data <= REAL and "pow_nonlit" not in flags:
        return "rcf"
    return "arith+"  # mixed Nat/Real indices, sequences


def sets_g1():
    import g1_full as g1  # noqa: F401  (for its cache paths only)
    rows = {r.row_id: r for r in proofnetverif("test")}
    for p in json.loads(f2.OUT.read_text(encoding="utf-8"))["pairs"]:
        r = rows[p["row_id"]]
        yield f"{r.row_id}:ref", r, f2.normalize(to_prop(r.gold))
        yield f"{r.row_id}:cand", r, f2.normalize(to_prop(r.pred))


def sets_g4():
    import g4_pnv as g4
    rows, _ = g4.load()
    canon = json.loads(g4.g1.CANON_CACHE.read_text(encoding="utf-8"))
    for r in rows:
        if canon.get(r.row_id, {}).get("status") is None:
            continue  # not among the usable 317
        g, p = to_prop(r.gold), to_prop(r.pred)
        if g is None or p is None:
            continue
        yield f"{r.row_id}:ref", r, f2.normalize(g)
        yield f"{r.row_id}:cand", r, f2.normalize(p)


def sets_g3(dataset: str):
    import g3_probe as g3
    g3.DATASET = dataset
    for r, p in g3.statements():
        yield f"{r.row_id}:ref", r, p


SETS = {"g1": sets_g1, "g4": sets_g4, "pns": lambda: sets_g3("proofnetsharp"),
        "mf": lambda: sets_g3("minif2f"), "pb": lambda: sets_g3("putnam")}


def run_all(jobs: list[tuple[str, object, str]], cache: dict) -> None:
    groups: dict[tuple, list] = defaultdict(list)
    for sid, r, prop in jobs:
        if sid in cache:
            continue
        imports, pre = f2.prelude(r)
        imports = tuple(sorted(set(imports) | {IMPORT}))
        groups[imports].append(Item(sid, imports, f"{pre}\n#fragment {lean_str(sid)} ({prop})"))
    batches = [g[i:i + 10] for g in groups.values() for i in range(0, len(g), 10)]
    print("batches", len(batches), flush=True)

    def run(batch):
        out, _ = _run_file(_build(batch)[0], 900)
        return batch, out

    done = 0
    with ThreadPoolExecutor(max_workers=LEAN_WORKERS) as pool:
        for batch, out in pool.map(run, batches):
            blocks = dict(re.findall(r"FRAG_BEGIN (\S+)\n(.*?)\n?FRAG_END \1", out, flags=re.DOTALL))
            for it in batch:
                b = blocks.get(it.item_id)
                if b is None:
                    cache[it.item_id] = {"status": "elab_fail"}
                elif b.startswith("FRAG_FAIL"):
                    cache[it.item_id] = {"status": "canon_fail", "detail": b[:300]}
                else:
                    f = {k: re.search(rf"FRAG_{k} ?(.*)", b).group(1).split() for k in ("DATA", "INST", "CONSTS", "FLAGS")}
                    cache[it.item_id] = {"status": "ok", "data": f["DATA"], "inst": f["INST"],
                                         "consts": f["CONSTS"], "flags": f["FLAGS"]}
            done += 1
            if done % 20 == 0:
                print("done", done, flush=True)
                OUT.write_text(json.dumps(cache, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")


def pair_class(a: str, b: str) -> str:
    return max(a, b, key=ORDER.index)


def summarize(cache: dict, which: list[str]) -> dict:
    summary = {}
    for name in which:
        ids = [k for k in cache if k.startswith(PREFIX[name])]
        stmts = Counter(classify(cache[k]) for k in ids)
        summary[name] = {"statements": dict(stmts)}
        if name in ("g1", "g4"):
            pairs = Counter()
            per_pair = {}
            for k in ids:
                if k.endswith(":ref") and k[:-4] + ":cand" in cache:
                    c = pair_class(classify(cache[k]), classify(cache[k[:-4] + ":cand"]))
                    pairs[c] += 1
                    per_pair[k[:-4]] = c
            summary[name]["pairs"] = dict(pairs)
            res_file = ROOT / "data" / "real" / ("g1_results.json" if name == "g1" else "g4_results.json")
            if res_file.exists():
                res = json.loads(res_file.read_text(encoding="utf-8"))
                cross = defaultdict(Counter)
                for p in res["pairs"]:
                    if p["row_id"] in per_pair:
                        cross[per_pair[p["row_id"]]][p["verdict"]] += 1
                summary[name]["verdict_by_class"] = {k: dict(v) for k, v in cross.items()}
    return summary


PREFIX = {"g1": "pnv-", "g4": "g4-", "pns": "pns-", "mf": "mf-", "pb": "pb-"}


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    which = sys.argv[1:] or list(SETS)
    t0 = time.time()
    cache = json.loads(OUT.read_text(encoding="utf-8")) if OUT.exists() else {}
    jobs = []
    for name in which:
        js = list(SETS[name]())
        print(name, len(js), "statements", flush=True)
        jobs += js
    run_all(jobs, cache)
    OUT.write_text(json.dumps(cache, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    summary = summarize(cache, which)
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    (ROOT / "data" / "real" / "e4_summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"{time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
