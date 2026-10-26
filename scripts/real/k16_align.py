#!/usr/bin/env python3
"""K16: does a fixed catalogue of canonical isomorphisms extend the alignment on the full set?

Separate experiment, not part of the paper's tables. `ExperimentsMathlib.CanonV2Ext` is
`CanonV2Var` with additional rules behind flags; with the empty flag string its goals are those
of `CanonV2`, used for the 1,140 G5 pairs. Every rule only changes the exhibited telescopes, so
soundness still rests on the two kernel-checked regrouping certificates.

For each variant the goals of every pair are recomputed. Pairs whose goals are unchanged keep
their G5 (Opus) verdict; changed pairs are proved again with the G1 budget, as in K12.

    k16_align.py diag              baseline goals with stop diagnostics (Lean only)
    k16_align.py dry               which pairs each variant changes (Lean only)
    k16_align.py run [FLAGS ...]   prove the changed pairs (uses the API)

Writes data/real/k16_align.json; cache in data/real/k16_canon_cache.json.
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
import g1_full as g1
from f7_component import COMP_TAC, SPLIT_TAC, SPLIT_TAC2
from f9_canon import lean_str, repair
from paper_check import verdict as final_verdict
from runner import ROOT, Item, _build, _run_file, check

D = ROOT / "data" / "real"
OUT = D / "k16_align.json"
CACHE = D / "k16_canon_cache.json"
MODULE = "ExperimentsMathlib.CanonV2Ext"
MODEL = os.environ.get("K16_MODEL", "anthropic/claude-opus-5.5")
VARIANTS = [v for v in os.environ.get("K16_VARIANTS", "").split(";") if v]
ALL_GOALS = ("acc", "cond", "nhyp", "ncin", "ncomp", "split_r", "split_s")
OPEN_GOALS = ("acc", "nhyp", "ncin", "ncomp", "split_r", "split_s")
WORKERS = int(os.environ.get("LLM_WORKERS", 12))
# Third regrouping tier: the `classdec` rule replaces decidability instances by classical ones.
SPLIT_TAC3 = ("first | (classical; constructor <;> intro h <;> intros <;> simp_all; done) "
              "| (classical; constructor <;> intro h <;> intros <;> (first | (convert h _ <;> simp_all; done) "
              "| (apply h <;> assumption) | aesop))")
DEFAULT = ["subtype", "classdec", "dropunused", "univ0", "onept2", "subtype,classdec,dropunused,univ0,onept2"]


def imports_of(r):
    imports, pre = f2.prelude(r)
    return tuple(sorted(set(imports) | {MODULE})), pre


def canon(stmt, rids, flags, cache) -> None:
    groups: dict[tuple, list] = {}
    for rid in rids:
        if f"{flags}|{rid}" in cache:
            continue
        r, g, s = stmt[rid]
        imports, pre = imports_of(r)
        groups.setdefault(imports, []).append(
            Item(f"{flags}|{rid}", imports, f"{pre}\n#canon2x_goals {lean_str(rid)} {lean_str(flags)} ({g}) ({s})"))
    batches = [g[i:i + 10] for g in groups.values() for i in range(0, len(g), 10)]
    if not batches:
        return

    def run(batch):
        out, _ = _run_file(_build(batch)[0], 900)
        return batch, out

    with ThreadPoolExecutor(max_workers=int(os.environ.get("LEAN_WORKERS", 6))) as pool:
        for batch, out in pool.map(run, batches):
            blocks = dict(re.findall(r"CANON_BEGIN (\S+)\n(.*?)\n?CANON_END \1", out, flags=re.DOTALL))
            for it in batch:
                b = blocks.get(it.item_id.split("|", 1)[1])
                if b is None or b.startswith("CANON_FAIL"):
                    cache[it.item_id] = {"status": "fail"}
                else:
                    info = re.search(r"CANON_INFO (.*)", b).group(1)
                    goals = dict(re.findall(r"CANON_GOAL (\w+) ::: (.*?)(?=\nCANON_GOAL |\Z)", b, flags=re.DOTALL))
                    cache[it.item_id] = {"status": "ok", "info": info, "goals": goals}
    tmp = CACHE.with_suffix(f".{os.getpid()}.tmp")
    tmp.write_text(json.dumps(cache, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(tmp, CACHE)


def prove(stmt, flags, jobs, tag) -> dict:
    items, keys = [], []
    for (rid, goal), proof in jobs:
        r, g, s = stmt[rid]
        imports, pre = imports_of(r)
        body = (f"{pre}\nset_option maxHeartbeats 200000 in\n"
                f"canon2x_prove {lean_str(flags)} {tag}_{goal} ({g}) ({s}) {goal} := by\n  {proof}")
        items.append(Item(f"{flags}|{rid}:{tag}:{goal}", imports, body))
        keys.append((rid, goal))
    res = check(items, batch_size=10, workers=6)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def run_variant(stmt, flags, rids, goals, info) -> dict[str, set]:
    proved = {rid: set() for rid in rids}

    def cur(rid):
        return final_verdict({"verdict": g1.classify(proved[rid] - {"split_r", "split_s"}), "proved": proved[rid],
                              "canon_info": info[rid], "closed": "unknown"})

    for tag, tac in (("v0", None), ("v0b", SPLIT_TAC2), ("v0c", SPLIT_TAC3)):
        jobs = []
        for rid in rids:
            for g in ALL_GOALS:
                if g in proved[rid]:
                    continue
                if tac is None:
                    jobs.append(((rid, g), SPLIT_TAC if g.startswith("split") else COMP_TAC))
                elif g.startswith("split"):
                    jobs.append(((rid, g), tac))
        for (rid, g), res in prove(stmt, flags, jobs, tag).items():
            if g1.ok(res):
                proved[rid].add(g)

    def todo(rid):
        return [] if cur(rid) != "unknown" else [g for g in OPEN_GOALS if g not in proved[rid]]

    def work(rid):
        names = todo(rid)
        return rid, (g1.propose(MODEL, stmt[rid][0], goals[rid], names) if names else {})

    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        props = dict(pool.map(work, rids))
    shot = prove(stmt, flags, [((rid, g), p) for rid, gs in props.items() for g, p in gs.items()], "v1")
    for (rid, g), res in shot.items():
        if g1.ok(res):
            proved[rid].add(g)
    failed = [((rid, g), res) for (rid, g), res in shot.items() if not g1.ok(res) and cur(rid) == "unknown"]

    def fix(item):
        (rid, g), res = item
        return (rid, g), repair(MODEL, stmt[rid][0], g, goals[rid][g], props[rid][g], res.errors)

    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        fixes = dict(pool.map(fix, failed))
    for (rid, g), res in prove(stmt, flags, [(k, p) for k, p in fixes.items() if p], "v2").items():
        if g1.ok(res):
            proved[rid].add(g)
    return proved


def load():
    base = {p["row_id"]: p for p in json.loads((D / "g5" / "g1_results_claude-opus-5.5.json")
                                               .read_text(encoding="utf-8"))["pairs"]}
    rows = {r.row_id: r for r in g1.proofnetverif("test")}
    stmt = {rid: (rows[rid], f2.normalize(g1.to_prop(rows[rid].gold)), f2.normalize(g1.to_prop(rows[rid].pred)))
            for rid in base}
    cache = json.loads(CACHE.read_text(encoding="utf-8")) if CACHE.exists() else {}
    return base, stmt, cache


def strip_diag(info: str) -> str:
    return info.split(" next_r=")[0]


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    mode = sys.argv[1] if len(sys.argv) > 1 else "diag"
    base, stmt, cache = load()
    canon(stmt, list(base), "", cache)
    ref = json.loads(g1.CANON_CACHE.read_text(encoding="utf-8")) if g1.CANON_CACHE.exists() else {}
    same = sum(cache.get(f"|{rid}", {}).get("goals") == ref.get(rid, {}).get("goals") for rid in base)
    print("baseline canon", f"{time.time() - t0:.0f}s", "goals equal to the CanonV2 cache:", same, "/", len(base),
          flush=True)
    if mode == "diag":
        return
    flags_list = sys.argv[2:] or VARIANTS or DEFAULT
    for flags in flags_list:
        canon(stmt, list(base), flags, cache)
    if mode == "dry":
        for flags in flags_list:
            ch = [rid for rid in base if cache.get(f"|{rid}", {}).get("goals") != cache.get(f"{flags}|{rid}", {}).get("goals")]
            full = Counter((("F" if base[r]["label"] else "U"), "full=true" in cache.get(f"{flags}|{r}", {}).get("info", ""))
                           for r in ch)
            fail = sum(cache.get(f"{flags}|{r}", {}).get("status") != "ok" for r in ch)
            print(flags, "changed", len(ch), "fail", fail, dict(full), flush=True)
        return
    out = json.loads(OUT.read_text(encoding="utf-8")) if OUT.exists() else {"model": MODEL, "variants": {}}
    for flags in flags_list:
        changed = [rid for rid in base
                   if cache.get(f"{flags}|{rid}", {}).get("status") == "ok"
                   and cache.get(f"|{rid}", {}).get("goals") != cache[f"{flags}|{rid}"]["goals"]
                   and (os.environ.get("K16_ONLY_GAIN") != "1"
                        or ("full=true" in cache[f"{flags}|{rid}"]["info"]
                            and "full=true" not in cache[f"|{rid}"]["info"]))]
        key, prev = flags, {}
        sample = os.environ.get("LLM_SAMPLE", "0")
        if sample != "0":
            # a second sample for the pairs the first run left unknown; proved goals are pooled
            prev = {p["row_id"]: p for p in out["variants"][flags]["pairs"]}
            changed = [rid for rid in changed if prev.get(rid, {}).get("new") == "unknown"]
            key = f"{flags}#sample{sample}"
        goals = {rid: cache[f"{flags}|{rid}"]["goals"] for rid in changed}
        info = {rid: strip_diag(cache[f"{flags}|{rid}"]["info"]) for rid in changed}
        proved = run_variant(stmt, flags, changed, goals, info)
        for rid in changed:
            proved[rid] |= set(prev.get(rid, {}).get("proved", []))
        flips, per_pair = Counter(), []
        for rid in changed:
            p = base[rid]
            old = final_verdict(p)
            new = final_verdict({"verdict": g1.classify(proved[rid] - {"split_r", "split_s"}), "proved": proved[rid],
                                 "canon_info": info[rid], "closed": p.get("closed")})
            flips[f"{'F' if p['label'] else 'U'}:{old}->{new}"] += 1
            per_pair.append({"row_id": rid, "label": p["label"], "old": old, "new": new, "new_info": info[rid],
                             "proved": sorted(proved[rid])})
        out["variants"][key] = {"changed": len(changed), "flips": dict(sorted(flips.items())), "pairs": per_pair}
        print(flags, "changed", len(changed), dict(sorted(flips.items())), f"{time.time() - t0:.0f}s", flush=True)
        tmp = OUT.with_suffix(f".{os.getpid()}.tmp")
        tmp.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
        os.replace(tmp, OUT)


if __name__ == "__main__":
    main()
