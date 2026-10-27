#!/usr/bin/env python3
"""K7: pointwise collapse of accepts.

For every accept in G1 and G4 (any prover tier) the goals of `ExperimentsMathlib.CanonV2Pt`
over the same canonical components are tried:

    ptr    ∀ x̄, C_R        the conclusion of R holds at every aligned point, hypotheses dropped
    pts    ∀ x̄, C_S        the same for S
    pfr    ∀ x̄, ¬ C_R      the conclusion of R fails at every aligned point
    pfs    ∀ x̄, ¬ C_S
    nptr, npts, npfr, npfs  their negations

An accept proves C_R ↔ C_S at every point, so the R- and S-goals stand or fall together. If
the conclusion is constant over the aligned points (ptr/pts or pfr/pfs proved) the accept is
`collapsed`: it certifies only ∀ x̄, H_R ↔ H_S (Proposition prop:residue; with an empty prefix
this is the closed comparison of two true or two false statements). If both kinds of constancy
are refuted (nptr/npts and npfr/npfs) it is `informative`; otherwise `open`. Fixed tactics
first, then one proposal and one repair round of the model.

Usage: k7_pointwise.py [g1|g4|g5 ...]   writes data/real/k7_pointwise.json
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
from a1_local import label, local
from f9_canon import repair
from realdata import proofnetverif
from runner import ROOT, Item, _build, _run_file, check
from stmt import to_prop

D = ROOT / "data" / "real"
OUT = D / "k7_pointwise.json"
MODEL = "anthropic/claude-opus-5.5"
PT_IMPORT = "ExperimentsMathlib.CanonV2Pt"
PT_GOALS = ("ptr", "pts", "nptr", "npts", "pfr", "pfs", "npfr", "npfs")
WORKERS = int(os.environ.get("K7_WORKERS", "4"))
PT_TAC = (
    "first | (intros; tauto) | (intros; simp_all; done) | (intros; aesop) | (intros; omega) "
    "| (intros; first | omega | linarith | nlinarith | simp_all | positivity) "
    "| (push_neg; first | (exact ⟨0, by simp⟩) | (exact ⟨1, by simp⟩) | (refine ⟨_, ?_⟩ <;> simp_all) | simp_all; done) "
    "| decide"
)
RESULTS = {
    "g1": ["g1_results.json", "g1_results_deepseek-v4.1-flash.json", "g1_results_gpt-4.1-mini.json",
           "g1_results_qwen3.8-27b-nothink.json"],
    "g4": ["g4_results.json", "g4_results_deepseek-v4.1-flash.json", "g4_results_gpt-4.1-mini.json",
           "g4_results_qwen3.8-27b-nothink.json"],
    "g5": ["g5/g1_results_claude-opus-5.5.json"],
}


def imports_of(r) -> tuple[tuple[str, ...], str]:
    imports, pre = f2.prelude(r)
    return tuple(sorted(set(imports) | {PT_IMPORT})), pre


def load(which: str):
    """Returns ({rid: (row, gold, pred)}, {rid: info about the accept})."""
    if which in ("g1", "g5"):
        rows = {r.row_id: r for r in proofnetverif("test")}
    else:
        import g4_pnv as g4
        rows = {r.row_id: r for r in g4.load()[0]}
    acc: dict[str, dict] = {}
    for f in RESULTS[which]:
        path = D / f
        if not path.exists():
            continue
        for p in json.loads(path.read_text(encoding="utf-8"))["pairs"]:
            if p.get("verdict") != "accept":
                continue
            a = acc.setdefault(p["row_id"], {"label": label(p), "local": local(p.get("canon_info")), "tiers": []})
            a["tiers"].append(f)
    stmt = {}
    for rid in acc:
        r = rows[rid]
        g, s = to_prop(r.gold), to_prop(r.pred)
        if g is not None and s is not None:
            stmt[rid] = (r, f2.normalize(g), f2.normalize(s))
    return stmt, {k: v for k, v in acc.items() if k in stmt}


def pt_goal_texts(stmt, rids) -> dict[str, dict[str, str]]:
    groups: dict[tuple, list] = {}
    for rid in rids:
        r, g, s = stmt[rid]
        imports, pre = imports_of(r)
        groups.setdefault(imports, []).append(Item(rid, imports, f"{pre}\n#canon2_pt_goals {g1.lean_str(rid)} ({g}) ({s})"))
    batches = [g[i:i + 10] for g in groups.values() for i in range(0, len(g), 10)]
    out = {}

    def run(batch):
        text, _ = _run_file(_build(batch)[0], 900)
        return text

    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        for text in pool.map(run, batches):
            for tag, b in re.findall(r"CANON_BEGIN (\S+)\n(.*?)\n?CANON_END \1", text, flags=re.DOTALL):
                if not b.startswith("CANON_FAIL"):
                    out[tag] = dict(re.findall(r"CANON_GOAL (\w+) ::: (.*?)(?=\nCANON_GOAL |\Z)", b, flags=re.DOTALL))
    return out


def prove(stmt, jobs, tag) -> dict:
    items, keys = [], []
    for (rid, goal), proof in jobs:
        r, g, s = stmt[rid]
        imports, pre = imports_of(r)
        body = (f"{pre}\nset_option maxHeartbeats 200000 in\n"
                f"canon2_pt_prove {tag}_{goal} ({g}) ({s}) {goal} := by\n  {proof}")
        items.append(Item(f"{rid}:{tag}:{goal}", imports, body))
        keys.append((rid, goal))
    res = check(items, batch_size=10, workers=WORKERS)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def ok(v) -> bool:
    return v.ok and not v.uses_sorry


def klass(p: set) -> str:
    true_, false_ = bool(p & {"ptr", "pts"}), bool(p & {"pfr", "pfs"})
    not_true, not_false = bool(p & {"nptr", "npts"}), bool(p & {"npfr", "npfs"})
    if (true_ and not_true) or (false_ and not_false):
        return "inconsistent"
    if true_ or false_:
        return "collapsed"
    return "informative" if not_true and not_false else "open"


def open_goals(p: set) -> list[str]:
    if klass(p) != "open":
        return []
    need = []
    if not p & {"nptr", "npts"}:
        need += ["ptr", "pts", "nptr", "npts"]
    if not p & {"npfr", "npfs"}:
        need += ["pfr", "pfs", "npfr", "npfs"]
    return [g for g in need if g not in p]


def run(which: str) -> dict:
    t0 = time.time()
    stmt, acc = load(which)
    rids = sorted(acc)
    proved = {rid: set() for rid in rids}
    src: dict[tuple, str] = {}
    for k, v in prove(stmt, [((rid, g), PT_TAC) for rid in rids for g in PT_GOALS], "k7t").items():
        if ok(v):
            proved[k[0]].add(k[1])
            src[k] = "tactic"
    print(which, "accepts", len(rids), "tactic", Counter(klass(p) for p in proved.values()), f"{time.time() - t0:.0f}s",
          flush=True)

    todo = [rid for rid in rids if open_goals(proved[rid])]
    texts = pt_goal_texts(stmt, todo)

    def ask(rid):
        return rid, g1.propose(MODEL, stmt[rid][0], texts[rid], open_goals(proved[rid]))

    with ThreadPoolExecutor(max_workers=8) as pool:
        props = dict(pool.map(ask, [rid for rid in todo if rid in texts]))
    jobs = [((rid, g), p) for rid, d in props.items() for g, p in d.items()]
    shot = prove(stmt, jobs, "k7l")
    fixes = {}
    for k, v in shot.items():
        if ok(v):
            proved[k[0]].add(k[1])
            src[k] = "llm"
        else:
            fixes[k] = (texts[k[0]][k[1]], dict(jobs)[k], v.errors)

    def fix(item):
        (rid, g), (goal, proof, errs) = item
        return (rid, g), repair(MODEL, stmt[rid][0], g, goal, proof, errs)

    with ThreadPoolExecutor(max_workers=8) as pool:
        reps = {k: p for k, p in pool.map(fix, [x for x in fixes.items() if klass(proved[x[0][0]]) == "open"]) if p}
    for k, v in prove(stmt, list(reps.items()), "k7r").items():
        if ok(v):
            proved[k[0]].add(k[1])
            src[k] = "llm_repair"
    pairs = {rid: {**acc[rid], "proved": sorted(p), "class": klass(p), "source": {g: src[(rid, g)] for g in p}}
             for rid, p in proved.items()}
    summary = {f"{'faithful' if lab else 'unfaithful'}:{'local' if loc else 'residual'}":
               dict(Counter(v["class"] for v in pairs.values() if v["label"] == lab and v["local"] == loc))
               for lab in (True, False) for loc in (True, False)}
    print(which, "final", summary, "sources", Counter(src.values()), f"{time.time() - t0:.0f}s", flush=True)
    return {"summary": summary, "pairs": pairs}


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    out = json.loads(OUT.read_text(encoding="utf-8")) if OUT.exists() else {}
    for which in sys.argv[1:] or ["g1", "g4"]:
        out[which] = run(which)
        OUT.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
