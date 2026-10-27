#!/usr/bin/env python3
"""K3: direction of certified rejects.

For every reject with both regrouping certificates (G1, G4, D2), the goals of
`ExperimentsMathlib.CanonV2Dir` over the same canonical components are tried:

    pimp   ∀ x̄, (H_R → C_R) ↔ (H_S → C_S)     vacuity-only reject (T6.vacuity_only_reject)
    npimp  ¬ pimp                              the pointwise claims differ somewhere
    rs     ∀ x̄, (H_R → C_R) → (H_S → C_S)     S claims at most R pointwise, so Cl R → Cl S
    sr     the converse

first with fixed tactics, then one proposal and one repair round of the model for the goals
still open. Classes: vacuity_only (pimp, or rs and sr), weaker (rs: Cl R → Cl S), stronger
(sr), differs (npimp only), unknown; `npimp` with a direction makes the direction strict.

Usage: k3_direction.py [g1|g4|d2 ...]   writes data/real/k3_direction.json
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
import g1_full as g1
from f9_canon import repair
from realdata import proofnetverif
from runner import ROOT, Item, _build, _run_file, check
from stmt import to_prop

D = ROOT / "data" / "real"
OUT = D / "k3_direction.json"
MODEL = "anthropic/claude-opus-5.5"
DIR_IMPORT = "ExperimentsMathlib.CanonV2Dir"
DIR_GOALS = ("pimp", "npimp", "rs", "sr")
DIR_TAC = (
    "first | (intros; tauto) | (intros; simp_all; done) | (intro; constructor <;> intros <;> simp_all; done) "
    "| (intros; aesop) | (intros; omega) "
    "| (intros; constructor <;> intros <;> first | omega | linarith | nlinarith | simp_all) "
    "| (push_neg; simp_all; done) | decide"
)


def imports_of(r) -> tuple[tuple[str, ...], str]:
    imports, pre = f2.prelude(r)
    return tuple(sorted(set(imports) | {DIR_IMPORT})), pre


def load(which: str):
    """Returns ({rid: (row, gold, pred)}, [rejected rids])."""
    if which == "d2":
        import d2_select as d2
        raw = json.loads((D / "d2_prove.json").read_text(encoding="utf-8"))["candidates"]
        stmt = {r.row_id: (r, g, s) for r, g, s in d2.load()[0] if r.row_id in raw}
        pairs = [{"row_id": k, **v} for k, v in raw.items()]
    else:
        if which in ("g1", "g5"):
            rows = {r.row_id: r for r in proofnetverif("test")}
            f = "g1_results.json" if which == "g1" else "g5/g1_results_claude-opus-5.5.json"
            res = json.loads((D / f).read_text(encoding="utf-8"))
        else:
            import g4_pnv as g4
            rows = {r.row_id: r for r in g4.load()[0]}
            res = json.loads((D / "g4_results.json").read_text(encoding="utf-8"))
        pairs = res["pairs"]
        stmt = {}
        for p in pairs:
            r = rows[p["row_id"]]
            g, s = to_prop(r.gold), to_prop(r.pred)
            if g is not None and s is not None:
                stmt[r.row_id] = (r, f2.normalize(g), f2.normalize(s))
    rej = [p["row_id"] for p in pairs if p.get("verdict") == "reject" and p.get("split_checked") and p["row_id"] in stmt]
    return stmt, rej


def dir_goal_texts(stmt, rids) -> dict[str, dict[str, str]]:
    groups: dict[tuple, list] = {}
    for rid in rids:
        r, g, s = stmt[rid]
        imports, pre = imports_of(r)
        groups.setdefault(imports, []).append(Item(rid, imports, f"{pre}\n#canon2_dir_goals {g1.lean_str(rid)} ({g}) ({s})"))
    batches = [g[i:i + 10] for g in groups.values() for i in range(0, len(g), 10)]
    out = {}

    def run(batch):
        text, _ = _run_file(_build(batch)[0], 900)
        return text

    with ThreadPoolExecutor(max_workers=6) as pool:
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
                f"canon2_dir_prove {tag}_{goal} ({g}) ({s}) {goal} := by\n  {proof}")
        items.append(Item(f"{rid}:{tag}:{goal}", imports, body))
        keys.append((rid, goal))
    res = check(items, batch_size=10, workers=6)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def ok(v) -> bool:
    return v.ok and not v.uses_sorry


def klass(p: set) -> str:
    if "pimp" in p or {"rs", "sr"} <= p:
        return "vacuity_only"
    if "rs" in p:
        return "weaker"
    if "sr" in p:
        return "stronger"
    return "differs" if "npimp" in p else "unknown"


def open_goals(p: set) -> list[str]:
    if klass(p) == "vacuity_only":
        return []
    if "npimp" in p:
        return [g for g in ("rs", "sr") if g not in p]
    return [g for g in DIR_GOALS if g not in p]


def run(which: str) -> dict:
    t0 = time.time()
    stmt, rej = load(which)
    proved = {rid: set() for rid in rej}
    src: dict[tuple, str] = {}
    for k, v in prove(stmt, [((rid, g), DIR_TAC) for rid in rej for g in DIR_GOALS], "k3t").items():
        if ok(v):
            proved[k[0]].add(k[1])
            src[k] = "tactic"
    print(which, "rejects", len(rej), "tactic", Counter(klass(p) for p in proved.values()), f"{time.time() - t0:.0f}s",
          flush=True)

    todo = [rid for rid in rej if open_goals(proved[rid])]
    texts = dir_goal_texts(stmt, todo)

    def ask(rid):
        return rid, g1.propose(MODEL, stmt[rid][0], texts[rid], open_goals(proved[rid]))

    with ThreadPoolExecutor(max_workers=8) as pool:
        props = dict(pool.map(ask, [rid for rid in todo if rid in texts]))
    jobs = [((rid, g), p) for rid, d in props.items() for g, p in d.items()]
    shot = prove(stmt, jobs, "k3l")
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
        reps = {k: p for k, p in pool.map(fix, fixes.items()) if p}
    for k, v in prove(stmt, list(reps.items()), "k3r").items():
        if ok(v):
            proved[k[0]].add(k[1])
            src[k] = "llm_repair"
    summary = Counter(klass(p) for p in proved.values())
    print(which, "final", dict(summary), "sources", Counter(src.values()), f"{time.time() - t0:.0f}s", flush=True)
    return {"summary": dict(summary), "pairs": {rid: {"proved": sorted(p), "class": klass(p),
                                                      "source": {g: src[(rid, g)] for g in p}}
                                                for rid, p in proved.items()}}


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    out = json.loads(OUT.read_text(encoding="utf-8")) if OUT.exists() else {}
    for which in sys.argv[1:] or ["g1", "g4", "d2"]:
        out[which] = run(which)
        OUT.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
