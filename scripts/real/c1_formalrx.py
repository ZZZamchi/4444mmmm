#!/usr/bin/env python3
"""C1: our certified-goal protocol on the FormalRx-CC eval204 benchmark.

Each FormalRx-CC item gives a candidate and an intended Lean definition with the same
arguments (a predicate, a term, or a premise). Instead of asking for a free-form witness, we
state fixed kernel goals over the shared arguments xs:

    Prop:     ci  := ∀ xs, C xs → I xs        nci := ¬ ∀ xs, C xs → I xs
              ic  := ∀ xs, I xs → C xs        nic := ¬ ∀ xs, I xs → C xs
    term:     eq  := ∀ xs, C xs = I xs        neq := ¬ ∀ xs, C xs = I xs
    premise:  the Prop goals, plus vac := ∀ xs, ¬ C xs and sat := ∃ xs, I xs

The semantic relation is read off the proved goals, so every non-unknown verdict carries a
kernel certificate whose meaning is fixed in advance. Goals go through a fixed tactic tier,
a bounded witness search over small values of base-typed arguments (no LLM), then one LLM
proposal per pair and one repair round per failed open goal.

Usage: c1_formalrx.py [MODEL]       Writes data/real/c1_results_<model>.json.
"""

from __future__ import annotations

import json
import re
import sys
import time
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from f7_component import MAX_TOKENS, PROVE
from f8_provers import REPAIR, clean
from g1_full import parse_sections
from llm import chat
from runner import ROOT, Item, check, split_imports

CCF = ROOT / "data" / "real" / "raw" / "papers" / "ccf"
DATA = CCF / "data" / "formalrx_cc_eval204.jsonl"
MODEL = sys.argv[1] if len(sys.argv) > 1 else "openai/gpt-4.1-mini"
OUT = ROOT / "data" / "real" / f"c1_results_{MODEL.split('/')[-1]}.json"
LEAN_WORKERS = 2

DEF_RE = re.compile(r"^def (\w+)\s*(.*?)\s*:\s*([^:=]+?)\s*:=\s*(.*)$", re.DOTALL)
TAC = (
    "(try simp only [{defs}]) <;> first | decide | (norm_num; done) | omega | (intros; omega) "
    "| (push_neg; first | exact ⟨0, by norm_num⟩ | exact ⟨1, by norm_num⟩ | exact ⟨-1, by norm_num⟩) "
    "| (aesop; done) | tauto"
)
SEARCH_GOALS = ("nci", "nic", "neq", "sat")
MAX_TUPLES = 160
PROP_GOALS = ("ci", "nci", "ic", "nic")
TERM_GOALS = ("eq", "neq")
PREMISE_GOALS = (*PROP_GOALS, "vac", "sat")


def binders(s: str) -> list[tuple[str, str]]:
    """Top-level `(a b : T)` groups -> [(name, T), ...]."""
    out, depth, start = [], 0, None
    for i, ch in enumerate(s):
        if ch in "([{":
            if depth == 0:
                start = i
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth == 0:
                names, _, ty = s[start + 1:i].partition(":")
                out.extend((n, ty.strip()) for n in names.split())
    return out


def pair_of(x: dict) -> dict:
    c = DEF_RE.match(x["candidate_statement"].strip())
    i = DEF_RE.match(x["intended_statement"].strip())
    cb, ib = binders(c.group(2)), binders(i.group(2))
    assert [t for _, t in cb] == [t for _, t in ib], x["idx"]
    vs = [f"v{k}" for k in range(len(cb))]
    quant = "∀ " + " ".join(f"({v} : {t})" for v, (_, t) in zip(vs, cb)) + ", " if cb else ""
    exq = "∃ " + " ".join(f"({v} : {t})" for v, (_, t) in zip(vs, cb)) + ", " if cb else ""
    ca = " ".join([c.group(1), *vs])
    ia = " ".join([i.group(1), *vs])
    kind = "premise" if c.group(1).endswith("Premise") else "prop" if c.group(3) == "Prop" else "term"
    goals = {}
    if kind == "term":
        goals["eq"] = f"{quant}{ca} = {ia}"
        goals["neq"] = f"¬ ({quant}{ca} = {ia})"
    else:
        goals["ci"] = f"{quant}{ca} → {ia}"
        goals["nci"] = f"¬ ({quant}{ca} → {ia})"
        goals["ic"] = f"{quant}{ia} → {ca}"
        goals["nic"] = f"¬ ({quant}{ia} → {ca})"
    if kind == "premise":
        goals["vac"] = f"{quant}¬ {ca}"
        goals["sat"] = f"{exq}{ia}" if cb else ia
    imports, rest = split_imports(x["header"])
    nc = "noncomputable section" in rest
    rest = rest.replace("noncomputable section", "").strip()
    defs = [("noncomputable " if nc else "") + s.strip()
            for s in (x["candidate_statement"], x["intended_statement"])]
    return {"kind": kind, "imports": imports, "pre": "\n".join([rest, *defs]).strip(),
            "names": [c.group(1), i.group(1)], "goals": goals, "types": [t for _, t in cb],
            "bodies": c.group(4) + " " + i.group(4)}


def values(ty: str, bodies: str) -> list[str] | None:
    """Small candidate values of a base type: 0..3, -1, and every literal of the bodies ±1."""
    ty = ty.replace("ℕ", "Nat").replace("ℤ", "Int").replace("ℝ", "Real").replace("Prod Nat Nat", "Nat × Nat")
    if ty == "Bool":
        return ["true", "false"]
    if ty == "Nat × Nat":
        return [f"({a}, {b})" for a in range(3) for b in range(3)]
    if ty not in ("Nat", "Int", "Real"):
        return None
    lits = {int(n) for n in re.findall(r"\d+", bodies)}
    vals = {0, 1, 2, 3, *lits, *(n + 1 for n in lits), *(n - 1 for n in lits)}
    if ty != "Nat":
        vals.add(-1)
    out = [f"({v} : {ty})" for v in sorted(vals) if ty != "Nat" or v >= 0]
    if ty == "Real":
        out += [f"(({a} : Real) / {b})" for a, b in re.findall(r"(\d+)\s*/\s*(\d+)", bodies)]
    return out


def search_tac(p: dict, goal: str) -> str | None:
    """Bounded witness search: one `first` branch per tuple of small values, checked by Lean."""
    pools = [values(t, p["bodies"]) for t in p["types"]]
    if not pools or any(v is None for v in pools):
        return None
    tuples = [[]]
    for pool in pools:
        tuples = [t + [v] for t in tuples for v in pool][:MAX_TUPLES]
    defs = ", ".join(p["names"])
    if goal == "sat":
        branches = [f"(exact ⟨{', '.join(t)}, by norm_num [{defs}]⟩)" for t in tuples]
        return "first\n  " + "\n  ".join(f"| {b}" for b in branches)
    branches = [f"(have hw := h {' '.join(t)}; norm_num [{defs}] at hw; done)" for t in tuples]
    return "intro h\n  first\n  " + "\n  ".join(f"| {b}" for b in branches)


def relation(kind: str, proved: set[str]) -> str:
    if kind == "term":
        return "local_delta" if "neq" in proved else "equivalent" if "eq" in proved else "unknown"
    if kind == "premise" and "vac" in proved:
        return "candidate_vacuous"
    c_to_i = True if "ci" in proved else False if "nci" in proved else None
    i_to_c = True if "ic" in proved else False if "nic" in proved else None
    table = {(True, True): "equivalent", (False, True): "candidate_weaker",
             (True, False): "candidate_stronger", (False, False): "candidate_incomparable"}
    if (c_to_i, i_to_c) in table:
        return table[(c_to_i, i_to_c)]
    return "inequivalent" if False in (c_to_i, i_to_c) else "unknown"


def prove(jobs, tag: str) -> dict:
    """jobs: list of ((key, goal), pair, proof)."""
    items, keys = [], []
    for (key, goal), p, proof in jobs:
        body = (f"{p['pre']}\nset_option maxHeartbeats 200000 in\n"
                f"theorem {tag}_{goal} : {p['goals'][goal]} := by\n  {proof}")
        items.append(Item(f"{key}:{tag}:{goal}", p["imports"], body))
        keys.append((key, goal))
    res = check(items, batch_size=20, workers=LEAN_WORKERS)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def ok(res) -> bool:
    return res.ok and not res.uses_sorry


def header(p) -> str:
    return "\n".join([*(f"import {m}" for m in p["imports"]), p["pre"]])


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    rows = [json.loads(l) for l in DATA.read_text(encoding="utf-8").splitlines() if l.strip()]
    pairs, key_of = {}, {}
    for x in rows:
        k = f"u{len(pairs):03d}"
        sig = (x["header"], x["candidate_statement"], x["intended_statement"])
        if sig not in key_of:
            key_of[sig] = k
            pairs[k] = pair_of(x)
        x["_key"] = key_of[sig]
    print("items", len(rows), "unique pairs", len(pairs), Counter(p["kind"] for p in pairs.values()), flush=True)

    tac = prove([((k, g), p, TAC.format(defs=", ".join(p["names"])))
                 for k, p in pairs.items() for g in p["goals"]], "t0")
    proved = {k: {g for g in p["goals"] if ok(tac[(k, g)])} for k, p in pairs.items()}
    search_jobs = []
    for k, p in pairs.items():
        for g in p["goals"]:
            tac_g = search_tac(p, g) if g in SEARCH_GOALS and g not in proved[k] else None
            if tac_g:
                search_jobs.append(((k, g), p, tac_g))
    for (k, g), res in prove(search_jobs, "s0").items():
        if ok(res):
            proved[k].add(g)
    tactic = {k: set(v) for k, v in proved.items()}
    print("tactic+search tier", Counter(relation(p["kind"], proved[k]) for k, p in pairs.items()),
          f"{time.time() - t0:.0f}s", flush=True)

    def settled(k) -> bool:
        r = relation(pairs[k]["kind"], proved[k])
        return r not in ("unknown", "inequivalent")

    def work(k):
        p = pairs[k]
        open_goals = [g for g in p["goals"] if g not in proved[k]]
        if settled(k) or not open_goals:
            return k, {}
        text = "\n\n".join(f"theorem {g} : {p['goals'][g]} := by\n  sorry" for g in open_goals)
        try:
            out = chat(MODEL, [{"role": "user", "content": PROVE.format(header=header(p), goals=text)}],
                       temperature=0.2, max_tokens=MAX_TOKENS)
        except RuntimeError:
            return k, {}
        return k, parse_sections(out, open_goals)

    with ThreadPoolExecutor(max_workers=12) as pool:
        props = dict(pool.map(work, pairs))
    shot = prove([((k, g), pairs[k], pf) for k, gs in props.items() for g, pf in gs.items()], "l1")
    for (k, g), res in shot.items():
        if ok(res):
            proved[k].add(g)
    failed = [((k, g), res) for (k, g), res in shot.items() if not ok(res) and not settled(k)]

    def fix(item):
        (k, g), res = item
        p = pairs[k]
        msg = REPAIR.format(header=header(p), name=g, goal=p["goals"][g], proof=props[k][g],
                            errors="\n".join(res.errors)[:3000])
        try:
            out = chat(MODEL, [{"role": "user", "content": msg}], temperature=0.2, max_tokens=MAX_TOKENS)
        except RuntimeError:
            return (k, g), None
        m = re.search(r"```(?:lean4?)?\n(.*?)```", out, flags=re.DOTALL)
        return (k, g), clean(m.group(1)) if m else None

    with ThreadPoolExecutor(max_workers=12) as pool:
        fixes = dict(pool.map(fix, failed))
    for (k, g), res in prove([((k, g), pairs[k], pf) for (k, g), pf in fixes.items() if pf], "l2").items():
        if ok(res):
            proved[k].add(g)

    per, conf, conf_tac = [], defaultdict(Counter), defaultdict(Counter)
    for x in rows:
        k = x["_key"]
        pred = relation(pairs[k]["kind"], proved[k])
        conf[x["semantic_relation"]][pred] += 1
        conf_tac[x["semantic_relation"]][relation(pairs[k]["kind"], tactic[k])] += 1
        per.append({"idx": x["idx"], "key": k, "kind": pairs[k]["kind"], "gold": x["semantic_relation"],
                    "witness_type": x["witness_type"], "pred": pred, "proved": sorted(proved[k]),
                    "tactic": sorted(tactic[k])})
    summary = {"model": MODEL, "items": len(rows), "unique_pairs": len(pairs),
               "confusion": {g: dict(c) for g, c in conf.items()},
               "confusion_tactic_only": {g: dict(c) for g, c in conf_tac.items()},
               "seconds": round(time.time() - t0, 1), "pairs": per}
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "pairs"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
