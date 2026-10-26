#!/usr/bin/env python3
"""G4: closed vs component verdicts on ProofNet-Verified (ProofNet# against its manual correction).

ProofNet-Verified (marcusm117) audits every ProofNet# statement by hand, gives a corrected
formalization, the relation of ProofNet# to it (faithful / weaker / stronger / incomparable)
and the truth value of the ProofNet# statement. Each pair is (reference = corrected statement,
candidate = ProofNet# statement), with labels taken from that audit, not from us. Items whose
informal statement is ambiguous or wrong are excluded.

The labels give a sharp test of the collapse theorem: an unfaithful candidate that is still
true is closed-equivalent to the (true) reference, so a strong enough closed oracle must accept
it, while the component criterion must not. Runs, with one strong proposer for both sides:
closed equivalence (F2 tactic tiers t0/t1, then one proposal and one repair), the component
criterion (G1 pipeline) and our port of BEq+.

Usage: g4_pnv.py [MODEL]         Writes data/real/g4_results.json and g4_beqplus.json.
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

import b1_beqplus as b1
import f2_oracle as f2
import f8_strong as f8
import g1_full as g1
from f7_component import classify
from realdata import PnvRow
from runner import ROOT, Item, check
from stmt import to_prop

PNV = ROOT / "data" / "real" / "raw" / "proofnet-verified"
OUT = ROOT / "data" / "real" / "g4_results.json"
BEQ_OUT = ROOT / "data" / "real" / "g4_beqplus.json"
g1.CANON_CACHE = ROOT / "data" / "real" / "g4_canon2.json"
MODEL = sys.argv[1] if len(sys.argv) > 1 else "anthropic/claude-opus-5.5"
g1.MODEL = MODEL
if MODEL != "anthropic/claude-opus-5.5":
    OUT = ROOT / "data" / "real" / f"g4_results_{MODEL.split('/')[-1]}.json"
CLOSED_TACTIC: dict[str, set] = {}


def opens(src: str) -> list[str]:
    return [l.strip() for l in src.splitlines() if l.strip().startswith("open ")]


def as_sorry(stmt: str) -> str:
    s = re.sub(r":=\s*by\s*sorry\s*$", ":= sorry", stmt.strip())
    return s if s.endswith(":= sorry") else s.rstrip().removesuffix(":=").rstrip() + " := sorry"


def load() -> tuple[list[PnvRow], dict]:
    sharp = {}
    for line in (PNV / "data" / "proofnet#" / "proofnet#.jsonl").open(encoding="utf-8"):
        d = json.loads(line)
        book, ex = d["id"].split("|")
        sharp[f"{book.replace('-', '_')}_{ex}"] = d
    tax = {json.loads(l)["stem"]: json.loads(l)
           for l in (PNV / "error_taxonomy" / "proofnet#" / "results.jsonl").open(encoding="utf-8")}
    rows, meta = [], {}
    for line in (PNV / "data" / "proofnet-verified.jsonl").open(encoding="utf-8"):
        m = json.loads(line)
        t = tax[f"proofnet-{m['index']}"]
        rel = t["q2_faithfulness"]
        if rel not in ("faithful", "weaker", "stronger", "incomparable"):
            continue
        s = sharp[m["name"].replace("-", "_")]
        ops = list(dict.fromkeys(opens(m["header"]) + opens(s["lean4_src_header"])))
        helper = m.get("helper", "").strip()
        header = "import Mathlib\n" + "\n".join(ops) + ("\n" + helper if helper else "")
        rid = f"g4-{m['index']}"
        rows.append(PnvRow(rid, "pnv", m["name"], m["informal_stmt"], header,
                           as_sorry(m["formal_stmt"]), as_sorry(s["lean4_formalization"]), rel == "faithful"))
        meta[rid] = {"name": m["name"], "relation": rel, "candidate_true": t["q3_provability"] == "true"}
    return rows, meta


def usable(rows) -> tuple[list, Counter]:
    conv, stats = [], Counter()
    for r in rows:
        g, p = to_prop(r.gold), to_prop(r.pred)
        if g is None or p is None:
            stats["no_conversion"] += 1
            continue
        conv.append((r, f2.normalize(g), f2.normalize(p)))
    items = []
    for r, g, p in conv:
        imports, pre = f2.prelude(r)
        items.append(Item(f"{r.row_id}:elab", imports, f"{pre}\nexample : ({g}) ∧ ({p}) → True := fun _ => trivial"))
    res = check(items, batch_size=25)
    out = []
    for x, it in zip(conv, items):
        if res[it.item_id].ok:
            out.append(x)
        else:
            stats["elab_fail"] += 1
    stats["usable"] = len(out)
    return out, stats


def closed(pairs, t0) -> dict:
    proved = {r.row_id: set() for r, _, _ in pairs}
    for tag, tactic, hb in (("t0", f2.T0, 20000), ("t1", f2.T1, 100000)):
        open_goals = {rid: set(f2.GOALS) - s for rid, s in proved.items()}
        for (rid, goal), good in f2.run_tactic_tier(pairs, tactic, hb, f"g4{tag}", open_goals).items():
            if good:
                proved[rid].add(goal)
        print("closed", tag, f"{time.time() - t0:.0f}s", flush=True)
    CLOSED_TACTIC.update({rid: set(s) for rid, s in proved.items()})
    if os.environ.get("G4_TACTIC_ONLY"):
        return proved
    f8.MODEL = MODEL
    f2.PROPOSER = MODEL
    jobs = [(r, g, p, goal) for r, g, p in pairs for goal in f2.LLM_GOALS if goal not in proved[r.row_id]]

    def work(job):
        r, g, p, goal = job
        text = f2.goal_text(goal, g, p)
        try:
            return (r.row_id, goal), (r, text, f2.propose(r, goal, text))
        except RuntimeError:
            return (r.row_id, goal), (r, text, None)

    with ThreadPoolExecutor(max_workers=12) as pool:
        init = dict(pool.map(work, jobs))
    for rid, goal in f8.propose_and_repair(init, "g4k"):
        proved[rid].add(goal)
    print("closed done", f"{time.time() - t0:.0f}s", flush=True)
    return proved


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    rows, meta = load()
    pairs, stats = usable(rows)
    print("rows", len(rows), dict(stats), f"{time.time() - t0:.0f}s", flush=True)
    stmt = {r.row_id: (r, g, s) for r, g, s in pairs}

    canon = g1.canon_all(pairs)
    print("canon", Counter(c["status"] for c in canon.values()), f"{time.time() - t0:.0f}s", flush=True)
    proved, tactic = g1.component(pairs, stmt, canon, t0)
    cl = closed(pairs, t0)
    if os.environ.get("G4_SKIP_BEQ"):
        beq = {}
    elif BEQ_OUT.exists():
        beq = {p["row_id"]: p["beq_plus"] for p in json.loads(BEQ_OUT.read_text(encoding="utf-8"))["pairs"]}
    else:
        beq = {p["row_id"]: p["beq_plus"] for p in b1.run([r for r, _, _ in pairs], BEQ_OUT)["pairs"]}

    per, table = [], Counter()
    for r, _, _ in pairs:
        rid, m = r.row_id, meta[r.row_id]
        c = canon[rid]
        v = classify(proved[rid]) if c["status"] == "ok" else c["status"]
        cs = f2.verdict(cl[rid])["status"]
        group = "faithful" if m["relation"] == "faithful" else \
            f"unfaithful_{'true' if m['candidate_true'] else 'false'}"
        table[f"{group}|n"] += 1
        table[f"{group}|closed_{cs}"] += 1
        table[f"{group}|comp_{v}"] += 1
        if beq:
            table[f"{group}|beq_{'equiv' if beq.get(rid) else 'not'}"] += 1
        per.append({"row_id": rid, **m, "closed": cs, "closed_proved": sorted(cl[rid]),
                    "closed_tactic": sorted(CLOSED_TACTIC.get(rid, ())), "verdict": v,
                    "proved": sorted(proved.get(rid, ())), "tactic": sorted(tactic.get(rid, ())),
                    "beq_plus": beq.get(rid), "canon_info": c.get("info")})
    summary = {"model": MODEL, "selection": dict(stats), "table": dict(sorted(table.items())),
               "seconds": round(time.time() - t0, 1), "pairs": per}
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "pairs"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
