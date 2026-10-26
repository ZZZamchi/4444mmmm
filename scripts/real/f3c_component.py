#!/usr/bin/env python3
"""F3c: the F3 ranking rescored with component verdicts.

Takes the stored F3 predictions (six systems x 60 problems), keeps those that compile, and
runs the G1 component pipeline (CanonV2 telescopes, fixed tactics, one proposal and one
repair round) against the gold. A system scores the share of problems whose prediction is
component-accepted; the closed scores come from data/real/f3_results.json.

Usage: f3c_component.py [MODEL]          Writes data/real/f3c_results.json.
"""

from __future__ import annotations

import json
import random
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import g1_full as g1
import runner
from f3_ranking import OUT as F3_OUT, SYSTEMS, kendall_tau_b
from f7_component import classify
from realdata import PnvRow, proofnetverif
from runner import ROOT, Item
from stmt import to_prop

OUT = ROOT / "data" / "real" / "f3c_results.json"
LEAN_WORKERS = 3
g1.CANON_CACHE = ROOT / "data" / "real" / "f3c_canon.json"
g1.MODEL = sys.argv[1] if len(sys.argv) > 1 else "anthropic/claude-opus-5.5"
g1.check = lambda items, batch_size=10, workers=LEAN_WORKERS: runner.check(items, batch_size=batch_size, workers=LEAN_WORKERS)


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    f3 = json.loads(F3_OUT.read_text(encoding="utf-8"))
    by_stmt = {}
    for r in proofnetverif("test"):
        by_stmt.setdefault(r.stmt_id, r)
    preds = f3["predictions"]
    stmts = sorted({k.split("|", 1)[1] for k in preds})

    items = []
    for key, p in preds.items():
        r = by_stmt[key.split("|", 1)[1]]
        imports, pre = f2.prelude(r)
        body = p if p and "theorem" in p else "example : False := by exact?"
        items.append(Item(key, imports, f"{pre}\n{body}"))
    cres = runner.check(items, batch_size=20, workers=LEAN_WORKERS)

    pairs = []
    for key, p in preds.items():
        r = by_stmt[key.split("|", 1)[1]]
        prop = to_prop(p) if cres[key].ok else None
        if prop is None:
            continue
        row = PnvRow(key, "test", r.stmt_id, r.nl, r.header, r.gold, p, None)
        pairs.append((row, f2.normalize(to_prop(r.gold)), f2.normalize(prop)))
    print("compiled pairs", len(pairs), "of", len(preds), f"{time.time() - t0:.0f}s", flush=True)

    pool_cls = g1.ThreadPoolExecutor
    g1.ThreadPoolExecutor = lambda max_workers: pool_cls(max_workers=LEAN_WORKERS)
    canon = g1.canon_all(pairs)
    g1.ThreadPoolExecutor = pool_cls
    print("canon", Counter(c["status"] for c in canon.values()), f"{time.time() - t0:.0f}s", flush=True)
    stmt = {r.row_id: (r, g, s) for r, g, s in pairs}
    proved, _ = g1.component(pairs, stmt, canon, t0)

    verdicts = {}
    for key in preds:
        if key not in stmt:
            verdicts[key] = "no_compile"
        elif canon[key]["status"] != "ok":
            verdicts[key] = canon[key]["status"]
        else:
            verdicts[key] = classify(proved[key])

    def scores(subset):
        out = {}
        for m in SYSTEMS:
            vs = [verdicts[f"{m}|{s}"] for s in subset]
            out[m] = {"comp_accept": sum(v == "accept" for v in vs) / len(vs),
                      "comp_reject": sum(v == "reject" for v in vs) / len(vs),
                      "comp_off_domain": sum(v == "off_domain" for v in vs) / len(vs)}
        return out

    sc = scores(stmts)
    closed = f3["scores"]
    metrics = ("compile", "t0", "t1", "t2")
    vec = lambda m_key, table: [table[m][m_key] for m in SYSTEMS]
    comp = vec("comp_accept", sc)
    taus = {t: round(kendall_tau_b(vec(t, closed), comp), 3) for t in metrics}
    rng = random.Random(0)
    boot = []
    for _ in range(500):
        sub = [rng.choice(stmts) for _ in stmts]
        boot.append(kendall_tau_b(vec("comp_accept", scores(sub)), comp))
    out = {
        "model": g1.MODEL,
        "n_problems": len(stmts),
        "scores": {m: {**{k: round(v, 3) for k, v in sc[m].items()},
                       **{t: closed[m][t] for t in metrics}} for m in SYSTEMS},
        "rankings": {"comp_accept": sorted(SYSTEMS, key=lambda m: -sc[m]["comp_accept"]),
                     **{t: sorted(SYSTEMS, key=lambda m: -closed[m][t]) for t in metrics}},
        "tau_closed_vs_comp": taus,
        "bootstrap_comp_self_tau_mean": round(sum(boot) / len(boot), 3),
        "verdict_counts": {m: dict(Counter(verdicts[f"{m}|{s}"] for s in stmts)) for m in SYSTEMS},
        "seconds": round(time.time() - t0, 1),
        "verdicts": verdicts,
    }
    OUT.write_text(json.dumps(out, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in out.items() if k != "verdicts"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
