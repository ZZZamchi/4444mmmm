#!/usr/bin/env python3
"""D2: verdicts on the D1 autoformalization candidates, for best-of-n selection.

Every distinct candidate from `d1_candidates.json` is compared with the corrected
ProofNet-Verified reference of its problem by
  ours     canonical telescope, fixed tactics, one proposal and one repair (as in G4)
  closed   closed equivalence, tactic tiers then proposal and repair (as in G4)
  judges   the J1 prompts (reference-based for all models, reference-free for Opus)
Candidates are processed in chunks so that an interrupted run resumes from the caches.

Usage: d2_select.py prove|judge
    Writes data/real/d2_prove.json or data/real/d2_judge.json (merged with earlier runs).
"""

from __future__ import annotations

import hashlib
import json
import os
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import g1_full as g1
import g4_pnv as g4
import j1_judge as j1
from f7_component import classify
from runner import ROOT

D = ROOT / "data" / "real"
OUT = {"prove": D / "d2_prove.json", "judge": D / "d2_judge.json"}
MODEL = "anthropic/claude-opus-5.5"
JUDGES = [("anthropic/claude-opus-5.5", "ref"), ("anthropic/claude-opus-5.5", "nl"),
          ("deepseek/deepseek-v4.1-flash", "ref"), ("openai/gpt-4.1-mini", "ref")]
CHUNK = 300


def load() -> tuple[list, dict]:
    d1 = json.loads((D / "d1_candidates.json").read_text(encoding="utf-8"))
    rows, _ = g4.load()
    by = {r.row_id: r for r in rows}
    pairs, ref = [], {}
    for c in d1["candidates"]:
        r = replace(by[c["problem"]], row_id=c["cand_id"], pred=c["src"], correct=None)
        pairs.append((r, c["gold"], f2.normalize(c["prop"])))
        ref[c["cand_id"]] = by[c["problem"]].gold
    return pairs, ref


def prove(pairs, old: dict, out: Path) -> None:
    g1.MODEL = g4.MODEL = MODEL
    # the canon cache is keyed by candidate id, which is only stable for one D1 file
    g1.CANON_CACHE = D / f"d2_canon_{d1_digest()}.json"
    todo = [x for x in pairs if x[0].row_id not in old]
    t0 = time.time()
    for i in range(0, len(todo), CHUNK):
        part = todo[i:i + CHUNK]
        canon = g1.canon_all(part)
        stmt = {r.row_id: (r, g, s) for r, g, s in part}
        proved, tactic = g1.component(part, stmt, canon, t0)
        cl = g4.closed(part, t0)
        for r, _, _ in part:
            rid, c = r.row_id, canon[r.row_id]
            old[rid] = {"verdict": classify(proved[rid]) if c["status"] == "ok" else c["status"],
                        "proved": sorted(proved.get(rid, ())), "tactic": sorted(tactic.get(rid, ())),
                        "closed": f2.verdict(cl[rid])["status"], "closed_proved": sorted(cl[rid]),
                        "closed_tactic": sorted(g4.CLOSED_TACTIC.get(rid, ())), "canon_info": c.get("info")}
        save(out, old)
        print("chunk", i // CHUNK, len(old), dict(Counter(v["verdict"] for v in old.values())),
              dict(Counter(v["closed"] for v in old.values())), f"{time.time() - t0:.0f}s", flush=True)


def judge(pairs, ref: dict, old: dict, out: Path) -> None:
    jobs = []
    for r, _, _ in pairs:
        x = {"nl": r.nl, "header": r.header, "ref": ref[r.row_id], "cand": r.pred}
        for m, st in JUDGES:
            key = f"{m.split('/')[-1]}:{st}"
            if key not in old.get(r.row_id, {}):
                jobs.append((r.row_id, key, m, st, x))
    print("judge jobs", len(jobs), flush=True)

    def work(job):
        rid, key, m, st, x = job
        r = j1.judge(m, st, x)
        return rid, key, r["verdict"] if r["reply_tail"] else None

    with ThreadPoolExecutor(max_workers=int(os.environ.get("JUDGE_WORKERS", 32))) as pool:
        for i, (rid, key, v) in enumerate(pool.map(work, jobs)):
            if v is not None:
                old.setdefault(rid, {})[key] = v
            if (i + 1) % 500 == 0:
                save(out, old)
                print("judged", i + 1, flush=True)
    save(out, old)
    for key in sorted({k for v in old.values() for k in v}):
        print(key, dict(Counter(v.get(key) for v in old.values())))


def d1_digest() -> str:
    return hashlib.sha256((D / "d1_candidates.json").read_bytes()).hexdigest()[:10]


def save(out: Path, v: dict) -> None:
    out.write_text(json.dumps({"model": MODEL, "d1": d1_digest(), "candidates": v}, indent=1,
                              ensure_ascii=False) + "\n", encoding="utf-8")


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    which = sys.argv[1]
    out = OUT[which]
    pairs, ref = load()
    prev = json.loads(out.read_text(encoding="utf-8")) if out.exists() else {}
    old = prev.get("candidates", {}) if prev.get("d1") == d1_digest() else {}
    print(which, "candidates", len(pairs), "done", len(old), flush=True)
    if which == "prove":
        prove(pairs, old, out)
    else:
        judge(pairs, ref, old, out)


if __name__ == "__main__":
    main()
