#!/usr/bin/env python3
"""K15: what each budget level of K11 costs, for the closed and the component check.

Replays `k11_budget` for one model from the caches alone (LLM_CACHE_ONLY=1, EXTRA=1) and
counts, per side and level, the model calls, their prompt and completion tokens (read from
the cached responses), and the Lean checks from L1 on. Those checks all run under the same
heartbeat limit, so their number stands in for Lean time, which the runner does not record
per item; L0 is fixed tactics on both sides and costs no model call. The verdict counts are recomputed as in K11 and compared with its stored table.

Usage: k15_cost.py MODEL        writes data/real/k15_cost_<model>.json
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import sys
import threading
from collections import defaultdict
from pathlib import Path

os.environ["LLM_CACHE_ONLY"] = "1"
os.environ["EXTRA"] = "1"
sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import f8_strong as f8
import f9_canon as f9
import g1_full as g1
import k11_budget as k11
import llm
from runner import ROOT

LOCK = threading.Lock()
COST = defaultdict(lambda: defaultdict(int))
STATE = {"side": "comp", "level": "L0"}
NEXT = {"g0": "L1", "g1": "L2", "g2": "L3", "k8": "L2", "k8r": "L3"}
LEVEL_OF_TAG = {"g0": "L0", "g1": "L1", "g2": "L2", "g3": "L3", "k8": "L1", "k8r": "L2", "k8rr": "L3"}


def usage_of(model, messages, temperature, sample, max_tokens) -> dict:
    sample = sample or int(os.environ.get("LLM_SAMPLE", "0"))
    key = hashlib.sha256(
        json.dumps([model, messages, temperature, sample, max_tokens], ensure_ascii=False).encode()
    ).hexdigest()[:32]
    f = llm.CACHE / f"{key}.json"
    return (json.loads(f.read_text(encoding="utf-8")).get("usage") or {}) if f.exists() else {}


def counted_chat(model, messages, temperature=0.0, sample=0, max_tokens=4096, retries=4):
    side, level = STATE["side"], STATE["level"]
    try:
        out = llm.chat(model, messages, temperature=temperature, sample=sample, max_tokens=max_tokens, retries=retries)
    except RuntimeError:
        with LOCK:
            COST[(side, level)]["cache_miss"] += 1
        raise
    u = usage_of(model, messages, temperature, sample, max_tokens)
    with LOCK:
        c = COST[(side, level)]
        c["calls"] += 1
        c["prompt_tokens"] += u.get("prompt_tokens") or 0
        c["completion_tokens"] += u.get("completion_tokens") or 0
    return out


def counted_prove_items(jobs, tag):
    COST[("comp", LEVEL_OF_TAG[tag])]["lean_checks"] += len(jobs)
    res = _prove_items(jobs, tag)
    if tag in NEXT:
        STATE["level"] = NEXT[tag]
    return res


def counted_check_round(jobs, tag):
    COST[("closed", LEVEL_OF_TAG[tag])]["lean_checks"] += len(jobs)
    res = _check_round(jobs, tag)
    if tag in NEXT:
        STATE["level"] = NEXT[tag]
    return res


def counted_closed(model, pairs):
    STATE.update(side="closed", level="L1")
    return _closed(model, pairs)


_prove_items, _check_round, _closed = g1.prove_items, f8.check_round, k11.closed
for mod in (g1, f8, f9, f2):
    mod.chat = counted_chat
g1.prove_items = k11.g1.prove_items = counted_prove_items
f8.check_round = k11.f8.check_round = counted_check_round
k11.closed = counted_closed


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    model = sys.argv[1]
    out = ROOT / "data" / "real" / f"k11_budget_{k11.short(model)}.json"
    stored = json.loads(out.read_text(encoding="utf-8"))
    bak = out.with_suffix(".bak")
    shutil.copy2(out, bak)
    try:
        k11.main()
        replay = json.loads(out.read_text(encoding="utf-8"))
    finally:
        os.replace(bak, out)
    cost = {f"{s}/{l}": dict(v) for (s, l), v in sorted(COST.items(), key=lambda kv: (kv[0][0], kv[0][1]))}
    summary = {"model": model, "table_matches_k11": replay["table"] == stored["table"],
               "table": replay["table"], "cost": cost}
    dst = ROOT / "data" / "real" / f"k15_cost_{k11.short(model)}.json"
    dst.write_text(json.dumps(summary, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
