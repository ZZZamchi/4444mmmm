#!/usr/bin/env python3
"""K1: re-check the closed-equivalence proofs behind suspicious G4 accepts, one per file.

For every G4 pair that MODEL proves closed-equivalent while the label is unfaithful and the
Opus run does not, the accepted proof is reconstructed from the caches (initial proposal, or
its repair from the cached Lean errors; no new LLM calls unless a cache entry is missing) and
re-checked alone, without the result cache, followed by `#print axioms`.

Usage: k1_audit_proofs.py MODEL      -> data/real/k1_audit_<model>.json
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

MODEL = sys.argv[1] if len(sys.argv) > 1 else "qwen/qwen3.8-27b-nothink"
sys.argv = [sys.argv[0], MODEL]
sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import f7_component as f7
import f8_strong as f8
import g4_pnv as g4
from runner import ROOT, Item, check

D = ROOT / "data" / "real"


def item(r, tag: str, goal: str, text: str, proof: str, extra: str = "") -> Item:
    imports, pre = f2.prelude(r)
    name = re.sub(r"\W", "_", f"{tag}_{goal}")
    return Item(f"{r.row_id}:{tag}:{goal}", imports, f"{pre}\n{f7.thm(name, text, proof, 200000)}{extra}"), name


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    short = MODEL.split("/")[-1]
    mine = {p["row_id"]: p for p in json.loads((D / f"g4_results_{short}.json").read_text(encoding="utf-8"))["pairs"]}
    opus = {p["row_id"]: p for p in json.loads((D / "g4_results.json").read_text(encoding="utf-8"))["pairs"]}
    rows, _ = g4.load()
    pairs, _ = g4.usable(rows)
    stmt = {r.row_id: (r, g, s) for r, g, s in pairs}
    sus = [rid for rid, p in mine.items() if p["closed"] == "proved" and p["relation"] != "faithful"
           and opus.get(rid, {}).get("closed") != "proved"]
    print("suspicious pairs", len(sus), flush=True)
    f2.PROPOSER = f8.MODEL = MODEL
    out = []
    for rid in sus:
        r, g, s = stmt[rid]
        for goal in ("fwd", "bwd"):
            if goal in set(mine[rid].get("closed_tactic") or []) or goal not in mine[rid]["closed_proved"]:
                continue
            text = f2.goal_text(goal, g, s)
            p0 = f2.propose(r, goal, text)
            src, proof = None, None
            if p0:
                it0, _ = item(r, "g4k", goal, text, p0)
                r0 = check([it0])[it0.item_id]
                if r0.ok and not r0.uses_sorry:
                    src, proof = "initial", p0
                else:
                    err = "\n".join(r0.errors) or ("timeout" if r0.timeout else "failed")
                    _, p1 = f8.repair(((rid, goal), r, text, p0, err))
                    if p1:
                        src, proof = "repair", p1
            if proof is None:
                out.append({"row_id": rid, "goal": goal, "source": None})
                continue
            tag = "g4k" if src == "initial" else "g4kr"
            cached, name = item(r, tag, goal, text, proof)
            alone, _ = item(r, tag, goal, text, proof, f"\n#print axioms {name}")
            rc = check([cached])[cached.item_id]
            ra = check([alone], batch_size=1, use_cache=False)[alone.item_id]
            out.append({"row_id": rid, "goal": goal, "source": src, "cached_ok": rc.ok and not rc.uses_sorry,
                        "alone_ok": ra.ok and not ra.uses_sorry, "alone_errors": ra.errors[:3], "proof": proof})
            print(rid, goal, src, "cached", out[-1]["cached_ok"], "alone", out[-1]["alone_ok"], flush=True)
    (D / f"k1_audit_{short}.json").write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
