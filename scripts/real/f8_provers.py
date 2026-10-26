#!/usr/bin/env python3
"""F8: is the low component-level refutation rate of F7 a method limit or a model limit?

Takes the F7 pairs whose split passed Lean but whose verdict stayed unknown, keeps the
F7 decomposition, and retries the open component goals with stronger proposers using the
same prompt as F7 (one shot), then one repair round that feeds back Lean's errors.

Writes data/real/f8_results.json.
"""

from __future__ import annotations

import json
import re
import sys
import textwrap
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from f2_oracle import FORBIDDEN, prelude
from f7_component import LLM_GOALS, MAX_TOKENS, OUT as F7_OUT, PROVE, classify, goal_texts, thm
from llm import chat
from realdata import proofnetverif
from runner import ROOT, Item, check, tactic_body

OUT = ROOT / "data" / "real" / "f8_results.json"
MODELS = ("deepseek/deepseek-v4.1-flash", "anthropic/claude-sonnet-5.5", "openai/gpt-5.6-sol",
          "deepseek/deepseek-v4-pro-0813")

REPAIR = """You are an expert in Lean 4 and Mathlib. Environment (already present):

{header}

Your proof of this theorem was rejected by Lean.

theorem {name} : {goal} := by
  {proof}

Lean errors:
{errors}

If the theorem is false, reply `skip`. Otherwise reply with ONLY a corrected tactic proof
inside one ```lean code block. Never use sorry, admit or native_decide."""


def header_of(r) -> str:
    return r.header.strip() + "\nuniverse u\nset_option autoImplicit false"


def clean(body: str) -> str | None:
    raw, body = body, body.strip()
    if not body or body == "skip" or FORBIDDEN.search(body):
        return None
    return tactic_body(raw)


def propose(model: str, r, d: dict, goals: list[str]) -> dict[str, str]:
    gt = goal_texts(d)
    text = "\n\n".join(f"theorem {g} : {gt[g]} := by\n  sorry" for g in goals)
    try:
        out = chat(model, [{"role": "user", "content": PROVE.format(header=header_of(r), goals=text)}],
                   temperature=0.2, max_tokens=MAX_TOKENS)
    except RuntimeError:
        return {}
    res = {}
    for name, body in re.findall(r"###\s*(\w+)\s*```(?:lean)?\n(.*?)```", out, flags=re.DOTALL):
        p = clean(body)
        if name in goals and p:
            res[name] = p
    return res


def repair(model: str, r, d: dict, goal: str, proof: str, errors: list[str]) -> str | None:
    gt = goal_texts(d)
    msg = REPAIR.format(header=header_of(r), name=goal, goal=gt[goal], proof=proof,
                        errors="\n".join(errors)[:3000])
    try:
        out = chat(model, [{"role": "user", "content": msg}], temperature=0.2, max_tokens=MAX_TOKENS)
    except RuntimeError:
        return None
    m = re.search(r"```(?:lean)?\n(.*?)```", out, flags=re.DOTALL)
    return clean(m.group(1)) if m else None


def lean_check(jobs: list[tuple], tag: str) -> dict:
    items, keys = [], []
    for (rid, goal), (r, d, proof) in jobs:
        imports, pre = prelude(r)
        items.append(Item(f"{rid}:{tag}:{goal}", imports, f"{pre}\n{thm(tag + '_' + goal, goal_texts(d)[goal], proof, 200000)}"))
        keys.append((rid, goal))
    res = check(items, batch_size=10, workers=6)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    f7 = json.loads(F7_OUT.read_text(encoding="utf-8"))
    rows = {r.row_id: r for r in proofnetverif("test")}
    targets = [p for p in f7["pairs"] if p["verdict"] == "unknown"]
    print("targets", len(targets), Counter(p["label"] for p in targets))

    summary = {"models": {}, "targets": len(targets)}
    per_pair = {p["row_id"]: {"label": p["label"], "f7_proved": p["proved"]} for p in targets}
    for model in MODELS:
        tag = re.sub(r"\W", "_", model.split("/")[1])

        def work(p):
            open_goals = [g for g in LLM_GOALS if g not in p["proved"]]
            return p["row_id"], propose(model, rows[p["row_id"]], p["decomposition"], open_goals)

        with ThreadPoolExecutor(max_workers=12) as pool:
            props = dict(pool.map(work, targets))
        dec = {p["row_id"]: p["decomposition"] for p in targets}
        jobs = [((rid, g), (rows[rid], dec[rid], pr)) for rid, gs in props.items() for g, pr in gs.items()]
        shot = lean_check(jobs, tag + "_s")
        proved = {p["row_id"]: set(p["proved"]) for p in targets}
        for (rid, g), res in shot.items():
            if res.ok and not res.uses_sorry:
                proved[rid].add(g)
        one_shot = {rid: classify(s) for rid, s in proved.items()}
        print(model, "one-shot", Counter((per_pair[r]["label"], v) for r, v in one_shot.items()), f"{time.time() - t0:.0f}s")

        failed = [((rid, g), res) for (rid, g), res in shot.items() if not res.ok and g not in proved[rid]]

        def fix(item):
            (rid, g), res = item
            return (rid, g), repair(model, rows[rid], dec[rid], g, props[rid][g], res.errors)

        with ThreadPoolExecutor(max_workers=12) as pool:
            fixes = dict(pool.map(fix, failed))
        jobs = [((rid, g), (rows[rid], dec[rid], pr)) for (rid, g), pr in fixes.items() if pr]
        rep = lean_check(jobs, tag + "_r")
        for (rid, g), res in rep.items():
            if res.ok and not res.uses_sorry:
                proved[rid].add(g)
        after = {rid: classify(s) for rid, s in proved.items()}
        print(model, "after repair", Counter((per_pair[r]["label"], v) for r, v in after.items()), f"{time.time() - t0:.0f}s")

        for rid in per_pair:
            per_pair[rid][tag] = {"one_shot": one_shot[rid], "repair": after[rid], "proved": sorted(proved[rid])}
        summary["models"][model] = {
            "proposals": sum(len(v) for v in props.values()),
            "one_shot": {f"{lab}:{v}": n for (lab, v), n in Counter((per_pair[r]["label"], v) for r, v in one_shot.items()).items()},
            "repair": {f"{lab}:{v}": n for (lab, v), n in Counter((per_pair[r]["label"], v) for r, v in after.items()).items()},
            "repair_attempts": len(jobs),
        }
    summary["seconds"] = round(time.time() - t0, 1)
    summary["pairs"] = per_pair
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "pairs"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
