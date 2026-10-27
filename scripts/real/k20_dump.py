#!/usr/bin/env python3
"""K20: record the Lean items of the full-set runs that the standalone recheck (K5) did not cover.

K5 rechecked the accepted model proofs recorded by the checker up to 18 October (6,544). The
full-set runs of Table full and the second repair round of Table budget were finished later. This
replays them from the caches with `LLM_CACHE_ONLY=1` (no model calls) and `RUNNER_DUMP`, so that
every Lean item they check is written to `cache/dump_post.jsonl`; results go to temporary files and
are compared with the stored ones. `k5_standalone_audit.py` with `K5_DUMP=dump_post.jsonl` then
rechecks a sample of the accepted model proofs alone.

Usage: k20_dump.py      -> data/real/k20_dump.json (replay agreement), cache/dump_post.jsonl
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

S = Path(__file__).resolve().parent
ROOT = S.parents[1]
D = ROOT / "data" / "real"
TMP = D / "k20_tmp"
ENV = {"LLM_CACHE_ONLY": "1", "RUNNER_DUMP": ".", "RUNNER_DUMP_FILE": "dump_post.jsonl", "PYTHONIOENCODING": "utf-8"}
BUDGET = ["anthropic/claude-opus-5.5", "deepseek/deepseek-v4.1-flash"]
FULL = ["qwen/qwen3.8-27b-nothink", "openai/gpt-4.1-mini"]


def run(cmd: list[str], env: dict) -> int:
    with (TMP / "log.txt").open("a", encoding="utf-8") as out:
        return subprocess.call(cmd, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT, env={**os.environ, **ENV, **env})


def main() -> None:
    TMP.mkdir(parents=True, exist_ok=True)
    res = {}
    for model in BUDGET:
        short = model.split("/")[-1]
        out = TMP / f"k11_budget_{short}.json"
        rc = run([sys.executable, str(S / "k11_budget.py"), model], {"EXTRA": "1", "K11_OUT": str(out)})
        stored = json.loads((D / f"k11_budget_{short}.json").read_text(encoding="utf-8"))["table"]
        new = json.loads(out.read_text(encoding="utf-8"))["table"] if out.exists() else None
        res[f"k11:{short}"] = {"exit": rc, "tables_equal": new == stored}
    for model in FULL:
        short = model.split("/")[-1]
        out = TMP / f"g1_results_{short}.json"
        code = (f"import sys; sys.path.insert(0, r'{S}'); import f2_oracle as f2, g1_full as g1; "
                f"f2.OUT = g1.ROOT / 'data' / 'real' / 'g5' / 'f2_full.json'; g1.MODEL = '{model}'; "
                f"g1.OUT = __import__('pathlib').Path(r'{out}'); g1.main()")
        rc = run([sys.executable, "-c", code], {})
        stored = {p["row_id"]: (p["verdict"], p["closed"]) for p in
                  json.loads((D / "g5" / f"g1_results_{short}.json").read_text(encoding="utf-8"))["pairs"]}
        new = ({p["row_id"]: (p["verdict"], p["closed"]) for p in json.loads(out.read_text(encoding="utf-8"))["pairs"]}
               if out.exists() else {})
        res[f"g5:{short}"] = {"exit": rc, "pairs": len(new), "same_verdicts": sum(new.get(k) == v for k, v in stored.items())}
    (D / "k20_dump.json").write_text(json.dumps(res, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
