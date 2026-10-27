#!/usr/bin/env python3
"""A1: split accepts into local accepts and residual (closed-level) accepts.

An accept is local when the alignment is total (every binder of both canonical telescopes
lies in the shared prefix) and the prefix is nonempty. Otherwise part of each statement is
compared as a closed sub-statement inside the conclusion, and the accept inherits only the
closed guarantee (residue of collapse, Theorem repr).

Usage: a1_local.py      Writes data/real/a1_local.json.
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from runner import ROOT

D = ROOT / "data" / "real"
FILES = ["g1_results.json", "g1_results_deepseek-v4.1-flash.json", "g1_results_gpt-4.1-mini.json",
         "g1_results_qwen3.8-27b-nothink.json",
         "g4_results.json", "g4_results_deepseek-v4.1-flash.json", "g4_results_gpt-4.1-mini.json",
         "g4_results_qwen3.8-27b-nothink.json"]


def local(info: str | None) -> bool:
    if not info:
        return False
    m = re.search(r"full=(\w+) prefix_r=(\d+)/\d+ prefix_s=(\d+)/\d+", info)
    return m is not None and m.group(1) == "true" and int(m.group(2)) + int(m.group(3)) > 0


def label(p: dict) -> bool:
    return p["label"] if "label" in p else p["relation"] == "faithful"


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    out = {}
    for f in FILES:
        d = json.loads((D / f).read_text(encoding="utf-8"))
        c = Counter()
        for p in d["pairs"]:
            if p["verdict"] != "accept":
                continue
            kind = "local" if local(p.get("canon_info")) else "residual"
            c[f"{'faithful' if label(p) else 'unfaithful'}_{kind}"] += 1
        out[f] = {"model": d.get("model"), **dict(sorted(c.items()))}
        print(f, out[f])
    (D / "a1_local.json").write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
