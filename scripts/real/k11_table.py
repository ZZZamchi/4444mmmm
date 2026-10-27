#!/usr/bin/env python3
"""K11 table: the controlled budget sweep, one block of rows per model.

Reads data/real/k11_budget_<model>.json and prints the LaTeX rows of `tab:budget`:
false accepts on the 694 inequivalent and accepts on the 446 equivalent pairs, for closed
equivalence, all our accepts and local accepts, at each budget level.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MODELS = [("claude-opus-5.5", "Claude Opus 5.5"), ("deepseek-v4.1-flash", "DeepSeek-V4.1-Flash"),
          ("gpt-4.1-mini", "GPT-4.1-mini"), ("qwen3.8-27b-nothink", "Qwen3.8-27B")]
NAMES = {"L0": "tactics", "L1": "+ proposal", "L2": "+ repair", "L3": "+ 2nd repair"}


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    for short, name in MODELS:
        d = json.loads((ROOT / "data" / "real" / f"k11_budget_{short}.json").read_text(encoding="utf-8"))
        levels = list(d["table"])
        for i, lev in enumerate(levels):
            t = d["table"][lev]
            first = name if i == 0 else ""
            print(f"{first} & {NAMES[lev]} & {t['closed_accU']} & {t['closed_accF']} & {t['accU']} & {t['accF']}"
                  f" & {t['localU']} & {t['localF']} & {t['rejectU']}\\\\")
        print(f"% {short}: extra={d['extra']} mismatch={d['mismatch_L2_vs_stored']}")


if __name__ == "__main__":
    main()
