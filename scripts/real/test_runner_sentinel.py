#!/usr/bin/env python3
"""Regression test for the runner sentinel: an item that cuts the batch file short must not let
the items after it pass. Usage: test_runner_sentinel.py (about two minutes of Lean)."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from runner import Item, _check_batch

IMP = ("Mathlib",)
GOOD = Item("good", IMP, "theorem a1 : 1 + 1 = 2 := by\n  norm_num")
FALSE = Item("false_after", IMP, "theorem a3 : 3 + 3 = 7 := by\n  norm_num")
CUTS = [
    Item("stray_import", IMP, "theorem a2 : 2 + 2 = 5 := by\n  import Mathlib\n  norm_num"),
    Item("open_comment", IMP, "theorem a5 : 2 = 3 := by\n  /- unterminated\n  norm_num"),
]

if __name__ == "__main__":
    for cut in CUTS:
        res = {r.item_id: r.ok for r in _check_batch([GOOD, cut, FALSE, GOOD], 600)}
        assert res == {"good": True, cut.item_id: False, "false_after": False}, res
        print(cut.item_id, "ok")
