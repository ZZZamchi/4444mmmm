#!/usr/bin/env python3
"""G5: BEq+ on all usable ProofNetVerif test pairs (the pairs of data/real/g5/f2_full.json).

Usage: g5_beq.py        writes data/real/g5/b1_results.json (shares b1_cache.json with B1)
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import b1_beqplus as b1
import f2_oracle as f2
from runner import ROOT

G5 = ROOT / "data" / "real" / "g5"

if __name__ == "__main__":
    f2.OUT = G5 / "f2_full.json"
    b1.OUT = G5 / "b1_results.json"
    b1.LEAN_WORKERS = int(os.environ.get("BEQ_WORKERS", 4))
    b1.main()
