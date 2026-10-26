#!/usr/bin/env python3
"""Print schema, label counts and one sample row of the ProofNetVerif splits."""

from __future__ import annotations

import sys
from pathlib import Path

import pandas as pd

RAW = Path(__file__).resolve().parents[2] / "data" / "real" / "raw" / "hf"


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    for split in ("valid", "test"):
        d = pd.read_parquet(RAW / f"ProofNetVerif-{split}.parquet")
        print(split, d.shape, list(d.columns))
        print(d["correct"].value_counts().to_dict())
        print("distinct statements:", d["id"].nunique())
    d = pd.read_parquet(RAW / "ProofNetVerif-test.parquet")
    print("headers:", d["lean4_src_header"].nunique())
    row = d.iloc[3]
    for c in d.columns:
        print(f"--- {c}")
        print(str(row[c])[:700])


if __name__ == "__main__":
    main()
