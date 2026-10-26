#!/usr/bin/env python3
"""Loaders that turn raw real-data sources into runner Items."""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path

import pandas as pd

from runner import Item, split_imports

ROOT = Path(__file__).resolve().parents[2]
RAW = ROOT / "data" / "real" / "raw"

THEOREM_NAME_RE = re.compile(r"\b(theorem|lemma)\s+([^\s:({\[]+)")


def close_with_sorry(stmt: str) -> str:
    s = stmt.rstrip()
    if s.endswith(":= sorry") or s.endswith(":= by sorry"):
        return s
    if s.endswith(":="):
        return s + " sorry"
    return s + " := sorry"


def theorem_name(stmt: str) -> str | None:
    m = THEOREM_NAME_RE.search(stmt)
    return m.group(2) if m else None


@dataclass(frozen=True)
class PnvRow:
    row_id: str
    split: str
    stmt_id: str
    nl: str
    header: str
    gold: str
    pred: str
    correct: bool


def proofnetverif(split: str) -> list[PnvRow]:
    d = pd.read_parquet(RAW / "hf" / f"ProofNetVerif-{split}.parquet")
    rows = []
    for i, r in d.iterrows():
        rows.append(
            PnvRow(
                f"pnv-{split}-{i}",
                split,
                r["id"],
                r["nl_statement"],
                r["lean4_src_header"],
                close_with_sorry(r["lean4_formalization"]),
                close_with_sorry(r["lean4_prediction"]),
                bool(r["correct"]),
            )
        )
    return rows


def pnv_item(row: PnvRow, which: str) -> Item:
    imports, opens = split_imports(row.header)
    body = row.gold if which == "gold" else row.pred
    return Item(f"{row.row_id}:{which}", imports, f"{opens}\n{body}")


def formaltcs() -> list[Item]:
    items = []
    base = RAW / "FormalTCS" / "benchmark" / "theorems"
    for d in sorted(base.iterdir()):
        f = d / "theorem.lean"
        if f.exists():
            imports, body = split_imports(f.read_text(encoding="utf-8"))
            items.append(Item(f"tcs-{d.name}", imports, body))
    return items


def t2_rows(dataset: str | None = None) -> list[dict]:
    path = RAW / "T2" / "data" / "final" / "research_papers.all.jsonl"
    rows = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
    return [r for r in rows if dataset is None or r["dataset_name"] == dataset]
