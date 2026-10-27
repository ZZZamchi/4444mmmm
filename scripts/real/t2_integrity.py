#!/usr/bin/env python3
"""Measure how many T2 research_papers target statements are syntactically incomplete.

A target counts as truncated when its brackets do not balance or when it has no
top-level type ascription after the binders. Writes data/real/t2_integrity.json.
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PATH = ROOT / "data" / "real" / "raw" / "T2" / "data" / "final" / "research_papers.all.jsonl"
OUT = ROOT / "data" / "real" / "t2_integrity.json"
PAIRS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}


def balanced(s: str) -> bool:
    stack = []
    for ch in s:
        if ch in PAIRS:
            stack.append(PAIRS[ch])
        elif ch in PAIRS.values():
            if not stack or stack.pop() != ch:
                return False
    return not stack


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    rows = [json.loads(line) for line in PATH.open(encoding="utf-8")]
    by_ds = {}
    last_chars = Counter()
    for r in rows:
        t = str(r.get("target_code", "")).strip()
        ok = balanced(t) and (":" in t)
        d = by_ds.setdefault(r["dataset_name"], Counter())
        d["rows"] += 1
        d["complete" if ok else "truncated"] += 1
        if not ok:
            nxt = t[-1:] if t else ""
            last_chars[nxt] += 1
    out = {
        "rows": len(rows),
        "by_dataset": {k: dict(v) for k, v in by_ds.items()},
        "truncated_share": round(sum(v["truncated"] for v in by_ds.values()) / len(rows), 3),
        "truncated_last_char": dict(last_chars.most_common(15)),
    }
    OUT.write_text(json.dumps(out, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(out, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
