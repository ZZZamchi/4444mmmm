#!/usr/bin/env python3
"""Print the shape of T2 research_papers rows (keys, headers, successor usage)."""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PATH = ROOT / "data" / "real" / "raw" / "T2" / "data" / "final" / "research_papers.all.jsonl"


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    rows = [json.loads(line) for line in PATH.open(encoding="utf-8")]
    print("rows", len(rows), "keys", sorted(rows[0]))
    print(Counter(r.get("dataset_name") for r in rows))
    imports = Counter()
    for r in rows:
        for line in str(r.get("header", "")).splitlines():
            if line.startswith("import"):
                imports[(r.get("dataset_name"), line.strip())] += 1
    for (ds, line), n in imports.most_common(40):
        print(f"{n:5d} {ds:28s} {line}")
    r = next(r for r in rows if r.get("dataset_name") == "math2001")
    for k, v in r.items():
        s = json.dumps(v, ensure_ascii=False)
        print(f"--- {k}: {s[:600]}")


if __name__ == "__main__":
    main()
