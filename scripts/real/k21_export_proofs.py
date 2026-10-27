#!/usr/bin/env python3
"""K21: export the accepted model proofs, so that they can be rechecked without the caches.

Reads the Lean items the checker recorded (`cache/dump_items.jsonl`, and `cache/dump_post.jsonl`
from K20), keeps those whose cached result is ok and whose proof came from a model, and writes
one record per distinct item (id, round tag, imports, Lean source) to
`data/real/accepted_proofs.jsonl.gz`. `k5_standalone_audit.py` with `K5_SOURCE=` that file compiles
each record alone, followed by `#print axioms`, against the pinned Mathlib of `lean/`.

Usage: k21_export_proofs.py      -> data/real/accepted_proofs.jsonl.gz
"""

from __future__ import annotations

import gzip
import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from k5_standalone_audit import NAME_RE
from runner import CACHE, Item, _key

OUT = Path(__file__).resolve().parents[2] / "data" / "real" / "accepted_proofs.jsonl.gz"
DUMPS = ("dump_items.jsonl", "dump_post.jsonl")
# rounds whose proofs a model wrote: proposals and repairs (k8rr: the second repair round of K11)
MODEL_TAGS = {"g1", "g2", "k8", "k8r", "k8rr", "g4k", "g4kr", "h1k", "h1kr"}
MODEL_TAG = MODEL_TAGS.__contains__


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    seen, tags = {}, Counter()
    for name in DUMPS:
        f = CACHE / name
        if not f.exists():
            continue
        for line in f.read_text(encoding="utf-8").splitlines():
            d = json.loads(line)
            parts = d["item"].split(":")
            tag = parts[1] if len(parts) >= 3 else ""
            if not MODEL_TAG(tag) or not NAME_RE.search(d["body"]):
                continue
            it = Item(d["item"], tuple(d["imports"]), d["body"])
            k = _key(it)
            if k in seen:
                continue
            r = CACHE / f"{k}.json"
            if r.exists() and json.loads(r.read_text(encoding="utf-8")).get("ok"):
                seen[k] = {"item": d["item"], "tag": tag, "imports": d["imports"], "body": d["body"]}
                tags[tag] += 1
    with gzip.open(OUT, "wt", encoding="utf-8") as fh:
        for rec in seen.values():
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n")
    print(len(seen), "accepted model proofs", dict(tags), "->", OUT)


if __name__ == "__main__":
    main()
