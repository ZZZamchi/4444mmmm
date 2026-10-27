#!/usr/bin/env python3
"""K5: standalone re-check of accepted model proofs.

Reads the items recorded by `RUNNER_DUMP` (cache/dump_items.jsonl), keeps those whose cached
result is ok and whose proof came from a model (proposal or repair round), samples up to PER_TAG
per round tag, and checks each alone in its own file, without the result cache, followed by
`#print axioms`. An item passes if the file reaches its sentinel, reports no error, and the
theorem depends on no axiom beyond propext, Classical.choice and Quot.sound.

Usage: k5_standalone_audit.py [PER_TAG]      -> data/real/k5_standalone_audit.json
"""

from __future__ import annotations

import json
import os
import random
import re
import secrets
import sys
import threading
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from runner import CACHE, DIAG_RE, ROOT, Item, _build, _key, _run_file

OUT = ROOT / "data" / "real" / os.environ.get("K5_OUT", "k5_standalone_audit.json")
MODEL_TAGS = set(os.environ.get("K5_TAGS", "g1,g2,k8,k8r,g4k,g4kr,h1k,h1kr").split(","))
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NAME_RE = re.compile(r"(?:canon2_prove|theorem)\s+(\w+)")
AXIOMS_RE = re.compile(r"depends on axioms: \[(.*?)\]")


def alone(it: Item, name: str) -> dict:
    sentinel = f"RUNNER_SENTINEL_{secrets.token_hex(8)}"
    source, _ = _build([Item(it.item_id, it.imports, f"{it.body}\n\n#print axioms {name}")], sentinel)
    out, timed_out = _run_file(source, 900)
    errors = [ln for ln in out.splitlines() if (m := DIAG_RE.match(ln)) and m.group("kind") == "error"]
    m = AXIOMS_RE.search(out)
    axioms = [a.strip() for a in m.group(1).split(",")] if m else []
    clean = "does not depend on any axioms" in out or (m is not None and set(axioms) <= STANDARD)
    ok = not timed_out and sentinel in out and not errors and clean
    return {"ok": ok, "timeout": timed_out, "truncated": sentinel not in out, "errors": errors[:2], "axioms": axioms}


def from_dump(name: str) -> dict[str, dict[str, tuple[Item, str]]]:
    by_tag: dict[str, dict[str, tuple[Item, str]]] = defaultdict(dict)
    for line in (CACHE / name).read_text(encoding="utf-8").splitlines():
        d = json.loads(line)
        parts = d["item"].split(":")
        tag = parts[1] if len(parts) >= 3 else ""
        if tag not in MODEL_TAGS:
            continue
        it = Item(d["item"], tuple(d["imports"]), d["body"])
        f = CACHE / f"{_key(it)}.json"
        m = NAME_RE.search(d["body"])
        res = json.loads(f.read_text(encoding="utf-8")) if m and f.exists() else {}
        if res.get("ok") and not res.get("uses_sorry"):
            by_tag[tag][_key(it)] = (it, m.group(1))
    return by_tag


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    per_tag = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    by_tag: dict[str, dict[str, tuple[Item, str]]] = defaultdict(dict)
    source = os.environ.get("K5_SOURCE")
    if source:
        # the exported accepted proofs (k21_export_proofs.py): already filtered, no cache needed
        import gzip
        for line in gzip.open(ROOT / source, "rt", encoding="utf-8"):
            d = json.loads(line)
            it = Item(d["item"], tuple(d["imports"]), d["body"])
            if m := NAME_RE.search(d["body"]):
                by_tag[d["tag"]][_key(it)] = (it, m.group(1))
    else:
        by_tag = from_dump(os.environ.get("K5_DUMP", "dump_items.jsonl"))
    if skip := os.environ.get("K5_SKIP"):
        # proofs already re-checked from an earlier dump (that run covered its whole population)
        seen = {k for v in from_dump(skip).values() for k in v}
        by_tag = defaultdict(dict, {t: {k: x for k, x in v.items() if k not in seen} for t, v in by_tag.items()})
    rng = random.Random(0)
    sample = []
    for tag in sorted(by_tag):
        pool = sorted(by_tag[tag].values(), key=lambda x: x[0].item_id)
        sample += [(tag, it, name) for it, name in rng.sample(pool, min(per_tag, len(pool)))]
    print("accepted model proofs", {t: len(v) for t, v in by_tag.items()}, "sampled", len(sample), flush=True)
    part = OUT.with_suffix(".partial.jsonl")
    done = {}
    if part.exists():
        for line in part.read_text(encoding="utf-8").splitlines():
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            done[r.get("key", r["item"])] = r
    todo = [x for x in sample if _key(x[1]) not in done]
    # random order, so that a run stopped early has checked a uniform sample of the population
    random.Random(1).shuffle(todo)
    if os.environ.get("K5_SUMMARY_ONLY") == "1":
        # summarize what a running or stopped check has done, without compiling anything
        sample = [x for x in sample if _key(x[1]) in done or x[1].item_id in done]
        todo = []
    lock = threading.Lock()
    print("resumed", len(done), "todo", len(todo), flush=True)

    def one(x):
        # keyed by content: one item id can carry different proofs in different runs
        r = {"tag": x[0], "item": x[1].item_id, "key": _key(x[1]), **alone(x[1], x[2])}
        with lock, open(part, "a", encoding="utf-8") as fh:
            fh.write(json.dumps(r, ensure_ascii=False) + "\n")
        return r

    with ThreadPoolExecutor(max_workers=int(os.environ.get("K5_WORKERS", "4"))) as pool:
        new = {r["key"]: r for r in pool.map(one, todo)}
    rows = [done.get(_key(it)) or done.get(it.item_id) or new[_key(it)] for _, it, _ in sample]
    summary = {"population": {t: len(v) for t, v in by_tag.items()},
               "complete": len(rows) == sum(len(v) for v in by_tag.values()),
               "checked": dict(Counter(r["tag"] for r in rows)),
               "passed": dict(Counter(r["tag"] for r in rows if r["ok"])),
               "failures": [r for r in rows if not r["ok"]]}
    print(json.dumps(summary, indent=1, ensure_ascii=False))
    OUT.write_text(json.dumps({"summary": summary, "rows": rows}, indent=1, ensure_ascii=False) + "\n",
                   encoding="utf-8")


if __name__ == "__main__":
    main()
