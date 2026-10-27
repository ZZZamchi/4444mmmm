#!/usr/bin/env python3
"""K4: audit of the proofs the runner fails for containing a file-level command.

For every distinct body recorded in `cache/truncate_bodies.jsonl`:

* alone: the body is compiled as a single file without the runner's pre-filter; it counts as
  accepted only if Lean reports no error in it and the trailing sentinel is printed;
* prefix: the body is cut at its first `import`/`#exit` line and checked normally, which asks
  whether the part before the stray command already proves the goal.

Writes data/real/k4_trunc_audit.json.
"""

from __future__ import annotations

import json
import re
import secrets
import sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from runner import CACHE, DIAG_RE, ROOT, TRUNCATE_RE, Item, _build, _run_file, check

OUT = ROOT / "data" / "real" / "k4_trunc_audit.json"


def alone(it: Item) -> tuple[bool, str]:
    sentinel = f"RUNNER_SENTINEL_{secrets.token_hex(8)}"
    source, _ = _build([it], sentinel)
    out, timed_out = _run_file(source, 900)
    errors = [ln for ln in out.splitlines() if (m := DIAG_RE.match(ln)) and m.group("kind") == "error"]
    if timed_out:
        return False, "timeout"
    if sentinel not in out:
        return False, "truncated"
    return not errors, (errors[0][:200] if errors else "")


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    seen, items = set(), []
    for line in (CACHE / "truncate_bodies.jsonl").read_text(encoding="utf-8").splitlines():
        d = json.loads(line)
        if d["key"] not in seen:
            seen.add(d["key"])
            items.append(Item(d["item"], tuple(d["imports"]), d["body"]))
    print("distinct bodies", len(items), flush=True)

    with ThreadPoolExecutor(max_workers=4) as pool:
        lone = dict(zip([it.item_id for it in items], pool.map(alone, items)))

    cut = []
    for it in items:
        m = TRUNCATE_RE.search(it.body)
        cut.append(Item(it.item_id + ":prefix", it.imports, it.body[: m.start()].rstrip()))
    pre = check(cut, batch_size=10, workers=4)

    rows = {}
    for it, c in zip(items, cut):
        r = pre[c.item_id]
        rows[it.item_id] = {"alone_ok": lone[it.item_id][0], "alone_detail": lone[it.item_id][1],
                            "prefix_ok": r.ok and not r.uses_sorry}
    kind = Counter("exit" if re.search(r"^\s*#exit\b", it.body, re.M) else "import" for it in items)
    summary = {"bodies": len(items), "kind": dict(kind),
               "alone_ok": sum(v["alone_ok"] for v in rows.values()),
               "alone_detail": dict(Counter(v["alone_detail"].split(":")[-1].strip()[:60] or "ok"
                                            for v in rows.values()).most_common(6)),
               "prefix_ok": sum(v["prefix_ok"] for v in rows.values()),
               "prefix_ok_items": sorted(k for k, v in rows.items() if v["prefix_ok"])}
    print(json.dumps(summary, indent=1, ensure_ascii=False))
    OUT.write_text(json.dumps({"summary": summary, "items": rows}, indent=1, ensure_ascii=False) + "\n",
                   encoding="utf-8")


if __name__ == "__main__":
    main()
