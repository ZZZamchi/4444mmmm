#!/usr/bin/env python3
"""Compile the OAI modules in dependency order with a bounded number of Lean processes.

`lake build` has no job limit and starts one Lean process per core. Run from the project
directory as `lake env python compile_seq.py TARGET... [-j N]`; Mathlib must already be
built or fetched with `lake exe cache get`.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import time
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path

ROOT = Path.cwd()
OUT = ROOT / ".lake" / "build" / "lib" / "lean"
IMPORT = re.compile(r"^\s*import\s+(OAI\.[\w.]+)", re.M)


def src(mod: str) -> Path:
    return ROOT.joinpath(*mod.split(".")).with_suffix(".lean")


def olean(mod: str) -> Path:
    return OUT.joinpath(*mod.split(".")).with_suffix(".olean")


def deps(mod: str) -> list[str]:
    return IMPORT.findall(src(mod).read_text(encoding="utf-8"))


def closure(targets: list[str]) -> dict[str, list[str]]:
    graph: dict[str, list[str]] = {}
    todo = list(targets)
    while todo:
        m = todo.pop()
        if m not in graph:
            graph[m] = deps(m)
            todo.extend(graph[m])
    return graph


def compile_one(mod: str) -> tuple[str, int, str, float]:
    t0 = time.time()
    o = olean(mod)
    o.parent.mkdir(parents=True, exist_ok=True)
    cmd = ["lean", "-o", str(o), "-i", str(o.with_suffix(".ilean")), str(src(mod))]
    p = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
    return mod, p.returncode, (p.stdout + p.stderr)[-3000:], time.time() - t0


def main() -> None:
    args = sys.argv[1:]
    jobs = 2
    if "-j" in args:
        i = args.index("-j")
        jobs = int(args[i + 1])
        del args[i:i + 2]
    graph = closure(args)
    done = {m for m in graph if olean(m).exists() and olean(m).stat().st_mtime >= src(m).stat().st_mtime}
    print(f"{len(graph)} modules, {len(done)} up to date, jobs={jobs}", flush=True)
    failed: set[str] = set()
    running = {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while True:
            ready = [m for m in graph if m not in done and m not in failed and m not in running
                     and all(d in done for d in graph[m])]
            for m in ready[: jobs - len(running)]:
                running[m] = pool.submit(compile_one, m)
            if not running:
                break
            fin, _ = wait(running.values(), return_when=FIRST_COMPLETED)
            for f in fin:
                mod, rc, log, dt = f.result()
                del running[mod]
                if rc == 0:
                    done.add(mod)
                    print(f"ok   {dt:6.1f}s {mod} ({len(done)}/{len(graph)})", flush=True)
                else:
                    failed.add(mod)
                    print(f"FAIL {dt:6.1f}s {mod}\n{log}", flush=True)
    blocked = [m for m in graph if m not in done and m not in failed]
    print(f"done={len(done)} failed={len(failed)} blocked={len(blocked)}", flush=True)
    sys.exit(1 if failed or blocked else 0)


if __name__ == "__main__":
    os.environ.setdefault("PYTHONUTF8", "1")
    main()
