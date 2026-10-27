#!/usr/bin/env python3
"""G6: two frontier models (OpenAI, Google) as provers on G1 and G4 and as judges.

Steps run as subprocesses with their own logs in data/real/g6/; a step whose marker
`<name>.done` exists is skipped, so the chain can be restarted after an interruption.
Within each prover wave the two models run in parallel; the judges run last, so that a model's
prover and judge calls do not compete for the same rate limit.

Usage: g6_frontier.py
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

S = Path(__file__).resolve().parent
ROOT = S.parents[1]
D = ROOT / "data" / "real"
G6 = D / "g6"
PY = sys.executable
MODELS = os.environ.get("G6_MODELS", "openai/gpt-6-astra,google/gemini-4-argon").split(",")
USAGE = D / "cache" / "llm_usage.jsonl"


def short(m: str) -> str:
    return m.split("/")[-1]


def g1_cmd(m: str) -> list[str]:
    code = (f"import sys; sys.path.insert(0, r'{S}'); import g1_full as g1; g1.MODEL = '{m}'; "
            f"g1.OUT = g1.ROOT / 'data' / 'real' / 'g1_results_{short(m)}.json'; g1.main()")
    return [PY, "-c", code]


def log(msg: str) -> None:
    with (G6 / "chain_log.txt").open("a", encoding="utf-8") as f:
        f.write(f"{time.strftime('%H:%M:%S')} {msg}\n")


def step(name: str, cmd: list[str], env: dict | None = None) -> int:
    if (G6 / f"{name}.done").exists():
        log(f"skip {name}")
        return 0
    log(f"start {name}")
    t = time.time()
    e = {**os.environ, "PYTHONIOENCODING": "utf-8", **(env or {})}
    with (G6 / f"{name}.log").open("a", encoding="utf-8") as out:
        p = subprocess.Popen(cmd, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT, env=e)
        rc = p.wait()
    refused = breaker = 0
    for line in USAGE.read_text(encoding="utf-8").splitlines():
        if f'"pid": {p.pid},' in line:
            refused += '"event": "refused"' in line
            breaker += '"event": "breaker"' in line
    log(f"{name} exit {rc} {time.time() - t:.0f}s refused {refused} breaker {breaker}")
    if rc == 0 and not breaker:
        (G6 / f"{name}.done").write_text("", encoding="utf-8")
    elif breaker:
        log(f"{name} INCOMPLETE: {breaker} calls skipped after refusals")
    return rc


def wave(steps: list[tuple[str, list[str], dict]]) -> None:
    with ThreadPoolExecutor(len(steps)) as pool:
        list(pool.map(lambda s: step(*s), steps))


def provers() -> None:
    wave([(f"g1_{short(m)}", g1_cmd(m), {}) for m in MODELS])
    wave([(f"g4_{short(m)}", [PY, str(S / "g4_pnv.py"), m], {"G4_SKIP_BEQ": "1"}) for m in MODELS])
    for m in MODELS:
        for which in ("g1", "g4"):
            f = D / f"{which}_results_{short(m)}.json"
            if f.exists():
                step(f"e2_{which}_{short(m)}", [PY, str(S / "e2_split_complete.py"), which, m, str(f)])


def main() -> None:
    G6.mkdir(parents=True, exist_ok=True)
    provers()
    for m in MODELS:
        step(f"j1_{short(m)}", [PY, str(S / "j1_judge.py"), "all", m])
    log("ALL DONE")


if __name__ == "__main__":
    main()
