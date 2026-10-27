#!/usr/bin/env python3
"""Run the G5 model steps after the f2 step, in parallel; resumable via .done markers.

Usage: g5_chain.py        logs to data/real/g5/<model>.log, markers data/real/g5/<model>.done
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
G5 = ROOT / "data" / "real" / "g5"
F2_FULL = G5 / "f2_full.json"
WAVES = [["anthropic/claude-opus-5.5", "deepseek/deepseek-v4.1-flash",
          "openai/gpt-4.1-mini", "qwen/qwen3.8-27b-nothink"]]
# Concurrent LLM calls per model; DeepSeek spends ~20k reasoning tokens per call.
LLM_WORKERS = {"deepseek/deepseek-v4.1-flash": "32"}


def stamp(*msg) -> None:
    print(time.strftime("%H:%M:%S"), *msg, flush=True)


def main() -> None:
    while not F2_FULL.exists():
        time.sleep(60)
    stamp("f2_full.json present")
    env = {**os.environ, "PYTHONIOENCODING": "utf-8", "LEAN_WORKERS": "4"}
    if not (G5 / "canon.done").exists():
        stamp("start canon")
        with open(G5 / "canon.log", "a", encoding="utf-8") as log:
            code = subprocess.run([sys.executable, str(ROOT / "scripts" / "real" / "g5_scale.py"), "canon"],
                                  cwd=ROOT, env={**env, "LEAN_WORKERS": "10"}, stdout=log, stderr=subprocess.STDOUT).returncode
        stamp("canon exit", code)
        if code != 0:
            return
        (G5 / "canon.done").write_text("", encoding="utf-8")
    for wave in WAVES:
        procs = []
        for model in wave:
            name = model.split("/")[-1]
            if (G5 / f"{name}.done").exists():
                continue
            log = open(G5 / f"{name}.log", "a", encoding="utf-8")
            stamp("start", name)
            p = subprocess.Popen([sys.executable, str(ROOT / "scripts" / "real" / "g5_scale.py"), model],
                                 cwd=ROOT, env={**env, "LLM_WORKERS": LLM_WORKERS.get(model, "16")},
                                 stdout=log, stderr=subprocess.STDOUT)
            procs.append((name, p, time.time()))
        for name, p, t0 in procs:
            code = p.wait()
            stamp(name, "exit", code, f"{time.time() - t0:.0f}s")
            if code == 0:
                (G5 / f"{name}.done").write_text("", encoding="utf-8")
    stamp("chain done")


if __name__ == "__main__":
    main()
