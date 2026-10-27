#!/usr/bin/env python3
"""Rerun the K3, K4 and K5 audits under checker v3, one after another.

Each step logs to data/real/kv3/<name>.log and writes <name>.done; finished steps are skipped
on restart.

Usage: k_rerun_v3.py
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path

S = Path(__file__).resolve().parent
ROOT = S.parents[1]
KV = ROOT / "data" / "real" / "kv3"
PY = sys.executable
STEPS = [
    ("k4", [PY, str(S / "k4_trunc_audit.py")], {}),
    ("k3", [PY, str(S / "k3_direction.py")], {}),
    ("k5", [PY, str(S / "k5_standalone_audit.py"), "1000000"], {"K5_WORKERS": "8"}),
]


def log(msg: str) -> None:
    with (KV / "chain_log.txt").open("a", encoding="utf-8") as f:
        f.write(f"{time.strftime('%H:%M:%S')} {msg}\n")


def main() -> None:
    KV.mkdir(parents=True, exist_ok=True)
    for name, cmd, env in STEPS:
        if (KV / f"{name}.done").exists():
            log(f"skip {name}")
            continue
        log(f"start {name}")
        t = time.time()
        with (KV / f"{name}.log").open("a", encoding="utf-8") as out:
            rc = subprocess.call(cmd, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT,
                                 env={**os.environ, "PYTHONIOENCODING": "utf-8", **env})
        log(f"{name} exit {rc} {time.time() - t:.0f}s")
        if rc == 0:
            (KV / f"{name}.done").write_text("", encoding="utf-8")
    log("ALL DONE")


if __name__ == "__main__":
    main()
