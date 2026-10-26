#!/usr/bin/env python3
"""K2 side runner: runs the named K2 steps that do not depend on the G1/G4/G3 reruns, in the given
order, so that they finish before the main k2_rerun.py reaches them (it skips steps with a .done).

Usage: k2_par.py STEP [STEP ...]
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from k2_rerun import D, K, STEPS

by_name = {s[0]: s for s in STEPS}
for name in sys.argv[1:]:
    _, cmd, outputs, extra = by_name[name]
    done = K / f"{name}.done"
    if done.exists():
        continue
    for o in outputs:
        (D / o).unlink(missing_ok=True)
    env = dict(os.environ, PYTHONIOENCODING="utf-8", LEAN_WORKERS=os.environ.get("LEAN_WORKERS", "3"), **extra)
    t0 = time.time()
    print(time.strftime("%H:%M:%S"), "start", name, flush=True)
    with open(K / f"{name}.log", "w", encoding="utf-8") as log:
        code = subprocess.run(cmd, cwd=D.parents[1], env=env, stdout=log, stderr=subprocess.STDOUT).returncode
    print(time.strftime("%H:%M:%S"), name, "exit", code, f"{time.time() - t0:.0f}s", flush=True)
    if code == 0:
        done.write_text(f"{time.time() - t0:.0f}\n", encoding="utf-8")
