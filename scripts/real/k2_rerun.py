#!/usr/bin/env python3
"""K2: rerun every pipeline whose Lean checks contain LLM proofs, after the runner sentinel fix.

Before the fix a batch cut short by a stray `import` (or `#exit`, or an unterminated comment)
reported no errors for the items after the cut, so their cached `ok` was not evidence. The runner
now rechecks every cached `ok` that predates the fix; this script reruns the pipelines in
dependency order so that every result file is rebuilt from rechecked results. Old result files are
in data/real/pre_sentinel/. Flipped items are logged in data/real/cache/flips.jsonl.

Usage: k2_rerun.py            resumable; a step is skipped once data/real/k2/<step>.done exists
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from runner import ROOT

D = ROOT / "data" / "real"
S = ROOT / "scripts" / "real"
K = D / ("k2_cacheonly" if os.environ.get("LLM_CACHE_ONLY") == "1" else "k2")
PY = sys.executable
TIERS = ["deepseek/deepseek-v4.1-flash", "openai/gpt-4.1-mini", "anthropic/claude-opus-5.5",
         "qwen/qwen3.8-27b-nothink"]


def short(m: str) -> str:
    return m.split("/")[-1]


def g1_out(m: str) -> str:
    return "g1_results.json" if m.endswith("opus-5.5") else f"g1_results_{short(m)}.json"


def g4_out(m: str) -> str:
    return "g4_results.json" if m.endswith("opus-5.5") else f"g4_results_{short(m)}.json"


def g1_cmd(m: str) -> list[str]:
    code = (f"import sys; sys.path.insert(0, r'{S}'); import g1_full as g1; g1.MODEL = '{m}'; "
            f"g1.OUT = g1.ROOT / 'data' / 'real' / '{g1_out(m)}'; g1.main()")
    return [PY, "-c", code]


STEPS: list[tuple[str, list[str], list[str], dict]] = []
for m in TIERS:
    STEPS.append((f"g1_{short(m)}", g1_cmd(m), [g1_out(m)], {}))
for m in TIERS:
    STEPS.append((f"g4_{short(m)}", [PY, str(S / "g4_pnv.py"), m], [g4_out(m)],
                  {} if m.endswith("opus-5.5") else {"G4_SKIP_BEQ": "1"}))
STEPS += [
    ("e2_g1", [PY, str(S / "e2_split_complete.py"), "g1"], [], {}),
    ("e2_g4", [PY, str(S / "e2_split_complete.py"), "g4"], [], {}),
    ("d2_prove", [PY, str(S / "d2_select.py"), "prove"], ["d2_prove.json"], {}),
    ("e2_d2", [PY, str(S / "e2_split_complete.py"), "d2"], [], {}),
]
for ds in ("proofnetsharp", "minif2f", "putnam"):
    sfx = "" if ds == "proofnetsharp" else f"_{ds}"
    STEPS.append((f"g3_{ds}", [PY, str(S / "g3_probe.py"), "anthropic/claude-opus-5.5", ds], [f"g3_results{sfx}.json"], {}))
    STEPS.append((f"e6_{ds}", [PY, str(S / "e6_global.py"), "anthropic/claude-opus-5.5", ds], [f"e6_results{sfx}.json"], {}))
STEPS += [
    ("h1_minif2f", [PY, str(S / "h1_top.py"), "minif2f"], [], {}),
    ("g2", [PY, str(S / "g2_drift.py"), "129"], [], {}),
    ("e5", [PY, str(S / "e5_meta.py")], [], {}),
    ("e1_embed", [PY, str(S / "e1_embed.py")], [], {}),
    ("c1_mini", [PY, str(S / "c1_formalrx.py"), "openai/gpt-4.1-mini"], [], {}),
    ("c1_opus", [PY, str(S / "c1_formalrx.py"), "anthropic/claude-opus-5.5"], [], {}),
    ("c1b", [PY, str(S / "c1b_ccwitness.py")], [], {}),
    ("c1b_eval51", [PY, str(S / "c1b_ccwitness.py"), "eval51"], [], {}),
    ("c1c", [PY, str(S / "c1c_correction.py")], [], {}),
    ("e1_table", [PY, str(S / "e1_sweep.py"), "table"], [], {}),
    ("a1_local", [PY, str(S / "a1_local.py")], [], {}),
    ("j1_analyze", [PY, str(S / "j1_analyze.py")], [], {}),
    ("d2_loose", [PY, str(S / "d2_analyze.py")], [], {"D2_GT": "loose"}),
    ("d2_strict", [PY, str(S / "d2_analyze.py")], [], {"D2_GT": "strict"}),
    ("d2_refuted", [PY, str(S / "d2_analyze.py")], [], {"D2_GT": "refuted"}),
]


def main() -> None:
    K.mkdir(parents=True, exist_ok=True)
    only = set(sys.argv[1:])
    for name, cmd, outputs, extra in STEPS:
        done = K / f"{name}.done"
        if done.exists() or (only and name not in only):
            continue
        for o in outputs:
            (D / o).unlink(missing_ok=True)
        env = dict(os.environ, PYTHONIOENCODING="utf-8", LEAN_WORKERS=os.environ.get("LEAN_WORKERS", "4"), **extra)
        t0 = time.time()
        print(time.strftime("%H:%M:%S"), "start", name, flush=True)
        with open(K / f"{name}.log", "w", encoding="utf-8") as log:
            code = subprocess.run(cmd, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT).returncode
        print(time.strftime("%H:%M:%S"), name, "exit", code, f"{time.time() - t0:.0f}s", flush=True)
        if code == 0:
            done.write_text(f"{time.time() - t0:.0f}\n", encoding="utf-8")


if __name__ == "__main__":
    main()
