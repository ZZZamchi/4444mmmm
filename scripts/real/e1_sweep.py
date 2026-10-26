#!/usr/bin/env python3
"""E1: prover-strength sweep. Runs the missing (dataset, model) combinations sequentially.

Tiers: tactics only (no LLM), deepseek-v4.1-flash, gpt-4.1-mini, claude-opus-5.5, on both the
closed and the component side. G1 = ProofNetVerif 300 pairs, G4 = ProofNet-Verified 317 pairs.

Usage: e1_sweep.py run              run missing combinations (long; LLM + Lean)
       e1_sweep.py table            print the false-accept table from whatever results exist
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from runner import ROOT

D = ROOT / "data" / "real"
MODELS = ["deepseek/deepseek-v4.1-flash", "openai/gpt-4.1-mini", "anthropic/claude-opus-5.5",
          "qwen/qwen3.8-27b-nothink"]
PY = sys.executable


def g1_file(model: str) -> Path:
    return D / ("g1_results.json" if model.endswith("opus-5.5") else f"g1_results_{model.split('/')[-1]}.json")


def g4_file(model: str) -> Path:
    return D / ("g4_results.json" if model.endswith("opus-5.5") else f"g4_results_{model.split('/')[-1]}.json")


def run() -> None:
    env = dict(os.environ, PYTHONIOENCODING="utf-8", LEAN_WORKERS=os.environ.get("LEAN_WORKERS", "3"), G4_SKIP_BEQ="1")
    for model in MODELS:
        if not g1_file(model).exists():
            print("G1", model, flush=True)
            code = (f"import sys; sys.path.insert(0, r'{ROOT / 'scripts' / 'real'}'); import g1_full as g1; "
                    f"g1.MODEL = '{model}'; g1.OUT = g1.ROOT / 'data' / 'real' / '{g1_file(model).name}'; g1.main()")
            subprocess.run([PY, "-c", code], cwd=ROOT, env=env, check=False)
        if not g4_file(model).exists():
            print("G4", model, flush=True)
            subprocess.run([PY, str(ROOT / "scripts" / "real" / "g4_pnv.py"), model], cwd=ROOT, env=env, check=False)


def closed_status(proved: set) -> str:
    import f2_oracle as f2
    return f2.verdict(proved)["status"]


def comp_status(proved: set) -> str:
    from f7_component import classify
    return classify(proved)


def table() -> None:
    import f2_oracle as f2
    rows = []
    f2_pairs = {p["row_id"]: p for p in json.loads(f2.OUT.read_text(encoding="utf-8"))["pairs"]}
    for ds, files in (("G1", g1_file), ("G4", g4_file)):
        tiers = []
        for model in MODELS:
            f = files(model)
            if f.exists():
                tiers.append((model.split("/")[-1], json.loads(f.read_text(encoding="utf-8"))["pairs"]))
        if not tiers:
            continue
        base = dict(tiers).get("claude-opus-5.5", tiers[-1][1])
        # tactic-only tier from the strongest available file
        if ds == "G1":
            tac = [{**p, "closed_proved": f2_pairs[p["row_id"]]["t1"], "proved": p["tactic"]} for p in base]
        else:
            tac = [{**p, "closed_proved": p.get("closed_tactic", []), "proved": p["tactic"]} for p in base]
        tiers.insert(0, ("tactics", tac))
        for name, pairs in tiers:
            if ds == "G1":
                neg = [p for p in pairs if not p["label"]]
                pos = [p for p in pairs if p["label"]]
            else:
                neg = [p for p in pairs if p["relation"] != "faithful"]
                pos = [p for p in pairs if p["relation"] == "faithful"]
            cfa = sum(closed_status(set(p["closed_proved"])) == "proved" for p in neg)
            kfa = sum(comp_status(set(p["proved"])) == "accept" for p in neg)
            cacc = sum(closed_status(set(p["closed_proved"])) == "proved" for p in pos)
            kacc = sum(comp_status(set(p["proved"])) == "accept" for p in pos)
            krej = sum(comp_status(set(p["proved"])) == "reject" for p in pos)
            rows.append((ds, name, len(neg), cfa, kfa, len(pos), cacc, kacc, krej))
    print(f"{'set':4} {'prover':24} {'n_unf':>5} {'closedFA':>8} {'compFA':>6} {'n_f':>5} {'closedAcc':>9} {'compAcc':>7} {'compRej':>7}")
    for r in rows:
        print(f"{r[0]:4} {r[1]:24} {r[2]:5} {r[3]:8} {r[4]:6} {r[5]:5} {r[6]:9} {r[7]:7} {r[8]:7}")
    (D / "e1_table.json").write_text(json.dumps([dict(zip(
        ("set", "prover", "n_unfaithful", "closed_false_accept", "comp_false_accept", "n_faithful",
         "closed_accept", "comp_accept", "comp_reject"), r)) for r in rows], indent=1) + "\n", encoding="utf-8")


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    (table if (sys.argv[1:] or ["table"])[0] == "table" else run)()
