#!/usr/bin/env python3
"""Compare our G3 ProofNet# probe flags with the ProofNet-Verified manual audit (marcusm117).

ProofNet-Verified classifies every ProofNet# formalization as faithful or unfaithful by hand.
We report, for the statements our probes flag and for the twelve we judged erroneous, how that
audit classifies them, and how many of its unfaithful items our probes reach at all.

Usage: pnv_compare.py
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from runner import ROOT

PNV = ROOT / "data" / "real" / "raw" / "proofnet-verified"
OURS = ["Munkres|exercise_24_3a", "Ireland-Rosen|exercise_4_4", "Rudin|exercise_5_3",
        "Herstein|exercise_2_5_43", "Herstein|exercise_4_2_5", "Herstein|exercise_2_5_37",
        "Herstein|exercise_2_8_12", "Ireland-Rosen|exercise_2_21", "Rudin|exercise_2_24",
        "Rudin|exercise_3_5", "Rudin|exercise_4_8b", "Pugh|exercise_3_63a"]


def key(stmt_id: str) -> str:
    book, ex = stmt_id.split("|")
    return f"{book.replace('-', '_')}_{ex}"


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    meta = [json.loads(l) for l in (PNV / "data" / "proofnet-verified.jsonl").open(encoding="utf-8")]
    tax = {json.loads(l)["stem"]: json.loads(l)
           for l in (PNV / "error_taxonomy" / "proofnet#" / "results.jsonl").open(encoding="utf-8")}
    audit = {m["name"].replace("-", "_"): tax[f"proofnet-{m['index']}"] for m in meta}

    probes = json.loads((ROOT / "data" / "real" / "g3_results.json").read_text(encoding="utf-8"))["probes"]
    probed = {p["stmt_id"] for p in probes}
    flagged = {p["stmt_id"] for p in probes if p["flag"] in ("implied", "idle")}

    def show(title, ids):
        c = Counter(audit[key(i)]["q2_faithfulness"] if key(i) in audit else "missing" for i in ids)
        print(f"{title}: {len(ids)}  {dict(c)}")

    show("our errors", OURS)
    for i in OURS:
        a = audit.get(key(i), {})
        print(f"  {i:32s} {a.get('q2_faithfulness','?'):12s} {a.get('q4_error_type','?'):40s} {a.get('reasoning','')[:110]}")
    show("flagged", sorted(flagged))
    show("flagged, judged benign by us", sorted(flagged - set(OURS)))
    for i in sorted(flagged - set(OURS)):
        a = audit.get(key(i), {})
        if a.get("q2_faithfulness") != "faithful":
            print(f"  benign-by-us but {a.get('q2_faithfulness')}: {i}  {a.get('q4_error_type')}  {a.get('reasoning','')[:160]}")
    unf = {k for k, a in audit.items() if a["q2_faithfulness"] != "faithful"}
    probed_keys = {key(i) for i in probed}
    print(f"audit non-faithful: {len(unf)}; with a hypothesis probe: {len(unf & probed_keys)}; "
          f"flagged: {len(unf & {key(i) for i in flagged})}")
    print("q4 types among non-faithful:", Counter(audit[k]["q4_error_type"] for k in unf))


if __name__ == "__main__":
    main()
