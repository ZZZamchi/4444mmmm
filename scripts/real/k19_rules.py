#!/usr/bin/env python3
"""K19: two canonicalization rules suggested by the blind audit, on the full set (G5, Opus).

The audit (sec:blind) found three canonicalization artefacts and a mislocated difference. Two rules
of `ExperimentsMathlib.CanonV2Ext` address them: `exhyp` reads a hypothesis `∃ x, P x` that nothing
mentions as a binder and a hypothesis (Putnam 2018 B4), and `nonempty` reads a data or instance
binder that nothing mentions as a hypothesis `Nonempty T` (Dummit--Foote 1.6.23, and Herstein 2.1.26
where `[Fintype G]` meets `[Finite G]`). The rules were chosen after seeing the audit, so they are a
separate variant, not the paper's criterion. `k16_align.py run "exhyp,nonempty"` reproves the
pairs whose goals change with the G1 budget; this script summarizes that run against the G5
verdicts and the blind audit.

Usage: k19_rules.py      -> data/real/k19_rules.json
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from h2_audit import read
from paper_check import D, load, located

FLAGS = "exhyp,nonempty"
OUT = D / "k19_rules.json"
TARGETS = {"pnv-test-310": "Putnam 2018 B4", "pnv-test-1135": "Herstein 2.1.26", "pnv-test-358": "Rudin 1.18b",
           "pnv-test-365": "Dummit-Foote 1.6.23", "pnv-test-167": "Dummit-Foote 1.6.23",
           "pnv-test-595": "Dummit-Foote 1.6.23"}


def compute() -> dict:
    run = json.loads((D / "k16_align.json").read_text(encoding="utf-8"))["variants"][FLAGS]
    base = {p["row_id"]: p for p in load(D / "g5" / "g1_results_claude-opus-5.5.json")}
    items = json.loads((D / "h2_items.json").read_text(encoding="utf-8"))
    row = {it["key"]: it["sheet_item"] for it in items if (it.get("cell") or it.get("f_cell")) == "faithful_reject"}
    ann = [read(str(D / f"h2_annot_{x}.csv")) for x in "AB"]
    human = lambda k: (lambda a, b: a if a == b else "split")(ann[0][row[k]]["faithful"], ann[1][row[k]]["faithful"])
    pairs = {p["row_id"]: p for p in run["pairs"]}
    loc_new = lambda p: located({"proved": p["proved"], "canon_info": p["new_info"]}) or "closed"
    res: dict = {"changed": run["changed"], "flips": run["flips"]}
    res["targets"] = {k: {"exercise": n, "old": pairs[k]["old"] if k in pairs else "unchanged",
                          "new": pairs[k]["new"] if k in pairs else "unchanged",
                          "old_loc": located(base[k]) or "closed",
                          "new_loc": loc_new(pairs[k]) if k in pairs and pairs[k]["new"] == "reject" else None}
                      for k, n in TARGETS.items()}
    f_rej = [p for p in pairs.values() if p["label"] and p["old"] == "reject"]
    res["equivalent_rejects"] = {
        "before": sum(1 for p in base.values() if p["label"] and p["verdict"] == "reject"
                      and {"split_r", "split_s"} <= set(p.get("proved") or [])),
        "changed": len(f_rej),
        "no_longer_reject": Counter(f"{p['new']}|{human(p['row_id']) if p['row_id'] in row else 'not audited'}"
                                    for p in f_rej if p["new"] != "reject"),
        "still_reject": sum(p["new"] == "reject" for p in f_rej)}
    res["new_false_accepts"] = sorted(p["row_id"] for p in pairs.values() if not p["label"] and p["new"] == "accept"
                                      and p["old"] != "accept")
    res["lost_faithful_accepts"] = sorted(p["row_id"] for p in pairs.values() if p["label"] and p["old"] == "accept"
                                          and p["new"] != "accept")
    res["new_faithful_accepts"] = sorted(p["row_id"] for p in pairs.values() if p["label"] and p["new"] == "accept"
                                         and p["old"] != "accept")
    u_rej = [p for p in pairs.values() if not p["label"] and p["old"] == "reject" and p["new"] == "reject"]
    res["inequivalent_reject_locations"] = Counter(f"{located(base[p['row_id']]) or 'closed'}->{loc_new(p)}"
                                                   for p in u_rej)
    return res


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    res = compute()
    OUT.write_text(json.dumps(res, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(res, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
