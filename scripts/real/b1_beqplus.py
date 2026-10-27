#!/usr/bin/env python3
"""B1: the original BEq+ procedure on the G1 pairs.

Port of `beq_plus` from LeanInteract `examples/beq_plus.py` (Poiroux et al., EMNLP 2025),
run in our Lean/Mathlib instead of the Lean REPL. The theorem-string helpers are loaded
verbatim from LeanInteract `utils.py` (data/real/raw/beqplus/). Per direction, with
`intros; symm_saturate` prepended to every proof, as in the original:

  0. the candidate must type-check with `sorry`;
  1. `exact?` succeeds with a proof mentioning the base theorem;
  2. if `assumption` closes the goal the direction fails;
  3. `apply base_theorem` then the apply solver;
  4. `have <conclusion of base> := by apply_rules [base_theorem]; ...` then the have solver
     (the original's "provable without have" guard concatenates `:= by` and `all_goals`
     without whitespace, so it never fires; it is omitted);
  5. `convert (config := .unfoldSameFun) base_theorem using k`, k = 0..4.

Differences from the original: Lean v4.27 Mathlib instead of v4.8; the per-proof limit
is 50000 heartbeats instead of a 60 s wall clock.

Usage: b1_beqplus.py          Writes data/real/b1_results.json.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
from realdata import proofnetverif
from runner import ROOT, _run_file

OUT = ROOT / "data" / "real" / "b1_results.json"
CACHE = ROOT / "data" / "real" / "b1_cache.json"
SRC = ROOT / "data" / "real" / "raw" / "beqplus" / "utils.py"
LEAN_WORKERS = 2
BATCH = 10
HEARTBEATS = 50000

_src = SRC.read_text(encoding="utf-8")
_ns: dict = {"re": re}
exec(_src[_src.index("def indent_code"):_src.index("class _GitUtilities")], _ns)
clean_last_theorem_string = _ns["clean_last_theorem_string"]
split_conclusion = _ns["split_conclusion"]
indent_code = _ns["indent_code"]

BASE, REFORM = "base_theorem", "reformulated_theorem"


def prove_all(tactics: list[str]) -> str:
    independent = " ; ".join(f"(all_goals try {t})" for t in tactics)
    combined = "all_goals (" + " ; ".join(f"(try {t})" for t in tactics) + ")"
    return "all_goals intros\nfirst | (" + independent + ") | (" + combined + ")"


PROOF_APPLY = prove_all(["tauto", "simp_all_arith!", "noncomm_ring", "exact?"])
PROOF_HAVE = prove_all(["tauto", "simp_all_arith!", "exact? using this"])
DIAG_RE = re.compile(r"^(?P<path>.+?):(?P<line>\d+):(?P<col>\d+): (?P<kind>error|warning)(?P<msg>.*)$")
MARK = "BEQ_MARK_"


def stage_proofs(base_code: str) -> list[tuple[str, str]]:
    out = [("exact", "exact?"), ("assumption", "assumption"), ("apply", f"apply {BASE}\n" + PROOF_APPLY)]
    idx = split_conclusion(base_code)
    if idx:
        conclusion = base_code[idx:base_code.rfind(":=")].strip()
        out.append(("have", f"have {conclusion} := by\n" + indent_code(f"apply_rules [{BASE}]\n" + PROOF_APPLY, 2)
                    + "\n" + PROOF_HAVE))
    out += [(f"convert{k}", f"convert (config := .unfoldSameFun) {BASE} using {k}\n" + PROOF_APPLY) for k in range(5)]
    return out


def item_body(pre: str, base: str, reform: str, proof: str) -> tuple[str, int]:
    """Returns the body and the 0-based line offset where the reformulated theorem starts."""
    head = f"{pre}\n{base}\n\nset_option maxHeartbeats {HEARTBEATS} in\n"
    body = head + f"{reform} := by\n" + indent_code("\nintros\nsymm_saturate\n" + proof, 2)
    return body, head.count("\n")


def run_batch(imports: tuple[str, ...], batch: list[tuple[str, str, int]], timeout: int = 1200) -> dict:
    lines = [f"import {m}" for m in imports]
    spans = []
    for i, (_, body, off) in enumerate(batch):
        lines.append(f"namespace BeqItem{i}")
        start = len(lines) + 1
        lines.extend(body.splitlines())
        spans.append((start, start + off, len(lines)))
        lines.append(f"end BeqItem{i}")
        lines.append(f'#eval IO.println "{MARK}{i}"')
    out, timed_out = _run_file("\n".join(lines) + "\n", timeout)
    if timed_out:
        if len(batch) == 1:
            return {batch[0][0]: {"ok": False, "sorry": False, "try": "", "timeout": True}}
        res = {}
        for it in batch:
            res.update(run_batch(imports, [it], 300))
        return res
    diags, current = [], None
    segs, seg = [], []
    for raw in out.splitlines():
        if raw.startswith(MARK):
            segs.append("\n".join(seg))
            seg, current = [], None
            continue
        seg.append(raw)
        m = DIAG_RE.match(raw)
        if m:
            current = [m.group("msg").lstrip(": ")]
            diags.append((int(m.group("line")), m.group("kind"), current))
        elif current is not None:
            current.append(raw)
    header_err = any(k == "error" and ln <= len(imports) for ln, k, _ in diags)
    res = {}
    for i, ((key, _, _), (start, rstart, end)) in enumerate(zip(batch, spans)):
        errs = [m for ln, k, m in diags if k == "error" and start - 1 <= ln <= end + 1]
        sorry = any("declaration uses 'sorry'" in "\n".join(m) for ln, k, m in diags
                    if k == "warning" and rstart <= ln <= end)
        text = segs[i] if i < len(segs) else ""
        tries = text.split("Try this:", 1)[1] if "Try this:" in text else ""
        res[key] = {"ok": not errs and not header_err and i < len(segs), "sorry": sorry, "try": tries[:2000], "timeout": False}
    return res


def check_all(jobs: dict[str, tuple[tuple[str, ...], str, int]]) -> dict:
    cache = json.loads(CACHE.read_text(encoding="utf-8")) if CACHE.exists() else {}
    h = lambda imp, body: hashlib.sha256(("\0".join(imp) + "\1" + body).encode()).hexdigest()[:24]
    todo: dict[tuple, list] = {}
    for key, (imp, body, off) in jobs.items():
        if h(imp, body) not in cache:
            todo.setdefault(imp, []).append((key, body, off))
    batches = [(imp, g[i:i + BATCH]) for imp, g in todo.items() for i in range(0, len(g), BATCH)]
    with ThreadPoolExecutor(max_workers=LEAN_WORKERS) as pool:
        for (imp, batch), res in zip(batches, pool.map(lambda b: run_batch(*b), batches)):
            for key, body, _ in batch:
                cache[h(imp, body)] = res[key]
            CACHE.write_text(json.dumps(cache, ensure_ascii=False) + "\n", encoding="utf-8")
    return {key: cache[h(imp, body)] for key, (imp, body, _) in jobs.items()}


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    rows = {r.row_id: r for r in proofnetverif("test")}
    pairs = [rows[p["row_id"]] for p in json.loads(f2.OUT.read_text(encoding="utf-8"))["pairs"]]
    if len(sys.argv) > 1:
        pairs = pairs[:int(sys.argv[1])]
    run(pairs, OUT)


def run(pairs, out_path: Path) -> dict:
    t0 = time.time()
    # direction 0: gold is the base, prediction is reformulated; direction 1 the reverse
    dirs = {}
    for r in pairs:
        imports, pre = f2.prelude(r)
        g, p = f2.normalize(r.gold), f2.normalize(r.pred)
        for d, (a, b) in enumerate(((g, p), (p, g))):
            try:
                base = clean_last_theorem_string(a, BASE, add_sorry=True)
                reform = clean_last_theorem_string(b, REFORM, add_sorry=False)
            except ValueError:
                dirs[(r.row_id, d)] = None
                continue
            dirs[(r.row_id, d)] = (imports, pre, base, reform)

    status = {k: ("invalid" if v is None else None) for k, v in dirs.items()}
    stage_log = Counter()

    def run_stage(name: str, proof_of, keys):
        jobs = {}
        for k in keys:
            imports, pre, base, reform = dirs[k]
            proof = proof_of(base)
            if proof is None:
                continue
            body, off = item_body(pre, base, reform, proof)
            jobs[f"{k[0]}|{k[1]}|{name}"] = (imports, body, off)
        res = check_all(jobs)
        return {tuple(key.split("|")[:2]): v for key, v in res.items()}

    for d in (0, 1):
        live = [k for k in dirs if k[1] == d and status[k] is None
                and (d == 0 or status[(k[0], 0)] == "proved")]
        res = run_stage("sorry", lambda base: "sorry", live)
        for k in live:
            if not res[(k[0], str(d))]["ok"]:
                status[k] = "ill_typed"
        for name in ("exact", "assumption", "apply", "have", "convert0", "convert1", "convert2", "convert3", "convert4"):
            live = [k for k in live if status[k] is None]
            if not live:
                break
            res = run_stage(name, lambda base, n=name: dict(stage_proofs(base)).get(n), live)
            for k in live:
                v = res.get((k[0], str(d)))
                if v is None or not v["ok"] or v["sorry"]:
                    continue
                if name == "exact":
                    if BASE in v["try"]:
                        status[k] = "proved"
                        stage_log[f"d{d}_exact"] += 1
                elif name == "assumption":
                    status[k] = "skip_assumption"
                    stage_log[f"d{d}_assumption"] += 1
                else:
                    status[k] = "proved"
                    stage_log[f"d{d}_{name}"] += 1
            print(f"direction {d} stage {name}: live {len(live)}", f"{time.time() - t0:.0f}s", flush=True)
        for k in live:
            if status[k] is None:
                status[k] = "failed"

    table = {True: Counter(), False: Counter()}
    per = []
    for r in pairs:
        eq = status.get((r.row_id, 0)) == "proved" and status.get((r.row_id, 1)) == "proved"
        table[r.correct]["beq_plus_equiv" if eq else "beq_plus_not"] += 1
        per.append({"row_id": r.row_id, "label": r.correct, "beq_plus": eq,
                    "d0": status.get((r.row_id, 0)), "d1": status.get((r.row_id, 1))})
    out = {"n_pairs": len(pairs), "label_inequivalent": dict(table[False]), "label_equivalent": dict(table[True]),
           "stages": dict(stage_log), "seconds": round(time.time() - t0, 1), "pairs": per}
    out_path.write_text(json.dumps(out, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in out.items() if k != "pairs"}, indent=2, ensure_ascii=False))
    return out


if __name__ == "__main__":
    main()
