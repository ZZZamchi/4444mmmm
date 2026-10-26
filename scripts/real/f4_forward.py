#!/usr/bin/env python3
"""F4: does a forward (successor-compiles) check accept unfaithful statements?

T2's research metric replaces a target theorem in its repository and accepts the
candidate when the repository still builds. This script reproduces that protocol
on Mathlib files in the local v4.27 environment (T2's own repositories are pinned
to Lean v4.3-v4.10 and 13.8% of their targets are truncated, see t2_integrity.py).

For a target theorem T, later declarations in the same file that mention its short
name are candidate successors. Each variant replaces T's statement and its proof by
`sorry`, keeps the file up to the last candidate, and compiles it:

  control   original statement           (candidates that fail here are dropped)
  delete    T removed                    (candidates that still pass do not depend on T)

The successors of T are the candidates that pass under control and fail under delete;
T is kept when it has at least two. The drifts are
  false     conclusion replaced by False  (strictly stronger, unsatisfiable)
  lt        first ≤ in the conclusion → <  (strictly stronger)
  drop_hyp  last explicit hypothesis (h… : …) removed (strictly stronger)

A drift is missed when every successor still compiles. Writes data/real/f4_results.json.
"""

from __future__ import annotations

import json
import random
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from runner import DIAG_RE, ROOT, _run_file

MATHLIB = ROOT / "lean" / ".lake" / "packages" / "mathlib" / "Mathlib"
OUT = ROOT / "data" / "real" / "f4_results.json"
DIRS = ("Order", "Data/Nat", "Data/Int", "Data/Finset", "Algebra/Order", "Data/List", "Data/Set")
N_TARGETS = 20
SEED = 0

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:protected|private|nonrec|noncomputable)\s+)*(?:theorem|lemma)\s+(\S+)"
)
OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"


def decls(lines: list[str]) -> list[tuple[int, int, str | None]]:
    """(start, end_exclusive, theorem name or None) for each top-level command."""
    starts = [i for i, l in enumerate(lines) if l and not l[0].isspace() and not l.startswith(("--", "-/", "/-"))]
    out = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(lines)
        while e > s + 1 and not lines[e - 1].strip():
            e -= 1
        m = DECL_RE.match(lines[s])
        out.append((s, e, m.group(1) if m else None))
    return out


def split_statement(text: str) -> tuple[int, int] | None:
    """Indices of the top-level type colon and of the `:=` that starts the proof."""
    depth, colon = 0, None
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif depth == 0 and text.startswith(":=", i):
            return (colon, i) if colon is not None else None
        elif depth == 0 and ch == ":" and colon is None:
            colon = i
        i += 1
    return None


def drift(header: str, concl: str, kind: str) -> str | None:
    if kind == "control":
        return f"{header}:{concl}"
    if kind == "false":
        return f"{header}: False"
    if kind == "lt":
        return f"{header}:{concl.replace('≤', '<', 1)}" if "≤" in concl else None
    if kind == "drop_hyp":
        binders = list(re.finditer(r"\((h\w*'*) : [^()]*(?:\([^()]*\)[^()]*)*\)", header))
        if not binders:
            return None
        b = binders[-1]
        if re.search(rf"(?<![\w.']){re.escape(b.group(1))}(?![\w'])", concl):
            return None
        return f"{header[: b.start()]}{header[b.end():]}:{concl}"
    raise ValueError(kind)


KINDS = ("control", "false", "lt", "drop_hyp")


def candidates() -> list[dict]:
    files = sorted(p for d in DIRS for p in (MATHLIB / d).rglob("*.lean"))
    rng = random.Random(SEED)
    rng.shuffle(files)
    found = []
    for path in files:
        lines = path.read_text(encoding="utf-8").splitlines()
        ds = decls(lines)
        for idx, (s, e, name) in enumerate(ds):
            if not name:
                continue
            short = name.split(".")[-1]
            if len(short) < 8 or "_" not in short:
                continue
            text = "\n".join(lines[s:e])
            cut = split_statement(text)
            if cut is None:
                continue
            pat = re.compile(rf"(?<![\w'])(?:[\w.]*\.)?{re.escape(short)}(?![\w'])")
            succ = [
                (s2, e2)
                for s2, e2, n2 in ds[idx + 1 :]
                if (n2 or "").split(".")[-1] != short and pat.search("\n".join(lines[s2:e2]))
            ]
            if len(succ) < 2:
                continue
            found.append({"file": str(path.relative_to(MATHLIB.parent)).replace("\\", "/"), "name": name,
                          "span": (s, e), "cut": cut, "succ": succ[:8], "lines": lines})
            break
        if len(found) >= N_TARGETS * 3:
            break
    return found


def variant_source(c: dict, kind: str) -> tuple[str, list[tuple[int, int]]] | None:
    lines = c["lines"]
    s, e = c["span"]
    text = "\n".join(lines[s:e])
    colon, assign = c["cut"]
    if kind == "delete":
        new_decl = []
    else:
        new_stmt = drift(text[:colon], text[colon + 1 : assign], kind)
        if new_stmt is None:
            return None
        new_decl = (new_stmt.rstrip() + " := by\n  sorry").splitlines()
    last = c["succ"][-1][1]
    out = lines[:s] + new_decl + lines[e:last]
    shift = len(new_decl) - (e - s)
    return "\n".join(out) + "\n", [(a + shift, b + shift) for a, b in c["succ"]]


def run_variant(c: dict, kind: str) -> dict | None:
    built = variant_source(c, kind)
    if built is None:
        return None
    src, ranges = built
    output, timed_out = _run_file(src, 1200)
    err_lines = [int(m.group("line")) for m in map(DIAG_RE.match, output.splitlines()) if m and m.group("kind") == "error"]
    passed = [not any(a < ln <= b for ln in err_lines) for a, b in ranges]
    return {"kind": kind, "timeout": timed_out, "successors_pass": passed, "all_pass": all(passed) and not timed_out}


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    cands = candidates()
    print("candidates", len(cands))

    with ThreadPoolExecutor(max_workers=3) as pool:
        controls = list(pool.map(lambda c: run_variant(c, "control"), cands))
        deletes = list(pool.map(lambda c: run_variant(c, "delete"), cands))
    kept = []
    for c, rc, rd in zip(cands, controls, deletes):
        if rc["timeout"] or rd["timeout"]:
            continue
        real = [sp for sp, pc, pd in zip(c["succ"], rc["successors_pass"], rd["successors_pass"]) if pc and not pd]
        if len(real) >= 2:
            kept.append({**c, "succ": real})
    n_dep = len(kept)
    kept = kept[:N_TARGETS]
    print("with >=2 dependent successors", n_dep, "kept", len(kept), f"{time.time() - t0:.0f}s")

    jobs = [(c, k) for c in kept for k in KINDS[1:]]
    with ThreadPoolExecutor(max_workers=3) as pool:
        res = list(pool.map(lambda j: run_variant(*j), jobs))

    targets = {}
    for (c, k), r in zip(jobs, res):
        t = targets.setdefault(c["name"], {"file": c["file"], "n_successors": len(c["succ"]), "drifts": {}})
        if r is not None:
            t["drifts"][k] = r
    summary = {}
    for k in KINDS[1:]:
        rs = [t["drifts"][k] for t in targets.values() if k in t["drifts"]]
        summary[k] = {
            "applicable": len(rs),
            "missed": sum(r["all_pass"] for r in rs),
            "miss_rate": round(sum(r["all_pass"] for r in rs) / len(rs), 3) if rs else None,
            "successor_pass_rate": round(
                sum(sum(r["successors_pass"]) for r in rs) / max(1, sum(len(r["successors_pass"]) for r in rs)), 3
            ),
        }
    all_rs = [r for t in targets.values() for r in t["drifts"].values()]
    out = {
        "n_candidates": len(cands),
        "n_with_dependent_successors": n_dep,
        "n_targets": len(kept),
        "by_drift": summary,
        "overall_miss_rate": round(sum(r["all_pass"] for r in all_rs) / len(all_rs), 3) if all_rs else None,
        "targets_with_some_miss": sum(any(r["all_pass"] for r in t["drifts"].values()) for t in targets.values()),
        "seconds": round(time.time() - t0, 1),
        "targets": targets,
    }
    OUT.write_text(json.dumps(out, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in out.items() if k != "targets"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
