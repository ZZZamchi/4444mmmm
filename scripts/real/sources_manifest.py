#!/usr/bin/env python3
"""Versions of everything the results depend on: Lean, Mathlib, and each third-party source.

Git sources under data/real/raw/ are recorded by remote and commit; downloaded files (the Hugging
Face parquet releases, the miniF2F jsonl) by SHA-256, since their hosts record no revision.

Usage: sources_manifest.py      -> data/real/sources.json
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RAW = ROOT / "data" / "real" / "raw"
OUT = ROOT / "data" / "real" / "sources.json"
FILES = ["hf/ProofNetVerif-test.parquet", "hf/ProofNetVerif-valid.parquet", "hf/ProofNetSharp-test.parquet",
         "hf/ProofNetSharp-valid.parquet", "minif2f/minif2f.jsonl"]
SEMANTEQ = {"url": "https://github.com/hlxr89/SemantEq", "commit": "f92767000e14d11744580946980cf874324f5d19",
            "files": ["test/results/pnv_test_verdicts.jsonl", "test/campaign/manifest.jsonl"]}


def git(d: Path, *args: str) -> str | None:
    r = subprocess.run(["git", "-C", str(d), *args], capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 and r.stdout.strip() else None


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    manifest = json.loads((ROOT / "lean" / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    out = {"lean_toolchain": (ROOT / "lean" / "lean-toolchain").read_text(encoding="utf-8").strip(),
           "mathlib": {"url": mathlib["url"], "rev": mathlib["rev"]},
           "git_sources": {}, "files_sha256": {}, "semanteq": SEMANTEQ}
    for d in sorted(p for p in RAW.iterdir() if (p / ".git").exists()):
        commit = git(d, "rev-parse", "HEAD")
        if commit and commit != "HEAD":
            out["git_sources"][d.name] = {"url": git(d, "remote", "get-url", "origin"), "commit": commit}
    for rel in FILES:
        out["files_sha256"][rel] = hashlib.sha256((RAW / rel).read_bytes()).hexdigest()
    OUT.write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
