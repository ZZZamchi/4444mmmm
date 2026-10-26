#!/usr/bin/env python3
"""Batch Lean checker for real-data items.

An item is (item_id, imports, body). `imports` is a tuple of module names;
`body` is Lean source that may contain `open` lines and declarations.
Items sharing the same imports are packed into one file, each inside its own
`namespace`, so that declaration names such as `dummy` never clash. Errors are
attributed to items by line range. Results are cached by content hash under
data/real/cache/.

Only the Lean project in lean/ (Mathlib v4.27.0-rc1) is used. Datasets pinned
to other versions are checked here as-is; the compile rate is what F1 reports.
"""

from __future__ import annotations

import functools
import hashlib
import json
import os
import re
import secrets
import subprocess
import tempfile
import textwrap
import threading
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean"
CACHE = ROOT / "data" / "real" / "cache"
LAKE = Path(os.environ["USERPROFILE"]) / ".elan" / "bin" / "lake.exe"

DIAG_RE = re.compile(r"^(?P<path>.+?):(?P<line>\d+):(?P<col>\d+): (?P<kind>error|warning)(?P<msg>.*)$")
IMPORT_RE = re.compile(r"^\s*import\s+(.+)$")
TRUNCATE_RE = re.compile(r"^\s*(import\s|#exit\b)", re.M)
CACHE_VERSION = 3
NO_WINDOW = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
_APPEND = threading.Lock()


@dataclass(frozen=True)
class Item:
    item_id: str
    imports: tuple[str, ...]
    body: str


@dataclass
class Result:
    item_id: str
    ok: bool
    errors: list[str] = field(default_factory=list)
    uses_sorry: bool = False
    timeout: bool = False


def split_imports(source: str) -> tuple[tuple[str, ...], str]:
    imports: list[str] = []
    rest: list[str] = []
    for line in source.splitlines():
        m = IMPORT_RE.match(line)
        if m:
            imports.extend(m.group(1).split())
        else:
            rest.append(line)
    return tuple(sorted(set(imports))), "\n".join(rest).strip("\n")


FILE_HEADER_RE = re.compile(r"\A(?:\s*(?:import|open|universe|set_option|namespace|section)\b[^\n]*\n)+")


def strip_file_header(body: str) -> str:
    """Drops leading file-level lines that some models copy from the prompt header; the
    `set_option ... in` form is a tactic-level prefix only after a declaration, so it is safe here."""
    return FILE_HEADER_RE.sub("", body.lstrip("\n"))


THEOREM_HEAD_RE = re.compile(r"^\s*theorem\s+\w+\s*:.*?:=\s*by[ \t]*\n?", re.DOTALL)


def tactic_body(text: str) -> str:
    """The tactic block of a model reply, indented by two spaces for `:= by\\n  `. The reply's own
    relative indentation is kept: Lean reads a line indented deeper than the previous tactic as
    its continuation, so stripping only the first line's indentation changes the proof."""
    body = THEOREM_HEAD_RE.sub("", strip_file_header(text.rstrip()), count=1)
    lines = textwrap.dedent(body).strip("\n").splitlines()
    if lines and lines[0].strip() == "by":
        lines = textwrap.dedent("\n".join(lines[1:])).strip("\n").splitlines()
    elif lines and lines[0].startswith("by "):
        lines[0] = lines[0][3:]
    return "\n  ".join(lines)


def _key(item: Item) -> str:
    h = hashlib.sha256()
    h.update("\0".join(item.imports).encode())
    h.update(b"\1")
    h.update(item.body.encode())
    return h.hexdigest()[:24]


def _safe_ns(i: int) -> str:
    return f"RealItem{i}"


def _build(items: list[Item], sentinel: str | None = None) -> tuple[str, list[tuple[int, int]]]:
    lines = [f"import {m}" for m in items[0].imports]
    ranges: list[tuple[int, int]] = []
    for i, it in enumerate(items):
        lines.append(f"namespace {_safe_ns(i)}")
        start = len(lines) + 1
        lines.extend(it.body.splitlines())
        end = len(lines)
        lines.append(f"end {_safe_ns(i)}")
        if sentinel:
            lines.append(f'#print "{sentinel}_{i}"')
        ranges.append((start, end))
    if sentinel:
        lines.append(f'#print "{sentinel}"')
    return "\n".join(lines) + "\n", ranges


@functools.cache
def _lean_env() -> tuple[str, dict[str, str]]:
    """Resolve `lake env` once; spawning lake per file costs two extra processes."""
    proc = subprocess.run(
        [str(LAKE), "env"], cwd=LEAN_DIR, capture_output=True, text=True, encoding="utf-8", check=True,
        creationflags=NO_WINDOW,
    )
    env = dict(os.environ)
    for line in proc.stdout.splitlines():
        key, sep, value = line.partition("=")
        if sep:
            env[key] = value
    return env["LEAN"], env


def _kill_tree(proc: subprocess.Popen) -> None:
    if os.name == "nt":
        subprocess.run(["taskkill", "/F", "/T", "/PID", str(proc.pid)], capture_output=True,
                       creationflags=NO_WINDOW)
    proc.kill()


def _run_file(source: str, timeout: int) -> tuple[str, bool]:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, encoding="utf-8") as fh:
        fh.write(source)
        path = fh.name
    lean, env = _lean_env()
    cmd = [lean, path]
    if mem := os.environ.get("LEAN_MEMORY_MB"):
        cmd.insert(1, f"--memory={mem}")
    proc = subprocess.Popen(
        cmd,
        cwd=LEAN_DIR,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        encoding="utf-8",
        errors="replace",
        creationflags=NO_WINDOW,
    )
    try:
        out, _ = proc.communicate(timeout=timeout)
        return out, False
    except subprocess.TimeoutExpired:
        _kill_tree(proc)
        out, _ = proc.communicate()
        return out or "", True
    finally:
        if proc.poll() is None:
            _kill_tree(proc)
            proc.wait()
        os.unlink(path)


def _check_batch(items: list[Item], timeout: int) -> list[Result]:
    """A file whose trailing sentinel is not printed was cut short (a stray
    `import`, `#exit` or unterminated comment); items after the cut report no
    errors, so such a batch is re-checked item by item and a lone item fails. Each item is
    followed by its own marker, which must be printed as well."""
    bad = [it for it in items if TRUNCATE_RE.search(it.body)]
    if bad:
        rest = [it for it in items if it not in bad]
        res = {it.item_id: Result(it.item_id, False, ["runner: body contains a file-level command"]) for it in bad}
        if rest:
            res.update((r.item_id, r) for r in _check_batch(rest, timeout))
        return [res[it.item_id] for it in items]
    sentinel = f"RUNNER_SENTINEL_{secrets.token_hex(8)}"
    source, ranges = _build(items, sentinel)
    output, timed_out = _run_file(source, timeout)
    if not timed_out and sentinel not in output:
        if len(items) > 1:
            return [r for it in items for r in _check_batch([it], timeout)]
        return [Result(items[0].item_id, False, ["runner: file truncated before sentinel"])]
    diags: list[tuple[int, str, str]] = []
    current: list[str] | None = None
    for raw in output.splitlines():
        if sentinel in raw:
            current = None
            continue
        m = DIAG_RE.match(raw)
        if m:
            current = [m.group("msg").lstrip(": ")]
            diags.append((int(m.group("line")), m.group("kind"), current))  # type: ignore[arg-type]
        elif current is not None:
            current.append(raw)
    results = []
    header_errors = [
        "\n".join(msg) for line, kind, msg in diags if kind == "error" and line <= len(items[0].imports)
    ]
    for it, (start, end) in zip(items, ranges):
        errs = [
            "\n".join(msg)[:800]
            for line, kind, msg in diags
            if kind == "error" and start - 1 <= line <= end + 1
        ]
        sorry = any(
            "declaration uses 'sorry'" in "\n".join(msg)
            for line, kind, msg in diags
            if kind == "warning" and start <= line <= end
        )
        errs = header_errors + errs
        results.append(Result(it.item_id, not errs and not timed_out, errs, sorry, timed_out))
    if timed_out:
        return results
    # Parser recovery after a malformed item can consume the following items, which then
    # report no error; each item must reach its own marker, and the item after a run of
    # missing markers may have lost its preamble, so those are re-checked alone.
    seen = set(re.findall(rf"{sentinel}_(\d+)", output))
    missing = {i for i in range(len(items)) if str(i) not in seen}
    if len(items) == 1 and missing:
        return [Result(items[0].item_id, False, results[0].errors or ["runner: item swallowed by parser recovery"],
                       results[0].uses_sorry)]
    for i in sorted(missing | {i + 1 for i in missing if i + 1 < len(items)}):
        results[i] = _check_batch([items[i]], timeout)[0]
    return results


def check(
    items: list[Item],
    batch_size: int = 20,
    workers: int = 4,
    timeout: int = 900,
    use_cache: bool = True,
) -> dict[str, Result]:
    CACHE.mkdir(parents=True, exist_ok=True)
    out: dict[str, Result] = {}
    todo: list[Item] = []
    dump = os.environ.get("RUNNER_DUMP")
    for it in items:
        if dump and re.search(dump, it.item_id):
            with _APPEND, open(CACHE / "dump_items.jsonl", "a", encoding="utf-8") as fh:
                fh.write(json.dumps({"item": it.item_id, "imports": it.imports, "body": it.body},
                                    ensure_ascii=False) + "\n")
        if TRUNCATE_RE.search(it.body):
            with _APPEND, open(CACHE / "truncate_bodies.jsonl", "a", encoding="utf-8") as fh:
                fh.write(json.dumps({"item": it.item_id, "key": _key(it), "imports": it.imports, "body": it.body},
                                    ensure_ascii=False) + "\n")
        f = CACHE / f"{_key(it)}.json"
        try:
            d = json.loads(f.read_text(encoding="utf-8")) if use_cache and f.exists() else None
        except (json.JSONDecodeError, UnicodeDecodeError):
            d = None  # truncated by an interrupted write; recheck
        if d is not None and (not d["ok"] or d.get("v", 1) >= CACHE_VERSION):
            out[it.item_id] = Result(it.item_id, d["ok"], d["errors"], d["uses_sorry"], d["timeout"])
        else:
            todo.append(it)
    stale = {it.item_id for it in todo if (CACHE / f"{_key(it)}.json").exists()}

    groups: dict[tuple[str, ...], list[Item]] = {}
    for it in todo:
        groups.setdefault(it.imports, []).append(it)
    batches = [g[i : i + batch_size] for g in groups.values() for i in range(0, len(g), batch_size)]

    def run(batch: list[Item]) -> list[tuple[Item, Result]]:
        res = _check_batch(batch, timeout)
        if len(batch) > 1 and any(r.timeout for r in res):
            res = [r for it in batch for r in _check_batch([it], timeout)]
        return list(zip(batch, res))

    workers = min(workers, int(os.environ.get("LEAN_WORKERS", workers)))
    with ThreadPoolExecutor(max_workers=workers) as pool:
        for pairs in pool.map(run, batches):
            for it, r in pairs:
                out[it.item_id] = r
                if it.item_id in stale and not r.ok:
                    with _APPEND, open(CACHE / "flips.jsonl", "a", encoding="utf-8") as fh:
                        fh.write(json.dumps({"item": it.item_id, "key": _key(it), "errors": r.errors[:2]}) + "\n")
                tmp = CACHE / f"{_key(it)}.{os.getpid()}.{threading.get_ident()}.tmp"
                tmp.write_text(
                    json.dumps(
                        {
                            "ok": r.ok,
                            "errors": r.errors,
                            "uses_sorry": r.uses_sorry,
                            "timeout": r.timeout,
                            "v": CACHE_VERSION,
                        },
                        ensure_ascii=False,
                    ),
                    encoding="utf-8",
                )
                os.replace(tmp, CACHE / f"{_key(it)}.json")
    return out
