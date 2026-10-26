#!/usr/bin/env python3
"""Turn `theorem name binders : concl := proof` into the closed Prop `∀ binders, concl`.

The scanner tracks bracket depth so that colons inside binders are skipped.
Anything it cannot split (no top-level `:`, auxiliary declarations before the
theorem, pattern-matching definitions) returns None and is counted separately.
"""

from __future__ import annotations

import re

OPEN = "([{⟨⦃"
CLOSE = ")]}⟩⦄"
KW_RE = re.compile(r"^\s*(theorem|lemma)\s+(\S+)", re.MULTILINE)
DECL_RE = re.compile(r"^\s*(theorem|lemma|def|abbrev|instance|structure|inductive|noncomputable|variable)\b", re.MULTILINE)


def strip_comments(src: str) -> str:
    src = re.sub(r"/-.*?-/", " ", src, flags=re.DOTALL)
    return "\n".join(line.split("--", 1)[0] for line in src.splitlines())


def _top_level(s: str, start: int):
    depth = 0
    i = start
    while i < len(s):
        c = s[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0:
            yield i
        i += 1


def to_prop(src: str) -> str | None:
    src = strip_comments(src)
    if len(DECL_RE.findall(src)) != 1:
        return None
    m = KW_RE.search(src)
    if m is None:
        return None
    rest = src[m.end():]
    colon = None
    assign = None
    for i in _top_level(rest, 0):
        if rest.startswith(":=", i):
            if colon is not None:
                assign = i
                break
        elif rest[i] == ":" and colon is None:
            colon = i
    if colon is None or assign is None:
        return None
    binders = " ".join(rest[:colon].split())
    concl = " ".join(rest[colon + 1 : assign].split())
    if not concl:
        return None
    if binders:
        return f"∀ {binders}, {concl}"
    return concl
