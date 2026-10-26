#!/usr/bin/env python3
"""K1: how many cached LLM replies would put top-level commands into a checked proof body."""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from llm import CACHE, extract_lean

CMD = re.compile(r"^\s*(import|theorem|lemma|example|def|namespace|end|section|universe|variable|instance|"
                 r"noncomputable|attribute|macro|syntax|elab|notation|#\w+)\b|^\s*(open|set_option)\b(?!.*\bin\s*$)",
                 re.M)

c, kinds = Counter(), Counter()
for f in CACHE.glob("*.json"):
    try:
        text = json.loads(f.read_text(encoding="utf-8"))["content"] or ""
    except (json.JSONDecodeError, KeyError):
        continue
    if "```" not in text:
        continue
    body = extract_lean(text)
    body = re.sub(r"^\s*theorem\s+\w+\s*:.*?:=\s*by\s*", "", body.strip(), flags=re.DOTALL)
    m = CMD.findall(body)
    c["lean_replies"] += 1
    if m:
        c["with_commands"] += 1
        kinds.update(a or b for a, b in m)
    if body.count("/-") != body.count("-/"):
        c["unbalanced_comment"] += 1
print(dict(c))
print(kinds.most_common(15))
