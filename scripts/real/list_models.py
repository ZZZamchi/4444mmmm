#!/usr/bin/env python3
"""List model ids offered by the configured OpenAI-compatible provider."""

from __future__ import annotations

import json
import sys
import urllib.request
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from llm import _env


def main() -> None:
    base, key = _env()
    req = urllib.request.Request(f"{base}/models", headers={"Authorization": f"Bearer {key}"})
    with urllib.request.urlopen(req, timeout=60) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    ids = sorted(m["id"] for m in data.get("data", []))
    pattern = sys.argv[1] if len(sys.argv) > 1 else ""
    for i in ids:
        if pattern in i:
            print(i)


if __name__ == "__main__":
    main()
