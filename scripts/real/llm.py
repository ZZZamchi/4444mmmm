#!/usr/bin/env python3
"""Minimal OpenAI-compatible chat client with an on-disk cache.

Reads LLM_BASE_URL and LLM_API_KEY from the environment or from the repo's .env; with
LLM_ANTHROPIC_BASE set, `anthropic/*` models go over the Anthropic Messages protocol instead.
Responses are cached by (model, messages, temperature, sample index, max_tokens), so
reruns cost nothing and results are reproducible; `LLM_SAMPLE=k` reruns with fresh samples. A reply that is empty because the
model spent the whole budget on reasoning is retried with a larger budget, and such
cached replies are treated as misses unless they already exhausted MAX_BUDGET.
"""

from __future__ import annotations

import hashlib
import http.client
import json
import os
import time
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CACHE = ROOT / "data" / "real" / "cache" / "llm"
USAGE = ROOT / "data" / "real" / "cache" / "llm_usage.jsonl"
REFUSED = ROOT / "data" / "real" / "cache" / "llm_refused"


MAX_BUDGET = 32768
MAX_THROTTLED = 20  # HTTP 429 retries, on top of `retries`
MAX_REFUSED = int(os.environ.get("LLM_MAX_REFUSED", "5"))  # refusals per model and process before the model is no longer called
_refused: dict[str, int] = {}
NOTHINK = "-nothink"  # model-name suffix: same weights with thinking disabled, cached separately


class OutOfCredits(Exception):
    """HTTP 402 from the provider. Not a RuntimeError, so callers that treat a failed call
    as a missing proposal or verdict do not swallow it and the run stops instead."""


def _exhausted(usage: dict | None, budget: int) -> bool:
    """Reasoning models can spend the whole budget thinking and return no content."""
    return bool(usage) and (usage.get("completion_tokens") or 0) >= budget


def _log(model: str, event: str, usage: dict | None = None, detail: str = "") -> None:
    """Every attempt that may be billed is logged, including the ones that are not cached."""
    rec = {"t": time.strftime("%Y-%m-%dT%H:%M:%S"), "pid": os.getpid(), "model": model, "event": event,
           "usage": usage}
    if detail:
        rec["detail"] = detail[:1000] if event == "refused" else detail[:200]
    with USAGE.open("a", encoding="utf-8") as u:
        u.write(json.dumps(rec) + "\n")


def _env() -> tuple[str, str, str]:
    env = dict(os.environ)
    dotenv = ROOT / ".env"
    if dotenv.exists():
        for line in dotenv.read_text(encoding="utf-8").splitlines():
            if "=" in line and not line.startswith("#"):
                k, v = line.split("=", 1)
                env.setdefault(k.strip(), v.strip())
    # LLM_KEY_VAR names the variable holding this process's key; a missing key fails rather
    # than falling back to the shared one.
    return (env["LLM_BASE_URL"].rstrip("/"), env.get("LLM_ANTHROPIC_BASE", "").rstrip("/"),
            env[os.environ.get("LLM_KEY_VAR", "LLM_API_KEY")])


def _request(base: str, anthropic_base: str, api_key: str, model: str, messages: list[dict],
             temperature: float, budget: int, extra: dict) -> urllib.request.Request:
    """The provider serves `anthropic/*` models only over the Anthropic Messages protocol."""
    if anthropic_base and model.startswith("anthropic/"):
        system = "\n\n".join(m["content"] for m in messages if m["role"] == "system")
        body = {"model": model, "messages": [m for m in messages if m["role"] != "system"],
                "temperature": temperature, "max_tokens": budget, **({"system": system} if system else {})}
        return urllib.request.Request(
            f"{anthropic_base}/messages", data=json.dumps(body).encode(),
            headers={"x-api-key": api_key, "anthropic-version": "2023-06-01", "Content-Type": "application/json"})
    body = {"model": model, "messages": messages, "temperature": temperature, "max_tokens": budget, **extra}
    return urllib.request.Request(
        f"{base}/chat/completions", data=json.dumps(body).encode(),
        headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"})


def _reply(data: dict) -> tuple[str, dict | None]:
    """Content and an OpenAI-style usage record from either protocol's response."""
    if "choices" in data:
        return data["choices"][0]["message"]["content"] or "", data.get("usage")
    u = data.get("usage") or {}
    usage = {"prompt_tokens": u.get("input_tokens"), "completion_tokens": u.get("output_tokens")} if u else None
    return "".join(b.get("text", "") for b in data["content"] if b.get("type") == "text"), usage


def chat(
    model: str,
    messages: list[dict],
    temperature: float = 0.0,
    sample: int = 0,
    max_tokens: int = 4096,
    retries: int = 4,
) -> str:
    CACHE.mkdir(parents=True, exist_ok=True)
    # LLM_SAMPLE draws a fresh, separately cached sample for every call that does not set one.
    sample = sample or int(os.environ.get("LLM_SAMPLE", "0"))
    key = hashlib.sha256(
        json.dumps([model, messages, temperature, sample, max_tokens], ensure_ascii=False).encode()
    ).hexdigest()[:32]
    f = CACHE / f"{key}.json"
    try:
        cached = json.loads(f.read_text(encoding="utf-8")) if f.exists() else None
    except (json.JSONDecodeError, UnicodeDecodeError):
        cached = None  # truncated by an interrupted write; call again
    if cached is not None:
        usage = cached.get("usage")
        if cached["content"].strip() or not _exhausted(usage, max_tokens) or _exhausted(usage, MAX_BUDGET):
            return cached["content"]
    if (REFUSED / f"{key}.json").exists():
        raise RuntimeError("request refused before; not resent")
    if _refused.get(model, 0) >= MAX_REFUSED:
        _log(model, "breaker", None, key)
        raise RuntimeError(f"{model}: {MAX_REFUSED} refusals in this process; no further requests")
    if os.environ.get("LLM_CACHE_ONLY") == "1":
        _log(model, "cache_miss", None, key)
        raise RuntimeError("cache miss under LLM_CACHE_ONLY")
    base, anthropic_base, api_key = _env()
    budget = max_tokens
    last: Exception | None = None
    api_model, extra = model, {}
    if model.endswith(NOTHINK):
        api_model, extra = model[: -len(NOTHINK)], {"enable_thinking": False}
    attempt, throttled = 0, 0
    while attempt < retries:
        req = _request(base, anthropic_base, api_key, api_model, messages, temperature, budget, extra)
        try:
            with urllib.request.urlopen(req, timeout=600) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            content, usage = _reply(data)
            if not content.strip() and _exhausted(usage, budget) and budget < MAX_BUDGET:
                _log(model, "exhausted_retry", usage, f"budget={budget}")
                budget = min(budget * 4, MAX_BUDGET)
                attempt += 1
                continue
            tmp = f.with_suffix(f".{os.getpid()}.tmp")
            tmp.write_text(json.dumps({"content": content, "usage": usage}, ensure_ascii=False), encoding="utf-8")
            os.replace(tmp, f)
            _log(model, "ok", usage)
            return content
        except (urllib.error.URLError, http.client.HTTPException, OSError, KeyError, json.JSONDecodeError) as exc:
            if isinstance(exc, urllib.error.HTTPError) and exc.code == 402:
                raise OutOfCredits(exc.read().decode("utf-8", "replace")[:300]) from exc
            if isinstance(exc, urllib.error.HTTPError) and exc.code == 400:
                # A refused request (e.g. a provider safety filter) is not retried: retries count
                # as further violations and lengthen the freeze of the whole key.
                body = exc.read().decode("utf-8", "replace")
                _log(model, "refused", None, f"{key} {body}")
                _refused[model] = _refused.get(model, 0) + 1
                REFUSED.mkdir(parents=True, exist_ok=True)
                (REFUSED / f"{key}.json").write_text(
                    json.dumps({"model": model, "body": body, "messages": messages}, ensure_ascii=False),
                    encoding="utf-8")
                raise RuntimeError(f"request refused (400): {body[:300]}") from exc
            last = exc
            _log(model, "error", None, repr(exc))
            # Rate limits are not the model's failure; a call that gives up here would count as
            # a missing proposal and lower that model's coverage.
            if isinstance(exc, urllib.error.HTTPError) and exc.code == 429 and throttled < MAX_THROTTLED:
                throttled += 1
                time.sleep(min(30 * throttled, 300))
                continue
            time.sleep(2 ** attempt * 3)
            attempt += 1
    raise RuntimeError(f"LLM call failed after {retries} attempts: {last}")


def extract_lean(text: str) -> str:
    if "```" in text:
        parts = text.split("```")
        blocks = [parts[i] for i in range(1, len(parts), 2)]
        if blocks:
            block = max(blocks, key=len)
            first, _, rest = block.partition("\n")
            return rest if first.strip().lower() in {"lean", "lean4", ""} else block
    return text
