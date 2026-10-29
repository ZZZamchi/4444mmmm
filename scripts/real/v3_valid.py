#!/usr/bin/env python3
"""Held-out evaluation of notes/protocol-v3.md: closed, v2 and v2.1 on the ProofNetVerif valid split.

Steps, each resumable through the Lean and LLM caches:

    overlap   stmt_id shared by the valid and test splits (first step after the freeze)
    f2        usable pairs and the closed tactic tiers           -> v3/valid/f2_full.json
    canon     canonical telescopes (CanonV2)                     -> v3/valid/canon.json
    model     component and closed proofs with Opus (G1 budget)  -> v3/valid/g1_results_<model>.json
    api       model-call outcomes since the run started; stops the chain above 5% failed calls
    e2        regrouping certificates of decided pairs (as in the paper's runs)
    post      v2.1: R0 (SPLIT_TAC2, SPLIT_TAC3 on every missing certificate) and R3 (reducible
              identity on residual pairs), Lean only                -> v3/valid/post.json
    score     the three arms, the metrics and hypotheses H1-H4 of the protocol -> v3/valid/scores.json

`--split test` runs `post` and `score` on the paper's full-set run (G5, Opus) instead, to check the
scoring against the published tables before the freeze. Reading the valid split needs the freeze
(`realdata.held_out_unlocked`).

Usage: v3_valid.py STEP [--split test]
"""

from __future__ import annotations

import functools
import json
import os
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import g1_full as g1
import g5_scale
import runner
from f7_component import SPLIT_TAC2
from paper_check import D, located, verdict, wilson
from realdata import proofnetverif
from stmt import to_prop
from v3_ident import IDENT_TAC
from v3_split import SPLIT_TAC3

MODEL = "anthropic/claude-opus-5.5"
SPLIT = "test" if "--split" in sys.argv and sys.argv[sys.argv.index("--split") + 1] == "test" else "valid"
if SPLIT == "valid":
    OUT_DIR = D / "v3" / "valid"
    F2_FILE = OUT_DIR / "f2_full.json"
    CANON = OUT_DIR / "canon.json"
    RESULTS = OUT_DIR / f"g1_results_{MODEL.split('/')[-1]}.json"
else:
    OUT_DIR = D / "v3" / "test"
    F2_FILE = D / "g5" / "f2_full.json"
    CANON = g1.CANON_CACHE
    RESULTS = D / "g5" / f"g1_results_{MODEL.split('/')[-1]}.json"
POST = OUT_DIR / "post.json"
SCORES = OUT_DIR / "scores.json"
# false accepts of v2 (Opus) on the 544 inequivalent full-set pairs outside the development subset (H4)
TEST_OUTSIDE_DEV = (14, 544)


def configure() -> None:
    f2.SPLIT = SPLIT
    f2.OUT = F2_FILE
    g1.CANON_CACHE = CANON
    g1.OUT = RESULTS
    g1.MODEL = MODEL
    OUT_DIR.mkdir(parents=True, exist_ok=True)


def pairs_of(rows: dict) -> list:
    return [(rows[p["row_id"]], f2.normalize(to_prop(rows[p["row_id"]].gold)), f2.normalize(to_prop(rows[p["row_id"]].pred)))
            for p in json.loads(F2_FILE.read_text(encoding="utf-8"))["pairs"]]


def step_overlap() -> None:
    test = {r.stmt_id for r in proofnetverif("test")}
    valid = {r.stmt_id for r in proofnetverif("valid")}
    out = {"test_statements": len(test), "valid_statements": len(valid), "shared": sorted(test & valid)}
    (OUT_DIR / "overlap.json").write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    print({k: (len(v) if isinstance(v, list) else v) for k, v in out.items()})


def step_f2() -> None:
    g5_scale.F2_FULL = F2_FILE
    g5_scale.G5 = OUT_DIR
    g5_scale.run_f2()


def step_canon() -> None:
    rows = {r.row_id: r for r in proofnetverif(SPLIT)}
    canon = g1.canon_all(pairs_of(rows))
    print("canon", Counter(c["status"] for c in canon.values()), flush=True)


def step_e2() -> None:
    sys.argv = ["e2_split_complete.py", "g1", MODEL, str(RESULTS)]
    import e2_split_complete as e2
    e2.main()


def step_api() -> None:
    """Model-call outcomes logged since the run started (OUT_DIR/started); fails above 5% errors."""
    from llm import USAGE
    since = (OUT_DIR / "started").read_text(encoding="utf-8").strip()
    c = Counter()
    for line in USAGE.read_text(encoding="utf-8").splitlines():
        try:
            r = json.loads(line)
        except json.JSONDecodeError:
            # concurrent writers can leave blank or partial lines
            continue
        # records written before the logger had timestamps and events carry neither field
        if r.get("model") == MODEL and r.get("t", "") >= since and "event" in r:
            c[r["event"]] += 1
    bad = c["error"] + c["refused"] + c["breaker"]
    ok = c["ok"]
    first = OUT_DIR / "round1_api_events.json"
    if first.exists():
        # a retry round resends only the requests that failed before, the others come from the cache:
        # the failed attempts of this round bound the requests left without a response, out of all
        # requests of the run
        ok += json.loads(first.read_text(encoding="utf-8"))["events"].get("ok", 0)
    out = {"since": since, "events": dict(c), "error_rate": round(bad / max(1, bad + ok), 4)}
    (OUT_DIR / "api_events.json").write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    print(out)
    if out["error_rate"] > 0.05:
        raise SystemExit("model calls failed above 5%: stop before scoring (protocol section 7)")


def load_results() -> list[dict]:
    return json.loads(RESULTS.read_text(encoding="utf-8"))["pairs"]


def step_post() -> None:
    ps = load_results()
    rows = {r.row_id: r for r in proofnetverif(SPLIT)}
    canon = json.loads(CANON.read_text(encoding="utf-8"))
    stmt = {p["row_id"]: (rows[p["row_id"]], f2.normalize(to_prop(rows[p["row_id"]].gold)),
                          f2.normalize(to_prop(rows[p["row_id"]].pred))) for p in ps}
    # R0: every missing regrouping goal of a pair with a canonical form, decided or not
    todo = [(p["row_id"], g) for p in ps if canon.get(p["row_id"], {}).get("status") == "ok"
            for g in ("split_r", "split_s") if g not in (p.get("proved") or [])]
    found: dict[tuple, str] = {}
    for tag, tac in (("v3s2", SPLIT_TAC2), ("v3s3", SPLIT_TAC3)):
        res = g1.prove_items([((rid, g), (*stmt[rid], tac)) for rid, g in todo if (rid, g) not in found], tag)
        found.update({k: tag for k, v in res.items() if v.ok and not v.uses_sorry})
    added = {p["row_id"]: sorted(g for (rid, g) in found if rid == p["row_id"]) for p in ps}
    # R3: reducible identity of the residual pairs
    resid = [p for p in ps if verdict(p, proved=set(p.get("proved") or []) | set(added[p["row_id"]])) == "residual"]
    ident = g1.prove_items([((p["row_id"], "acc"), (*stmt[p["row_id"]], IDENT_TAC)) for p in resid], "v3id")
    post = {p["row_id"]: {"splits_added": added[p["row_id"]],
                          "identical": bool(ident.get((p["row_id"], "acc")) and ident[(p["row_id"], "acc")].ok
                                            and not ident[(p["row_id"], "acc")].uses_sorry)} for p in ps}
    POST.write_text(json.dumps(post, indent=1) + "\n", encoding="utf-8")
    print("R0 goals", len(todo), "proved", Counter(found.values()), "R3 residual", len(resid),
          "identical", sum(v["identical"] for v in post.values()), flush=True)


def arms(p: dict, post: dict) -> dict[str, str]:
    v2 = verdict(p)
    proved = set(p.get("proved") or []) | set(post["splits_added"])
    v21 = verdict(p, proved=proved)
    if v21 == "residual" and post["identical"]:
        v21 = "accept"
    return {"closed": "accept" if p.get("closed") == "proved" else "reject" if p.get("closed") == "refuted" else "undecided",
            "v2": v2, "v2.1": v21, "v2_located": bool(v2 == "reject" and located(p)),
            "v2.1_located": bool(v21 == "reject" and located({**p, "proved": sorted(proved)}))}


def exact_mcnemar(b: int, c: int, one_sided: bool = False) -> float:
    from scipy.stats import binomtest
    if b + c == 0:
        return 1.0
    return binomtest(b, b + c, 0.5, alternative="greater" if one_sided else "two-sided").pvalue


def step_score() -> None:
    from scipy.stats import fisher_exact
    ps = load_results()
    post = json.loads(POST.read_text(encoding="utf-8"))
    a = {p["row_id"]: arms(p, post[p["row_id"]]) for p in ps}
    lab = {p["row_id"]: bool(p["label"]) for p in ps}
    U = [r for r in a if not lab[r]]
    F = [r for r in a if lab[r]]
    pct = lambda k, n: round(100 * k / n, 2) if n else None
    ci = lambda k, n: [round(100 * x, 2) for x in wilson(k, n)]
    metrics = {}
    for arm in ("closed", "v2", "v2.1"):
        fa = sum(a[r][arm] == "accept" for r in U)
        acc = sum(a[r][arm] == "accept" for r in F)
        rej_u = sum(a[r][arm] == "reject" for r in U)
        rej_f = sum(a[r][arm] == "reject" for r in F)
        dec = sum(a[r][arm] in ("accept", "reject") for r in a)
        m = {"false_accept": fa, "false_accept_pct": pct(fa, len(U)), "false_accept_ci": ci(fa, len(U)),
             "accept": acc, "accept_pct": pct(acc, len(F)), "accept_ci": ci(acc, len(F)),
             "reject_inequivalent": rej_u, "reject_equivalent": rej_f,
             "reject_precision_pct": pct(rej_u, rej_u + rej_f), "decided_pct": pct(dec, len(a)),
             "verdicts": dict(Counter(f"{'F' if lab[r] else 'U'}:{a[r][arm]}" for r in a))}
        if arm != "closed":
            loc = sum(a[r][f"{arm}_located"] for r in U)
            m.update({"located_rejects": loc, "located_pct": pct(loc, rej_u)})
        metrics[arm] = m
    disc = lambda x, y, rs: (sum(a[r][x] == "accept" and a[r][y] != "accept" for r in rs),
                             sum(a[r][y] == "accept" and a[r][x] != "accept" for r in rs))
    b1, c1 = disc("closed", "v2", U)
    b2, c2 = disc("v2.1", "v2", F)
    fa_diff = metrics["v2.1"]["false_accept_pct"] - metrics["v2"]["false_accept_pct"]
    hyp = {
        "H1_closed_vs_v2_false_accepts": {"discordant": [b1, c1], "p": exact_mcnemar(b1, c1),
                                          "holds": exact_mcnemar(b1, c1) < 0.05 and b1 > c1},
        "H2_v21_vs_v2_accepts": {"discordant": [b2, c2], "p_one_sided": exact_mcnemar(b2, c2, True),
                                 "false_accept_increase_pp": round(fa_diff, 2),
                                 "holds": exact_mcnemar(b2, c2, True) < 0.05 and fa_diff <= 1.0},
    }
    # descriptive only (protocol section 5): R0 adds unlocated rejects by definition
    located_report = {arm: {"located": metrics[arm]["located_rejects"], "share_pct": metrics[arm]["located_pct"]}
                      for arm in ("v2", "v2.1")}
    if SPLIT == "valid":
        k, n = TEST_OUTSIDE_DEV
        p4 = fisher_exact([[metrics["v2"]["false_accept"], len(U) - metrics["v2"]["false_accept"]], [k, n - k]])[1]
        hyp["H4_v2_valid_vs_test_outside_dev"] = {"valid": [metrics["v2"]["false_accept"], len(U)], "test": [k, n],
                                                  "p": p4, "holds": p4 >= 0.05}
    out = {"split": SPLIT, "pairs": len(a), "inequivalent": len(U), "equivalent": len(F),
           "metrics": metrics, "hypotheses": hyp, "located": located_report}
    SCORES.write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(out, indent=1))


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    step = sys.argv[1]
    configure()
    if SPLIT == "valid":
        f2.check = functools.partial(runner.check, workers=int(os.environ.get("G5_WORKERS", 10)))
    {"overlap": step_overlap, "f2": step_f2, "canon": step_canon, "model": g1.main, "api": step_api,
     "e2": step_e2, "post": step_post, "score": step_score}[step]()


if __name__ == "__main__":
    main()
