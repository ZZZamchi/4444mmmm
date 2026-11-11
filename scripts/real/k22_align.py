#!/usr/bin/env python3
"""K22: normal forms and alignment by search for coverage (notes/protocol-v4.md).

Variants of `ExperimentsMathlib.CanonV4` on the 1,140 G5 pairs of ProofNetVerif test (development),
named by their flag strings (`univ0m`, `align`, `anon`, `shuffle`, ...). The baseline is v2.1 of the
held-out protocol (`v3_valid.py`): CanonV2 goals, proofs with Opus, R0 and R3. `--split valid` runs
the same steps on the held-out split and needs the v4 freeze (`data/real/v4_freeze.json`, and
`K22_VALID_UNLOCK` set to its commit). Results for the flag `perm` (an earlier version that only
permuted inside the greedy prefix, superseded by `align`) are kept in the outputs as a record.

Two kinds of change are measured.

* Goals. A pair whose canonical goals change is proved again with the G5 budget: fixed tactics,
  one Opus proposal for the open component goals, one repair; the regrouping goals get the R0
  tiers and a residual pair the R3 identity tactic, as in v2.1. Other pairs keep their v2.1 proofs.
* Locality (`L`). An accept is local when the alignment is total, or when the prefix is nonempty,
  one side is aligned completely and the remainder of the other contains no hypothesis: that
  remainder is then a conclusion quantified over binders the first side does not have, compared at
  every aligned input as the conclusion of a total alignment. When both sides keep a remainder
  (a type mismatch on both sides), the remainders are two closed statements and collapse; the
  dry run on test found 14 such false accepts for the two-sided version, so it is not used.

    k22_align.py dry FLAGS...        goals of each variant against CanonV2 (Lean only)
    k22_align.py tactics FLAGS...    tactic tiers on the pairs whose goals change (Lean only)
    k22_align.py run FLAGS...        Opus on the changed pairs the tactics leave undecided
    k22_align.py report FLAGS...     verdicts of each variant, with and without L, against v2.1

    k22_align.py nf FLAGS...         normal-form identity on residual and unknown pairs (Lean only)

Writes data/real/k22_align.json; caches data/real/k22_canon_cache.json and data/real/k22_proved.json
(with `--split valid`: data/real/v4/valid/{scores,canon_cache,proved}.json).
"""

from __future__ import annotations

import json
import os
import re
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f2_oracle as f2
import g1_full as g1
from f7_component import COMP_TAC, GOALS, LLM_GOALS, SPLIT_TAC, SPLIT_TAC2, classify
from f9_canon import lean_str, repair
from paper_check import verdict as paper_verdict
from runner import ROOT, Item, _build, _run_file, check
from v3_ident import IDENT_TAC
from v3_split import SPLIT_TAC3

# Normal-form identity: both sides of each component equivalence rewritten with content-free
# logical and order lemmas (orientation of `=` and `≠`, `>`/`≥`, negation through quantifiers,
# bounded quantifiers, AC of `∧`/`∨`/`∩`/`∪`), closed only when they become syntactically equal.
NF_LEMMAS = ("ne_eq, gt_iff_lt, ge_iff_le, not_not, not_exists, not_forall, not_and, not_or, exists_prop, "
             "exists_and_left, exists_and_right, and_imp, forall_exists_index, eq_comm, and_comm, and_assoc, "
             "and_left_comm, or_comm, or_assoc, or_left_comm, Set.mem_setOf_eq, Set.nonempty_iff_ne_empty, "
             "Set.inter_comm, Set.union_comm, iff_self")
NF_TAC = f"intros; constructor <;> first | exact Iff.rfl | (simp only [{NF_LEMMAS}]; done)"
D = ROOT / "data" / "real"
SPLIT = "valid" if "--split" in sys.argv and sys.argv[sys.argv.index("--split") + 1] == "valid" else "test"
if SPLIT == "valid":
    OUT_DIR = D / "v4" / "valid"
    OUT, CACHE, PROVED = OUT_DIR / "scores.json", OUT_DIR / "canon_cache.json", OUT_DIR / "proved.json"
    RESULTS, POST, CANON_V2 = (D / "v3" / "valid" / "g1_results_claude-opus-5.5.json", D / "v3" / "valid" / "post.json",
                               D / "v3" / "valid" / "canon.json")
else:
    OUT, CACHE, PROVED = D / "k22_align.json", D / "k22_canon_cache.json", D / "k22_proved.json"
    RESULTS, POST, CANON_V2 = (D / "g5" / "g1_results_claude-opus-5.5.json", D / "v3" / "test" / "post.json",
                               g1.CANON_CACHE)
FREEZE = D / "v4_freeze.json"
MODULE = "ExperimentsMathlib.CanonV4"
MODEL = os.environ.get("K22_MODEL", "anthropic/claude-opus-5.5")
SPLITS = ("split_r", "split_s")
WORKERS = int(os.environ.get("LLM_WORKERS", 12))
LEAN_WORKERS = int(os.environ.get("LEAN_WORKERS", 4))


def imports_of(r):
    imports, pre = f2.prelude(r)
    return tuple(sorted(set(imports) | {MODULE})), pre


def load():
    if SPLIT == "valid":
        frozen = json.loads(FREEZE.read_text(encoding="utf-8"))["commit"] if FREEZE.exists() else None
        if not frozen or os.environ.get("K22_VALID_UNLOCK") != frozen:
            raise PermissionError("the valid split is held out from v4 until the v4 freeze (notes/protocol-v4.md)")
        # proofnetverif still gates on the v3 freeze; unlock it for this process once v4 is unlocked
        v3 = D / "v3_freeze.json"
        if v3.exists():
            os.environ.setdefault("PNV_VALID_UNLOCK", json.loads(v3.read_text(encoding="utf-8"))["commit"])
        OUT_DIR.mkdir(parents=True, exist_ok=True)
    base = {p["row_id"]: p for p in json.loads(RESULTS.read_text(encoding="utf-8"))["pairs"]}
    post = json.loads(POST.read_text(encoding="utf-8"))
    rows = {r.row_id: r for r in g1.proofnetverif(SPLIT)}
    stmt = {rid: (rows[rid], f2.normalize(g1.to_prop(rows[rid].gold)), f2.normalize(g1.to_prop(rows[rid].pred)))
            for rid in base}
    cache = json.loads(CACHE.read_text(encoding="utf-8")) if CACHE.exists() else {}
    return base, post, stmt, cache


def save(path: Path, obj) -> None:
    tmp = path.with_suffix(f".{os.getpid()}.tmp")
    tmp.write_text(json.dumps(obj, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(tmp, path)


def canon(stmt, rids, flags, cache) -> None:
    groups: dict[tuple, list] = {}
    for rid in rids:
        if f"{flags}|{rid}" in cache:
            continue
        r, g, s = stmt[rid]
        imports, pre = imports_of(r)
        groups.setdefault(imports, []).append(
            Item(f"{flags}|{rid}", imports, f"{pre}\n#canon4_goals {lean_str(rid)} {lean_str(flags)} ({g}) ({s})"))
    batches = [g[i:i + 10] for g in groups.values() for i in range(0, len(g), 10)]
    if not batches:
        return

    def run(batch):
        out, _ = _run_file(_build(batch)[0], 900)
        return batch, out

    with ThreadPoolExecutor(max_workers=LEAN_WORKERS) as pool:
        for batch, out in pool.map(run, batches):
            blocks = dict(re.findall(r"CANON_BEGIN (\S+)\n(.*?)\n?CANON_END \1", out, flags=re.DOTALL))
            for it in batch:
                b = blocks.get(it.item_id.split("|", 1)[1])
                if b is None or b.startswith("CANON_FAIL"):
                    cache[it.item_id] = {"status": "fail"}
                else:
                    info = re.search(r"CANON_INFO (.*)", b).group(1)
                    goals = dict(re.findall(r"CANON_GOAL (\w+) ::: (.*?)(?=\nCANON_GOAL |\Z)", b, flags=re.DOTALL))
                    cache[it.item_id] = {"status": "ok", "info": info, "goals": goals}
    save(CACHE, cache)


def prove(stmt, flags, jobs, tag) -> dict:
    items, keys = [], []
    for (rid, goal), proof in jobs:
        r, g, s = stmt[rid]
        imports, pre = imports_of(r)
        body = (f"{pre}\nset_option maxHeartbeats 200000 in\n"
                f"canon4_prove {lean_str(flags)} {tag}_{goal} ({g}) ({s}) {goal} := by\n  {proof}")
        items.append(Item(f"k22|{flags}|{rid}:{tag}:{goal}", imports, body))
        keys.append((rid, goal))
    res = check(items, batch_size=10, workers=LEAN_WORKERS)
    return {k: res[it.item_id] for k, it in zip(keys, items)}


def field(info: str, name: str) -> str | None:
    m = re.search(rf"\b{name}=(\S+)", info or "")
    return m.group(1) if m else None


def local_l(info: str) -> bool:
    """Total alignment, or a nonempty prefix, one side aligned completely and no hypothesis left
    in the remainder of the other."""
    m = re.search(r"full=(\w+) prefix_r=(\d+)/(\d+) prefix_s=(\d+)/(\d+)", info or "")
    if not m or int(m.group(2)) + int(m.group(4)) == 0:
        return False
    if m.group(1) == "true":
        return True
    one_side = m.group(2) == m.group(3) or m.group(4) == m.group(5)
    return one_side and field(info, "rest_hyp_r") == "0" and field(info, "rest_hyp_s") == "0"


def final(proved: set, info: str, closed: str | None, ident: bool, rule_l: bool, nf: bool = False) -> str:
    """`nf`: `acc` holds by normal-form identity, which like `ident` is intensional evidence."""
    proved = proved | {"acc"} if nf else proved
    v = paper_verdict({"verdict": classify(proved - set(SPLITS)), "proved": sorted(proved),
                       "canon_info": info, "closed": closed})
    if v == "residual" and (ident or nf or (rule_l and local_l(info))):
        return "accept"
    return v


def nf_tier(stmt, flags, rids, store) -> None:
    jobs = [((rid, "acc"), NF_TAC) for rid in rids if f"nf|{flags}|{rid}" not in store]
    for (rid, _), res in prove(stmt, flags, jobs, "nf").items():
        store[f"nf|{flags}|{rid}"] = bool(g1.ok(res))


def changed_pairs(base, cache, flags) -> list[str]:
    return [rid for rid in base
            if cache.get(f"{flags}|{rid}", {}).get("status") == "ok"
            and cache.get(f"|{rid}", {}).get("goals") != cache[f"{flags}|{rid}"]["goals"]]


def tactics(stmt, flags, rids, goals, store) -> None:
    """Fixed tiers on the given pairs; results pooled in `store[flags|rid]`."""
    st = {rid: store.setdefault(f"{flags}|{rid}", {"tactic": [], "llm": [], "ident": False}) for rid in rids}
    jobs = [((rid, g), SPLIT_TAC if g in SPLITS else COMP_TAC) for rid in rids for g in (*GOALS, *SPLITS)
            if g not in st[rid]["tactic"]]
    for (rid, g), res in prove(stmt, flags, jobs, "t0").items():
        if g1.ok(res):
            st[rid]["tactic"].append(g)
    for tag, tac in (("t2", SPLIT_TAC2), ("t3", SPLIT_TAC3)):
        jobs = [((rid, g), tac) for rid in rids for g in SPLITS if g not in st[rid]["tactic"]]
        for (rid, g), res in prove(stmt, flags, jobs, tag).items():
            if g1.ok(res):
                st[rid]["tactic"].append(g)
    jobs = [((rid, "acc"), IDENT_TAC) for rid in rids if not st[rid]["ident"]]
    for (rid, _), res in prove(stmt, flags, jobs, "id").items():
        if g1.ok(res):
            st[rid]["ident"] = True
            if "acc" not in st[rid]["tactic"]:
                st[rid]["tactic"].append("acc")
    for rid in rids:
        st[rid]["tactic"] = sorted(set(st[rid]["tactic"]))


def opus(stmt, flags, rids, goals, store) -> None:
    """The G5 budget on component goals: one proposal for the open goals, one repair."""
    st = {rid: store[f"{flags}|{rid}"] for rid in rids}
    proved = {rid: set(st[rid]["tactic"]) | set(st[rid]["llm"]) for rid in rids}
    todo = {rid: [g for g in LLM_GOALS if g not in proved[rid]] for rid in rids
            if classify(proved[rid]) != "reject" and not st[rid].get("llm_done")}

    def work(rid):
        return rid, (g1.propose(MODEL, stmt[rid][0], goals[rid], todo[rid]) if todo[rid] else {})

    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        props = dict(pool.map(work, list(todo)))
    shot = prove(stmt, flags, [((rid, g), p) for rid, gs in props.items() for g, p in gs.items()], "o1")
    for (rid, g), res in shot.items():
        if g1.ok(res):
            proved[rid].add(g)
    failed = [((rid, g), res) for (rid, g), res in shot.items() if not g1.ok(res) and classify(proved[rid]) == "unknown"]

    def fix(item):
        (rid, g), res = item
        return (rid, g), repair(MODEL, stmt[rid][0], g, goals[rid][g], props[rid][g], res.errors)

    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        fixes = dict(pool.map(fix, failed))
    for (rid, g), res in prove(stmt, flags, [(k, p) for k, p in fixes.items() if p], "o2").items():
        if g1.ok(res):
            proved[rid].add(g)
    for rid in todo:
        st[rid]["llm"] = sorted(proved[rid] - set(st[rid]["tactic"]))
        st[rid]["llm_done"] = True


def baseline(p, post) -> tuple[set, bool]:
    q = post[p["row_id"]]
    return set(p.get("proved") or []) | set(q["splits_added"]), bool(q["identical"])


def verdicts(base, post, cache, store, flags, rules: str, stage: str) -> dict[str, str]:
    """rules: subset of `L,NF`; stage: `tactics` (changed pairs with fixed tactics only) or `full`."""
    rule_l, rule_nf = "L" in rules.split(","), "NF" in rules.split(",")
    changed = set(changed_pairs(base, cache, flags)) if flags else set()
    out = {}
    for rid, p in base.items():
        c = cache.get(f"{flags}|{rid}", {})
        if c.get("status") != "ok" and p["verdict"] != "canon_fail":
            out[rid] = "unknown"
            continue
        info = c.get("info") or p.get("canon_info")
        if rid in changed:
            s = store.get(f"{flags}|{rid}")
            if s is None:
                out[rid] = "pending"
                continue
            nf = rule_nf and store.get(f"nf|{flags}|{rid}", False)
            proved = set(s["tactic"]) | (set(s["llm"]) if stage == "full" else set())
            out[rid] = final(proved, info, p.get("closed"), s["ident"], rule_l, nf)
        else:
            if p["verdict"] == "canon_fail":
                out[rid] = "unknown"
                continue
            nf = rule_nf and store.get(f"nf||{rid}", False)
            proved, ident = baseline(p, post)
            out[rid] = final(proved, info, p.get("closed"), ident, rule_l, nf)
    return out


def semanteq_labels(base) -> dict[str, bool]:
    """ProofNetVerif labels with SemantEq's adjudication of the pairs labelled equivalent."""
    from k17_semanteq import manifest
    man = manifest()
    return {r: (man[r]["label"] == "equivalent" if r in man else True) if p["label"] else False
            for r, p in base.items()}


def tally(base, vs, labels=None) -> dict:
    lab = labels or {r: p["label"] for r, p in base.items()}
    c = Counter(f"{'F' if lab[r] else 'U'}:{v}" for r, v in vs.items())
    nF = sum(lab.values())
    nU = len(base) - nF
    return {"F_accept": c["F:accept"], "F_accept_pct": round(100 * c["F:accept"] / nF, 2),
            "U_accept": c["U:accept"], "U_accept_pct": round(100 * c["U:accept"] / nU, 2),
            "verdicts": dict(sorted(c.items()))}


V4_FLAGS = "univ0m,align"
V4_RULES = "L,NF"


def score(base, post, cache, store) -> dict:
    """v2.1 against v4 (`V4_FLAGS` with `V4_RULES`) and its ablations; H5 of notes/protocol-v4.md."""
    from paper_check import wilson
    from v3_valid import exact_mcnemar
    arms = {"v2.1": verdicts(base, post, cache, store, "", "", "full"),
            "v4": verdicts(base, post, cache, store, V4_FLAGS, V4_RULES, "full"),
            "v2.1+L,NF": verdicts(base, post, cache, store, "", V4_RULES, "full"),
            f"{V4_FLAGS} only": verdicts(base, post, cache, store, V4_FLAGS, "", "full")}
    U = [r for r in base if not base[r]["label"]]
    F = [r for r in base if base[r]["label"]]
    pct = lambda k, n: round(100 * k / n, 2)
    ci = lambda k, n: [round(100 * x, 2) for x in wilson(k, n)]
    metrics = {}
    for arm, a in arms.items():
        fa = sum(a[r] == "accept" for r in U)
        acc = sum(a[r] == "accept" for r in F)
        metrics[arm] = {"false_accept": fa, "false_accept_pct": pct(fa, len(U)), "false_accept_ci": ci(fa, len(U)),
                        "accept": acc, "accept_pct": pct(acc, len(F)), "accept_ci": ci(acc, len(F)),
                        "verdicts": dict(sorted(Counter(f"{'F' if r in F else 'U'}:{a[r]}" for r in base).items()))}
    b = sum(arms["v4"][r] == "accept" and arms["v2.1"][r] != "accept" for r in F)
    c = sum(arms["v2.1"][r] == "accept" and arms["v4"][r] != "accept" for r in F)
    fa_diff = metrics["v4"]["false_accept_pct"] - metrics["v2.1"]["false_accept_pct"]
    p = exact_mcnemar(b, c, True)
    return {"split": SPLIT, "pairs": len(base), "inequivalent": len(U), "equivalent": len(F), "metrics": metrics,
            "H5_v4_vs_v21_accepts": {"discordant": [b, c], "p_one_sided": p,
                                     "false_accept_increase_pp": round(fa_diff, 2),
                                     "holds": p < 0.05 and fa_diff <= 1.0},
            "changed_pairs": len(changed_pairs(base, cache, V4_FLAGS)),
            "new_false_accepts": sorted(r for r in U if arms["v4"][r] == "accept" and arms["v2.1"][r] != "accept")}


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    t0 = time.time()
    args = [a for i, a in enumerate(sys.argv) if a != "--split" and sys.argv[i - 1] != "--split"]
    mode = args[1]
    flags_list = args[2:]
    base, post, stmt, cache = load()
    canon(stmt, list(base), "", cache)
    ref = json.loads(CANON_V2.read_text(encoding="utf-8"))
    same = sum(cache.get(f"|{rid}", {}).get("goals") == ref.get(rid, {}).get("goals") for rid in base)
    print("CanonV4 with no flags: goals equal to CanonV2 on", same, "/", len(base), f"{time.time() - t0:.0f}s",
          flush=True)
    for flags in flags_list:
        canon(stmt, list(base), flags, cache)
    store = json.loads(PROVED.read_text(encoding="utf-8")) if PROVED.exists() else {}
    if mode == "dry":
        v21 = verdicts(base, post, cache, store, "", "", "full")
        lab = {r: "F" if p["label"] else "U" for r, p in base.items()}
        for flags in ["", *flags_list]:
            ch = changed_pairs(base, cache, flags) if flags else []
            infos = {rid: cache.get(f"{flags}|{rid}", {}).get("info", "") for rid in base}
            print(repr(flags), "changed", len(ch),
                  "fail", sum(cache.get(f"{flags}|{rid}", {}).get("status") != "ok" for rid in base),
                  "moved", dict(Counter(lab[r] for r in base if field(infos[r], "moved") == "true")),
                  "full", dict(Counter(lab[r] for r in base if "full=true" in infos[r])),
                  "local_L", dict(Counter(lab[r] for r in base if local_l(infos[r]))),
                  "changed by v2.1 verdict", dict(sorted(Counter(f"{lab[r]}:{v21[r]}" for r in ch).items())),
                  flush=True)
            if flags.endswith("shuffle"):
                plain = flags[:-len("shuffle")].rstrip(",")
                comp = ("acc", "cond", "nhyp", "ncin", "ncomp")
                same = lambda r: all(cache.get(f"{flags}|{r}", {}).get("goals", {}).get(g)
                                     == cache.get(f"{plain}|{r}", {}).get("goals", {}).get(g) for g in comp)
                moved_runs = [r for r in base if cache.get(f"{flags}|{r}", {}).get("goals", {}).get("split_s")
                              != cache.get(f"{plain}|{r}", {}).get("goals", {}).get("split_s")]
                diff = [r for r in moved_runs if not same(r)]
                print(f"   reversing same-type runs changes the candidate in {len(moved_runs)} pairs; the component"
                      f" goals differ from {plain!r} in {len(diff)}",
                      dict(sorted(Counter(f"{lab[r]}:{v21[r]}" for r in diff).items())), flush=True)
            elif flags.endswith("anon"):
                named = flags[:-len("anon")].rstrip(",")
                diff = [r for r in base if field(infos[r], "map")
                        != field(cache.get(f"{named}|{r}", {}).get("info", ""), "map")]
                print("   renaming every candidate binder changes the alignment of", len(diff), "pairs vs",
                      repr(named), dict(sorted(Counter(f"{lab[r]}:{v21[r]}" for r in diff).items())), flush=True)
        return
    for flags in flags_list if mode in ("tactics", "run") else []:
        ch = changed_pairs(base, cache, flags)
        goals = {rid: cache[f"{flags}|{rid}"]["goals"] for rid in ch}
        tactics(stmt, flags, ch, goals, store)
        save(PROVED, store)
        if mode == "run":
            info = {rid: cache[f"{flags}|{rid}"]["info"] for rid in ch}
            und = [rid for rid in ch
                   if final(set(store[f"{flags}|{rid}"]["tactic"]), info[rid], base[rid].get("closed"),
                            store[f"{flags}|{rid}"]["ident"], True) == "unknown"]
            print(flags, "changed", len(ch), "undecided after tactics", len(und), flush=True)
            opus(stmt, flags, und, goals, store)
            save(PROVED, store)
        print(flags, mode, "done", f"{time.time() - t0:.0f}s", flush=True)
    if mode == "nf":
        # normal-form identity on every pair that is residual or unknown with the tactic and Opus proofs
        for flags in ["", *flags_list]:
            vs = verdicts(base, post, cache, store, flags, "L", "full")
            changed = set(changed_pairs(base, cache, flags)) if flags else set()
            todo = [r for r, v in vs.items() if v in ("residual", "unknown") and (not flags or r in changed)
                    and cache.get(f"{flags}|{r}", {}).get("status") == "ok"]
            nf_tier(stmt, flags, todo, store)
            save(PROVED, store)
            print(repr(flags), "normal-form identity on", len(todo), "pairs:", sum(store[f"nf|{flags}|{r}"] for r in todo),
                  f"{time.time() - t0:.0f}s", flush=True)
    if mode == "score":
        out = score(base, post, cache, store)
        save(D / "k22_score_test.json" if SPLIT == "test" else OUT, out)
        print(json.dumps({k: v for k, v in out.items() if k != "metrics"}, indent=1))
        for arm, m in out["metrics"].items():
            print(f"{arm:22s} accept {m['accept']} ({m['accept_pct']}%) false accept {m['false_accept']}"
                  f" ({m['false_accept_pct']}%)")
        return
    if mode in ("report", "tactics", "run", "nf"):
        out = json.loads(OUT.read_text(encoding="utf-8")) if OUT.exists() else {}
        sem = semanteq_labels(base) if SPLIT == "test" else None
        v21 = verdicts(base, post, cache, store, "", "", "full")
        for flags in ["", *flags_list]:
            for rules in ("", "L", "NF", "L,NF"):
                for stage in (("full",) if not flags else ("tactics", "full")):
                    vs = verdicts(base, post, cache, store, flags, rules, stage)
                    if "pending" in vs.values():
                        continue
                    key = f"{flags or 'v2.1'}{'+' + rules if rules else ''}@{stage}"
                    flips = Counter(f"{'F' if base[r]['label'] else 'U'}:{v21[r]}->{vs[r]}" for r in base if vs[r] != v21[r])
                    out[key] = {**tally(base, vs), "flips": dict(sorted(flips.items()))}
                    if sem:
                        out[key]["semanteq"] = tally(base, vs, sem)
                    t, s = out[key], out[key].get("semanteq")
                    print(f"{key:28s} F {t['F_accept']} ({t['F_accept_pct']}%)  U {t['U_accept']} ({t['U_accept_pct']}%)"
                          + (f" | SemantEq F {s['F_accept']} ({s['F_accept_pct']}%) U {s['U_accept']} ({s['U_accept_pct']}%)"
                             if s else "") + f" | {dict(sorted(flips.items()))}", flush=True)
        save(OUT, out)


if __name__ == "__main__":
    main()
