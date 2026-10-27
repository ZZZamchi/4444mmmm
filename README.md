# What can a prover certify about autoformalization faithfulness? (code and data)

Anonymous release accompanying the paper. It contains everything needed to recompute the paper's tables
from the stored results and to recheck the Lean certificates; it does not rerun the language models.

- `paper/main.tex`: the paper source. `python scripts/real/paper_check.py` recomputes every main table and
  the numbers stated in the prose from `data/real/` and compares them with the source, cell by cell.
- `lean/Formalization/`, `lean/ExperimentsMathlib/`: Lean 4 developments. `CanonV2.lean` computes canonical
  telescopes and the fixed goals, `Probe.lean` the per-hypothesis probes, `BenchErrors.lean` the
  certificates for benchmark reference errors, `T1`-`T9` the formalized theory (no `sorry`, no added axioms).
- `scripts/real/`: one script per experiment; `paper_check.py` lists which results feed which table.
- `data/real/`: results and canonicalization caches. `data/real/ext/semanteq_manifest.jsonl` and
  `semanteq_pnv_test_verdicts.jsonl` are `test/campaign/manifest.jsonl` and `test/results/pnv_test_verdicts.jsonl`
  of SemantEq (github.com/hlxr89/SemantEq, commit f927670), under its Apache-2.0 license in
  `data/real/ext/SEMANTEQ_LICENSE`.

Code and data are released under the Apache License 2.0 (`LICENSE`).

The blind audit is in `data/real/h2_*`: the sheet the annotators saw (`h2_sheet.md`, `h2_sheet.csv`), the
items behind each sheet row (`h2_items.json`), the two answer files (`h2_annot_A.csv`, `h2_annot_B.csv`) and
the scores (`h2_scores.json`, from `scripts/real/h2_audit.py score`); `paper/h2_results.tex` is rendered from
the scores by `scripts/real/h2_tex.py`.

Not included: the language-model response cache, a language model's pre-annotation of the audit sheet
(never shown to the annotators and not used as evidence) and third-party benchmark files (the loaders in
`scripts/real/realdata.py` name their sources).

## Setup

- Lean `leanprover/lean4:v4.27.0-rc1` with Mathlib at the revision in `lean/lake-manifest.json`. Inside `lean/`,
  check a file with `lake env lean <file>`; the modules the scripts import are built with
  `lake env lean -o .lake/build/lib/lean/ExperimentsMathlib/X.olean ExperimentsMathlib/X.lean`.
- Python 3.11 or later with `pip install -r requirements.txt` (`pandas` and `pyarrow` read the parquet
  releases of the benchmarks, `scipy` the exact tests). Run every script from the repository root.

## Reproducing

From cheapest to most expensive:

1. `python scripts/real/paper_check.py` (seconds, Python only) recomputes the main tables and the checked
   prose numbers from `data/real/` and fails on any difference. It writes `data/real/paper_manifest.json`
   (the unit, denominator and label set of each kind of count, and every checked table and claim) and
   `data/real/paper_coverage.json` (the result numbers in the paper that no check covers yet).
2. Inside `lean/`, `lake env lean ExperimentsMathlib/BenchErrors.lean` checks the certificates for the
   benchmark reference errors, one row each in `data/real/bench_errors.csv`; the files of
   `lean/Formalization/` check the theory.
3. `K5_SOURCE=data/real/accepted_proofs.jsonl.gz K5_OUT=k5_recheck.json K5_WORKERS=8
   python scripts/real/k5_standalone_audit.py 100000` compiles each accepted model proof behind the tables
   alone, in a fresh file without any cache, followed by `#print axioms`, and fails it on any error, on a
   truncated file or on an axiom beyond `propext`, `Classical.choice` and `Quot.sound` (several CPU hours;
   the stored results are `data/real/k5_standalone_audit.json` and `k5_standalone_post.json`).
4. Each `scripts/real/<id>_*.py` reruns one experiment. The model calls need an OpenAI-compatible endpoint
   (`LLM_BASE_URL`, `LLM_API_KEY`; `LLM_ANTHROPIC_BASE` for `anthropic/*` models), and new calls need not
   return the proofs we obtained; see below.

## Versions

`data/real/sources.json` (from `scripts/real/sources_manifest.py`) records the Lean toolchain, the Mathlib
commit, the commit of every third-party repository the experiments read and the SHA-256 of the downloaded
files: the Hugging Face releases `PAug/ProofNetVerif` and `PAug/ProofNetSharp` and the miniF2F jsonl. The
labels are ProofNetVerif's published labels (in those files), SemantEq's adjudicated labels (its commit
above) and the blind audit (`data/real/h2_*`).

## What this release cannot reproduce

- The model responses. The response cache is not included, and the same request to the same model name
  need not return the same proof later. The results record which goals each run proved and every accepted
  proof, so each verdict can be rechecked in Lean, but a rerun will not match the tables call for call.
- The third-party benchmark files, which are not redistributed; `sources.json` pins their versions.
- The token and call counts of the cost table, which are as logged at run time.
- The human audits: the sheets and both annotators' answers are included, the judgments themselves are not
  repeatable by a script.
