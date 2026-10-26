# What can a prover certify about autoformalization faithfulness? (code and data)

Anonymous release accompanying the paper. It contains everything needed to recompute the paper's tables
from the stored results and to recheck the Lean certificates; it does not rerun the language models.

- `paper/main.tex`: the paper source. `python scripts/real/paper_check.py` recomputes every main table and
  the numbers stated in the prose from `data/real/` and compares them with the source, cell by cell.
- `lean/Formalization/`, `lean/ExperimentsMathlib/`: Lean 4 developments. `CanonV2.lean` computes canonical
  telescopes and the fixed goals, `Probe.lean` the per-hypothesis probes, `BenchErrors.lean` the
  certificates for benchmark reference errors, `T1`-`T9` the formalized theory (no `sorry`, no added axioms).
- `scripts/real/`: one script per experiment; `paper_check.py` lists which results feed which table.
- `data/real/`: results and canonicalization caches. `data/real/ext/semanteq_manifest.jsonl` is
  `test/campaign/manifest.jsonl` of SemantEq (github.com/hlxr89/SemantEq, commit f927670), under its Apache-2.0
  license in `data/real/ext/SEMANTEQ_LICENSE`.

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
- Python 3.11 or later; reading the parquet releases of the benchmarks needs `pandas` with `pyarrow`.
  Run every script from the repository root.
