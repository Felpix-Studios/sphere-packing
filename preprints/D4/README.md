# A global sphere-packing upper bound in dimension four

The result is **upper density < 0.629521681653 for every packing of congruent balls in R4**. It is an upper bound, not a proof of D4 optimality.

## Contents

- [paper.pdf](paper.pdf) and [paper.tex](paper.tex): the preprint and editable source.
- [data/](data/README.md): exact scalar/kernel coefficients, 124 census floors, and both kernel-box certificates.
- [verify/](verify/README.md): all verification code and inherited certificate dependencies, with two additional kernel cross-checks.
- [lean/](lean/README.md): separate, work-in-progress Lean 4/Mathlib formalization. It is not required by the non-Lean verifier below.
- [REVIEW.md](REVIEW.md): historical replay results and the current formalization/clean-build status.
- [PROOF_DEPENDENCIES.md](PROOF_DEPENDENCIES.md): the mathematical dependency chain and the precise boundary between machine checks, written arguments, and cited theorems.

No executable certificate input comes from outside this folder. Historical absolute filenames inside some data files are provenance strings. Standard software dependencies are installed separately.

## Reproduce

Run from this folder, using Python 3.10 or later, the pinned packages, and a C++20 compiler:

```sh
python3 -m pip install -r verify/requirements.txt
python3 verify/verify_all.py --out /tmp/d4-full-check --mode full --workers 2
```

Use a new output directory. Do not use `python -O` or `PYTHONOPTIMIZE`: inherited checkers use assertions. `--mode quick` omits the 112 triangle subdivisions and is **not a fresh verification of the global theorem**.

The command above is the complete non-Lean computer-assisted proof replay. It reads only `data/` and `verify/` in this folder, plus the listed Python, FLINT, Arb and C++ dependencies. It does not import, compile or inspect the Lean project.

The Lean formalization is separate. If desired, install elan and the pinned Mathlib cache as described in [lean/README.md](lean/README.md), then run:

```sh
python3 verify/verify_lean.py --out /tmp/d4-lean-check
```

This builds the separate publication modules and checks their axiom reports. It is independent of the non-Lean replay; `verify_all.py` has no Lean flag or Lean prerequisite.

The expanded Lean project has not yet completed its final clean build or full spherical sign-tree replay in Lean. Earlier passing build receipts apply to the earlier recovery snapshot; individual compiled components are not a substitute for the final integrated check.

The Lean theorem and its remaining hypotheses are not part of the non-Lean proof claim. The non-Lean proof uses the written density-transfer theorem in `paper.tex` together with the five certificate stages and the two exact kernel cross-checks.

To rebuild the preprint:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```
