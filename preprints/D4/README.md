# A global sphere-packing upper bound in dimension four

The result is **upper density < 0.629521681653 for every packing of congruent balls in R4**. It is an upper bound, not a proof of D4 optimality.

## Contents

- [paper.pdf](paper.pdf) and [paper.tex](paper.tex): the preprint and editable source.
- [data/](data/README.md): exact scalar/kernel coefficients, 124 census floors, and both kernel-box certificates.
- [verify/](verify/README.md): all verification code and inherited certificate dependencies, with two additional kernel cross-checks.
- [lean/](lean/README.md): pinned Lean 4/Mathlib project, including the density transfer, scalar Fourier identity, geometry, and component-energy lemmas.
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

For Lean, install elan and the pinned Mathlib cache as described in [lean/README.md](lean/README.md), then run:

```sh
python3 verify/verify_lean.py --out /tmp/d4-lean-check
```

This builds the publication modules one at a time and checks the axiom reports. Alternatively, add `--lean` to the full verification command. The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`; no `sorry` or `native_decide` is used.

The expanded Lean project has not yet completed its final clean build or full spherical sign-tree replay in Lean. Earlier passing build receipts apply to the earlier recovery snapshot; individual compiled components are not a substitute for the final integrated check.

The concrete Lean theorem now takes seven explicit certificate hypotheses; seven of the original fourteen have been discharged or replaced by proved sufficient statements. The complete proof combines that theorem with the packaged written arguments and exact/interval certificate checks; it is not an unconditional end-to-end Lean proof of the concrete kernel.

To rebuild the preprint:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```
