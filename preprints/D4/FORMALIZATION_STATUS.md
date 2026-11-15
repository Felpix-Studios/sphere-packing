# Formalization status

This folder holds two separate proofs of the same bound. Each stands alone:
neither uses code, inputs or results of the other.

1. The non-Lean computer-assisted proof: the written arguments in `paper.tex`,
   the exact data in `data/` and the replay programs in `verify/`.
2. The Lean formalization in [`lean/`](lean/README.md).

## Lean result

`D4Bound.d4_density_bound_concrete` (`lean/D4Bound/ConcreteMain.lean`) states
that every set of centres in four dimensions with pairwise distance at least 1
has upper density below 629521681653/10^12. It takes only the packing and its
`IsUnitPacking` proof; every certificate statement is proved inside Lean.

- No `sorry` and no added `axiom` declaration.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` and 125 `native_decide`
  axioms, one per finite certificate check run as compiled code. These trust
  the Lean compiler and six checker libraries built from the Lean sources.
  The reductions and all checker soundness proofs use only the three standard
  axioms.
- Clean build, 2026-11-15: all 575 modules compiled from a frozen copy of the
  sources, 12,900 theorems audited, about 3.7 hours with four workers on a
  10-core machine. The result file, axiom report, per-module times and source
  hashes are in [`lean/verify/recorded/`](lean/verify/recorded/).

Reproduce from `lean/` (Lean 4.33.1 and Mathlib v4.33.1, see the Lean README):

```sh
lake exe cache get
python3 verify/verify_lean.py --out /tmp/d4-lean-check --workers 4 --require-unconditional
```
