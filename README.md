# Sphere packing upper bounds

Preprints, proof sources, and reproducible certificates for global sphere-packing upper bounds.

## Dimension four

Every packing of congruent balls in **R4 has upper density less than 0.629521681653**. This covers lattice, non-lattice, periodic, and nonperiodic packings. It does not prove that the D4 lattice, whose density is pi²/16 ≈ 0.616850, is optimal.

The [D4 package](preprints/D4/README.md) contains the [preprint PDF](preprints/D4/paper.pdf), its [LaTeX source](preprints/D4/paper.tex), all certificate data, verification programs, written component proofs, and the Lean project. It needs no private research checkout. Python/FLINT, a C++20 compiler, and (for Lean) the pinned public Lean/Mathlib dependencies must be installed.

From `preprints/D4`:

```sh
python3 -m pip install -r verify/requirements.txt
python3 verify/verify_all.py --out /tmp/d4-full-check --mode full --workers 2
```

The output folder must not already exist. Add `--lean` after installing the dependencies described in [lean/README.md](preprints/D4/lean/README.md). The [proof dependency map](preprints/D4/PROOF_DEPENDENCIES.md) distinguishes exact and interval checks, written proofs, Lean theorems, and cited classical inputs. Lean now defines the concrete kernel and discharges seven of the original fourteen certificate premises. Its concrete density theorem still has seven explicit premises supplied by the rest of the computer-assisted package.

## Completeness and proof scope

This is a standalone **computer-assisted proof package**, using written mathematics, exact/interval certificate checks, and Lean. All mathematical certificate data and project sources are included; no private research checkout is needed. Lean proves Schoenberg positivity on S² and S³ and supplies an exact projected eight-point certificate in place of the cited nine-point theorem. The [dependency map](preprints/D4/PROOF_DEPENDENCIES.md#classical-mathematical-inputs) distinguishes those completed proofs from the remaining concrete sign and energy bridges.

The earlier incomplete package omitted executable dependencies. The current package addresses those omissions as follows:

| Earlier completeness objection | Included correction |
|---|---|
| Base pair/triangle sign verifiers omitted | [Stage 1](preprints/D4/verify/stage1_v7/README.md) includes the Python/C++ sources and freshly checks seven pair pieces and all 112 cyclic branches. |
| Count census and spherical certificates missing | [Stage 2](preprints/D4/verify/stage2_origin/README.md) includes the named spherical certificate JSONs, their exact verifier, and the full 165,503-vector census; [stage 3](preprints/D4/verify/stage3_census/README.md) checks all 124 refined floors. |
| Kernel-box trees lack an evaluator | [Stage 5](preprints/D4/verify/stage5_kernelbox/README.md) includes the interval evaluator and replays all 286 and 4,663 leaves. The [exact kernel link](preprints/D4/verify/kernel_link/README.md) connects its formula to stage 1. |
| Allocation and density transfer assumed in Lean | [Allocation.lean](preprints/D4/lean/D4Bound/Allocation.lean) proves the allocation identities and far-pair bound; [Transfer.lean](preprints/D4/lean/D4Bound/Transfer.lean) proves transfer to arbitrary packings. |
| Lean compilation alone proves only a conditional implication | **Still true.** [ConcreteMain.lean](preprints/D4/lean/D4Bound/ConcreteMain.lean) retains seven explicit certificate hypotheses. The complete argument uses the supplied certificate checks and written component proofs to discharge them; compilation alone is not validation of the concrete packing bound. |

The [verification review](preprints/D4/REVIEW.md) preserves the passing full five-stage replay, exact kernel comparisons, clean Lean build, and failure controls for the earlier recovery snapshot. It distinguishes the separate fresh runs from the final driver-composition check. The expanded Lean sources have individual component checks, but their final clean build and full spherical sign-tree replay in Lean are still pending; the earlier 22-module build does not certify those later additions. See [current formalization status](preprints/D4/REVIEW.md#current-formalization-status). Quick mode is incomplete and must not be cited as a full replay. Hash manifests establish artifact identity, not mathematical correctness.

The [remaining-obligation table](preprints/D4/lean/HYPOTHESIS_AUDIT.md#remaining-obligations-in-the-concrete-theorem) tracks the seven premises. The concrete census composition now includes the twelve affine floors and ungauged pair sign; its remaining inputs are three spherical triangle-sign proofs. The clean Lean driver reconstructs all six spherical replay trees and offers `--require-unconditional` to reject any final density theorem that still requires certificate premises. That stronger gate has not yet passed.

For publication, include the entire `preprints/D4/` source/data tree along with the PDF; distributing the PDF and `data/` alone recreates the earlier omission. `.gitignore` excludes local caches and build products while keeping the checker, certificate, Lean, and LaTeX sources publishable.

| Comparison | Upper bound | Status |
|---|---:|---|
| Cohn–de Laat–Salmon | 0.636108 | Published three-point bound |
| Kravatskiy repository, commit 9160050 | 0.633428734445 | Cited computer-assisted bound |
| This package | **0.629521681653** | Computer-assisted global bound |

Sources and exact scope are given in the preprint. The comparison is not a fresh literature survey.

## Related work

- Cohn, de Laat and Salmon, [Three-point bounds for sphere packing](https://arxiv.org/abs/2206.15373).
- Kravatskiy, [SpherePackingUpperBounds](https://github.com/alexlegeartis/SpherePackingUpperBounds).
