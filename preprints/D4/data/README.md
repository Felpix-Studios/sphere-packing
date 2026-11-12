# D4 certificate data

Inputs for the bound Δ₄ < 0.629521681653 in [`../paper.pdf`](../paper.pdf). Numbers are exact rationals stored as strings `"p/q"`.

| File | What it is | Paper |
|---|---|---|
| `v7/scalar.json` | The scalar function: coefficients of `F` (degree 49) and `G`, with `f(x) = exp(-2|x|²) F(2|x|²)` | Section 3 |
| `v7/kernel.json` | The harmonic Gram kernel: radial breaks, degree-six Bernstein pieces, and the 19 blocks as integer rays with a common denominator | Section 3 |
| `v7/origin.json` | Origin coupling, pointed caps, tents and allocations, conditional rays and count polynomials, spherical energies and the base objective | Section 3 |
| `v7/graph_energies.json` | Weights of the graph energies | Table 2 |
| `census_floors.json` | Exact raw objective, the 124 group floors after the finite-count refinement (`profile`), and the refined bound 0.629526945573 | Sections 4 and 5 |
| `kernel-box/kbox_j1.json`, `kbox_j5.json` | The kernel-box subdivision trees proving `-K ≥ λ q` on `B₁` (λ = 3/10⁶, 286 leaves) and `B₅` (λ = 1/10⁶, 4663 leaves) | Section 6 |
| `kernel-box/ledger.json` | The final ledger: raised floor, binding groups and the bound | Section 6 |
| `D4Bound.lean` | Lean 4 formalization of the reduction from the certified inputs to the bound | Section 7 |
| `check_lean_inputs.py` | Checks that the rounded constants in `D4Bound.lean` bound the exact values in `census_floors.json` | Section 7 |

The `status` field in `v7/origin.json` is a historical label from the producer. The certificate was later verified in full: all 112 triangle cases, the pair pieces and the scalar signs.

## Lean

`D4Bound.lean` compiles against Mathlib v4.33.1 with no `sorry`. `#print axioms D4Bound.d4_density_bound` lists only `propext`, `Classical.choice` and `Quot.sound`. To check it, put the file in a Lake project that depends on Mathlib v4.33.1 and run `lake env lean D4Bound.lean`. It takes about two minutes.

The main theorem `D4Bound.d4_density_bound` proves the bound from these hypotheses:

1. `hpair`, `hgamma`: the pair and triangle signs of the reallocated kernel. These come from the interval and Bernstein checks of the base certificate.
2. `hraw`: `(f(0) + A)/8 ≤ urawUp`, from the base objective.
3. `hcensus`: for each anchor, its energy splits as `E + H`. `E` is at least the floor of one of the 124 census groups plus the broad-graph slack 3/10⁶. `H` is at least `λ_j max(Q_N, 0)`. The second part is `far_pair_sum_max`, proved in the file, applied with the certified kernel-box bound.
4. `transfer`: the passage from the finite inequality to density, by Poisson summation and periodization (Theorem 2.1 of the paper).

Proved in Lean, with no hypotheses beyond those listed:

- `finite_local_energy`: the finite local-energy inequality.
- `quartic_offdiag_ge`: the quartic sum over unit vectors in ℝ⁴ (Lemma 6.1).
- `cap_le`, `far_of_lt`, `far_pair_sum_max`: the geometry and summation of the far-pair lemma.
- `groups_ge`, `final_arith`: the minimum over all 124 groups and the final inequality.

## Check the Lean inputs

    python3 check_lean_inputs.py

It prints `PASS` and exits 0 when every Lean group floor is a lower rounding, and `urawUp` an upper rounding, of the exact values, each within 10⁻²⁴.

## Not included yet

The programs that verify the sign conditions of the base certificate and the count census are not in this folder. They are a 600 MB tree with a C++20 interval engine.
