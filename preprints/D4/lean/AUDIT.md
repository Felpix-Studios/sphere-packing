# Audit of the Lean proof

Audit of `data/D4Bound.lean` (the single-file export of 2026-11-12) against the paper and the old `data/README.md`, and what this folder changes. Date: 2026-11-13.

## Findings on the old file

1. **The main theorem said nothing about packings.** `d4_density_bound` concluded `density < 0.629521681653` for a free real variable `density`. The hypothesis `transfer` asserted, for that variable, that the finite inequality implies `density ≤ C/8`. So the theorem was "if some number is bounded by `C/8` whenever the finite inequality holds, it is below the bound". The Cohn-Elkies passage, the definition of density and the link to any packing were all inside an assumption. Fixed: `upperDensity` and `IsUnitPacking` are now definitions (`Density.lean`), and `transfer` is a proved theorem (`Transfer.lean`, by the lean-transfer agent).

2. **`f`, `K` and `A` were arbitrary.** `f` was not the certificate's function and `A` was not tied to `K(0,0)`. The hypotheses `hpair`, `hgamma`, `hraw` were therefore about unrelated objects. Fixed: `f` is defined from the 50 exact coefficients in `data/v7/scalar.json`, `A` is `K(0,0)`, and the sign and decay facts about `f` are proved.

3. **The far-pair lemma was not used.** `hcensus` asked for a split `energy = E + H` with `E ≥ floor + 3/10⁶` and `H ≥ λ_j max(Q_N, 0)`. Because `E` and `H` were existentially quantified, this is the same as assuming the full raised floor `energy ≥ floor + 3/10⁶ + λ_j max(Q_N, 0)` at every centre. `far_pair_sum_max` was proved but never applied, although the README and Section 7 of the paper said it was. Fixed: the allocation `H` is now defined from `K` as in Section 6, and `far_pair_nbhd` derives `∑ H ≥ λ_j max(Q_N, 0)` from the kernel-box hypothesis through `far_pair_sum_max`.

4. **The census groups were not tied to the counts.** The old `hcensus` only said that each anchor lies in some group of the list, with no condition linking `(N, j)` to the anchor. Any group would do, so the hypothesis did not say what the census checker checks. Fixed: `CensusFloor` requires the group with `N = #{x ∈ X : ‖x‖ ≤ R₅}` and `j` the least index with `#{x ∈ X : ‖x‖ ≤ R_j} = N`, with closed inequalities.

5. **The triangle sum of the reallocated kernel.** The old `hgamma` was stated for the reallocated kernel, and the paper says the triangle sum of `K' = K + H` is `Γ - Γ = 0` "since the three anchors share `-Γ` equally". For a single ordered triangle this needs `K(x,y) = K(y,x)`: the cyclic sums seen from the three vertices are equal only for a symmetric kernel. Lean now proves the weaker statement that is needed: the sum of `K'` over all ordered triples of a unit-separated family is exactly 0 (`tripleSum_Kalloc`). It uses only that `K(x,y) = 0` when `‖x‖ > 7/4` or `‖y‖ > 7/4`, not symmetry. Suggest the paper either note that `K` is symmetric or argue with the ordered triple sum.

6. **The scalar sign facts were outside Lean.** `G > 0` on `[0, ∞)`, `F < 0` on `[49/8, ∞)` and `G(0) = 1` were certified only by Sturm sequences in Python. They are now proved in Lean by exact kernel computation, independently of the Sturm check. Pólya's method does not work here: `G` and `F` have complex roots within angle `2·10⁻⁴` of the positive axis, so we used dyadic interval certificates instead.

7. **The Fourier identity.** The old file had no statement of it. It is now proved: `Fourier.lean` (by the lean-transfer agent) computes the transform of any polynomial in `2‖x‖²` times `e^{-2‖x‖²}`, and `Scalar.lean` matches it to `F` and `G` through the coefficient identity, which the kernel checks on the 50 exact coefficients.

## Checks that passed

- **Norms.** The old `sqn x = ∑ x_a²` and the condition `1 ≤ sqn x` match `‖x‖ ≥ 1`. The new files use the Euclidean norm on `EuclideanSpace ℝ (Fin 4)` throughout.
- **Ordered sums.** The anchored energy sums over ordered pairs `(x, y)`, including `x = y`, as in the paper's `E(X)`. Pair terms `2K(x,0) + K(x,x)` and the triple identity `3 · ∑_{ordered distinct} K = ∑_{ordered distinct} Γ` (`three_tripleSum`) match equation (2.1).
- **Graph slack.** The energy slack is `3/10⁶` and the density slack `3/8000000`: with `δ = 1/50000000`, `δ (1358 - 1208) = 3/10⁶`, divided by 8. Lean uses `C = 8 urawUp - aLow - 3/10⁶` and `C/8 = urawUp - aLow/8 - 3/8000000`.
- **Kernel-box multipliers.** `λ(1) = 3/10⁶` on `B₁` and `λ(j) = 1/10⁶` on `B₅` for `j ≥ 2`, as in Section 6. For `j ≥ 2` every near neighbour lies within `R₅`, so `B₅` applies.
- **`Q_N`.** `QN N = N(13561 N - 179244)/250000 = N²(1/8 - a²/4) - N(1 - a²)` with `a = 133/250` (`QN_formula`).
- **Ledger roundings.** `scripts/check_lean_inputs.py` confirms that the 124 Lean floors are lower roundings, and `urawUp` an upper rounding, of the exact values, each within `10⁻²⁴`. It fails, as it should, when one floor is raised by `10⁻²⁴` or when `lam` is changed (tested on a copy).
- **Fourier normalization.** Mathlib's `𝓕 g(ξ) = ∫ g(x) e^{-2πi⟨x,ξ⟩} dx` matches the paper. A 25-digit numerical Hankel transform agrees with `f̂(ξ) = (π²/4) e^{-s} G(s)` at `|ξ| = 0.1, 0.5, 1, 1.7`, and `∫ f = π²/4`. So the Fourier hypothesis is not false by a convention error.
- **Upper density.** `upperDensity` counts centres in balls about the origin. The bound holds for every packing, hence for every translate, so the choice of centre loses nothing.

## Possible vacuity

The hypotheses about `K` cannot be shown satisfiable inside Lean: a Lean witness would itself prove the bound. Each one is stated as the matching checker's claim, with closed inequalities and the paper's constants, and the Lean floors are weaker than the exact ones. Two hypotheses contain implicit claims that a reader should know about:

- `CensusFloor` asserts that every admissible neighbourhood falls in one of the 124 groups. This includes the count bounds `n ≤ (24, 24, 24, 25, 26)` and the two implications of Section 4, which the census proves.
- `SupportedIn` is a property of the kernel's construction (all radial pieces lie in `[1, 7/4]`), not a numerical check. Stage 1 confirms it.

## Questions sent to the stage owners

The exact statements of `SupportedIn`, `PairSign`, `CyclicSign`, `RawObjective` (stage 1), `CensusFloor` (stages 2 and 3), `GraphSlack` and `KernelBox` (stages 4 and 5) were sent to the agents who package those checkers. Their answers are summarized below.

- **Stage 1.** `SupportedIn`, `PairSign`, `CyclicSign` and `RawObjective` are as the checker states them. `K` is a genuine pointwise function of `(‖x‖, ‖y‖, ⟪x,y⟫)`, and it is symmetric. Components defined from neighbourhood quantities (counts, caps, graph edges, the pair gauge) are linear or quadratic in point sums, so each is a pointwise kernel with an origin constant, a linear term and a pair term. `K(0,0)` includes all graph origin charges. The stage 1 agent did not separately audit each capacity lemma.
- **Stages 2 and 3.** `CensusFloor` is right as stated: closed counts, `N = n₅`, `j` the least index with `n_j = N` (`N = 0` gives `j = 1`), and the floor bounds the energy of `K - Kg`. The census counts every other graph energy only as nonnegative. `X` need not lie inside radius `7/4`. Every admissible `X` falls in one of the 124 groups because of the caps `n ≤ (24, 24, 24, 25, 26)`.
- **Stage 4.** `GraphSlack` is right as stated. The proof uses only mutual separation and cites Schütte and van der Waerden.
- **Stage 5.** The checker proves `-K(r,s,t) ≥ λ_j t²(t² - a²)` for all `r, s ∈ [1, R_j]` and `t ∈ [-1, -a]`, closed, with no further condition. Since `K` is a function of `(r, s, t)`, this is `KernelBox`. At a break radius `r = R_k`, `K` uses the piece `[R_{k-1}, R_k]`, as the certificate does.

Since stage 1 says `K` is symmetric, the paper's per-triangle sentence in finding 5 holds for this `K`. The Lean proof does not need it.
