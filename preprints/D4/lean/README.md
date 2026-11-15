# Lean proof of the four-dimensional bound

This Lake project proves in Lean that every packing of unit-separated centres in four dimensions has upper density below 0.629521681653. The concrete theorem `d4_density_bound_concrete` takes only a packing and its `IsUnitPacking` proof. All fourteen original premises are discharged inside Lean.

The proof has no `sorry` and no added `axiom` declaration. It depends on `propext`, `Classical.choice`, `Quot.sound` and 125 `native_decide` axioms, one per finite certificate check run as compiled code. Those 125 checks add trust in the Lean compiler and in six precompiled checker libraries built from the Lean sources here.

This Lean proof is separate from the non-Lean computer-assisted proof in `../verify`. Neither one uses code, inputs or results of the other.

## Validation status

Clean build on 2026-11-15: `python3 verify/verify_lean.py --workers 4 --require-unconditional` passed. It compiled all 575 modules from a frozen copy of the sources in 13151 s of wall time, audited the axioms of 12900 theorems, and checked that the concrete theorem takes only the packing. [verify/recorded/lean.json](verify/recorded/lean.json) is the result file, with the hashes of the six checker libraries.

## Build

You need [elan](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain` (Lean 4 v4.33.1) and Mathlib in `lake-manifest.json` (v4.33.1, commit `0df444a360eaa60ab8c11dca51a86af692955474`).

```
cd lean
lake exe cache get      # download the compiled Mathlib
lake build              # build this project
lake env lean Check.lean
```

`Check.lean` prints the complete concrete theorem type, reports the axioms of the main theorems, and audits every imported publication theorem. There is no `sorry` and no added `axiom` declaration. Finite certificate checks may use `native_decide` (allowed since 2026-11-14), which adds Lean compiler trust; every other reported axiom must belong to `{propext, Classical.choice, Quot.sound}`, and the audit counts the native axioms separately. An allowed axiom list does not discharge explicit theorem premises.

The recommended clean build entry point, from this folder, is:

```sh
python3 verify/verify_lean.py --out /tmp/d4-lean-check --workers 4 --require-unconditional
```

This build is separate from the non-Lean computer-assisted proof in `../verify`: it reads nothing outside this folder and shares no code, input or result with those checkers. It freezes the Lean sources, then compiles every source in dependency order, including sources the umbrella module does not import, with up to `--workers` Lean processes at once (default 2, about 3.5 GB each). The executable certificate checkers are compiled to shared libraries and loaded into the modules that run them with `native_decide`. The build rejects a `sorry` warning, stale project artifacts, changes to publication sources during compilation, missing axiom reports and axioms outside the allowed set. It does not update dependencies. Mathlib's prebuilt dependency cache is reused, but the publication modules are compiled from the included source. `--require-unconditional` also checks that the concrete density theorem takes only a packing and its `IsUnitPacking` proof. [LEAN_STAGING.md](verify/LEAN_STAGING.md) describes the build, its options and what `native_decide` adds to the trust base; 

With `--check-generators` the verifier also runs every generator listed in `verify/verify_lean.py` in check mode. That compares the Lean data modules with the certificate files of the D4 package; it is a provenance check and the Lean proof does not depend on it. Two foundational checks can also be run directly from this folder:

```
python3 scripts/check_lean_inputs.py   # ledger floors and urawUp are outward roundings of data/census_floors.json
python3 scripts/gen_scalar.py --check  # ScalarData.lean and ScalarCert.lean are generated from data/v7/scalar.json
```

Both print `PASS` and exit 0.

## The concrete theorem

[`ConcreteMain.lean`](D4Bound/ConcreteMain.lean) specializes the generic theorem to `V7.kernel`:

```lean
theorem d4_density_bound_concrete
    (P : Set E4) (hP : IsUnitPacking P) :
    upperDensity P < ENNReal.ofReal (629521681653 / 1000000000000)
```

`E4` is `EuclideanSpace ℝ (Fin 4)`. `IsUnitPacking P` means distinct centres have distance at least 1, corresponding to balls of radius 1/2. `upperDensity` is the limit superior of the normalized centre count in growing balls. The scalar is `f(x) = exp(-2‖x‖²) F(2‖x‖²)`, with the exact degree-49 polynomial from `data/v7/scalar.json`.

The generic `d4_density_bound` accepts an arbitrary kernel with its premises. The concrete specialization supplies every one of them for `V7.kernel`. Both versions internally supply the two latitude proofs and the graph proof.

## Discharged premises

| Original premise | Lean proof |
|---|---|
| `v7_support` | `V7.kernel_supported`, from the concrete definition |
| `v7_pair` | `V7.kernel_pair`, exact gauge cancellation and scalar tail sign |
| `v7_raw` | `V7.kernel_raw`, rational objective comparison in the Lean kernel |
| `latitude_15`, `latitude_24` | `LatitudeCheck.latitude15/24`, full bivariate Bernstein trees and polynomial identities |
| `annular_151` | `annular_151_proved`, degree-20 polynomial, full interval sign and cardinality argument |
| `v7_cyclic` | `V7.cyclicSign_kernel` (`V7CyclicSignNative.lean`): Bernstein subdivision checker with proved soundness, run on 84 full and 28 outside cases; 117 native axioms |
| `census` | `V7.censusFloor_kernel` (`V7CensusNative.lean`): three degree-16 surplus sign trees; 3 native axioms |
| `kernel_box_1`, `kernel_box_5` | `KBN.kernel_box_1_native`, `KBN.kernel_box_5_native`: interval checker with proved soundness on both box trees; 4 native axioms, two of them shared with the cyclic sign |
| `code_24`, `code_25`, `code_26` | `SphericalConcrete.C24/C25/C26.code_bound_unconditional`: exact sign trees for the three Delsarte certificates; 3 native axioms |
| `svdw` (replaced) | Replaced by `projected_eight_proved` at the actual cutoff `223/735`; `GraphSlackExact.lean` proves the geometric transfer |

Weighted Schoenberg positivity on both S³ and S² is now proved for every degree. The graph needs only the weaker code bound `A(3,223/735) ≤ 8`, proved by an exact Legendre certificate. The full classical Schütte–van der Waerden theorem at cutoff `1/3` is not claimed to be formalized and is no longer a premise of this density theorem.

## Statements of the original premises

Each row is now a theorem; the table above names its proof.

Notation: `E_K(X) = K(0,0) + 2 ∑_{x∈X} K(x,0) + ∑_{x,y∈X} K(x,y)`. A neighbourhood `X` is admissible if it is finite, `‖x‖ ≥ 1` on `X` and `‖x - y‖ ≥ 1` for distinct `x, y ∈ X`. Radii `R₁ = 501473/500000`, `R₂ = 1005643/1000000`, `R₃ = 50379/50000`, `R₄ = 50767/50000`, `R₅ = 102597/100000`; `n_j = #{x ∈ X : ‖x‖ ≤ R_j}`.

| Hypothesis | Lean definition | Statement |
|---|---|---|
| `v7_support` | `SupportedIn K` (`Allocation.lean`) | `K(x,y) = 0` if `‖x‖ > 7/4` or `‖y‖ > 7/4` |
| `v7_pair` | `PairSign K` (`Main.lean`) | `f(x) + 2K(x,0) + K(x,x) ≤ 0` for `‖x‖ ≥ 1` |
| `v7_cyclic` | `CyclicSign K` (`Allocation.lean`) | `K(x,y) + K(-x,y-x) + K(-y,x-y) ≤ 0` when `‖x‖, ‖y‖, ‖x-y‖ ≥ 1` |
| `v7_raw` | `RawObjective K` (`Main.lean`) | `f(0) + K(0,0) ≤ 8 · urawUp` |
| `census` | `CensusFloor K` (`Main.lean`) | For every admissible `X` whose count vector lies in the count domain (`InCountDomain`, below) and every ledger group `(N, j, floor)` with `N = n₅` and `j` the least index with `n_j = N`: `floor ≤ E_{K - Kg}(X)` |
| `kernel_box_1`, `kernel_box_5` | `KernelBox K R λ` (`Allocation.lean`) | `-K(y,z) ≥ λ (t⁴ - a²t²)` for `1 ≤ ‖y‖, ‖z‖ ≤ R` and `t = ⟪y,z⟫/(‖y‖‖z‖) ≤ -a`, `a = 133/250`; `(R, λ) = (R₁, 3/10⁶)` and `(R₅, 1/10⁶)` |
| `code_24`, `code_25`, `code_26` | `SphericalCodeBound s m` (`Geometry.lean`) | Every finite set of unit vectors in `ℝ⁴` with pairwise inner products at most `s` has at most `m` elements; `(s, m) = (203/400, 24)`, `(103/200, 25)`, `(21/40, 26)` |
| `latitude_15`, `latitude_24` | `LatitudeCert r R` (`CountDomain.lean`) | With `S = 203/400`, `s = 1 - 1/(2r²)`, `c = (r² + R² - 1)/(2rR)`, `β = max(0, (c - S)/(1 + c))`: for all `a, b ∈ [-1, c]` with `D = 1 - s² + 2sab - a² - b² ≥ 0`, one of `P ≥ 0 ∧ V ≤ 0`, `P ≥ 0 ∧ H ≥ 0`, `V ≤ 0 ∧ H ≤ 0` holds (`P`, `V`, `H` as in `latP`, `latH`); `(r, R) = (R₁, R₅)` and `(R₂, R₄)` |
| `annular_151` | `SphericalCodeBound (41/49) 151` (`Geometry.lean`) | At most 151 unit vectors in `ℝ⁴` with pairwise inner products at most `41/49` |
| `svdw` (replaced) | `SchutteVanDerWaerden` (`GraphSlack.lean`) | Among any nine unit vectors in `ℝ³` there are two with inner product at least `1/3` |

The count domain `InCountDomain X` (`CountDomain.lean`) is the set `C` of the census: `n₁ ≤ … ≤ n₅`, `n ≤ (24, 24, 24, 25, 26)`, `(23 - n₁)(n₅ - n₁) ≥ 0` and `(23 - n₂)(n₄ - n₂) ≥ 0`. Each group floor is a lower bound over the vectors of `C` in that group. Given the three spherical-code bounds and the proved latitude certificates, Lean proves that every admissible `X` lies in `C` (`countDomain_of_admissible`). It also proves that each vector in `C` belongs to one of the 124 groups (`group_mem`).

The former hypothesis `graph_slack` is now the unconditional theorem `graphSlack_proved`: at most 1208 ordered broad-graph edges. Its annular and projected code bounds are proved within Lean.

`Kg` is the broad graph energy written as a kernel (`Neighbourhood.lean`): `Kg(0,0) = 1358/50000000`, `Kg(y,z) = -1/50000000` on the edges of the broad graph (pairs with `33/28 ≤ ‖y‖, ‖z‖ ≤ 7/4` and `⟪y,z⟫ ≤ -(7/8)‖y‖‖z‖`), `0` elsewhere. The census floors treat this graph energy only as nonnegative, which is why `census` is stated for `K - Kg`.

The census floors and the kernel-box bound use closed inequalities. The Lean ledger floors are lower roundings of the exact floors.

## Formal theorem inventory

| File | Content |
|---|---|
| `LocalEnergy.lean` | The finite local-energy inequality `∑_{i,j} f(p_j - p_i) ≤ n (f(0) + A - β)` (`finite_local_energy`, `finite_local_energy_of_tripleSum`) |
| `Spherical.lean` | `∑_{i≠k} (t⁴ - a²t²) ≥ (1/8 - a²/4) n² - (1 - a²) n` for unit vectors in ℝ⁴ (`quartic_offdiag_ge`, Lemma 6.1) |
| `FarPair.lean` | Lemma 6.2 and the summation of Proposition 6.3 on unit vectors (`far_pair_sum_max`) |
| `Neighbourhood.lean` | Neighbourhoods, counts `n_j`, groups `(N, j)`, the broad graph kernel `Kg` and `E_Kg(X) ≥ 3/10⁶` from 1208 edges; the energy of a centre equals the energy of its neighbourhood |
| `Geometry.lean` | The shell-to-sphere transfer `⟪x,y⟫ ≤ (1 - 1/(2R²))‖x‖‖y‖` for `1 ≤ ‖x‖, ‖y‖ ≤ R`, `R² ≤ 2`, `‖x - y‖ ≥ 1` (`shell_inner_le`), its two-radius form (`two_shell_inner_le`), the annulus bound `41/49` (`annulus_inner_le`), and `card_le_of_cos_le` (directions of a set with cosines at most `ρ < 1` are distinct) |
| `GraphSlack.lean` | Lemma 5.1: at most 151 broad-graph vertices, degree at most 8 by projecting the neighbours of a vertex to the orthogonal complement of its direction (pairwise inner products below `1/3`, `proj_scalar`), so at most 1208 ordered edges (`broadEdges_le`) |
| `CountDomain.lean` | Lemma 4.1: the caps `n₃ ≤ 24`, `n₄ ≤ 25`, `n₅ ≤ 26`, monotonicity, and the two implications by the affine latitude map, including the meridian reduction of `AFFINE_LATITUDE_THEOREM.md` section 3 (`lat_key`, `latitude_count`); `countDomain_of_admissible`; the 124 group keys are distinct and cover every group allowed by the caps (`groupKeys_nodup`, `groupKeys_complete`, `group_mem`) |
| `Allocation.lean` | The allocation `H = -Γ/k` of Section 6; the triple sum of `K + H` over any unit-separated family is exactly 0 (`tripleSum_Kalloc`); Proposition 6.3 on a neighbourhood, from the kernel-box bound (`far_pair_nbhd`) |
| `Ledger.lean` | The 124 group floors, `groups_ge` (each raised floor is at least `aLow`) and `final_arith` |
| `ScalarData.lean`, `ScalarCheck.lean`, `ScalarCert.lean` | `F`, `G` as exact rationals, and kernel-checked interval certificates (`decide +kernel` on integer Taylor shifts over 221 dyadic intervals plus two tails) |
| `Fourier.lean` | For any real polynomial, the Fourier transform of `e^{-2‖x‖²} ∑ c_k (2‖x‖²)^k` on ℝ⁴ (`fourier_polyGauss`), by differentiating the Gaussian transform in its parameter |
| `Scalar.lean` | The coefficient identity `G_j = ∑_{k≥j} F_k (-1)^j k!/j! C(k+1,k-j)` (`coeff_identity`), `𝓕 f = f̂` with `f̂(ξ) = (π²/4) e^{-s} G(s)` (`fourierIdentity`), `G(0) = 1`, `G(s) > 0` for `s ≥ 0`, `F(t) < 0` for `t ≥ 49/8`, `f ≤ 0` for `‖x‖ ≥ 7/4`, `f` continuous and integrable, `f̂` integrable and positive, `∫ f = π²/4` |
| `Density.lean`, `Transfer.lean` | Unit packings, upper density, and the transfer from the finite inequality to density (`transfer`, `transfer_quarter`), by Fourier inversion and positive definiteness, without Poisson summation |
| `Main.lean`, `ConcreteMain.lean` | `energy_floor`, `d4_patch_bound`, the generic `d4_density_bound`, and its concrete specialization with no premises beyond the packing |

The proof of `d4_patch_bound` follows the paper. Put `K' = K + H`. Pair terms of `K'` equal those of `K` (`H(x,0) = H(x,x) = 0`). The triple sum of `K'` vanishes. At each centre, `E_{K'} = E_{K-Kg} + E_{Kg} + ∑ H ≥ floor + 3/10⁶ + λ_j max(Q_N, 0) ≥ aLow + 3/10⁶`. The finite inequality then gives `∑ f(p_j - p_i) ≤ n (8 urawUp - aLow - 3/10⁶)`, and `transfer_quarter` turns this into upper density at most `urawUp - aLow/8 - 3/8000000 < 0.629521681653`.

## Recovered component proofs

The main project also imports `ComponentsCapacity.lean` and its dependencies:

| File | Proved content |
|---|---|
| `SchoenbergS3.lean` | Weighted positive definiteness of `U_l(t)/(l+1)` on S³, for every degree, via a polynomial Fischer inner product |
| `ComponentsGram.lean` | Nonnegative harmonic Gram energies and the origin-credit square identity |
| `ComponentsGauge.lean` | Capacity-minus-usage and pair-count gauge identities and positivity |
| `ComponentsCapacity.lean` | Ball-count and translated tent inequalities, the P-star capacity and the two-level step capacity, and their allocation energies |
| `SupportRestriction.lean` | Restriction to the closed kernel support preserves energy, admissibility, all census counts and the group key |
| `V7Conditional.lean` | The two actual conditional count-ray energies equal the weighted count products and are nonnegative on the count domain |
| `V7Allocations.lean`, `V7Tents.lean` | The actual two antipodal allocations and four pointed tents equal their capacity-minus-usage formulas and have nonnegative energy |
| `ComponentsObtuse.lean`, `ComponentsBall.lean` | Strictly negative pairwise inner products imply affine independence; a closed ball of squared radius less than `1/2` contains at most five unit-separated points in ℝ⁴ |

[ENERGY_COMPONENTS.md](ENERGY_COMPONENTS.md) states exact theorem scopes. `V7Kernel.lean` defines the concrete kernel, and `SchoenbergS2.lean` proves the transverse Legendre positivity.

## Files

- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`: the project.
- `D4Bound.lean`: imports the integrated theorem modules; the full verifier also discovers and compiles every other publication source.
- `Check.lean`: main theorem type and axiom reports, plus the audit of all imported publication theorems.
- `scripts/gen_scalar.py`: writes `ScalarData.lean` and `ScalarCert.lean` from `data/v7/scalar.json`; `--check` compares.
- `scripts/check_lean_inputs.py`: checks the ledger constants against `data/census_floors.json`.
- `AUDIT.md`: what changed from the earlier single-file version and why.
- `HYPOTHESIS_AUDIT.md`: historical audits of earlier snapshots, when the theorem still had premises. It compares those premises with the non-Lean checkers and is not evidence for the Lean proof.
