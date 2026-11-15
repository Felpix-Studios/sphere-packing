# Hypothesis audit of `D4Bound.d4_density_bound`

**Historical record, superseded on 2026-11-15.** `d4_density_bound_concrete` now has no premises beyond the packing; see [README.md](README.md). The audits below describe earlier snapshots, when the theorem had eight, fourteen and then seven premises, and compare those premises with the non-Lean checkers. The Lean proof does not depend on anything in this file.

Auditor: lean-transfer agent, 2026-11-13. This is a read-only audit of `lean/` against the stage
checkers in `../verify/`. I changed no Lean file. This is the only file I wrote here.

## Result

I found **no MISMATCH**. Every hypothesis of `d4_density_bound` is implied by what the stage
checkers certify, for one concrete kernel `K`: the symmetric polarization of the complete raw V7
energy. Two are weaker than what is certified, and the others match exactly. The hypotheses are
jointly satisfiable, so the theorem is not vacuous. The three stage agents confirmed every
reading that depended on checker semantics (section 7). No verdict is pending.

| # | Lean hypothesis | Certified by | Verdict |
|---|---|---|---|
| 1 | `v7_support : SupportedIn K` | stage 1 (V7 kernel defined on radii `[1, 7/4]`) | OK |
| 2 | `v7_pair : PairSign K` | stage 1 item 5 + gauge row 15 | WEAKER (the lifted pair is exactly `0` on `[1, 7/4]`) |
| 3 | `v7_cyclic : CyclicSign K` | stage 1 item 6 | OK (confirmed by stage1-v7) |
| 4 | `v7_raw : RawObjective K` | stage 1 item 7; `check_lean_inputs.py` | WEAKER (`urawUp` rounded up) |
| 5 | `census : CensusFloor K` | stages 2 and 3; `check_lean_inputs.py` | OK (confirmed by stage23-origin; floors rounded down, so WEAKER in the constants) |
| 6 | `graph_slack : GraphSlack` | stage 4 | OK (confirmed by stage45-kernelbox; rests on the cited Schütte–van der Waerden theorem) |
| 7 | `kernel_box_1 : KernelBox K R1 (3/10⁶)` | stage 5 gate 4 (`kbox_j1.json`) | OK (confirmed by stage45-kernelbox) |
| 8 | `kernel_box_5 : KernelBox K R5 (1/10⁶)` | stage 5 gate 4 (`kbox_j5.json`) | OK (confirmed by stage45-kernelbox) |
| 9 | `IsUnitPacking`, `upperDensity` | definitions | OK (standard; see section 4) |
| 10 | non-vacuity | section 3 | OK |

I also rebuilt the whole package myself in a separate build directory (`lake build D4Bound`,
2810 jobs, success). `Check.lean` prints `[propext, Classical.choice, Quot.sound]` for all 22
listed theorems. `grep` finds no `sorry`, `admit`, `native_decide` or `axiom` in `D4Bound/`.
`python3 scripts/check_lean_inputs.py` prints `PASS: 124 groups, floors rounded down and urawUp
rounded up by less than 10^-24; radii, lam and QN as in the paper`.

## 1. The kernel `K` that satisfies every hypothesis

The Lean `K : E4 → E4 → ℝ` is a free variable. All hypotheses must hold for one function. Take
`K` from the complete raw V7 energy `E(X)`, as written out in
`verify/stage5_kernelbox/src/raw_v7.py` (`evaluate`, lines 214-247):

* `K(0,0) = A`, where `A = 8 U_raw - F(0)` (raw_v7.py:48). This is the full origin constant,
  with all four graph charges (COMPONENTS.md, "The objective uses these constants").
* For `x, y ≠ 0`, `K(x,y)` is the symmetric cross term. Each component's energy is a quadratic
  form in the star: Gram blocks, count polynomials, caps, tents, allocations, spherical rays,
  conditional rays, graphs, and the gauge `(Σ w)(1 - Σ ψ)`. The gauge's off-diagonal kernel is
  symmetrized, `-(w(r)ψ(s) + w(s)ψ(r))/2`
  (`verify/stage1_v7/record/current/base/new_work/pointed/full_pair_count_gauge.py:10`). The
  same symmetrized formula is in stage 5 (`proofs/kernel_box_method.md:25`).
* `K(x,0) = h(x)` (the linear term) and `K(x,x)` is the diagonal. Only `2h(x) + K(x,x) =
  E({x}) - A` enters any hypothesis.
* `K(0,y) = 0` for `y ≠ 0`, and `K = 0` whenever an argument has norm `> 7/4`. The evaluator
  drops every point with `|v|² > 49/16` from the energy (raw_v7.py:218, 228), and the support of
  every component is `[1, 7/4]` (allocations: `"support": ["1", "7/4"]` in `data/v7/origin.json`).

The anchored energy `E(X) = A + 2 Σ h + Σ_{x,y ∈ X} k`, with the diagonal included (raw_v7.py:118,
"ordered multiplicity, including diagonal pairs"), is exactly `nbhdEnergy K X`
(Neighbourhood.lean:51-52).

## 2. Each hypothesis

### 2.1 `SupportedIn` (Allocation.lean:49-50)

```lean
def SupportedIn (K : E4 → E4 → ℝ) : Prop :=
  ∀ x y : E4, (7 / 4 < ‖x‖ ∨ 7 / 4 < ‖y‖) → K x y = 0
```

Certified: stage 1 README, "`K` is the V7 kernel, supported on radii in `[1, 7/4]`". The stage 5
evaluator gives no energy to points with `|v| > 7/4` (raw_v7.py:218, 228). The support is
**closed**: the kernel may be nonzero at `|x| = 7/4`, and Lean only asks for zero at `> 7/4`.
This holds by construction, not by a checked inequality. Note that the antipodal allocations sum
only over active points (`hist` is built from `active`, raw_v7.py:228-230). So `Cap(x + y)` with
`|x| > 7/4` contributes nothing, and the support claim also holds for that component. **OK.**

### 2.2 `PairSign` (Main.lean:39-40)

```lean
def PairSign (K : E4 → E4 → ℝ) : Prop :=
  ∀ x : E4, 1 ≤ ‖x‖ → f x + 2 * K x 0 + K x x ≤ 0
```

Certified: stage 1 item 5. The unlifted pair `q = f + 2h + k(x,x) ≤ 0` holds on each of the 7
closed pieces of `[1, 7/4]`, and `f < 0` for `|x| ≥ 7/4` (scalar signs, Lean `f_nonpos` too). The
gauge is then attached with pair contribution `w(1-ψ) = -q`, so the full lifted pair is
**identically 0** on `[1, 7/4]` (`full_pair_count_gauge.py:9-11`, COMPONENTS.md row 15). For
`|x| > 7/4` the pair is `f(x) < 0`. At `|x| = 7/4` it is `0 + 0 ≤ 0`. The scalar is the same
function: `scalar.json` has `alpha = 2`, and Lean `f x = exp(-2‖x‖²) F(2‖x‖²)` with `F` generated
from `scalar.json`. The diagonal convention is the same (`pair_convention` in `origin.json`:
`f+2*pair_origin_v*b+PSD_diagonal-...`). **WEAKER** (Lean asks `≤ 0`, certified `= 0` on the
support, `< 0` outside).

### 2.3 `CyclicSign` (Allocation.lean:36, 53-54)

```lean
def cyc (K : E4 → E4 → ℝ) (x y : E4) : ℝ := K x y + K (-x) (y - x) + K (-y) (x - y)
def CyclicSign (K : E4 → E4 → ℝ) : Prop :=
  ∀ x y : E4, 1 ≤ ‖x‖ → 1 ≤ ‖y‖ → 1 ≤ ‖x - y‖ → cyc K x y ≤ 0
```

Certified: stage 1 item 6, `Γ(x,y) ≤ 0` for all `x, y` with `|x|, |y|, |x-y| ≥ 1`.

* For symmetric `K` that depends only on norms and the inner product, `cyc` is the sum over the
  three vertices of the triangle `{0, x, y}` of `K` at the two adjacent sides. So it is a function
  of the three side lengths only, which is what the 84 interior cases and 28 exterior cases cover.
* If two or more sides exceed `7/4`, every term vanishes by support. If one side exceeds `7/4`,
  one term survives. That is the exterior case.
* The gauge correction in the triangle checks is the symmetrized kernel summed over the three
  side pairs (`kind='full'`) or the one surviving pair (`kind='outside'`)
  (`full_pair_count_gauge.py:129-145`). So the non-symmetric gauge causes no orientation gap.
* Tolerance: the acceptance test is "every upper Bernstein coefficient of `P - η_b` is at most the
  positive factor times a lower bound for the nonnegative corrections". `η_b` is the exact
  count-term constant of the case (README item 6). So the certified sign is `Γ ≤ 0` exactly,
  with no positive slack. The `η = 10⁻⁶`, `ε` repairs belong to the *spherical certificates*
  (`spherical_sdp/THEOREM.md`, "Uniform repair"). They enter only the proof that the spherical
  component energy is nonnegative and the stage 2/3 surplus. They do not leave slack in the V7
  `Γ`.

**OK.** Confirmed by stage1-v7 (section 7).

### 2.4 `RawObjective` (Main.lean:43-44)

```lean
def RawObjective (K : E4 → E4 → ℝ) : Prop :=
  f 0 + K 0 0 ≤ 8 * (urawUp : ℝ)
```

Certified: `U_raw = (F(0) + A)/8` (stage 1 item 7). `A = K(0,0)` is the same constant the
checkers use: raw_v7.py:48 defines `A = 8 U_raw - F(0)`, and stage 4 rechecks that `U_raw`
includes the graph charge `4769/25000000` (stage 4 README, "What it checks" 3). Lean `f 0 = F 0`
(`f_zero`). `check_lean_inputs.py` checks `U_raw ≤ urawUp < U_raw + 10⁻²⁴`. **WEAKER.**

### 2.5 `CensusFloor` (Main.lean:48-50) with `Kg` (Neighbourhood.lean:71-83)

```lean
def CensusFloor (K : E4 → E4 → ℝ) : Prop :=
  ∀ X : Finset E4, Admissible X → ∃ g ∈ groups, g.1 = nearCount X ∧ g.2.1 = firstRadius X ∧
    (g.2.2 : ℝ) ≤ nbhdEnergy (fun x y => K x y - Kg x y) X

def broadEdge (x y : E4) : Prop :=
  33 / 28 ≤ ‖x‖ ∧ ‖x‖ ≤ 7 / 4 ∧ 33 / 28 ≤ ‖y‖ ∧ ‖y‖ ≤ 7 / 4 ∧ ⟪x, y⟫ ≤ -(7 / 8) * (‖x‖ * ‖y‖)
noncomputable def Kg (x y : E4) : ℝ :=
  if x = 0 ∧ y = 0 then 1358 / 50000000 else if broadEdge x y then -(1 / 50000000) else 0
```

Certified: stage 2 item 2 and stage 3 item 1, `E(X) ≥ new_floor(N, j)` for every admissible `X`
in group `(N, j)`.

* **Which kernel.** The floor is `max(Q, L_1..L_12)` (degree-zero Gram) plus the three count
  energies plus the spherical surplus. "Every other original local energy remains nonnegative
  and unchanged" (stage2 `PROOF.md:117`) and is dropped. That includes the broad graph E9.
  Stage 4 README:10 says "The census floors use only that it is at least 0". `grep` finds no
  graph term in the stage 2/3 code apart from the constant `graph_saving` (stage3 `run.py:184`).
  So the floor bounds `E_full(X) - E_E9(X)`. That is `nbhdEnergy (K - Kg) X` exactly when `Kg` is
  E9's kernel.
* **`Kg` equals E9.** raw_v7.py:97-112 (`graph_energy`, row `broad_antipodal`): weight
  `graphs["weights"][2] = 1/50000000`, capacity 1358, closed radii `33/28 ≤ |x|, |y| ≤ 7/4`,
  `h < 0` and `h² ≥ 4mn (7/8)²` (that is `⟪x,y⟫ ≤ -(7/8)|x||y|`), ordered pairs. Energy
  `δ(1358 - e)`. COMPONENTS.md row 11 gives the same data. Lean's `Kg` has origin value `1358δ`,
  `Kg(x,0) = 0` (Neighbourhood.lean:85, `not_broadEdge_zero`), `-δ` per ordered edge and no
  diagonal edge. Lean `nbhdEnergy_Kg` proves `E_Kg = δ(1358 - e)`. **Identical.**
* **No double counting.** `energy_floor` (Main.lean:79-110) adds three separate terms:
  `E_{K-Kg} ≥ floor` (census, no graph or allocation term in it), `E_Kg ≥ 3/10⁶` (graph slack,
  E9 only), and `Σ H ≥ λ max(Q_N, 0)` (far-pair lemma, the allocation `H` is not part of V7 and
  not in the census). E9 is counted once, at `δ(1358 - e) ≥ 150δ`. The other three graphs (120,
  604, 1880) stay inside `K - Kg` and are dropped by the census as `≥ 0`. This matches the stage 5
  ledger `U_new = U_raw - a_new/8 - 3/8000000`.
* **Group definition.** Counts are closed, `n_i = #{|x| ≤ R_i}` (stage 2 README; stage2
  `PROOF.md:36-38`, "the first radial piece includes its left endpoint; later pieces are open on
  the left and closed on the right"). `N = n_5` and `j` is the least index with `n_j = N`. Lean:
  `countWithin` (`‖x‖ ≤ r`), `nearCount`, `firstRadius` (Neighbourhood.lean:56-67). Same radii
  (`check_lean_inputs.py` checks R1..R5). **Identical.**
* **Coverage of all 124 groups.** Every admissible `X` has `n(X) ∈ C`. C is defined by the caps
  `(24,24,24,25,26)` from three certified spherical codes and the two affine-latitude
  implications (stage 2 item 1). Realizability is not assumed, so C is a superset. Its groups are
  exactly 124: `N = 0` (j = 1), `N = 1..24` (j = 1..5), `N = 25` (j = 4, 5), `N = 26` (j = 5).
  `census_floors.json` and the Lean list have the same 124 keys (`check_lean_inputs.py`). An
  admissible `X` with `N ≥ 27` or `(25, j ≤ 3)` cannot exist, by the certified spherical caps. So
  the `∃ g ∈ groups` clause never fails for a real neighbourhood. `X = ∅` is group `(0, 1)`
  (stage2 `PROOF.md:116`, "N=0 is included").
* **Admissible.** Lean (Neighbourhood.lean:47-48): `‖x‖ ≥ 1` and pairwise `≥ 1`, finite. Stage 2:
  "a finite subset of `R^4 \ {0}` and `X ∪ {0}` is unit separated". Identical. Points with
  `|x| > 7/4` are allowed in both and carry no energy.
* Floors are `new_floor` rounded down by less than `10⁻²⁴` (`check_lean_inputs.py`).

**OK** (WEAKER in the rounded constants). Confirmed by stage23-origin (section 7).

### 2.6 `GraphSlack` (Main.lean:53-54)

```lean
def GraphSlack : Prop :=
  ∀ X : Finset E4, Admissible X → broadEdges X ≤ 1208
```

Certified: stage 4, `e ≤ 1208` for every centre of any unit-separated packing, with vertices at
distance in `[33/28, 7/4]`, cosine in `[-1, -7/8]`, "Both intervals are closed", ordered edges
(stage 4 README:7). There is no assumption on the group or the counts. The proof is at most 151
vertices (exact polynomial certificate, rerun) times degree at most 8. The degree bound is
**CITED**: Schütte and van der Waerden, `φ_3(9) = arccos(1/3)`, not opened by the project; the
statement was read in Barg–Musin. The admissible-neighbourhood form is the same as "neighbours of
a centre". **OK**, with that cited dependency.

### 2.7 `KernelBox` (Allocation.lean:59-62)

```lean
def KernelBox (K : E4 → E4 → ℝ) (R lam : ℝ) : Prop :=
  ∀ y z : E4, 1 ≤ ‖y‖ → ‖y‖ ≤ R → 1 ≤ ‖z‖ → ‖z‖ ≤ R →
    ⟪y, z⟫ ≤ -(133 / 250) * (‖y‖ * ‖z‖) →
    lam * ((⟪y, z⟫ / (‖y‖ * ‖z‖)) ^ 4 - (133 / 250) ^ 2 * (⟪y, z⟫ / (‖y‖ * ‖z‖)) ^ 2) ≤ -K y z
```

Certified: stage 5 item 1, `-K(y,z) ≥ λ_j q(t)` on `B_j = {|y|, |z| ∈ [1, R_j], t ∈ [-1, -a]}`,
with `a = 133/250` and `q(t) = t²(t² - a²) = t⁴ - a² t²`. That is Lean's polynomial, closed on all
sides.

* **Same `K`.** `K` is "the raw V7 pair kernel, the polarization of `src/raw_v7.py`"
  (`kernel_box_method.md` section 1). Section 2 lists all components: Gram, spherical rays, count
  and conditional polynomials, the symmetrized gauge, and `Pos` (caps, tents, allocations,
  graphs, with nonnegative coefficients in `-K`). It is the same symmetric polarization as in
  section 1 here.
* **Breaks.** Closed-inner convention, with the face `r = R_k` in region `k-1`
  (`kernel_box_method.md:53`). This matches raw_v7 `features` (raw_v7.py:61) and the closed counts.
  The `B_1` face `r = R_1` lies in region 0, which is inside `B_1`.
* **Kinks.** Undecided kinks are replaced by lower bounds of terms that enter `-K` with
  nonnegative coefficients (section 3), so the replacement lowers `-K`. Sound.
* Use in Lean: `R1` with `3/10⁶` when `firstRadius X = 1`, `R5` with `1/10⁶` otherwise
  (Main.lean:98-105). This matches `lam` (Ledger.lean:147) and stage 5 item 2.

**OK.** Confirmed by stage45-kernelbox (section 7).

## 3. Non-vacuity

The hypotheses mention `K` only through `K(0,0)`, `K(x,0)` with `‖x‖ ≥ 1`, and `K(x,y)` with
`‖x‖, ‖y‖ ≥ 1` (plus the support condition, which also forces `K(0,y) = 0` for `‖y‖ > 7/4`). The
kernel of section 1 satisfies:

* 2.1 by construction;
* 2.2 because the certified lifted pair is `0`, and `f < 0` outside;
* 2.3 because of the stage 1 cyclic sign;
* 2.4 with equality before rounding;
* 2.5 by the census;
* 2.7 by stage 5.

`GraphSlack` does not mention `K` and holds by stage 4. So the hypotheses are jointly
satisfiable, given the stage certificates and their written lemmas, and the theorem is not
vacuous. No hypothesis is stronger than what is certified.

Two places where a careless formalization could have been vacuous are fine:

* `CensusFloor` demands a group for *every* admissible `X`. This is true because the 124 groups
  cover the certified count domain C.
* `SupportedIn` would fail if any component reached beyond `7/4`, for example the antipodal
  allocation `Cap(x+y)`. It does not, because raw_v7 sums only over points with `|x| ≤ 7/4`.

## 4. Definitions in the statement

* `IsUnitPacking P := ∀ x ∈ P, ∀ y ∈ P, x ≠ y → 1 ≤ dist x y` (Density.lean:35-36). The Euclidean
  distance on `EuclideanSpace ℝ (Fin 4)` (L2 norm, not sup norm) gives non-overlapping balls of
  radius 1/2. Infinite and empty `P` are allowed. **OK.**
* `upperDensity P := limsup_{R→∞} vol(B(0,1/2)) · #(P ∩ B(0,R)) / vol(B(0,R))` in `ℝ≥0∞`
  (Density.lean:39-41), with `encard` and Lebesgue `volume` on `EuclideanSpace`. This is the
  center-count form of the standard upper density with origin-centred balls. It differs from the
  volume-fraction form only by boundary terms of order `R³`, so the limsups agree. A translate of
  a unit packing is a unit packing, so origin-centred balls lose nothing. `Transfer.lean` proves
  that `P ∩ B(0,R)` is finite, so the count is a natural number. There is no loophole: the value
  is not forced to 0 or ∞, and `R ≤ 0` does not matter under `atTop`. **OK.**
* Scope: the statement covers unit packings, that is congruent balls of radius 1/2. A packing of
  balls of radius `ρ` reduces by scaling, which is not formalized. This is standard. The density
  definition is scale invariant.
* Conclusion `upperDensity P < ENNReal.ofReal (629521681653 / 10¹²)`. It is strict, and the
  arithmetic is `final_arith` (Ledger.lean:168), `decide`/`norm_num`. **OK.**
* `f` is concrete (Scalar.lean), and all its properties are proved, including the Fourier identity
  (`fourierIdentity`, via `Fourier.lean`). **OK.**

## 5. What remains outside Lean and outside the programs

Lean proves the theorem from the eight hypotheses. The programs certify the hypotheses. The
following are checked by neither. They are trust, not mismatches.

1. **Written proofs that no program tests.** Programs check only the parameters these lemmas
   need, such as `a² < T/(2(T+1))`, `a + b = 1`, `3b² < 1` or a cutoff below an onset. The general
   inequalities themselves are written proofs:
   - the pointed-cap ball-count lemmas and the tent occupancy bound;
   - the classical-improvement allocation capacity and the two-level step capacity;
   - the affine-latitude reduction to a spherical code;
   - the spherical-to-shell transfer `1 - 1/(2R²) ≤ s`;
   - the gauge identity `(Σ w)(1 - Σ ψ) ≥ 0`.
   Source: stage 1 `COMPONENTS.md`, "Gaps and trusted parts" item 1. The local-energy lemmas of
   the census (stage 2 `PROOF.md`) and the finite-count inequality (stage 3
   `finite_count_gain.md`) are written proofs whose arithmetic the programs recheck.
2. **Cited theorems, not proved in the project.**
   - Schoenberg: positive definiteness of Gegenbauer and Legendre polynomials on spheres. The
     Gram rows, the graph capacities and the spherical certificates use it.
   - Schütte and van der Waerden: `φ_3(9) = arccos(1/3)`, the degree bound 8 behind
     `graph_slack`. The project read the statement in Barg–Musin and did not open the original.
   - The cross-polytope allocation source (Fejes Tóth–Fodor–Vigh) and Blichfeldt's inequality are
     also cited. The classical-improvement capacity also has a complete written proof.
3. **One implementation of the kernel assembly.** Stage 1's coordinator builds the pair and
   triangle polynomials of the full V7 kernel as the sum of all component contributions. This is
   reviewed code with no second implementation of the full triangle expression. It is partly
   cross-checked by 672 polynomial identities and 560 signed spherical identities (COMPONENTS.md,
   "Gaps" item 3). Stage 5's `kformula` is an independent derivation of the pair kernel only, and
   it is compared with `raw_v7` at 72 points and 88 band points.
4. **Scaling to other radii.** Lean states the bound for unit packings: centres at mutual distance
   `≥ 1`, that is balls of radius `1/2`. A packing of congruent balls of any other radius reduces
   to this case by scaling, and density is scale invariant. That reduction is standard but not
   formalized.
5. **Trust base of the programs.** CPython, `fractions`, NumPy integer arrays, python-flint/Arb,
   the two C++ helpers of stage 1 compiled fresh, and the hardware. Stage 1's per-leaf
   subdivision trees are not stored; rerunning is the check.

## 6. Questions sent to stage agents

* stage1-v7: exactness of `Γ ≤ 0` (no `η` slack), gauge orientation, break convention and
  closed case coverage, and the lifted pair being `0`.
* stage23-origin: E9 used only as `≥ 0`, closed counts, group coverage, `X = ∅`.
* stage45-kernelbox: `kformula` = full polarization, closed `B_j`, safe kinks, and stage 4 with no
  group assumption.

Section 7 records their replies.

## 7. Agent replies (2026-11-13)

All three agents confirmed my reading. No verdict changes.

* **stage1-v7.** `Γ ≤ 0` is certified exactly. `η_b` is an exact per-case constant, because each
  region lies wholly inside or outside each count radius (coordinator
  `verify_combined_binary_six_exterior_graphs_small_cap_bounds.py:171-181, 803-806`;
  `certificate_core.py:111`). Acceptance is per box: the maximum upper Bernstein coefficient is
  at most the factor times the correction lower bound
  (`interval_combined_binary_six_graphs_correlated_small_cap_bounds.py:161`). The `ε`/`η` repairs
  exist only inside the signed spherical certificates (`signed_spherical_exact.py:30-35`). The gauge
  is symmetrized (`full_pair_count_gauge.py:6-11, 129-144`). Each case is certified on the closed
  product of its regions, so both one-sided closures at a break are covered (`certificate_core.py:88,
  107`). There are 84 full cases (all three anchors built) and 28 exterior cases with third side
  from exactly `7/4` up to `r + s`. The full pair term is identically `0` on `[1, 7/4]`, and
  `f < 0` strictly for `|x| ≥ 7/4`.
* **stage23-origin.** The census uses no graph energy, allocation or far-pair gain. Every other
  component enters only as `≥ 0` (`enumerate_radial_origin_envelope.py:74-109`). Counts are closed
  (`verify_joint_count_origin_credit.py:44, 127`). Surplus applicability is `ns[j] == N`
  (`enumerate_radial_origin_envelope.py:102`). C is a superset defined only by monotonicity, the
  caps and the two implications, `N = 0` included. Points beyond `7/4` add neither energy nor
  counts. Caveat: `K − Kg` is right only if `Kg` is exactly stage 1's E9, including endpoint
  conventions. I checked this: stage 1's E9 helper uses closed containment for both the radial
  window `[33/28, 7/4]` and the angular window `[-1, -7/8]` (`six_exterior_graph_route/
  graph_repair_bounds.py:9-10, 16-18, 56`; `verify_antipodal_wide_exterior_graph.py:47-48`).
  raw_v7 and kformula use the same closed rule, with weight `1/50000000` and capacity 1358. Lean's
  `broadEdge` is closed in all five conditions. **Identical.**
* **stage45-kernelbox.** `kformula` is the complete polarization, with no term dropped
  (`kformula.py:323-357`; all four graphs in `GRAPH_SPECS`, lines 296-301; symmetric gauge,
  lines 337-339). All `pos` weights and radial-weight coefficients are `≥ 0` (checked on
  `origin.json` today). `B_j` is closed (`kbox_run.py:25-27`, `check_kernelbox.py:93-96`), and the
  lower-region value is used at breaks (`kformula.py:69-72`). Safe branches only lower `-K`
  (`kcert.py:158-250`). Self, count and graph-radius kinks must be decided or the run aborts. Stage 4
  holds for every finite unit-separated `X`, with no group assumption (`graph_slack.md:11-14,
  67-71`), closed windows and ordered edges. It depends on the cited Schütte–van der Waerden
  theorem.

Final classification: no MISMATCH. WEAKER: `v7_pair`, `v7_raw` and the rounded census floors.
Everything else is OK.


## Recovery audit addendum: current theorem signature (2026-11-13)

This addendum is a new source review by the D4 publication recovery
proof-audit agent. The preceding audit is retained as historical evidence;
its eight-hypothesis signature and its descriptions of the old implementation
cross-checks are not the current signature or current verification report.
This addendum does not claim a new Lean compile or a full certificate replay.
Those are separate coordinator checks.

The current `Main.lean` has **fourteen mathematical certificate hypotheses**:
`v7_support`, `v7_pair`, `v7_cyclic`, `v7_raw`, `census`,
`kernel_box_1`, `kernel_box_5`, `code_24`, `code_25`, `code_26`,
`latitude_15`, `latitude_24`, `annular_151`, and `svdw`.
The parameter `K`, the packing `P`, and `IsUnitPacking P` are separate
arguments. The actual kernel is still not defined in Lean.

The changes are mathematically appropriate:

- `census` now assumes `InCountDomain X`, and supplies the floor for **every**
  matching listed group. The finite minimization in stages 2 and 3 has exactly
  this scope. `countDomain_of_admissible` and `group_mem` now prove existence
  of such a group, using three code bounds and the two latitude certificates.
  Thus an impossible count vector is not smuggled in as a certificate premise,
  and the empty neighbourhood is covered by `(0,1)`.
- `LatitudeCert` uses exactly the `P`, `V`, `H`, `D`, beta and radii of
  `affine_latitude_counts.py`. Its disjunction preserves the signs before
  squaring. The meridian reduction in `lat_meridian` handles the case where
  the maximal possible original dot product at fixed latitudes lies below
  `s`; `lat_key` combines it with the feasible `D>=0` case. The north pole is
  separate, and the southern endpoint is included.
- `graph_slack` is now a derived theorem, `graphSlack_of`, using the annular
  spherical-code bound and the named nine-point theorem. `annulus_inner_le`
  gives the closed cutoff `41/49`, `proj_scalar` gives a strict bound below
  `1/3`, and the zero-projection case is separate. `svdw` permits repeated
  vectors; this is implied by the usual theorem for distinct vectors, since
  repetitions have inner product 1.
- `energy_floor` splits `Kalloc` into `K-Kg`, `Kg`, and the newly allocated
  slack. The census uses no positive floor for `Kg`, so the graph credit
  `3/10^6` is spent exactly once. The far-pair allocation has zero origin and
  diagonal contributions and is not part of the original census.

The detailed current source map and the precise classical theorem statements
are in [PROOF_DEPENDENCIES.md](../PROOF_DEPENDENCIES.md). The opened
Barg–Musin arXiv v2 text, article pages 8–9, confirms exactly the needed
nine-point inequality; this audit did not open the 1951 proof. A proof of
Schoenberg on S3 does not by itself discharge the Legendre/S2 positivity used
in transverse anchored kernels and the original broad-graph bound.

The analytic pointed-cap probability and enclosure derivation that the
publication's `pointed/THEOREM.md` linked to was missing from the export. It
has now been restored, unchanged, at
[`POINTED_VERIFICATION.md`](../verify/stage1_v7/proofs/current/base/new_work/audit/POINTED_VERIFICATION.md).
Its source was the corresponding proof file in the retained V7 record.
Historical finite test counts in that note remain historical attribution,
not a claim that this recovery audit reran them.

No new mathematical mismatch was identified in the reviewed hypothesis
reductions. This is a source-review conclusion. Successful replay of the
current exact identity programs, full certificate stages and Lean build
remains the final execution gate, and point samples alone cannot discharge
kernel identity.

## Formalization update: seven original premises discharged

The earlier inventories are historical. `ConcreteMain.lean` now fixes `V7.kernel` and supplies support, pair sign and raw objective from compiled concrete proofs. `Main.lean` supplies both latitude certificates, annular151 and the projected eight-point bound. `GraphSlackExact.lean` proves the exact cutoff223/735 transfer, replacing the full Schütte–van der Waerden input. S² and S³ Schoenberg positivity are proved for all degrees.

The concrete theorem still assumes cyclic sign, census floor, the two kernel boxes and three near-code bounds: seven premises. Finite arithmetic census checks and generic energy/interval soundness are components of these obligations, not replacements for their remaining concrete analytic bridges. Clean full compilation after all integrations remains to be recorded separately.

## Current formalization audit (2026-11-13)

This documentation/source audit read the actual `ConcreteMain.lean` signature:
`v7_cyclic`, `census`, `kernel_box_1`, `kernel_box_5`, `code_24`, `code_25`,
and `code_26` are the seven certificate premises. `P` and `IsUnitPacking P`
are the packing inputs. The specialization fixes `V7.kernel` and supplies
its support, pair sign and raw objective. `Main.lean` supplies both latitude
certificates and `graphSlack_proved`, using the formal annular151 and
projected-eight certificates. This confirms the source interface, not a new
compile or theorem discharge.

Individual successful compilation receipts were inspected for ConcreteMain,
Main's graph integration, GraphSlackExact, the concrete allocation/tent
lemmas, strict-obtuse cardinality and the strict ball-count corollary. The
final clean compilation of the expanded project remains pending. The full
concrete spherical sign-tree replay in Lean is also unfinished. Generic tree
soundness and coefficient identities are not the three spherical code
bounds; finite census arithmetic is not the analytic domination of its
expression by the actual kernel energy. None of the seven premises is
removed by this audit.

The earlier complete external certificate replay remains historical evidence
for the mixed written/computational proof. Its 22-module Lean build does not
certify the later source tree. The current validation boundary is stated at
the top of [REVIEW.md](../REVIEW.md).

Further individually compiled components now include the full 165,503-case
finite census, actual count and graph energy identities, concrete Gram origin
completion, and all 98 cap energies. The latter uses a proved normalized S²
cap-area formula, including closed endpoints. `V7Census.lean` composes the
actual kernel with the finite census and the proved twelve affine floors and
ungauged pair sign. Its sole remaining component input is the spherical surplus.
`V7CensusFromSigns.lean` supplies that comparison from exactly three physical
spherical triangle-sign premises. Both integration modules have compiled. These
advances do not change the seven-premise signature above; complete sign replay
and the final clean build are still pending.

### Remaining obligations in the concrete theorem

This table counts premises of `d4_density_bound_concrete`, rather than completed
helper lemmas. A component compilation does not reduce the count until the
concrete theorem consumes its unconditional proof.

| Premise | Completed components | Remaining formal connection |
|---|---|---|
| `v7_cyclic` | Concrete kernel and exact pair-expression semantics | Full triangle-domain coverage, correction-term bounds and replay of all cyclic branches |
| `census` | All 165,503 finite cases; actual count/graph energies; origin completion, Gram projection and twelve affine floors; allocation/tent/conditional energies; all 98 cap energies; ungauged pair sign; actual spherical energy/table transfer | Three degree-16 spherical triangle-sign proofs, then their concrete census integration |
| `kernel_box_1` | Generic interval, Taylor and tree soundness; concrete expression linkage | Smooth lower bounds across branch boundaries, complete certificate replay and the actual `R1` kernel-box conclusion |
| `kernel_box_5` | Same shared machinery | Complete replay and the actual `R5` conclusion |
| `code_24` | Spherical positivity, polynomial reductions and concrete count-bound assembly | Complete sign-tree replay |
| `code_25` | Spherical positivity, polynomial reductions and concrete count-bound assembly | Complete sign-tree replay |
| `code_26` | Spherical positivity, polynomial reductions and concrete count-bound assembly | Complete sign-tree replay |

These are specific certificate obligations. The two former classical inputs
have already been handled: all-degree Schoenberg positivity on S² and S³ is
proved, and the needed Schütte–van der Waerden consequence is replaced by the
proved projected-eight certificate. Neither is a remaining external premise.

The clean build driver now stages all three complete near-code and all three
degree-16 surplus replay trees before resolving imports and rejects incomplete
generation or cached project artifacts. Its 12 Lean-driver and seven overall-driver
regression tests passed during coordinator review. This validates the build machinery, not the still-pending full build
or the seven mathematical conclusions above.
