import D4Bound.ComponentsGauge

/-!
# Component lemmas: antipodal allocation capacities

`COMPONENTS.md` row 5 (independent antipodal allocations), with the proofs of
`proofs/current/base/new_work/copositive/CLASSICAL_SHIFTED_ANTIPODAL_CAPACITY.md` section 1 (a) and
the docstring of `record/current/base/new_work/pointed/two_capacity_antipodal_allocation_exact.py`
(b). Everything holds in any real inner product space.

A finite set `Z` is *unit separated* if distinct points are at distance at least `1`.

* `sep_quadratic`: `2 n ∑|z|² ≥ n(n-1) + 2|∑ z|²` (the pair-distance identity).
* `blichfeldt`: `∑ P(|z|) ≤ 1` with `P(r) = (1 - 2r²)₊`.
* `pstar_capacity`: `∑ P_*(|z - c|) ≤ 1` for every centre `c`, with
  `P_*(r) = min(1, 2(1-r)²)` for `r ≤ 1/2` and `P(r)` for `r > 1/2` (row 5a).
* `step_capacity`: the two-level step `1` (`r < a`), `1/2` (`a ≤ r ≤ b`), `0` (`r > b`) has
  `∑ ≤ 1` when `0 ≤ a ≤ b`, `a + b ≤ 1` and `3b² < 1` (row 5b; the certificate has
  `a = 8453/20000`, `b = 11547/20000`, `a + b = 1`).
* `pstar_allocation_nonneg`, `step_allocation_nonneg`: the allocation energies
  `∑_y u(y)(1 - ∑_x Cap(|x - c(y)|))` are `≥ 0` for `u ≥ 0` and any test centres `c(y)`.
-/

open Finset
open scoped RealInnerProductSpace

namespace D4Bound
namespace Components

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Distinct points at distance at least `1`. -/
def UnitSep (Z : Finset V) : Prop := ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → 1 ≤ ‖x - y‖

omit [InnerProductSpace ℝ V] in
lemma UnitSep.mono {Z W : Finset V} (h : UnitSep Z) (hW : W ⊆ Z) : UnitSep W :=
  fun x hx y hy hxy => h x (hW hx) y (hW hy) hxy

lemma sum_sum_norm_sub_sq (Z : Finset V) :
    ∑ x ∈ Z, ∑ y ∈ Z, ‖x - y‖ ^ 2 =
      2 * Z.card * ∑ x ∈ Z, ‖x‖ ^ 2 - 2 * ‖∑ x ∈ Z, x‖ ^ 2 := by
  have hin : ∑ x ∈ Z, ∑ y ∈ Z, ⟪x, y⟫ = ‖∑ x ∈ Z, x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    exact Finset.sum_congr rfl fun x _ => (inner_sum _ _ _).symm
  simp only [norm_sub_sq_real, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  rw [hin]
  ring

omit [InnerProductSpace ℝ V] in
lemma sep_sum_ge (Z : Finset V) (h : UnitSep Z) :
    (Z.card : ℝ) * ((Z.card : ℝ) - 1) ≤ ∑ x ∈ Z, ∑ y ∈ Z, ‖x - y‖ ^ 2 := by
  classical
  have hx : ∀ x ∈ Z, (Z.card : ℝ) - 1 ≤ ∑ y ∈ Z, ‖x - y‖ ^ 2 := by
    intro x hxZ
    rw [← Finset.sum_erase Z (a := x) (f := fun y => ‖x - y‖ ^ 2) (by simp)]
    have hc : ((Z.erase x).card : ℝ) = (Z.card : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem hxZ, Nat.cast_pred (Finset.card_pos.mpr ⟨x, hxZ⟩)]
    rw [← hc, ← nsmul_one, ← Finset.sum_const]
    · refine Finset.sum_le_sum fun y hy => ?_
      have h1 := h x hxZ y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm
      nlinarith
  calc (Z.card : ℝ) * ((Z.card : ℝ) - 1) = ∑ _x ∈ Z, ((Z.card : ℝ) - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum hx

/-- The pair-distance identity: `2 n T ≥ n(n-1) + 2|S|²` with `T = ∑|z|²`, `S = ∑ z`. -/
theorem sep_quadratic (Z : Finset V) (h : UnitSep Z) :
    (Z.card : ℝ) * ((Z.card : ℝ) - 1) + 2 * ‖∑ x ∈ Z, x‖ ^ 2 ≤
      2 * Z.card * ∑ x ∈ Z, ‖x‖ ^ 2 := by
  have := sep_sum_ge Z h
  rw [sum_sum_norm_sub_sq] at this
  linarith

/-- **Row 3, pair-distance ball count.** If `2(T+1)r² < T`, a closed ball of radius
`r` contains at most `T` unit-separated points. This is the dimension-free branch of
`validate_caps`; the separate strictly-obtuse `T=5` branch is not asserted here. -/
theorem card_le_of_ball (Z : Finset V) (h : UnitSep Z) (r : ℝ) (T : ℕ)
    (hr : 2 * ((T : ℝ) + 1) * r ^ 2 < T) (hZ : ∀ x ∈ Z, ‖x‖ ≤ r) : Z.card ≤ T := by
  have hq := sep_quadratic Z h
  have hT : ∑ x ∈ Z, ‖x‖ ^ 2 ≤ Z.card * r ^ 2 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun x hx => pow_le_pow_left₀ (norm_nonneg _) (hZ x hx) 2
  by_contra hc
  have hn : (T : ℝ) + 1 ≤ Z.card := by exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_of_not_ge hc))
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) < Z.card := by linarith
  have h1 : (Z.card : ℝ) * ((Z.card : ℝ) - 1) ≤ Z.card * (2 * Z.card * r ^ 2) := by
    nlinarith [sq_nonneg ‖∑ x ∈ Z, x‖]
  have h2 : (Z.card : ℝ) - 1 ≤ 2 * Z.card * r ^ 2 := le_of_mul_le_mul_left h1 hn0
  have hp : 0 < 1 - 2 * r ^ 2 := by
    by_contra hneg
    have : ((T : ℝ) + 1) * (1 - 2 * r ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_not_gt hneg)
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hn) hp.le
  nlinarith

/-- `P(r) = (1 - 2r²)₊`. -/
noncomputable def capP (r : ℝ) : ℝ := max 0 (1 - 2 * r ^ 2)

lemma capP_eq (r : ℝ) : capP r = if 2 * r ^ 2 < 1 then 1 - 2 * r ^ 2 else 0 := by
  unfold capP
  split_ifs with h
  · exact max_eq_right (by linarith)
  · exact max_eq_left (by linarith)

/-- The sum of `1 - 2|z|²` over a unit-separated set is at most `1`. -/
lemma sum_one_sub_le (W : Finset V) (h : UnitSep W) :
    ∑ x ∈ W, (1 - 2 * ‖x‖ ^ 2) ≤ 1 := by
  have hq := sep_quadratic W h
  have hS := sq_nonneg ‖∑ x ∈ W, x‖
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_one, ← Finset.mul_sum]
  set n : ℝ := (W.card : ℝ)
  set T := ∑ x ∈ W, ‖x‖ ^ 2
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases eq_or_lt_of_le hn with h0 | hpos
  · rw [← h0]; nlinarith
  · by_contra hc
    nlinarith

/-- **Blichfeldt's inequality**: `∑ (1 - 2|z|²)₊ ≤ 1` on a unit-separated set. -/
theorem blichfeldt (Z : Finset V) (h : UnitSep Z) : ∑ x ∈ Z, capP ‖x‖ ≤ 1 := by
  classical
  simp only [capP_eq]
  rw [← Finset.sum_filter]
  exact sum_one_sub_le _ (h.mono (Finset.filter_subset _ _))

/-- `P_*(r) = min(1, 2(1-r)²)` for `r ≤ 1/2`, `P(r)` for `r > 1/2`. -/
noncomputable def capPstar (r : ℝ) : ℝ := if r ≤ 1 / 2 then min 1 (2 * (1 - r) ^ 2) else capP r

lemma capPstar_eq_capP {r : ℝ} (hr : 1 / 2 ≤ r) : capPstar r = capP r := by
  unfold capPstar
  split_ifs with h
  · have : r = 1 / 2 := le_antisymm h hr
    subst this
    norm_num [capP]
  · rfl

/-- The core inequality of section 1: `T ≥ (m-1)/2 + (1-a)²` from the two lower bounds. -/
lemma core_bound (m T t a : ℝ) (hm : 1 ≤ m) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (ht : 0 ≤ t)
    (h1 : m * (m - 1) + 2 * t ^ 2 ≤ 2 * m * T) (h2 : m * (1 - a ^ 2) - 2 * a * t ≤ T) :
    (m - 1) / 2 + (1 - a) ^ 2 ≤ T := by
  set s := Real.sqrt m
  have hs : s ^ 2 = m := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hm
  by_cases hcase : s * (1 - a) ≤ t
  · have hts : m * (1 - a) ^ 2 ≤ t ^ 2 := by
      rw [← hs]
      have h0 : 0 ≤ s * (1 - a) := by nlinarith
      nlinarith
    have hmpos : 0 < m := by linarith
    by_contra hc
    push Not at hc
    nlinarith
  · push Not at hcase
    have h3 : m * (1 - a ^ 2) - 2 * a * (s * (1 - a)) ≤ T := by nlinarith
    have hid : m * (1 - a ^ 2) - 2 * a * (s * (1 - a)) - ((m - 1) / 2 + (1 - a) ^ 2) =
        (m - 1) * (1 / 2 - a) + a * (1 - a) * (s - 1) ^ 2 := by
      rw [← hs]; ring
    have hpos : 0 ≤ (m - 1) * (1 / 2 - a) + a * (1 - a) * (s - 1) ^ 2 := by
      have : 0 ≤ (m - 1) * (1 / 2 - a) := mul_nonneg (by linarith) (by linarith)
      have : 0 ≤ a * (1 - a) * (s - 1) ^ 2 :=
        mul_nonneg (mul_nonneg ha0 (by linarith)) (sq_nonneg _)
      linarith
    linarith

/-- **Row 5a.** The classical improvement of Blichfeldt's inequality, centred at the origin. -/
theorem pstar_capacity_zero (Z : Finset V) (h : UnitSep Z) : ∑ x ∈ Z, capPstar ‖x‖ ≤ 1 := by
  classical
  by_cases hz : ∃ z0 ∈ Z, ‖z0‖ < 1 / 2
  · obtain ⟨z0, hz0, ha⟩ := hz
    set a := ‖z0‖
    have ha0 : 0 ≤ a := norm_nonneg _
    set Z' := Z.erase z0
    have hfar : ∀ x ∈ Z', 1 - a ≤ ‖x‖ := by
      intro x hx
      have h1 := h x (Finset.mem_of_mem_erase hx) z0 hz0 (Finset.ne_of_mem_erase hx)
      have h2 := norm_sub_le x z0
      linarith
    have hsep' : UnitSep Z' := h.mono (Finset.erase_subset _ _)
    rw [← Finset.add_sum_erase _ _ hz0]
    have hpa : capPstar a = min 1 (2 * (1 - a) ^ 2) := by
      unfold capPstar; rw [if_pos ha.le]
    rw [hpa, Finset.sum_congr rfl fun x hx => capPstar_eq_capP (by linarith [hfar x hx])]
    simp only [capP_eq]
    rw [← Finset.sum_filter]
    set W := Z'.filter fun x => 2 * ‖x‖ ^ 2 < 1
    have hW : UnitSep W := hsep'.mono (Finset.filter_subset _ _)
    -- the remaining sum is at most `max 0 (1 - 2(1-a)²)`
    have key : ∑ x ∈ W, (1 - 2 * ‖x‖ ^ 2) ≤ max 0 (1 - 2 * (1 - a) ^ 2) := by
      rcases Nat.eq_zero_or_pos W.card with h0 | hpos
      · rw [Finset.card_eq_zero.mp h0]; simp
      · refine le_max_of_le_right ?_
        set m : ℝ := (W.card : ℝ)
        set T := ∑ x ∈ W, ‖x‖ ^ 2
        set t := ‖∑ x ∈ W, x‖
        have hm : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hpos
        have h1 := sep_quadratic W hW
        have h2 : m * (1 - a ^ 2) - 2 * a * t ≤ T := by
          have hx : ∀ x ∈ W, 1 ≤ ‖x‖ ^ 2 - 2 * ⟪x, z0⟫ + a ^ 2 := by
            intro x hx
            have hxZ : x ∈ Z := Finset.mem_of_mem_erase (Finset.mem_of_mem_filter _ hx)
            have hne : x ≠ z0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_filter _ hx)
            have := h x hxZ z0 hz0 hne
            rw [← norm_sub_sq_real]
            nlinarith
          have hsum := Finset.sum_le_sum hx
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_add_distrib,
            Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner] at hsum
          have hcs : -(t * a) ≤ ⟪∑ x ∈ W, x, z0⟫ := by
            have := abs_real_inner_le_norm (∑ x ∈ W, x) z0
            linarith [neg_abs_le ⟪∑ x ∈ W, x, z0⟫]
          nlinarith
        have h3 := core_bound m T t a hm ha0 ha.le (norm_nonneg _) h1 h2
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_one, ← Finset.mul_sum]
        linarith
    have hmm : min 1 (2 * (1 - a) ^ 2) + max 0 (1 - 2 * (1 - a) ^ 2) = 1 := by
      rcases le_total 1 (2 * (1 - a) ^ 2) with hc | hc
      · rw [min_eq_left hc, max_eq_left (by linarith)]; ring
      · rw [min_eq_right hc, max_eq_right (by linarith)]; ring
    linarith
  · push Not at hz
    rw [Finset.sum_congr rfl fun x hx => capPstar_eq_capP (hz x hx)]
    exact blichfeldt Z h

omit [InnerProductSpace ℝ V] in
/-- Translation preserves unit separation, so a capacity bound at `0` holds at every centre. -/
lemma sum_translate {f : ℝ → ℝ} (hf : ∀ Z : Finset V, UnitSep Z → ∑ x ∈ Z, f ‖x‖ ≤ 1)
    (Z : Finset V) (h : UnitSep Z) (c : V) : ∑ x ∈ Z, f ‖x - c‖ ≤ 1 := by
  classical
  have hinj : Set.InjOn (fun x => x - c) Z := fun x _ y _ hxy => sub_left_inj.mp hxy
  have hsep : UnitSep (Z.image fun x => x - c) := by
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    have : x' ≠ y' := fun e => hxy (by rw [e])
    simpa [sub_sub_sub_cancel_right] using h x' hx' y' hy' this
  have := hf _ hsep
  rwa [Finset.sum_image hinj] at this

/-- **Row 4, tent occupancy.** The Blichfeldt tent has capacity one about any centre. -/
theorem blichfeldt_translate (Z : Finset V) (h : UnitSep Z) (c : V) :
    ∑ x ∈ Z, capP ‖x - c‖ ≤ 1 :=
  sum_translate (fun Z hZ => blichfeldt Z hZ) Z h c

/-- **Row 5a.** `∑_i P_*(|z_i - c|) ≤ 1` for every unit-separated set and every centre `c`. -/
theorem pstar_capacity (Z : Finset V) (h : UnitSep Z) (c : V) :
    ∑ x ∈ Z, capPstar ‖x - c‖ ≤ 1 :=
  sum_translate (fun Z hZ => pstar_capacity_zero Z hZ) Z h c

/-- The two-level step `1` (`r < a`), `1/2` (`a ≤ r ≤ b`), `0` (`r > b`). -/
noncomputable def capStep (a b r : ℝ) : ℝ := if r < a then 1 else if r ≤ b then 1 / 2 else 0

/-- A closed `b`-ball with `3b² < 1` holds at most two unit-separated points. -/
lemma card_le_two_of_ball (W : Finset V) (h : UnitSep W) (b : ℝ) (hb : 3 * b ^ 2 < 1)
    (hW : ∀ x ∈ W, ‖x‖ ≤ b) : W.card ≤ 2 := by
  have hq := sep_quadratic W h
  have hT : ∑ x ∈ W, ‖x‖ ^ 2 ≤ W.card * b ^ 2 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun x hx => pow_le_pow_left₀ (norm_nonneg _) (hW x hx) 2
  by_contra hc
  push Not at hc
  have h3 : (3 : ℝ) ≤ W.card := by exact_mod_cast hc
  have hS := sq_nonneg ‖∑ x ∈ W, x‖
  set n : ℝ := (W.card : ℝ)
  have hnpos : 0 < n := by linarith
  have h5 : n * (n - 1) ≤ n * (2 * n * b ^ 2) := by nlinarith
  have h4 : n - 1 ≤ 2 * n * b ^ 2 := le_of_mul_le_mul_left h5 hnpos
  nlinarith [mul_lt_mul_of_pos_left hb hnpos]

/-- `∑ step(|z|) ≤ 1` at the origin. -/
theorem step_capacity_zero (a b : ℝ) (hab : a ≤ b) (hsum : a + b ≤ 1) (hb : 3 * b ^ 2 < 1)
    (Z : Finset V) (h : UnitSep Z) : ∑ x ∈ Z, capStep a b ‖x‖ ≤ 1 := by
  classical
  by_cases hz : ∃ z0 ∈ Z, ‖z0‖ < a
  · obtain ⟨z0, hz0, ha⟩ := hz
    rw [← Finset.add_sum_erase _ _ hz0]
    have hrest : ∀ x ∈ Z.erase z0, capStep a b ‖x‖ = 0 := by
      intro x hx
      have h1 := h x (Finset.mem_of_mem_erase hx) z0 hz0 (Finset.ne_of_mem_erase hx)
      have h2 := norm_sub_le x z0
      have hxb : b < ‖x‖ := by linarith
      unfold capStep
      rw [if_neg (by linarith), if_neg (by linarith)]
    rw [Finset.sum_congr rfl hrest, Finset.sum_const_zero]
    unfold capStep
    rw [if_pos ha]
    norm_num
  · push Not at hz
    have heq : ∀ x ∈ Z, capStep a b ‖x‖ = if ‖x‖ ≤ b then 1 / 2 else 0 := by
      intro x hx
      unfold capStep
      rw [if_neg (not_lt.mpr (hz x hx))]
    rw [Finset.sum_congr rfl heq, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have := card_le_two_of_ball (Z.filter fun x => ‖x‖ ≤ b)
      (h.mono (Finset.filter_subset _ _)) b hb (fun x hx => (Finset.mem_filter.mp hx).2)
    have : ((Z.filter fun x => ‖x‖ ≤ b).card : ℝ) ≤ 2 := by exact_mod_cast this
    linarith

/-- **Row 5b.** The two-level step capacity at every centre. -/
theorem step_capacity (a b : ℝ) (hab : a ≤ b) (hsum : a + b ≤ 1) (hb : 3 * b ^ 2 < 1)
    (Z : Finset V) (h : UnitSep Z) (c : V) : ∑ x ∈ Z, capStep a b ‖x - c‖ ≤ 1 :=
  sum_translate (fun Z hZ => step_capacity_zero a b hab hsum hb Z hZ) Z h c

/-- The certificate's parameters `a = 8453/20000`, `b = 11547/20000` satisfy the hypotheses. -/
lemma step_params_ok :
    (8453 / 20000 : ℝ) ≤ 11547 / 20000 ∧ (8453 / 20000 : ℝ) + 11547 / 20000 ≤ 1 ∧
      3 * (11547 / 20000 : ℝ) ^ 2 < 1 := by norm_num

/-! ## Allocation energies -/

/-- **Row 5a, energy.** `E_u(X) = ∑_y u(y)(1 - ∑_x P_*(|x - c(y)|)) ≥ 0` for `u ≥ 0`, any test
centres `c(y)` and any unit-separated `X ⊆ ℝ⁴ \ {0}`. -/
theorem pstar_allocation_nonneg (u : R4 → ℝ) (c : R4 → R4) (X : Finset R4) (hX : (0 : R4) ∉ X)
    (hsep : UnitSep X) (hu : ∀ y ∈ X, 0 ≤ u y) :
    0 ≤ anchoredEnergy (usageKernel u fun y x => capPstar ‖x - c y‖) X :=
  usage_energy_nonneg _ _ X hX hu fun y _ => pstar_capacity X hsep (c y)

/-- **Row 5b, energy.** The same for the two-level step. -/
theorem step_allocation_nonneg (a b : ℝ) (hab : a ≤ b) (hsum : a + b ≤ 1) (hb : 3 * b ^ 2 < 1)
    (u : R4 → ℝ) (c : R4 → R4) (X : Finset R4) (hX : (0 : R4) ∉ X) (hsep : UnitSep X)
    (hu : ∀ y ∈ X, 0 ≤ u y) :
    0 ≤ anchoredEnergy (usageKernel u fun y x => capStep a b ‖x - c y‖) X :=
  usage_energy_nonneg _ _ X hX hu fun y _ => step_capacity a b hab hsum hb X hsep (c y)

end Components
end D4Bound
