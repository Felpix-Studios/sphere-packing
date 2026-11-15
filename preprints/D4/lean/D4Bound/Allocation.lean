import D4Bound.Neighbourhood

/-!
# Reallocating triangle slack, and the far-pair bound on a neighbourhood

For the base kernel `K` and a triangle `{0, x, y}` the cyclic sum is

  `Γ(x, y) = K(x, y) + K(-x, y - x) + K(-y, x - y)`.

The allocation (Section 6 of the paper) is

  `H(x, y) = -Γ(x, y) / k`  if `x ≠ y` and `1 ≤ ‖x‖, ‖y‖ ≤ 7/4`, and `0` otherwise,

where `k = 3` if `‖x - y‖ ≤ 7/4` and `k = 1` otherwise (the number of vertices of the triangle
whose two incident sides are at most `7/4`). The allocated kernel is `K' = K + H`.

Proved here:

* `alloc_zero_right`, `alloc_diag`: `H(x, 0) = H(x, x) = 0`, so the pair terms of `K'` are those
  of `K` and `K'(0,0) = K(0,0)`;
* `tripleSum_Kalloc`: if `K` vanishes when either argument has norm `> 7/4`, the triple sum of
  `K'` over any unit-separated family is exactly `0` (no symmetry of `K` is needed);
* `far_pair_nbhd`: if moreover `Γ ≤ 0` on separated triangles and `-K ≥ λ q(t)` on the box
  `B(R)`, then `∑_{x,y ∈ X} H(x,y) ≥ λ max(Q_N, 0)` for every admissible `X` whose near
  neighbours (norm `≤ R₅`) all have norm `≤ R`. This is Proposition 6.3 of the paper.
-/

open Finset
open scoped RealInnerProductSpace

namespace D4Bound

/-! ## Definitions -/

/-- The cyclic sum `Γ(x, y) = K(x, y) + K(-x, y - x) + K(-y, x - y)` of the triangle `{0,x,y}`. -/
def cyc (K : E4 → E4 → ℝ) (x y : E4) : ℝ := K x y + K (-x) (y - x) + K (-y) (x - y)

open Classical in
/-- The allocation `H(x, y) = -Γ(x, y)/k`. -/
noncomputable def alloc (K : E4 → E4 → ℝ) (x y : E4) : ℝ :=
  if x ≠ y ∧ 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 7 / 4 ∧ 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 7 / 4 then
    -cyc K x y / (if ‖x - y‖ ≤ 7 / 4 then 3 else 1)
  else 0

/-- The allocated kernel `K' = K + H`. -/
noncomputable def Kalloc (K : E4 → E4 → ℝ) (x y : E4) : ℝ := K x y + alloc K x y

/-- `K(x, y) = 0` whenever `‖x‖ > 7/4` or `‖y‖ > 7/4`. -/
def SupportedIn (K : E4 → E4 → ℝ) : Prop :=
  ∀ x y : E4, (7 / 4 < ‖x‖ ∨ 7 / 4 < ‖y‖) → K x y = 0

/-- Condition (3) of Theorem 2.1: `Γ(x, y) ≤ 0` when `‖x‖, ‖y‖, ‖x - y‖ ≥ 1`. -/
def CyclicSign (K : E4 → E4 → ℝ) : Prop :=
  ∀ x y : E4, 1 ≤ ‖x‖ → 1 ≤ ‖y‖ → 1 ≤ ‖x - y‖ → cyc K x y ≤ 0

/-- The kernel-box bound `-K(y,z) ≥ λ q(t)` on
`B(R) = {(y,z) : 1 ≤ ‖y‖, ‖z‖ ≤ R, t ≤ -133/250}`, `t = ⟪y,z⟫/(‖y‖‖z‖)`,
`q(t) = t⁴ - (133/250)² t²`. -/
def KernelBox (K : E4 → E4 → ℝ) (R lam : ℝ) : Prop :=
  ∀ y z : E4, 1 ≤ ‖y‖ → ‖y‖ ≤ R → 1 ≤ ‖z‖ → ‖z‖ ≤ R →
    ⟪y, z⟫ ≤ -(133 / 250) * (‖y‖ * ‖z‖) →
    lam * ((⟪y, z⟫ / (‖y‖ * ‖z‖)) ^ 4 - (133 / 250) ^ 2 * (⟪y, z⟫ / (‖y‖ * ‖z‖)) ^ 2) ≤ -K y z

/-! ## Basic facts -/

lemma alloc_zero_right (K : E4 → E4 → ℝ) (x : E4) : alloc K x 0 = 0 := by
  simp [alloc]

lemma alloc_diag (K : E4 → E4 → ℝ) (x : E4) : alloc K x x = 0 := by
  simp [alloc]

lemma Kalloc_zero_right (K : E4 → E4 → ℝ) (x : E4) : Kalloc K x 0 = K x 0 := by
  simp [Kalloc, alloc_zero_right]

lemma Kalloc_diag (K : E4 → E4 → ℝ) (x : E4) : Kalloc K x x = K x x := by
  simp [Kalloc, alloc_diag]

lemma alloc_nonneg {K : E4 → E4 → ℝ} (hcyc : CyclicSign K) {x y : E4}
    (hxy : x = y ∨ 1 ≤ ‖x - y‖) : 0 ≤ alloc K x y := by
  unfold alloc
  split_ifs with h hk
  · rcases hxy with e | hxy
    · exact absurd e h.1
    · have := hcyc x y h.2.1 h.2.2.2.1 hxy
      rw [neg_div]; exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg this (by norm_num))
  · rcases hxy with e | hxy
    · exact absurd e h.1
    · have := hcyc x y h.2.1 h.2.2.2.1 hxy
      rw [neg_div]; exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg this (by norm_num))
  · exact le_rfl

/-- On a far pair only the anchor carries the triangle, and `H = -K`. -/
lemma alloc_far {K : E4 → E4 → ℝ} (hK : SupportedIn K) {x y : E4}
    (hx1 : 1 ≤ ‖x‖) (hx2 : ‖x‖ ≤ 7 / 4) (hy1 : 1 ≤ ‖y‖) (hy2 : ‖y‖ ≤ 7 / 4)
    (hfar : 7 / 4 < ‖x - y‖) : alloc K x y = -K x y := by
  have hne : x ≠ y := by
    intro e; rw [e, sub_self, norm_zero] at hfar; linarith
  have h1 : K (-x) (y - x) = 0 := hK _ _ (Or.inr (by rwa [norm_sub_rev]))
  have h2 : K (-y) (x - y) = 0 := hK _ _ (Or.inr hfar)
  have hk : ¬ ‖x - y‖ ≤ 7 / 4 := not_le.mpr hfar
  simp only [alloc, cyc, hne, ne_eq, not_false_eq_true, hx1, hx2, hy1, hy2, and_self,
    if_true, hk, if_false, h1, h2, add_zero, div_one]

/-! ## The triple sum of the allocated kernel vanishes -/

section triple

variable {n : ℕ}

/-- Sum over ordered triples of distinct indices. -/
def S3 (F : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, (if j ≠ i ∧ k ≠ i ∧ k ≠ j then F i j k else 0)

lemma S3_congr {F G : Fin n → Fin n → Fin n → ℝ}
    (h : ∀ i j k, j ≠ i → k ≠ i → k ≠ j → F i j k = G i j k) : S3 F = S3 G := by
  unfold S3
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hc
  · exact h i j k hc.1 hc.2.1 hc.2.2
  · rfl

lemma S3_sub (F G : Fin n → Fin n → Fin n → ℝ) :
    S3 (fun i j k => F i j k - G i j k) = S3 F - S3 G := by
  unfold S3
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

lemma S3_zero {F : Fin n → Fin n → Fin n → ℝ}
    (h : ∀ i j k, j ≠ i → k ≠ i → k ≠ j → F i j k = 0) : S3 F = 0 := by
  rw [S3_congr (G := fun _ _ _ => 0) h]; simp [S3]

lemma sum_cyc' (G : Fin n → Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, ∑ k, G i j k = ∑ i, ∑ j, ∑ k, G k i j := by
  rw [sum_swap13]; exact sum_swap12 (fun i j k => G k j i)

lemma S3_perm12 (F : Fin n → Fin n → Fin n → ℝ) : S3 F = S3 (fun i j k => F j i k) := by
  unfold S3
  rw [sum_swap12]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => if_congr ?_ rfl rfl
  exact ⟨fun h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩, fun h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩

lemma S3_perm231 (F : Fin n → Fin n → Fin n → ℝ) : S3 F = S3 (fun i j k => F j k i) := by
  unfold S3
  rw [← sum_cyc' (fun i j k => if k ≠ j ∧ i ≠ j ∧ i ≠ k then F j k i else 0)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => if_congr ?_ rfl rfl
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;>
    first | assumption | exact Ne.symm (by assumption)

lemma tripleSum_eq_S3 (K : E4 → E4 → ℝ) (p : Fin n → E4) :
    tripleSum K p = S3 (fun i j k => K (p j - p i) (p k - p i)) := rfl

open Classical in
/-- The share of anchor `i` in the triangle `{i, j, k}`. -/
noncomputable def share (p : Fin n → E4) (i j k : Fin n) : ℝ :=
  if ‖p j - p i‖ ≤ 7 / 4 ∧ ‖p k - p i‖ ≤ 7 / 4 then
    1 / (if ‖p k - p j‖ ≤ 7 / 4 then 3 else 1)
  else 0

lemma alloc_triple (K : E4 → E4 → ℝ) {p : Fin n → E4} (hp : Separated p) {i j k : Fin n}
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    alloc K (p j - p i) (p k - p i) = -(share p i j k *
      (K (p j - p i) (p k - p i) + K (p i - p j) (p k - p j) + K (p i - p k) (p j - p k))) := by
  have hne : p j - p i ≠ p k - p i := by
    intro e
    have := hp j k hkj
    rw [show p k - p j = p k - p i - (p j - p i) by abel, ← e, sub_self, norm_zero] at this
    linarith
  have h1 := hp i j hji
  have h2 := hp i k hki
  have ec : cyc K (p j - p i) (p k - p i) =
      K (p j - p i) (p k - p i) + K (p i - p j) (p k - p j) + K (p i - p k) (p j - p k) := by
    unfold cyc
    rw [show -(p j - p i) = p i - p j by abel, show p k - p i - (p j - p i) = p k - p j by abel,
      show -(p k - p i) = p i - p k by abel, show p j - p i - (p k - p i) = p j - p k by abel]
  have ed : ‖p j - p i - (p k - p i)‖ = ‖p k - p j‖ := by
    rw [show p j - p i - (p k - p i) = p j - p k by abel, norm_sub_rev]
  unfold alloc share
  rw [ec, ed]
  by_cases hc : ‖p j - p i‖ ≤ 7 / 4 ∧ ‖p k - p i‖ ≤ 7 / 4
  · have hc' : p j - p i ≠ p k - p i ∧ 1 ≤ ‖p j - p i‖ ∧ ‖p j - p i‖ ≤ 7 / 4 ∧
        1 ≤ ‖p k - p i‖ ∧ ‖p k - p i‖ ≤ 7 / 4 := ⟨hne, h1, hc.1, h2, hc.2⟩
    rw [if_pos hc', if_pos hc]
    ring
  · have hc' : ¬ (p j - p i ≠ p k - p i ∧ 1 ≤ ‖p j - p i‖ ∧ ‖p j - p i‖ ≤ 7 / 4 ∧
        1 ≤ ‖p k - p i‖ ∧ ‖p k - p i‖ ≤ 7 / 4) := fun h => hc ⟨h.2.2.1, h.2.2.2.2⟩
    rw [if_neg hc', if_neg hc]
    ring

/-- The shares of the three vertices add up to `1` wherever the anchored kernel is nonzero. -/
lemma share_sum {K : E4 → E4 → ℝ} (hK : SupportedIn K) (p : Fin n → E4) (i j k : Fin n) :
    K (p j - p i) (p k - p i) * (1 - share p i j k - share p j i k - share p j k i) = 0 := by
  by_cases hc : ‖p j - p i‖ ≤ 7 / 4 ∧ ‖p k - p i‖ ≤ 7 / 4
  · have e1 : ‖p i - p j‖ = ‖p j - p i‖ := norm_sub_rev _ _
    have e2 : ‖p i - p k‖ = ‖p k - p i‖ := norm_sub_rev _ _
    unfold share
    simp only [e1, e2, hc, and_self, if_true]
    by_cases h3 : ‖p k - p j‖ ≤ 7 / 4
    · simp only [h3, and_self, if_true]; norm_num
    · simp [h3]
  · rw [not_and_or, not_le, not_le] at hc
    rw [hK _ _ hc, zero_mul]

/-- The triple sum of the allocated kernel is zero. -/
theorem tripleSum_Kalloc {K : E4 → E4 → ℝ} (hK : SupportedIn K) {p : Fin n → E4}
    (hp : Separated p) : tripleSum (Kalloc K) p = 0 := by
  rw [tripleSum_eq_S3]
  have hsplit : S3 (fun i j k => Kalloc K (p j - p i) (p k - p i)) =
      S3 (fun i j k => K (p j - p i) (p k - p i) * (1 - share p i j k)
        - share p i j k * K (p i - p j) (p k - p j))
      - S3 (fun i j k => share p i j k * K (p i - p k) (p j - p k)) := by
    rw [← S3_sub]
    refine S3_congr fun i j k hji hki hkj => ?_
    simp only [Kalloc, alloc_triple K hp hji hki hkj]
    ring
  rw [hsplit, S3_sub, S3_perm12 (fun i j k => share p i j k * K (p i - p j) (p k - p j)),
    S3_perm231 (fun i j k => share p i j k * K (p i - p k) (p j - p k)), ← S3_sub, ← S3_sub]
  exact S3_zero fun i j k _ _ _ => by
    have := share_sum hK p i j k
    linear_combination this

end triple

/-! ## The far-pair bound on a neighbourhood -/

lemma ofLp_sum_sq (x : E4) : ∑ a, (WithLp.ofLp x) a ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp

lemma ofLp_sum_mul (x y : E4) : ∑ a, (WithLp.ofLp x) a * (WithLp.ofLp y) a = ⟪x, y⟫ := by
  simp [PiLp.inner_apply, mul_comm]

/-- Proposition 6.3: the allocation of a neighbourhood is at least `λ max(Q_N, 0)`. -/
theorem far_pair_nbhd {K : E4 → E4 → ℝ} (hK : SupportedIn K) (hcyc : CyclicSign K)
    {X : Finset E4} (hX : Admissible X) {R lam : ℝ} (hlam : 0 ≤ lam)
    (hbox : KernelBox K R lam) (hin : ∀ x ∈ X, ‖x‖ ≤ R5 → ‖x‖ ≤ R) :
    lam * max ((nearCount X : ℝ) * (13561 * nearCount X - 179244) / 250000) 0 ≤
      ∑ x ∈ X, ∑ y ∈ X, alloc K x y := by
  classical
  have hR5 : R5 ≤ 7 / 4 := by norm_num [R5]
  set Y := X.filter fun x => ‖x‖ ≤ R5 with hY
  have hYX : Y ⊆ X := Finset.filter_subset _ _
  have hNY : nearCount X = Y.card := by
    simp only [nearCount, countWithin, hY]
  have hnnX : ∀ x ∈ X, ∀ y ∈ X, 0 ≤ alloc K x y := fun x hx y hy => by
    by_cases e : x = y
    · exact alloc_nonneg hcyc (Or.inl e)
    · exact alloc_nonneg hcyc (Or.inr (hX.2 x hx y hy e))
  -- restrict to the near neighbours
  have hsub : ∑ x ∈ Y, ∑ y ∈ Y, alloc K x y ≤ ∑ x ∈ X, ∑ y ∈ X, alloc K x y := by
    calc ∑ x ∈ Y, ∑ y ∈ Y, alloc K x y ≤ ∑ x ∈ Y, ∑ y ∈ X, alloc K x y :=
          Finset.sum_le_sum fun x hx => Finset.sum_le_sum_of_subset_of_nonneg hYX
            fun y hy _ => hnnX x (hYX hx) y hy
      _ ≤ ∑ x ∈ X, ∑ y ∈ X, alloc K x y :=
          Finset.sum_le_sum_of_subset_of_nonneg hYX fun x hx _ =>
            Finset.sum_nonneg fun y hy => hnnX x hx y hy
  -- enumerate the near neighbours
  set N := Y.card
  let e : Fin N ≃ Y := Y.equivFin.symm
  let yv : Fin N → E4 := fun i => (e i : E4)
  have hyY : ∀ i, yv i ∈ Y := fun i => (e i).2
  have hyX : ∀ i, yv i ∈ X := fun i => hYX (hyY i)
  have hy1 : ∀ i, 1 ≤ ‖yv i‖ := fun i => hX.1 _ (hyX i)
  have hy5 : ∀ i, ‖yv i‖ ≤ R5 := fun i => (Finset.mem_filter.mp (hyY i)).2
  have hyR : ∀ i, ‖yv i‖ ≤ R := fun i => hin _ (hyX i) (hy5 i)
  have hyinj : ∀ i k, k ≠ i → yv i ≠ yv k := fun i k hki h =>
    hki (e.injective (Subtype.ext h)).symm
  have hsumY : ∀ g : E4 → ℝ, ∑ y ∈ Y, g y = ∑ i, g (yv i) := fun g => by
    rw [← Finset.sum_coe_sort Y g]
    exact (Equiv.sum_comp e (fun y : Y => g y)).symm
  have hYsum : ∑ x ∈ Y, ∑ y ∈ Y, alloc K x y = ∑ i, ∑ k, alloc K (yv i) (yv k) := by
    rw [hsumY]; simp only [hsumY]
  -- unit vectors
  have hrpos : ∀ i, 0 < ‖yv i‖ := fun i => lt_of_lt_of_le one_pos (hy1 i)
  let u : Fin N → Fin 4 → ℝ := fun i a => (WithLp.ofLp (yv i)) a / ‖yv i‖
  let r : Fin N → ℝ := fun i => ‖yv i‖
  have hip : ∀ i k, ip u i k = ⟪yv i, yv k⟫ / (‖yv i‖ * ‖yv k‖) := fun i k => by
    simp only [ip, u]
    rw [← ofLp_sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    field_simp
  have hu : ∀ i, ∑ a, u i a ^ 2 = 1 := fun i => by
    simp only [u, div_pow]
    rw [← Finset.sum_div, ofLp_sum_sq, div_self (by have := hrpos i; positivity)]
  have hsepE : ∀ i k, r i ^ 2 + r k ^ 2 - 2 * r i * r k * ip u i k = ‖yv i - yv k‖ ^ 2 :=
    fun i k => by
      rw [hip, norm_sub_sq_real]
      simp only [r]
      have := hrpos i; have := hrpos k
      field_simp
      ring
  have hsep : ∀ i k, k ≠ i → 1 ≤ r i ^ 2 + r k ^ 2 - 2 * r i * r k * ip u i k := fun i k hki => by
    rw [hsepE]
    have := hX.2 _ (hyX i) _ (hyX k) (hyinj i k hki)
    nlinarith
  have hnn : ∀ i k, k ≠ i → 0 ≤ alloc K (yv i) (yv k) := fun i k _ =>
    hnnX _ (hyX i) _ (hyX k)
  have hfar : ∀ i k, k ≠ i → 49 / 16 < r i ^ 2 + r k ^ 2 - 2 * r i * r k * ip u i k →
      ip u i k < -(133 / 250) →
      lam * (ip u i k ^ 4 - (133 / 250) ^ 2 * ip u i k ^ 2) ≤ alloc K (yv i) (yv k) := by
    intro i k _ hd ht
    rw [hsepE] at hd
    have hd' : 7 / 4 < ‖yv i - yv k‖ := by
      by_contra hle; push Not at hle
      have := norm_nonneg (yv i - yv k)
      nlinarith
    rw [alloc_far hK (hy1 i) ((hy5 i).trans hR5) (hy1 k) ((hy5 k).trans hR5) hd', hip]
    rw [hip] at ht
    have hpos : 0 < ‖yv i‖ * ‖yv k‖ := mul_pos (hrpos i) (hrpos k)
    refine hbox _ _ (hy1 i) (hyR i) (hy1 k) (hyR k) ?_
    have := (div_lt_iff₀ hpos).mp ht
    linarith
  have hmain := far_pair_sum_max u hu r hy1 hy5 hsep lam hlam
    (fun i k => alloc K (yv i) (yv k)) hnn hfar
  have hdiag : ∑ i, ∑ k, (if k ≠ i then alloc K (yv i) (yv k) else 0) ≤
      ∑ i, ∑ k, alloc K (yv i) (yv k) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => by
      split_ifs
      · exact le_rfl
      · exact hnnX _ (hyX i) _ (hyX k)
  rw [hNY]
  linarith

end D4Bound
