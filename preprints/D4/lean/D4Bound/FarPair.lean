import D4Bound.Spherical

/-!
# The far-pair lemma

Let an anchor have near neighbours `yᵢ = rᵢ uᵢ` with `uᵢ` unit vectors in `ℝ⁴`,
`1 ≤ rᵢ ≤ R₅ = 102597/100000`, and `|yᵢ - y_k| ≥ 1`. Put `a = 133/250` and
`q(t) = t²(t² - a²)`. Let `h i k ≥ 0` be the allocation terms, and suppose that a
certified kernel bound gives `h i k ≥ λ q(t_ik)` whenever the pair is far
(`|yᵢ - y_k|² > 49/16`) and `t_ik < -a`. Then

  ∑_{i ≠ k} h i k ≥ λ Q_N,   Q_N = N(13561 N - 179244)/250000.

The geometric facts used are: separated near neighbours have cosine at most `a`, and a
pair with cosine below `-a` is farther apart than `7/4`.
-/

namespace D4Bound

open Finset

/-- The outermost near radius `R₅`. -/
noncomputable def R5 : ℝ := 102597 / 100000

/-- Separated near neighbours have cosine at most `a = 133/250`. -/
lemma cap_le {r s t : ℝ} (hr : 1 ≤ r) (hr' : r ≤ R5) (hs : 1 ≤ s) (hs' : s ≤ R5)
    (hsep : 1 ≤ r ^ 2 + s ^ 2 - 2 * r * s * t) : t ≤ 133 / 250 := by
  unfold R5 at hr' hs'
  have hrs : 0 < r * s := by positivity
  have key : r ^ 2 + s ^ 2 - 1 ≤ 2 * (133 / 250) * (r * s) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hs),
      mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hs'),
      mul_nonneg (sub_nonneg.mpr hr') (sub_nonneg.mpr hs),
      mul_nonneg (sub_nonneg.mpr hr') (sub_nonneg.mpr hs'),
      mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hr'),
      mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hs')]
  by_contra h
  push Not at h
  nlinarith [mul_lt_mul_of_pos_left h (by positivity : (0 : ℝ) < 2 * (r * s))]

/-- A pair with cosine below `-a` is farther apart than `7/4`. -/
lemma far_of_lt {r s t : ℝ} (hr : 1 ≤ r) (hs : 1 ≤ s) (ht : t < -(133 / 250)) :
    49 / 16 < r ^ 2 + s ^ 2 - 2 * r * s * t := by
  have hrs : 1 ≤ r * s := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left ht (by positivity : (0 : ℝ) < 2 * (r * s))]

/-- `q(t) = t⁴ - a² t² ≤ 0` when `|t| ≤ a`. -/
lemma q_nonpos {t : ℝ} (h1 : -(133 / 250) ≤ t) (h2 : t ≤ 133 / 250) :
    t ^ 4 - (133 / 250) ^ 2 * t ^ 2 ≤ 0 := by
  have : t ^ 2 ≤ (133 / 250) ^ 2 := by nlinarith
  nlinarith [sq_nonneg t]

/-- The far-pair lemma. -/
theorem far_pair_sum {n : ℕ} (u : Fin n → Fin 4 → ℝ) (hu : ∀ i, ∑ a, u i a ^ 2 = 1)
    (r : Fin n → ℝ) (hr1 : ∀ i, 1 ≤ r i) (hr2 : ∀ i, r i ≤ R5)
    (hsep : ∀ i k, k ≠ i → 1 ≤ r i ^ 2 + r k ^ 2 - 2 * r i * r k * ip u i k)
    (lam : ℝ) (hlam : 0 ≤ lam) (h : Fin n → Fin n → ℝ)
    (hnn : ∀ i k, k ≠ i → 0 ≤ h i k)
    (hfar : ∀ i k, k ≠ i → 49 / 16 < r i ^ 2 + r k ^ 2 - 2 * r i * r k * ip u i k →
      ip u i k < -(133 / 250) →
      lam * (ip u i k ^ 4 - (133 / 250) ^ 2 * ip u i k ^ 2) ≤ h i k) :
    lam * ((n : ℝ) * (13561 * n - 179244) / 250000) ≤
      ∑ i, ∑ k, (if k ≠ i then h i k else 0) := by
  -- termwise: h i k ≥ λ q(t_ik)
  have hterm : ∀ i k, k ≠ i →
      lam * (ip u i k ^ 4 - (133 / 250) ^ 2 * ip u i k ^ 2) ≤ h i k := by
    intro i k hki
    have hcap := cap_le (hr1 i) (hr2 i) (hr1 k) (hr2 k) (hsep i k hki)
    by_cases hlt : ip u i k < -(133 / 250)
    · exact hfar i k hki (far_of_lt (hr1 i) (hr1 k) hlt) hlt
    · push Not at hlt
      have := q_nonpos hlt hcap
      nlinarith [hnn i k hki]
  have hsum : lam * ∑ i, ∑ k,
      (if k ≠ i then ip u i k ^ 4 - (133 / 250) ^ 2 * ip u i k ^ 2 else 0) ≤
      ∑ i, ∑ k, (if k ≠ i then h i k else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro k _
    split_ifs with hki
    · exact hterm i k hki
    · simp
  have hq := quartic_offdiag_ge u hu ((133 / 250) ^ 2) (by norm_num) (by norm_num)
  have hQ : (1 / 8 - (133 / 250) ^ 2 / 4) * (n : ℝ) ^ 2 - (1 - (133 / 250) ^ 2) * n =
      (n : ℝ) * (13561 * n - 179244) / 250000 := by ring
  rw [hQ] at hq
  nlinarith [mul_le_mul_of_nonneg_left hq hlam]

/-- With `h ≥ 0`, the sum is also at least `λ max(Q_N, 0)`. -/
theorem far_pair_sum_max {n : ℕ} (u : Fin n → Fin 4 → ℝ) (hu : ∀ i, ∑ a, u i a ^ 2 = 1)
    (r : Fin n → ℝ) (hr1 : ∀ i, 1 ≤ r i) (hr2 : ∀ i, r i ≤ R5)
    (hsep : ∀ i k, k ≠ i → 1 ≤ r i ^ 2 + r k ^ 2 - 2 * r i * r k * ip u i k)
    (lam : ℝ) (hlam : 0 ≤ lam) (h : Fin n → Fin n → ℝ)
    (hnn : ∀ i k, k ≠ i → 0 ≤ h i k)
    (hfar : ∀ i k, k ≠ i → 49 / 16 < r i ^ 2 + r k ^ 2 - 2 * r i * r k * ip u i k →
      ip u i k < -(133 / 250) →
      lam * (ip u i k ^ 4 - (133 / 250) ^ 2 * ip u i k ^ 2) ≤ h i k) :
    lam * max ((n : ℝ) * (13561 * n - 179244) / 250000) 0 ≤
      ∑ i, ∑ k, (if k ≠ i then h i k else 0) := by
  have h1 := far_pair_sum u hu r hr1 hr2 hsep lam hlam h hnn hfar
  have h0 : 0 ≤ ∑ i, ∑ k, (if k ≠ i then h i k else 0) := by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro k _
    split_ifs with hki
    · exact hnn i k hki
    · exact le_rfl
  rcases le_total ((n : ℝ) * (13561 * n - 179244) / 250000) 0 with hle | hle
  · rw [max_eq_right hle]; simpa using h0
  · rw [max_eq_left hle]; exact h1

end D4Bound
