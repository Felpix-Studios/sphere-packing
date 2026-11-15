import D4Bound.ComponentsCapacity

/-! The exact refined capacity used by the two V7 tents at displacement 3/5.
For this parameter the integer quadratic test holds for every cardinality,
so the proof does not need a dimension-specific strictly obtuse set bound. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.Components

noncomputable def tentCapacity : ℝ := 44923461417477 / 62500000000000

theorem tent_capacity_positive : 0 < tentCapacity := by norm_num [tentCapacity]

theorem tent_integer_comparison (n : ℕ) :
    (tentCapacity + (43/25 : ℝ)*n)^2 ≥ (72/25 : ℝ)*n*(n+1) := by
  rcases lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num [tentCapacity]
  · have hn : (3 : ℝ) ≤ n := by exact_mod_cast h
    have hs := sq_nonneg ((n : ℝ)-3)
    dsimp [tentCapacity]
    nlinarith only [hn, hs]

theorem tent_capacity_algebra (n : ℕ) (Q S J : ℝ)
    (hQ : (n : ℝ) ≤ Q) (hS : 0 ≤ S)
    (hsep : (n : ℝ)*((n : ℝ)-1)+2*S^2 ≤ 2*n*Q)
    (hJ : J ≤ (3/5 : ℝ)*S) :
    (n : ℝ)-2*Q-(18/25 : ℝ)*n+4*J ≤ tentCapacity := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hC := tent_capacity_positive.le
  have hp := tent_integer_comparison n
  have hq : 0 ≤ Q-n := sub_nonneg.mpr hQ
  have hcross : 0 ≤ (Q-n)*(tentCapacity+(7/25 : ℝ)*n) :=
    mul_nonneg hq (by positivity)
  have hq2 := sq_nonneg (Q-n)
  have hA : 0 ≤ tentCapacity+2*Q-(7/25 : ℝ)*n := by linarith
  have hsq : ((12/5 : ℝ)*S)^2 ≤ (tentCapacity+2*Q-(7/25 : ℝ)*n)^2 := by
    nlinarith
  have hroot : (12/5 : ℝ)*S ≤ tentCapacity+2*Q-(7/25 : ℝ)*n := by
    nlinarith
  linarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem refined_tent_capacity (X : Finset V) (hsep : UnitSep X)
    (hX : ∀ x ∈ X, 1 ≤ ‖x‖) (c : V) (hc : ‖c‖ = 3/5) :
    ∑ x ∈ X, capP ‖x-c‖ ≤ tentCapacity := by
  classical
  simp only [capP_eq]
  rw [← Finset.sum_filter]
  let W := X.filter fun x => 2*‖x-c‖^2 < 1
  have hWX : W ⊆ X := Finset.filter_subset _ _
  have hW : UnitSep W := hsep.mono hWX
  have hQ : (W.card : ℝ) ≤ ∑ x ∈ W, ‖x‖^2 := by
    calc (W.card : ℝ) = ∑ _x ∈ W, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun x hx => by nlinarith [hX x (hWX hx)]
  have hJ : ⟪∑ x ∈ W, x, c⟫ ≤ (3/5 : ℝ)*‖∑ x ∈ W, x‖ := by
    calc ⟪∑ x ∈ W, x, c⟫ ≤ |⟪∑ x ∈ W, x, c⟫| := le_abs_self _
      _ ≤ ‖∑ x ∈ W, x‖*‖c‖ := abs_real_inner_le_norm _ _
      _ = _ := by rw [hc]; ring
  have halg := tent_capacity_algebra W.card (∑ x ∈ W, ‖x‖^2)
    ‖∑ x ∈ W, x‖ ⟪∑ x ∈ W, x, c⟫ hQ (norm_nonneg _) (sep_quadratic W hW) hJ
  have he : (∑ x ∈ W, (1-2*‖x-c‖^2)) =
      (W.card : ℝ)-2*(∑ x ∈ W, ‖x‖^2)-(18/25 : ℝ)*W.card+4*⟪∑ x ∈ W, x, c⟫ := by
    simp only [norm_sub_sq_real, hc, mul_add, mul_sub, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Finset.mul_sum, ← sum_inner]
    ring
  change (∑ x ∈ W, (1-2*‖x-c‖^2)) ≤ tentCapacity
  rw [he]
  exact halg

end D4Bound.Components
