import D4Bound.V7CapsNonneg
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Average the proved pointwise occupancy bound. The marginal identification
is an explicit premise of this interface, not an axiom or a completed proof
of the nondegenerate spherical probability formula. -/
open Finset MeasureTheory
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

/-- A closed-ball membership indicator in the space of probe centres. -/
def probeIndicator (c : Cap) (x p : E4) : ℝ :=
  if ‖x-p‖^2 ≤ (c.a2 : ℝ) then 1 else 0

theorem probeIndicator_sum_le {c : Cap} (hc : CapValid c)
    {X : Finset E4} (hX : Admissible X) {p : E4} (hp : ‖p‖ = (c.d : ℝ)) :
    ∑ x ∈ X, probeIndicator c x p ≤ (c.multiplicity : ℝ) := by
  have h := cap_nonorigin_ball_count hc hX p hp
  rw [Finset.card_filter] at h
  push_cast at h
  exact h

/-- The probe centres may be parametrized by any probability space. -/
theorem cap_capacity_of_parametrized_measure {Ω : Type*} [MeasurableSpace Ω]
    {c : Cap} (hc : CapValid c)
    (hmeasure : ∀ y : E4, y ≠ 0 → ∃ (μ : Measure Ω) (p : Ω → E4),
      IsProbabilityMeasure μ ∧
      (∀ᵐ u ∂μ, ‖p u‖ = (c.d : ℝ)) ∧
      (∀ x : E4, x ≠ 0 → Integrable (fun u => probeIndicator c x (p u)) μ) ∧
      (∀ x : E4, x ≠ 0 → capProbability c ‖x‖ (⟪x,y⟫/(‖x‖*‖y‖)) =
        ∫ u, probeIndicator c x (p u) ∂μ)) : CapProbabilityCapacity c := by
  intro X hX y hy
  obtain ⟨μ,p,hprob,hnorm,hint,heq⟩ := hmeasure y hy
  letI : IsProbabilityMeasure μ := hprob
  have hn : ∀ x ∈ X, x ≠ 0 := by
    intro x hx he
    have h := hX.1 x hx
    rw [he, norm_zero] at h
    norm_num at h
  have hi : Integrable (fun u => ∑ x ∈ X, probeIndicator c x (p u)) μ :=
    integrable_finsetSum X fun x hx => hint x (hn x hx)
  have he : (∑ x ∈ X, capProbability c ‖x‖ (⟪x,y⟫/(‖x‖*‖y‖))) =
      ∫ u, ∑ x ∈ X, probeIndicator c x (p u) ∂μ := by
    rw [integral_finsetSum X (fun x hx => hint x (hn x hx))]
    exact Finset.sum_congr rfl fun x hx => heq x (hn x hx)
  rw [he]
  calc
    (∫ u, ∑ x ∈ X, probeIndicator c x (p u) ∂μ) ≤
        (∫ _u, (c.multiplicity : ℝ) ∂μ) := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [hnorm] with u hu
      exact probeIndicator_sum_le hc hX hu
    _ = (c.multiplicity : ℝ) := by simp

/-- A probability measure with the declared marginals turns the geometric
ball count into the cap probability capacity. -/
theorem cap_capacity_of_probability_measure {c : Cap} (hc : CapValid c)
    (hmeasure : ∀ y : E4, y ≠ 0 → ∃ μ : Measure E4,
      IsProbabilityMeasure μ ∧
      (∀ᵐ p ∂μ, ‖p‖ = (c.d : ℝ)) ∧
      (∀ x : E4, x ≠ 0 → Integrable (probeIndicator c x) μ) ∧
      (∀ x : E4, x ≠ 0 → capProbability c ‖x‖ (⟪x,y⟫/(‖x‖*‖y‖)) =
        ∫ p, probeIndicator c x p ∂μ)) : CapProbabilityCapacity c := by
  intro X hX y hy
  obtain ⟨μ,hprob,hnorm,hint,heq⟩ := hmeasure y hy
  letI : IsProbabilityMeasure μ := hprob
  have hn : ∀ x ∈ X, x ≠ 0 := by
    intro x hx he
    have h := hX.1 x hx
    rw [he, norm_zero] at h
    norm_num at h
  have hi : Integrable (fun p => ∑ x ∈ X, probeIndicator c x p) μ :=
    integrable_finsetSum X fun x hx => hint x (hn x hx)
  have he : (∑ x ∈ X, capProbability c ‖x‖ (⟪x,y⟫/(‖x‖*‖y‖))) =
      ∫ p, ∑ x ∈ X, probeIndicator c x p ∂μ := by
    rw [integral_finsetSum X (fun x hx => hint x (hn x hx))]
    exact Finset.sum_congr rfl fun x hx => heq x (hn x hx)
  rw [he]
  calc
    (∫ p, ∑ x ∈ X, probeIndicator c x p ∂μ) ≤ (∫ _p, (c.multiplicity : ℝ) ∂μ) := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [hnorm] with p hp
      exact probeIndicator_sum_le hc hX hp
    _ = (c.multiplicity : ℝ) := by simp

end
end D4Bound.V7
