import D4Bound.V7CapsTransport
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Convert measurable spherical tail probabilities to the integral interface. -/
open MeasureTheory
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

theorem transverseLaw_of_tail {e : E4} (μ : Measure E4) [IsProbabilityMeasure μ]
    (hsupport : ∀ᵐ u ∂μ, ‖u‖ = 1 ∧ ⟪e,u⟫ = 0)
    (htail : ∀ z : E4, z ≠ 0 → ⟪z,e⟫ = 0 → ∀ a : ℝ,
      μ.real {u | a ≤ ⟪z,u⟫} = max 0 (min 1 ((1-a/‖z‖)/2))) :
    TransverseLaw e μ := by
  refine ⟨hsupport, ?_⟩
  intro z hz hze a
  have hm : MeasurableSet {u : E4 | a ≤ ⟪z,u⟫} :=
    (isClosed_le continuous_const (continuous_const.inner continuous_id)).measurableSet
  have hi : Integrable ({u : E4 | a ≤ ⟪z,u⟫}.indicator (fun _ : E4 => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hm
  have he : ({u : E4 | a ≤ ⟪z,u⟫}.indicator (fun _ : E4 => (1 : ℝ))) =
      (fun u => if a ≤ ⟪z,u⟫ then (1 : ℝ) else 0) := rfl
  rw [he] at hi
  refine ⟨hi, ?_⟩
  rw [← he]
  simpa using (integral_indicator_const (μ := μ) (1 : ℝ) hm).trans
    (by simpa using htail z hz hze a)

theorem transverseLaw_of_unit_tail {e : E4} (μ : Measure E4) [IsProbabilityMeasure μ]
    (hsupport : ∀ᵐ u ∂μ, ‖u‖ = 1 ∧ ⟪e,u⟫ = 0)
    (htail : ∀ z : E4, ‖z‖ = 1 → ⟪z,e⟫ = 0 → ∀ a : ℝ,
      μ.real {u | a ≤ ⟪z,u⟫} = max 0 (min 1 ((1-a)/2))) :
    TransverseLaw e μ := by
  apply transverseLaw_of_tail μ hsupport
  intro z hz hze a
  have ho : ⟪dir z,e⟫ = 0 := by simp only [dir, real_inner_smul_left, hze, mul_zero]
  have he : {u : E4 | a ≤ ⟪z,u⟫} = {u : E4 | a/‖z‖ ≤ ⟪dir z,u⟫} := by
    ext u
    simp only [Set.mem_setOf_eq, dir, real_inner_smul_left]
    rw [mul_comm ‖z‖⁻¹, ← div_eq_mul_inv,
      div_le_div_iff_of_pos_right (norm_pos_iff.mpr hz)]
  rw [he]
  exact htail (dir z) (norm_dir hz) ho (a/‖z‖)

end
end D4Bound.V7
