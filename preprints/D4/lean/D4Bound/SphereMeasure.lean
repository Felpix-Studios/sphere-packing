import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! Measure-theoretic ingredients for pointed-cap averaging. -/
open MeasureTheory Set Finset
open scoped ENNReal RealInnerProductSpace

namespace D4Bound.SphereMeasure
noncomputable section
open Classical

/-- Averaging a finite pointwise occupancy bound over a probability space.
The events may overlap; the bound counts every event with its multiplicity. -/
theorem sum_event_probabilities_le {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) (M : ℕ)
    (hcount : ∀ ω, (s.filter fun i => ω ∈ A i).card ≤ M) :
    ∑ i ∈ s, μ.real (A i) ≤ M := by
  have hi : ∀ i ∈ s, Integrable ((A i).indicator (fun _ : Ω => (1 : ℝ))) μ :=
    fun i hi => (integrable_const (1 : ℝ)).indicator (hA i hi)
  have hsum : (∫ ω, ∑ i ∈ s, (A i).indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ) =
      ∑ i ∈ s, μ.real (A i) := by
    rw [integral_finsetSum s hi]
    apply Finset.sum_congr rfl
    intro i hi
    simpa using integral_indicator_const (μ := μ) (1 : ℝ) (hA i hi)
  rw [← hsum]
  have hpoint : ∀ ω, (∑ i ∈ s, (A i).indicator (fun _ : Ω => (1 : ℝ)) ω) ≤ (M : ℝ) := by
    intro ω
    have he : (∑ i ∈ s, (A i).indicator (fun _ : Ω => (1 : ℝ)) ω) =
        ((s.filter fun i => ω ∈ A i).card : ℝ) := by
      simp only [Set.indicator, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero]
    rw [he]
    exact_mod_cast hcount ω
  simpa using integral_mono (integrable_finsetSum s hi)
    (integrable_const (M : ℝ)) hpoint

def clip (x : ℝ) : ℝ := max 0 (min 1 x)

/-- The uniform probability measure on the closed interval `[-1,1]`. -/
def uniformInterval : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • volume.restrict (Icc (-1) 1)

instance : IsProbabilityMeasure uniformInterval := by
  constructor
  norm_num [uniformInterval, Measure.smul_apply, Measure.restrict_apply,
    Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- Closed upper-tail probability, including both endpoints and exterior values. -/
theorem uniformInterval_Ici (a : ℝ) :
    uniformInterval.real (Ici a) = clip ((1-a)/2) := by
  have he : Ici a ∩ Icc (-1 : ℝ) 1 = Icc (max a (-1)) 1 := by
    ext x
    simp only [mem_inter_iff,Set.mem_Ici,Set.mem_Icc,max_le_iff]
    tauto
  rw [uniformInterval,measureReal_ennreal_smul_apply,
    measureReal_restrict_apply measurableSet_Ici,he,Real.volume_real_Icc]
  norm_num only [ENNReal.toReal_inv,ENNReal.toReal_ofNat]
  unfold clip
  rcases le_total a (-1) with h | h
  · rw [max_eq_right h,max_eq_left (by norm_num),min_eq_left (by linarith),
      max_eq_right (by norm_num)]
    norm_num
  · rw [max_eq_left h]
    rcases le_total a 1 with h1 | h1
    · rw [max_eq_left (by linarith),min_eq_right (by linarith),
        max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith),min_eq_right (by linarith),
        max_eq_left (by linarith)]
      ring

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev UnitSphere := Metric.sphere (0 : R3) 1

/-- Surface area measure from radial disintegration of three-dimensional volume. -/
def area : Measure UnitSphere := (volume : Measure R3).toSphere

instance : IsFiniteMeasure area :=
  inferInstanceAs (IsFiniteMeasure (volume : Measure R3).toSphere)

theorem area_univ_ne_zero : area univ ≠ 0 := by
  exact (Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero (volume : Measure R3)))

/-- A fixed common probability measure for all cap directions. -/
def uniformSphere : Measure UnitSphere := (area univ)⁻¹ • area

instance : IsProbabilityMeasure uniformSphere := by
  constructor
  rw [uniformSphere,Measure.smul_apply,smul_eq_mul,
    ENNReal.inv_mul_cancel area_univ_ne_zero (measure_ne_top area univ)]

end
end D4Bound.SphereMeasure
