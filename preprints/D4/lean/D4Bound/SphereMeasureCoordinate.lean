import D4Bound.SphereMeasureCone
import D4Bound.SphereMeasureSector

/-! Volume-preserving coordinates and algebra of the conical sector. -/
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace D4Bound.SphereMeasure
noncomputable section
open Classical

def pole : R3 := EuclideanSpace.single 0 1

theorem norm_pole : ‖pole‖ = 1 := by simp [pole]

theorem inner_pole (x : R3) : ⟪x,pole⟫ = x 0 := by
  simp [pole, EuclideanSpace.inner_single_right]

def split (x : R3) : ℝ × R2 := (x 0, WithLp.toLp 2 (fun i : Fin 2 => x i.succ))

theorem split_measurePreserving : MeasurePreserving split := by
  have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))
  convert h using 1
  · ext x i <;>
    simp [split, Function.comp_def, MeasurableEquiv.piFinSuccAbove,
      Fin.insertNthEquiv, Fin.succAbove_zero, Fin.tail]
  · rfl

theorem split_norm_sq (x : R3) : ‖x‖^2 = (split x).1^2 + ‖(split x).2‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, split, Fin.sum_univ_succ,
    PiLp.toLp_apply]

theorem openSector_volume_eq_closed (v : R3) (a : ℝ) :
    volume (openSector v a) = volume (closedSector v a) := by
  apply measure_congr
  have h0 : ∀ᵐ x : R3 ∂volume, x ≠ 0 := by
    simpa only [ae_iff, not_not, Set.setOf_eq_eq_singleton] using
      (measure_singleton (0 : R3) : volume ({0} : Set R3) = 0)
  have h1 : ∀ᵐ x : R3 ∂volume, ‖x‖ ≠ 1 := by
    have h : volume (Metric.sphere (0 : R3) 1) = 0 := Measure.addHaar_sphere volume _ _
    simpa only [ae_iff, not_not, Metric.sphere, dist_zero_right] using h
  filter_upwards [h0,h1] with x hx0 hx1
  apply propext
  change (0 < ‖x‖ ∧ ‖x‖ < 1 ∧ a*‖x‖ ≤ ⟪x,v⟫) ↔
    (‖x‖ ≤ 1 ∧ a*‖x‖ ≤ ⟪x,v⟫)
  constructor
  · exact fun h => ⟨h.2.1.le,h.2.2⟩
  · exact fun h => ⟨norm_pos_iff.mpr hx0,lt_of_le_of_ne h.1 hx1,h.2⟩

end
end D4Bound.SphereMeasure
