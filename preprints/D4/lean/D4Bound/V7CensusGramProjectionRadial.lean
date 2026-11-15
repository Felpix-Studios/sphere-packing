import D4Bound.V7CensusGramProjectionRange
import D4Bound.V7CensusGramProjectionGeometry
namespace D4Bound.V7.CensusGram
noncomputable section
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem projectionTarget_radial (j : ℕ) {r : ℝ} (hr : r ≤ 7/4) :
    radialValue (projectionTargetQ j) r =
      ((List.range 5).map fun l => (projectionGramQ l j : ℝ)*
        indicator (breaks.getD (l+1) 0) r).sum := by
  let c : ℚ := ((List.range 5).map fun l =>
    if radialPiece r ≤ l then projectionGramQ l j else 0).sum
  have he : radialValue (projectionTargetQ j) r = (c : ℝ) := by
    unfold radialValue
    have hterm : ∀ i ∈ List.range 7, (projectionTargetQ j).getD (7*radialPiece r+i) 0 = c := by
      intro i hi
      have hilt := List.mem_range.mp hi
      have hp := radialPiece_lt_seven hr
      rw [projectionTargetQ_get j _ (by omega)]
      have he : (7*radialPiece r+i)/7 = radialPiece r := by omega
      rw [he]
    calc
      _ = ((List.range 7).map fun i => (c : ℝ)*basisValue (radialPiece r) i r).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro i hi
        rw [hterm i hi]
      _ = c := by rw [List.sum_map_mul_left,basisValue_sum,mul_one]
  rw [he]
  dsimp only [c]
  rw [cast_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  have hiff := radialPiece_le_countRadius hr l (List.mem_range.mp hl)
  by_cases h : radialPiece r ≤ l
  · rw [if_pos h,indicator,if_pos (hiff.mp h),mul_one]
  · rw [if_neg h,indicator,if_neg (fun hh => h (hiff.mpr hh)),mul_zero,Rat.cast_zero]

theorem projection_range_radial (j : ℕ) (hj : j < 5) {r : ℝ} (hr : r ≤ 7/4) :
    ((List.range 34).map fun i => (projectionWeightQ i : ℝ)*(projectionDualQ i j : ℝ)*
      radialValue (ray i).vector r).sum =
      ((List.range 5).map fun l => (projectionGramQ l j : ℝ)*
        indicator (breaks.getD (l+1) 0) r).sum := by
  have h := radialValue_combination (List.range 34)
    (fun i => projectionWeightQ i*projectionDualQ i j) (fun i => (ray i).vector)
    (projectionTargetQ j) (fun k hk => projection_range_coeff k j hk hj) hr
  simpa only [Rat.cast_mul,projectionTarget_radial j hr] using h

end
end D4Bound.V7.CensusGram
