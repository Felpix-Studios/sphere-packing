import D4Bound.V7CensusGramProjectionData
import Mathlib.Data.List.GetD
namespace D4Bound.V7.CensusGram
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem projectionTargetQ_get (j k : ℕ) (hk : k < 49) :
    (projectionTargetQ j).getD k 0 =
      ((List.range 5).map fun l => if k/7 ≤ l then projectionGramQ l j else 0).sum := by
  rw [List.getD_eq_getElem (projectionTargetQ j) 0 (by simpa [projectionTargetQ] using hk)]
  simp [projectionTargetQ]

theorem list_sum_div_q {α : Type*} (L : List α) (f : α → ℚ) (d : ℚ) :
    (L.map fun i => f i/d).sum = (L.map f).sum/d := by
  simp only [div_eq_mul_inv,List.sum_map_mul_right]

theorem projection_range_coeff (k j : ℕ) (hk : k < 49) (hj : j < 5) :
    ((List.range 34).map fun i => projectionWeightQ i*projectionDualQ i j*
      (ray i).vector.getD k 0).sum = (projectionTargetQ j).getD k 0 := by
  have hg : (gramDen : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt den_pos.1)
  have hd : (dualDen : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt den_pos.2.1)
  have hi : (inverseDen : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt den_pos.2.2.1)
  rw [projectionTargetQ_get j k hk]
  have he : ((List.range 34).map fun i => projectionWeightQ i*projectionDualQ i j*
      (ray i).vector.getD k 0).sum =
      (((List.range 34).map fun i => rayWeights[i]!*(rayVectors[i]!)[k]!*(dualNums[i]!)[j]!).sum : ℤ) /
      ((gramDen : ℚ)*(dualDen : ℚ)) := by
    rw [Int.cast_list_sum,List.map_map]
    rw [← list_sum_div_q]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi'
    have hilt := List.mem_range.mp hi'
    simp only [Function.comp_apply,Int.cast_mul]
    rw [ray_weight_checked i hilt,ray_vector_checked i k hilt hk,gram_den_checked]
    unfold projectionWeightQ projectionDualQ
    ring
  have he' : ((List.range 5).map fun l => if k/7 ≤ l then projectionGramQ l j else 0).sum =
      (((List.range 5).map fun l => if k/7 ≤ l then (inverseNums[l]!)[j]! else 0).sum : ℤ) /
      (inverseDen : ℚ) := by
    rw [Int.cast_list_sum,List.map_map,← list_sum_div_q]
    apply congrArg List.sum
    apply List.map_congr_left
    intro l hl
    simp only [Function.comp_apply,projectionGramQ]
    split_ifs <;> simp
  rw [he,he']
  apply (div_eq_div_iff (mul_ne_zero hg hd) hi).mpr
  have h := congrArg (fun z : ℤ => (z : ℚ)) (range_integer k j hk hj)
  simpa only [Int.cast_mul,mul_comm,mul_left_comm,mul_assoc] using h

theorem projection_inverse_coeff (j k : ℕ) (hj : j < 5) (hk : k < 5) :
    ((List.range 34).map fun i => projectionWeightQ i*projectionDualQ i j*
      projectionDualQ i k).sum = projectionGramQ j k := by
  have hg : (gramDen : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt den_pos.1)
  have hd : (dualDen : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt den_pos.2.1)
  have hi : (inverseDen : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt den_pos.2.2.1)
  have he : ((List.range 34).map fun i => projectionWeightQ i*projectionDualQ i j*
      projectionDualQ i k).sum =
      (((List.range 34).map fun i => rayWeights[i]!*(dualNums[i]!)[j]!*(dualNums[i]!)[k]!).sum : ℤ) /
      ((gramDen : ℚ)*(dualDen : ℚ)^2) := by
    rw [Int.cast_list_sum,List.map_map,← list_sum_div_q]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi'
    have hilt := List.mem_range.mp hi'
    simp only [Function.comp_apply,Int.cast_mul]
    rw [ray_weight_checked i hilt,gram_den_checked]
    unfold projectionWeightQ projectionDualQ
    ring
  rw [he,projectionGramQ]
  apply (div_eq_div_iff (mul_ne_zero hg (pow_ne_zero _ hd)) hi).mpr
  have h := congrArg (fun z : ℤ => (z : ℚ)) (inverse_integer j k hj hk)
  simpa only [Int.cast_mul,Int.cast_pow,mul_comm,mul_left_comm,mul_assoc] using h

end
end D4Bound.V7.CensusGram
