import D4Bound.V7CensusGramProjectionBasic
import D4Bound.V7CensusGramProjectionRadial
namespace D4Bound.V7.CensusGram
noncomputable section
open Finset Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem fin5_sum (f : ℕ → ℝ) : (∑ j : Fin 5, f j) = ((List.range 5).map f).sum := by
  simp [Fin.sum_univ_succ,List.range_succ]

theorem projection_gram_symm (j k : ℕ) (hj : j < 5) (hk : k < 5) :
    projectionGramQ j k = projectionGramQ k j := by
  rw [← projection_inverse_coeff j k hj hk,← projection_inverse_coeff k j hk hj]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  ring

def projectionCounts (X : Finset E4) (j : ℕ) : ℝ :=
  (countWithin X ((breaks.getD (j+1) 0 : ℚ) : ℝ) : ℝ) + (projectionOffsetQ j : ℝ)

def projectionOriginOK (j : ℕ) : Prop :=
  ((List.range 34).map fun i => projectionWeightQ i*originOffsetQ (ray i)*
    projectionDualQ i j).sum =
  ((List.range 5).map fun k => projectionGramQ j k*projectionOffsetQ k).sum

instance (j : ℕ) : Decidable (projectionOriginOK j) := inferInstanceAs (Decidable (_ = _))

theorem projection_cross (j : ℕ) (hj : j < 5) (ho : projectionOriginOK j)
    (X : Finset E4) (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) :
    ((List.range 34).map fun i => (projectionWeightQ i : ℝ)*
      (originOffset (ray i) + ∑ x ∈ X, radialValue (ray i).vector ‖x‖)*
      (projectionDualQ i j : ℝ)).sum =
    ∑ k : Fin 5, (projectionGramQ j k : ℝ)*projectionCounts X k := by
  have ho' := congrArg (fun q : ℚ => (q : ℝ)) ho
  simp only [cast_list_sum,Rat.cast_mul] at ho'
  change ((List.range 34).map fun i => (projectionWeightQ i : ℝ)*originOffset (ray i)*
    (projectionDualQ i j : ℝ)).sum =
    ((List.range 5).map fun k => (projectionGramQ j k : ℝ)*(projectionOffsetQ k : ℝ)).sum at ho'
  have hr : ((List.range 34).map fun i => (projectionWeightQ i : ℝ)*
      (∑ x ∈ X, radialValue (ray i).vector ‖x‖)*(projectionDualQ i j : ℝ)).sum =
      ((List.range 5).map fun k => (projectionGramQ j k : ℝ)*
        (countWithin X ((breaks.getD (k+1) 0 : ℚ) : ℝ) : ℝ)).sum := by
    have he : ∀ i, (projectionWeightQ i : ℝ)*
        (∑ x ∈ X, radialValue (ray i).vector ‖x‖)*(projectionDualQ i j : ℝ) =
        ∑ x ∈ X, (projectionWeightQ i : ℝ)*(projectionDualQ i j : ℝ)*
          radialValue (ray i).vector ‖x‖ := by
      intro i
      rw [← Finset.mul_sum]
      ring
    simp_rw [he]
    rw [← sum_list_map]
    have hrad : (∑ x ∈ X, ((List.range 34).map fun i =>
        (projectionWeightQ i : ℝ)*(projectionDualQ i j : ℝ)*
          radialValue (ray i).vector ‖x‖).sum) =
        ∑ x ∈ X, ((List.range 5).map fun k => (projectionGramQ k j : ℝ)*
          indicator (breaks.getD (k+1) 0) ‖x‖).sum :=
      Finset.sum_congr rfl fun x hx => projection_range_radial j hj (hR x hx)
    rw [hrad]
    rw [sum_list_map]
    simp_rw [← Finset.mul_sum,indicator_sum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    rw [projection_gram_symm k j (List.mem_range.mp hk) hj]
  simp_rw [mul_add,add_mul]
  rw [List.sum_map_add,ho',hr,
    fin5_sum (fun k => (projectionGramQ j k : ℝ)*projectionCounts X k)]
  rw [← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  unfold projectionCounts
  ring

theorem projection_energy_of_origin
    (ho : ∀ j, j < 5 → projectionOriginOK j)
    (X : Finset E4) (hX : (0 : E4) ∉ X) (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) :
    (∑ j : Fin 5, ∑ k : Fin 5, projectionCounts X j *
      (projectionGramQ j k : ℝ)*projectionCounts X k) ≤ gramEnergy X := by
  have hw : ∀ i ∈ List.range 34, 0 ≤ (projectionWeightQ i : ℝ) := by
    intro i hi
    have hr : ray i ∈ gramRays0 := by
      rw [← gramRays0_range]
      exact List.mem_map.mpr ⟨i,hi,rfl⟩
    have h := gram_weights_nonneg gramRays0 (by simp [gramRays]) (ray i) hr
    simpa only [projectionWeightQ,Rat.cast_div] using
      div_nonneg (Rat.cast_nonneg.mpr h) gramDenominator_pos.le
  have hG : ∀ j k : Fin 5,
      ((List.range 34).map fun i => (projectionWeightQ i : ℝ)*
        (projectionDualQ i j : ℝ)*(projectionDualQ i k : ℝ)).sum =
        (projectionGramQ j k : ℝ) := by
    intro j k
    have h := congrArg (fun q : ℚ => (q : ℝ))
      (projection_inverse_coeff j k j.isLt k.isLt)
    simpa only [cast_list_sum,Rat.cast_mul] using h
  have h := weighted_projection_bound (List.range 34)
    (fun i => (projectionWeightQ i : ℝ))
    (fun i => originOffset (ray i)+∑ x ∈ X, radialValue (ray i).vector ‖x‖)
    (fun (i : ℕ) (j : Fin 5) => (projectionDualQ i j : ℝ))
    (fun j k : Fin 5 => (projectionGramQ j k : ℝ))
    (fun j : Fin 5 => projectionCounts X j) hw
    (fun j => projection_cross j j.isLt (ho j j.isLt) X hR) hG
  have he : ((List.range 34).map fun i => (projectionWeightQ i : ℝ)*
      (originOffset (ray i)+∑ x ∈ X, radialValue (ray i).vector ‖x‖)^2).sum =
      (gramRays0.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ)*
        (originOffset ray+∑ x ∈ X, radialValue ray.vector ‖x‖)^2).sum := by
    rw [← gramRays0_range,List.map_map]
    simp only [Function.comp_def,projectionWeightQ,Rat.cast_div]
  rw [he] at h
  exact h.trans (gram_energy_ge_origin_squares X hX hR)

end
end D4Bound.V7.CensusGram
