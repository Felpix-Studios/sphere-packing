import D4Bound.V7CensusGramOriginCheck0
import D4Bound.V7CensusGramOriginCheck1
import D4Bound.V7CensusGramOriginCheck2
import D4Bound.V7CensusGramOriginCheck3
import D4Bound.V7CensusGramOriginCheck4
import D4Bound.V7CensusGramOriginCheck5
import D4Bound.V7CensusGramOriginCheck6
import D4Bound.V7GramEnergy

namespace D4Bound.V7.CensusGram
open Finset
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem origin_rows_checked (k : ℕ) (hk : k < 49) : originRowOK k = true := by
  interval_cases k
  · exact origin_row_0
  · exact origin_row_1
  · exact origin_row_2
  · exact origin_row_3
  · exact origin_row_4
  · exact origin_row_5
  · exact origin_row_6
  · exact origin_row_7
  · exact origin_row_8
  · exact origin_row_9
  · exact origin_row_10
  · exact origin_row_11
  · exact origin_row_12
  · exact origin_row_13
  · exact origin_row_14
  · exact origin_row_15
  · exact origin_row_16
  · exact origin_row_17
  · exact origin_row_18
  · exact origin_row_19
  · exact origin_row_20
  · exact origin_row_21
  · exact origin_row_22
  · exact origin_row_23
  · exact origin_row_24
  · exact origin_row_25
  · exact origin_row_26
  · exact origin_row_27
  · exact origin_row_28
  · exact origin_row_29
  · exact origin_row_30
  · exact origin_row_31
  · exact origin_row_32
  · exact origin_row_33
  · exact origin_row_34
  · exact origin_row_35
  · exact origin_row_36
  · exact origin_row_37
  · exact origin_row_38
  · exact origin_row_39
  · exact origin_row_40
  · exact origin_row_41
  · exact origin_row_42
  · exact origin_row_43
  · exact origin_row_44
  · exact origin_row_45
  · exact origin_row_46
  · exact origin_row_47
  · exact origin_row_48

theorem origin_coefficients (k : ℕ) (hk : k < 49) :
    (gramRays0.map fun ray => ray.weight/gramDenominator*originOffsetQ ray*
      ray.vector.getD k 0).sum = originVector.getD k 0 := by
  exact of_decide_eq_true (origin_rows_checked k hk)

theorem cast_list_sum {α : Type*} (L : List α) (f : α → ℚ) :
    ((L.map f).sum : ℝ) = (L.map fun a => (f a : ℝ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem origin_constant :
    (gramRays0.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ)*
      (originOffset ray)^2).sum = (gramOrigin : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) origin_constant_checked
  rw [cast_list_sum] at h
  simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, originOffset] using h

theorem origin_radial {r : ℝ} (hr : r ≤ 7/4) :
    (gramRays0.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ)*
      originOffset ray*radialValue ray.vector r).sum = radialValue originVector r := by
  have h := radialValue_combination gramRays0
    (fun ray => ray.weight/gramDenominator*originOffsetQ ray)
    Ray.vector originVector origin_coefficients hr
  simpa only [Rat.cast_mul, Rat.cast_div, originOffset] using h

theorem gram_energy_ge_origin_squares (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) :
    (gramRays0.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ)*
      (originOffset ray + ∑ x ∈ X, radialValue ray.vector ‖x‖)^2).sum ≤ gramEnergy X :=
  gram_energy_ge_ray_squares originOffset X hX origin_constant
    (fun x hx => origin_radial (hR x hx))

end
end D4Bound.V7.CensusGram
