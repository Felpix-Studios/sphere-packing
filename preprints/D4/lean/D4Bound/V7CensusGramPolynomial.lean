import D4Bound.V7CensusGramPolynomialCheck0
import D4Bound.V7CensusGramPolynomialCheck1
import D4Bound.V7CensusGramPolynomialCheck2
import D4Bound.V7CensusGramPolynomialCheck3
import D4Bound.V7CensusGramPolynomialOrigin0
import D4Bound.V7CensusGramPolynomialOrigin1
import D4Bound.V7CensusGramPolynomialOrigin2
import D4Bound.V7CensusGramPolynomialOrigin3
import D4Bound.V7CensusGramPolynomialOrigin4

/-! Exact projection coefficients and origin/dual crossings, interpreted over reals. -/
namespace D4Bound.V7.CensusGram
open CensusArithmetic
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem projection_origin_cross (j : ℕ) (hj : j < 5) :
    ((List.range 34).map fun a => projectionWeightQ a *
      originOffsetQ (ray a) * projectionDualQ a j).sum =
    ((List.range 5).map fun k => projectionGramQ j k * projectionOffsetQ k).sum := by
  interval_cases j
  · exact projection_origin_cross_0
  · exact projection_origin_cross_1
  · exact projection_origin_cross_2
  · exact projection_origin_cross_3
  · exact projection_origin_cross_4

theorem projection_coefficients_checked (i : ℕ) (hi : i < 21) :
    projectionCoefficients projectionGramQ projectionOffsetQ i =
      ((totalCoeffs[i]! : ℚ)-(countCoeffs[i]! : ℚ))/(denominator : ℚ) := by
  interval_cases i
  · exact projection_coefficient_0
  · exact projection_coefficient_1
  · exact projection_coefficient_2
  · exact projection_coefficient_3
  · exact projection_coefficient_4
  · exact projection_coefficient_5
  · exact projection_coefficient_6
  · exact projection_coefficient_7
  · exact projection_coefficient_8
  · exact projection_coefficient_9
  · exact projection_coefficient_10
  · exact projection_coefficient_11
  · exact projection_coefficient_12
  · exact projection_coefficient_13
  · exact projection_coefficient_14
  · exact projection_coefficient_15
  · exact projection_coefficient_16
  · exact projection_coefficient_17
  · exact projection_coefficient_18
  · exact projection_coefficient_19
  · exact projection_coefficient_20

theorem projection_gram_symmetric : ∀ j k : Fin 5,
    projectionGramQ j.val k.val = projectionGramQ k.val j.val := by decide +kernel

theorem projection_coefficients_cast (i : ℕ) (hi : i < 21) :
    ((projectionCoefficients projectionGramQ projectionOffsetQ i : ℚ) : ℝ) =
      projectionCoefficients (fun j k => (projectionGramQ j k : ℝ))
        (fun j => (projectionOffsetQ j : ℝ)) i := by
  interval_cases i <;>
    simp only [projectionCoefficients,List.getD_cons_zero,List.getD_cons_succ,
      matrixProjection,cast_list_sum,Rat.cast_add,Rat.cast_mul,Rat.cast_zero]

theorem projection_polynomial_identity (v : Counts) :
    matrixProjection (fun j k => (projectionGramQ j k : ℝ))
      (fun j => (projectionOffsetQ j : ℝ)) (fun j => (countsAt v j : ℝ)) =
      projectionPart v := by
  rw [matrixProjection_expand _ _ _ (fun j k hj hk =>
    congrArg (fun q : ℚ => (q : ℝ)) (projection_gram_symmetric ⟨j,hj⟩ ⟨k,hk⟩)),
    projectionPart_eval]
  apply projectionEval_congr
  intro i hi
  rw [← projection_coefficients_cast i hi]
  have h := congrArg (fun q : ℚ => (q : ℝ)) (projection_coefficients_checked i hi)
  simpa only [Rat.cast_div,Rat.cast_sub,Rat.cast_intCast] using h

end
end D4Bound.V7.CensusGram

#print axioms D4Bound.V7.CensusGram.projection_origin_cross
#print axioms D4Bound.V7.CensusGram.projection_polynomial_identity
