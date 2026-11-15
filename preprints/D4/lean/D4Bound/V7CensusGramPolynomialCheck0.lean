import D4Bound.V7CensusGramProjectionData
import D4Bound.V7CensusGramPolynomialBasic
namespace D4Bound.V7.CensusGram
open CensusArithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem projection_coefficient_0 :
    projectionCoefficients projectionGramQ projectionOffsetQ 0 =
    ((totalCoeffs[0]! : ℚ)-(countCoeffs[0]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_1 :
    projectionCoefficients projectionGramQ projectionOffsetQ 1 =
    ((totalCoeffs[1]! : ℚ)-(countCoeffs[1]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_2 :
    projectionCoefficients projectionGramQ projectionOffsetQ 2 =
    ((totalCoeffs[2]! : ℚ)-(countCoeffs[2]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_3 :
    projectionCoefficients projectionGramQ projectionOffsetQ 3 =
    ((totalCoeffs[3]! : ℚ)-(countCoeffs[3]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_4 :
    projectionCoefficients projectionGramQ projectionOffsetQ 4 =
    ((totalCoeffs[4]! : ℚ)-(countCoeffs[4]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_5 :
    projectionCoefficients projectionGramQ projectionOffsetQ 5 =
    ((totalCoeffs[5]! : ℚ)-(countCoeffs[5]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
end D4Bound.V7.CensusGram
