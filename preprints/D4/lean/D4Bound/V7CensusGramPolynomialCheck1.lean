import D4Bound.V7CensusGramProjectionData
import D4Bound.V7CensusGramPolynomialBasic
namespace D4Bound.V7.CensusGram
open CensusArithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem projection_coefficient_6 :
    projectionCoefficients projectionGramQ projectionOffsetQ 6 =
    ((totalCoeffs[6]! : ℚ)-(countCoeffs[6]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_7 :
    projectionCoefficients projectionGramQ projectionOffsetQ 7 =
    ((totalCoeffs[7]! : ℚ)-(countCoeffs[7]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_8 :
    projectionCoefficients projectionGramQ projectionOffsetQ 8 =
    ((totalCoeffs[8]! : ℚ)-(countCoeffs[8]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_9 :
    projectionCoefficients projectionGramQ projectionOffsetQ 9 =
    ((totalCoeffs[9]! : ℚ)-(countCoeffs[9]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_10 :
    projectionCoefficients projectionGramQ projectionOffsetQ 10 =
    ((totalCoeffs[10]! : ℚ)-(countCoeffs[10]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_11 :
    projectionCoefficients projectionGramQ projectionOffsetQ 11 =
    ((totalCoeffs[11]! : ℚ)-(countCoeffs[11]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
end D4Bound.V7.CensusGram
