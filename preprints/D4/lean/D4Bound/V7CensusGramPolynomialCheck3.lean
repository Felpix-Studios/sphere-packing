import D4Bound.V7CensusGramProjectionData
import D4Bound.V7CensusGramPolynomialBasic
namespace D4Bound.V7.CensusGram
open CensusArithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem projection_coefficient_18 :
    projectionCoefficients projectionGramQ projectionOffsetQ 18 =
    ((totalCoeffs[18]! : ℚ)-(countCoeffs[18]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_19 :
    projectionCoefficients projectionGramQ projectionOffsetQ 19 =
    ((totalCoeffs[19]! : ℚ)-(countCoeffs[19]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_20 :
    projectionCoefficients projectionGramQ projectionOffsetQ 20 =
    ((totalCoeffs[20]! : ℚ)-(countCoeffs[20]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
end D4Bound.V7.CensusGram
