import D4Bound.V7CensusGramProjectionData
import D4Bound.V7CensusGramPolynomialBasic
namespace D4Bound.V7.CensusGram
open CensusArithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem projection_coefficient_12 :
    projectionCoefficients projectionGramQ projectionOffsetQ 12 =
    ((totalCoeffs[12]! : ℚ)-(countCoeffs[12]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_13 :
    projectionCoefficients projectionGramQ projectionOffsetQ 13 =
    ((totalCoeffs[13]! : ℚ)-(countCoeffs[13]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_14 :
    projectionCoefficients projectionGramQ projectionOffsetQ 14 =
    ((totalCoeffs[14]! : ℚ)-(countCoeffs[14]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_15 :
    projectionCoefficients projectionGramQ projectionOffsetQ 15 =
    ((totalCoeffs[15]! : ℚ)-(countCoeffs[15]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_16 :
    projectionCoefficients projectionGramQ projectionOffsetQ 16 =
    ((totalCoeffs[16]! : ℚ)-(countCoeffs[16]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
theorem projection_coefficient_17 :
    projectionCoefficients projectionGramQ projectionOffsetQ 17 =
    ((totalCoeffs[17]! : ℚ)-(countCoeffs[17]! : ℚ))/(denominator : ℚ) := by
  decide +kernel
end D4Bound.V7.CensusGram
