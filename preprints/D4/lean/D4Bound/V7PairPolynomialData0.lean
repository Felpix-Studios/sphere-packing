import D4Bound.V7PairPolynomialTrim
import D4Bound.V7PairGramData0
import D4Bound.V7PairSignData0

set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option Elab.async false
namespace D4Bound.V7.PairPoly
open PairSignData

/-- The uncut diagonal polynomial is computed from the actual component data. -/
theorem diagonal0_checked : diagonal 0 = pairD0 := by
  unfold diagonal
  rw [gram0_checked]
  decide +kernel

/-- Exact change of coordinates to the closed unit interval. -/
theorem negativeD0_identity :
    trim (comp pairD0 [1, (1473/500000:ℚ)]) =
      trim (scale (-1/(negativeD0Den : ℚ)) (negativeD0.map Int.cast)) := by decide +kernel

/-- The complete scalar-plus-Taylor polynomial, including every scalar coefficient. -/
theorem negativeP0_identity :
    trim (comp (add (comp Fq [0,0,2]) (mul pairD0 (taylor 25))) [1, (1473/500000:ℚ)]) =
      trim (scale (-1/(negativeP0Den : ℚ)) (negativeP0.map Int.cast)) := by decide +kernel

end D4Bound.V7.PairPoly
