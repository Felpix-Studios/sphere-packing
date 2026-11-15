import D4Bound.V7PairPolynomialTrim
import D4Bound.V7PairGramDataRest
import D4Bound.V7PairSignData1
import D4Bound.V7PairSignDataRest

set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option Elab.async false
namespace D4Bound.V7.PairPoly
open PairSignData

/-- The uncut diagonal polynomial is computed from the actual component data. -/
theorem diagonal1_checked : diagonal 1 = pairD1 := by
  unfold diagonal
  rw [gram1_checked]
  decide +kernel

/-- Exact change of coordinates to the closed unit interval. -/
theorem negativeD1_identity :
    trim (comp pairD1 [(501473/500000:ℚ), (2697/1000000:ℚ)]) =
      trim (scale (-1/(negativeD1Den : ℚ)) (negativeD1.map Int.cast)) := by decide +kernel

/-- The complete scalar-plus-Taylor polynomial, including every scalar coefficient. -/
theorem negativeP1_identity :
    trim (comp (add (comp Fq [0,0,2]) (mul pairD1 (taylor 25))) [(501473/500000:ℚ), (2697/1000000:ℚ)]) =
      trim (scale (-1/(negativeP1Den : ℚ)) (negativeP1.map Int.cast)) := by decide +kernel

end D4Bound.V7.PairPoly

set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option Elab.async false
namespace D4Bound.V7.PairPoly
open PairSignData

/-- The uncut diagonal polynomial is computed from the actual component data. -/
theorem diagonal2_checked : diagonal 2 = pairD2 := by
  unfold diagonal
  rw [gram2_checked]
  decide +kernel

/-- Exact change of coordinates to the closed unit interval. -/
theorem negativeD2_identity :
    trim (comp pairD2 [(1005643/1000000:ℚ), (1937/1000000:ℚ)]) =
      trim (scale (-1/(negativeD2Den : ℚ)) (negativeD2.map Int.cast)) := by decide +kernel

/-- The complete scalar-plus-Taylor polynomial, including every scalar coefficient. -/
theorem negativeP2_identity :
    trim (comp (add (comp Fq [0,0,2]) (mul pairD2 (taylor 25))) [(1005643/1000000:ℚ), (1937/1000000:ℚ)]) =
      trim (scale (-1/(negativeP2Den : ℚ)) (negativeP2.map Int.cast)) := by decide +kernel

end D4Bound.V7.PairPoly

set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option Elab.async false
namespace D4Bound.V7.PairPoly
open PairSignData

/-- The uncut diagonal polynomial is computed from the actual component data. -/
theorem diagonal3_checked : diagonal 3 = pairD3 := by
  unfold diagonal
  rw [gram3_checked]
  decide +kernel

/-- Exact change of coordinates to the closed unit interval. -/
theorem negativeD3_identity :
    trim (comp pairD3 [(50379/50000:ℚ), (97/12500:ℚ)]) =
      trim (scale (-1/(negativeD3Den : ℚ)) (negativeD3.map Int.cast)) := by decide +kernel

/-- The complete scalar-plus-Taylor polynomial, including every scalar coefficient. -/
theorem negativeP3_identity :
    trim (comp (add (comp Fq [0,0,2]) (mul pairD3 (taylor 25))) [(50379/50000:ℚ), (97/12500:ℚ)]) =
      trim (scale (-1/(negativeP3Den : ℚ)) (negativeP3.map Int.cast)) := by decide +kernel

end D4Bound.V7.PairPoly

set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option Elab.async false
namespace D4Bound.V7.PairPoly
open PairSignData

/-- The uncut diagonal polynomial is computed from the actual component data. -/
theorem diagonal4_checked : diagonal 4 = pairD4 := by
  unfold diagonal
  rw [gram4_checked]
  decide +kernel

/-- Exact change of coordinates to the closed unit interval. -/
theorem negativeD4_identity :
    trim (comp pairD4 [(50767/50000:ℚ), (1063/100000:ℚ)]) =
      trim (scale (-1/(negativeD4Den : ℚ)) (negativeD4.map Int.cast)) := by decide +kernel

/-- The complete scalar-plus-Taylor polynomial, including every scalar coefficient. -/
theorem negativeP4_identity :
    trim (comp (add (comp Fq [0,0,2]) (mul pairD4 (taylor 25))) [(50767/50000:ℚ), (1063/100000:ℚ)]) =
      trim (scale (-1/(negativeP4Den : ℚ)) (negativeP4.map Int.cast)) := by decide +kernel

end D4Bound.V7.PairPoly

set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option Elab.async false
namespace D4Bound.V7.PairPoly
open PairSignData

/-- The uncut diagonal polynomial is computed from the actual component data. -/
theorem diagonal5_checked : diagonal 5 = pairD5 := by
  unfold diagonal
  rw [gram5_checked]
  decide +kernel

/-- Exact change of coordinates to the closed unit interval. -/
theorem negativeD5_identity :
    trim (comp pairD5 [(102597/100000:ℚ), (47403/100000:ℚ)]) =
      trim (scale (-1/(negativeD5Den : ℚ)) (negativeD5.map Int.cast)) := by decide +kernel

/-- The complete scalar-plus-Taylor polynomial, including every scalar coefficient. -/
theorem negativeP5_identity :
    trim (comp (add (comp Fq [0,0,2]) (mul pairD5 (taylor 25))) [(102597/100000:ℚ), (47403/100000:ℚ)]) =
      trim (scale (-1/(negativeP5Den : ℚ)) (negativeP5.map Int.cast)) := by decide +kernel

end D4Bound.V7.PairPoly

set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option Elab.async false
namespace D4Bound.V7.PairPoly
open PairSignData

/-- The uncut diagonal polynomial is computed from the actual component data. -/
theorem diagonal6_checked : diagonal 6 = pairD6 := by
  unfold diagonal
  rw [gram6_checked]
  decide +kernel

/-- Exact change of coordinates to the closed unit interval. -/
theorem negativeD6_identity :
    trim (comp pairD6 [(3/2:ℚ), (1/4:ℚ)]) =
      trim (scale (-1/(negativeD6Den : ℚ)) (negativeD6.map Int.cast)) := by decide +kernel

/-- The complete scalar-plus-Taylor polynomial, including every scalar coefficient. -/
theorem negativeP6_identity :
    trim (comp (add (comp Fq [0,0,2]) (mul pairD6 (taylor 25))) [(3/2:ℚ), (1/4:ℚ)]) =
      trim (scale (-1/(negativeP6Den : ℚ)) (negativeP6.map Int.cast)) := by decide +kernel

end D4Bound.V7.PairPoly
