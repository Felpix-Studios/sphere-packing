import D4Bound.V7CensusGramData
import D4Bound.V7CensusGramRadial

/-! Exact origin completion of the actual degree-zero Gram rays. The ray's first
coordinate uniquely identifies these 34 fixed data rows; the lookup is checked
by the explicit coefficient equations, not assumed injective. -/
namespace D4Bound.V7.CensusGram
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rayIndex (r : Ray) : ℕ :=
  rayVectors.toList.findIdx (fun v => decide (((v[0]! : ℤ) : ℚ) = r.vector.getD 0 0))
def originOffsetQ (r : Ray) : ℚ := (originNums[rayIndex r]! : ℚ)/(originDen : ℚ)
noncomputable def originOffset (r : Ray) : ℝ := originOffsetQ r

def originRowOK (k : ℕ) : Bool := decide (
  (gramRays0.map fun ray => ray.weight/gramDenominator*originOffsetQ ray*
    ray.vector.getD k 0).sum = originVector.getD k 0)

theorem origin_constant_checked :
    (gramRays0.map fun ray => ray.weight/gramDenominator*(originOffsetQ ray)^2).sum =
      gramOrigin := by decide +kernel

end D4Bound.V7.CensusGram
