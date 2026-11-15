import D4Bound.V7CountEnergy
import D4Bound.CensusCheck

/-! Exact linkage of the three concrete count energies to the census polynomial.
This is an identity for every finite neighbourhood, with no count-domain premise. -/
namespace D4Bound.V7
open Finset CensusArithmetic
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem counts_energy_census (X : Finset E4) :
    countsEnergy X = (quadratic countCoeffs (ofNeighbourhood X) : ℝ) /
      (denominator : ℝ) := by
  rw [counts_energy_identity]
  norm_num [countPolynomials, countValue, quadratic, countCoeffs, denominator,
    ofNeighbourhood, nearCount, R1, R2, R3, R4, R5, List.range_succ]
  <;> ring

end
end D4Bound.V7

#print axioms D4Bound.V7.counts_energy_census
