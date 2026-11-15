import D4Bound.V7CensusGramProjectionCountLink
import D4Bound.V7CensusGramPolynomial

/-! The concrete count projection is a lower bound for the actual V7 Gram
energy. All range, origin and polynomial coefficient identities are checked
against the supplied rational rays. -/
namespace D4Bound.V7.CensusGram
noncomputable section
open Finset CensusArithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem gram_energy_ge_projection_nonzero (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) :
    projectionPart (ofNeighbourhood X) ≤ gramEnergy X := by
  rw [← projection_polynomial_identity,projection_counts_matrix]
  exact projection_energy_of_origin projection_origin_cross X hX hR

/-- Final projection interface for the actual census energy composition. -/
theorem gram_energy_ge_projection (X : Finset E4) (hX : Admissible X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) :
    projectionPart (ofNeighbourhood X) ≤ gramEnergy X := by
  apply gram_energy_ge_projection_nonzero X _ hR
  intro hz
  have hn := hX.1 0 hz
  norm_num at hn

end
end D4Bound.V7.CensusGram

#print axioms D4Bound.V7.CensusGram.gram_energy_ge_projection
