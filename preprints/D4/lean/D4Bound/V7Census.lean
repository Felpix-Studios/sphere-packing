import D4Bound.V7CensusCount
import D4Bound.V7Graphs
import D4Bound.V7Allocations
import D4Bound.V7Tents
import D4Bound.V7Conditional
import D4Bound.V7CapsFinal
import D4Bound.V7CensusGramProjection
import D4Bound.V7CensusGramPlanes
import D4Bound.V7PairSign
import D4Bound.CensusEnvelope
import D4Bound.CensusEnergy
import D4Bound.SupportRestriction

/-! Composition of the actual V7 energies with the complete finite census.
The remaining analytic input is explicit here: spherical surplus.
The actual Gram projection, all twelve affine floors and the ungauged pair
sign are proved from their exact data and coefficient identities.
No input is replaced by an abstract energy or a certificate acceptance flag. -/
namespace D4Bound.V7
open CensusArithmetic
noncomputable section

theorem census_lower_on_support {X : Finset E4} (hX : Admissible X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (hD : InCountDomain X)
    (hsurplus : surplusPart (ofNeighbourhood X) ≤ sphericalEnergy X) :
    (lower (ofNeighbourhood X) : ℝ) ≤
      nbhdEnergy (fun x y => kernel x y - Kg x y) X := by
  have hgauge := gauge_energy_nonneg_proved X hX hR hD.2.2.2.2.2.2.1
  have halloc := allocations_energy_nonneg hX hR
  have htents := tents_energy_nonneg hX hR
  have hcond := conditional_energy_nonneg hD
  have hgraph := graphs_residual_nonneg hX
  have hcaps := caps_energy_nonneg hX hR
  have hc : countPart (ofNeighbourhood X) = countsEnergy X :=
    (counts_energy_census X).symm
  have henv := lower_le_of_components (ofNeighbourhood X) (gramEnergy X)
    (sphericalEnergy X) (CensusGram.gram_energy_ge_projection X hX hR)
    (CensusGram.gram_energy_ge_census_plane X hX hR) hsurplus
  rw [hc] at henv
  rw [nbhdEnergy_sub,energy_decomposition X (fun x hx => ⟨hX.1 x hx,hR x hx⟩)]
  linarith

/-- Every count group, including the empty neighbourhood, is covered by the
checked finite census. Arbitrary exterior points are removed by support. -/
theorem censusFloor_of_component_bounds
    (hsurplus : ∀ X : Finset E4, Admissible X →
      (∀ x ∈ X, ‖x‖ ≤ 7/4) → InCountDomain X →
      surplusPart (ofNeighbourhood X) ≤ sphericalEnergy X) :
    CensusFloor kernel := by
  apply censusFloor_of_supported kernel_supported
  intro X hX hR hD g hg hN hj
  have hn := numeric_floor (ofNeighbourhood_valid hD) hg hN hj
  apply (Rat.cast_le.mpr hn).trans
  exact census_lower_on_support hX hR hD (hsurplus X hX hR hD)

end
end D4Bound.V7
