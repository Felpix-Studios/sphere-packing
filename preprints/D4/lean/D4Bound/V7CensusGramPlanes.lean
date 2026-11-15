import D4Bound.V7CensusGramPlaneCheck0
import D4Bound.V7CensusGramPlaneCheck1
import D4Bound.V7CensusGramPlaneCheck2
import D4Bound.V7CensusGramPlaneCheck3
import D4Bound.V7CensusGramPlaneCheck4
import D4Bound.V7CensusGramPlaneCheck5
import D4Bound.V7CensusGramPlaneCheck6
import D4Bound.V7CensusGramPlaneCheck7
import D4Bound.V7CensusGramPlaneCheck8
import D4Bound.V7CensusGramPlaneCheck9
import D4Bound.V7CensusGramPlaneCheck10
import D4Bound.V7CensusGramPlaneCheck11

namespace D4Bound.V7.CensusGram
open CensusArithmetic
noncomputable section
theorem gram_energy_ge_census_plane (X : Finset E4) (hX : Admissible X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (c : Array ℤ) (hc : c ∈ planeCoeffs) :
    (affine c (ofNeighbourhood X) : ℝ)/(denominator : ℝ) ≤ gramEnergy X := by
  have h0 : (0 : E4) ∉ X := by
    intro hz
    have hn := hX.1 0 hz
    norm_num at hn
  have hsize : planeCoeffs.size = 12 := by decide +kernel
  obtain ⟨j,hj,rfl⟩ := Array.mem_iff_getElem.mp hc
  have hj12 : j < 12 := by simpa only [hsize] using hj
  interval_cases j
  · exact gram_energy_ge_plane0 X h0 hR hX.1
  · exact gram_energy_ge_plane1 X h0 hR hX.1
  · exact gram_energy_ge_plane2 X h0 hR hX.1
  · exact gram_energy_ge_plane3 X h0 hR hX.1
  · exact gram_energy_ge_plane4 X h0 hR hX.1
  · exact gram_energy_ge_plane5 X h0 hR hX.1
  · exact gram_energy_ge_plane6 X h0 hR hX.1
  · exact gram_energy_ge_plane7 X h0 hR hX.1
  · exact gram_energy_ge_plane8 X h0 hR hX.1
  · exact gram_energy_ge_plane9 X h0 hR hX.1
  · exact gram_energy_ge_plane10 X h0 hR hX.1
  · exact gram_energy_ge_plane11 X h0 hR hX.1
end
end D4Bound.V7.CensusGram

#print axioms D4Bound.V7.CensusGram.gram_energy_ge_census_plane
