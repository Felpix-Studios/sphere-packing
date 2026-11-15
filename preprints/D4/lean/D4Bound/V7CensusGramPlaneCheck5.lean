import D4Bound.V7CensusGramPlanesBasic
import D4Bound.V7CensusGramPlane5
import D4Bound.CensusArithmetic
import D4Bound.V7CensusGramCensusIdentity
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem plane5_constant : planeConstantOK planeCentres5 planeConstant5 = true := by decide +kernel
theorem plane5_row0 : planeRowOK planeCentres5 planeLinear5 0 = true := by decide +kernel
theorem plane5_row1 : planeRowOK planeCentres5 planeLinear5 1 = true := by decide +kernel
theorem plane5_row2 : planeRowOK planeCentres5 planeLinear5 2 = true := by decide +kernel
theorem plane5_row3 : planeRowOK planeCentres5 planeLinear5 3 = true := by decide +kernel
theorem plane5_row4 : planeRowOK planeCentres5 planeLinear5 4 = true := by decide +kernel
theorem plane5_row5 : planeRowOK planeCentres5 planeLinear5 5 = true := by decide +kernel
theorem plane5_row6 : planeRowOK planeCentres5 planeLinear5 6 = true := by decide +kernel
theorem plane5_row7 : planeRowOK planeCentres5 planeLinear5 7 = true := by decide +kernel
theorem plane5_row8 : planeRowOK planeCentres5 planeLinear5 8 = true := by decide +kernel
theorem plane5_row9 : planeRowOK planeCentres5 planeLinear5 9 = true := by decide +kernel
theorem plane5_row10 : planeRowOK planeCentres5 planeLinear5 10 = true := by decide +kernel
theorem plane5_row11 : planeRowOK planeCentres5 planeLinear5 11 = true := by decide +kernel
theorem plane5_row12 : planeRowOK planeCentres5 planeLinear5 12 = true := by decide +kernel
theorem plane5_row13 : planeRowOK planeCentres5 planeLinear5 13 = true := by decide +kernel
theorem plane5_row14 : planeRowOK planeCentres5 planeLinear5 14 = true := by decide +kernel
theorem plane5_row15 : planeRowOK planeCentres5 planeLinear5 15 = true := by decide +kernel
theorem plane5_row16 : planeRowOK planeCentres5 planeLinear5 16 = true := by decide +kernel
theorem plane5_row17 : planeRowOK planeCentres5 planeLinear5 17 = true := by decide +kernel
theorem plane5_row18 : planeRowOK planeCentres5 planeLinear5 18 = true := by decide +kernel
theorem plane5_row19 : planeRowOK planeCentres5 planeLinear5 19 = true := by decide +kernel
theorem plane5_row20 : planeRowOK planeCentres5 planeLinear5 20 = true := by decide +kernel
theorem plane5_row21 : planeRowOK planeCentres5 planeLinear5 21 = true := by decide +kernel
theorem plane5_row22 : planeRowOK planeCentres5 planeLinear5 22 = true := by decide +kernel
theorem plane5_row23 : planeRowOK planeCentres5 planeLinear5 23 = true := by decide +kernel
theorem plane5_row24 : planeRowOK planeCentres5 planeLinear5 24 = true := by decide +kernel
theorem plane5_row25 : planeRowOK planeCentres5 planeLinear5 25 = true := by decide +kernel
theorem plane5_row26 : planeRowOK planeCentres5 planeLinear5 26 = true := by decide +kernel
theorem plane5_row27 : planeRowOK planeCentres5 planeLinear5 27 = true := by decide +kernel
theorem plane5_row28 : planeRowOK planeCentres5 planeLinear5 28 = true := by decide +kernel
theorem plane5_row29 : planeRowOK planeCentres5 planeLinear5 29 = true := by decide +kernel
theorem plane5_row30 : planeRowOK planeCentres5 planeLinear5 30 = true := by decide +kernel
theorem plane5_row31 : planeRowOK planeCentres5 planeLinear5 31 = true := by decide +kernel
theorem plane5_row32 : planeRowOK planeCentres5 planeLinear5 32 = true := by decide +kernel
theorem plane5_row33 : planeRowOK planeCentres5 planeLinear5 33 = true := by decide +kernel
theorem plane5_row34 : planeRowOK planeCentres5 planeLinear5 34 = true := by decide +kernel
theorem plane5_row35 : planeRowOK planeCentres5 planeLinear5 35 = true := by decide +kernel
theorem plane5_row36 : planeRowOK planeCentres5 planeLinear5 36 = true := by decide +kernel
theorem plane5_row37 : planeRowOK planeCentres5 planeLinear5 37 = true := by decide +kernel
theorem plane5_row38 : planeRowOK planeCentres5 planeLinear5 38 = true := by decide +kernel
theorem plane5_row39 : planeRowOK planeCentres5 planeLinear5 39 = true := by decide +kernel
theorem plane5_row40 : planeRowOK planeCentres5 planeLinear5 40 = true := by decide +kernel
theorem plane5_row41 : planeRowOK planeCentres5 planeLinear5 41 = true := by decide +kernel
theorem plane5_row42 : planeRowOK planeCentres5 planeLinear5 42 = true := by decide +kernel
theorem plane5_row43 : planeRowOK planeCentres5 planeLinear5 43 = true := by decide +kernel
theorem plane5_row44 : planeRowOK planeCentres5 planeLinear5 44 = true := by decide +kernel
theorem plane5_row45 : planeRowOK planeCentres5 planeLinear5 45 = true := by decide +kernel
theorem plane5_row46 : planeRowOK planeCentres5 planeLinear5 46 = true := by decide +kernel
theorem plane5_row47 : planeRowOK planeCentres5 planeLinear5 47 = true := by decide +kernel
theorem plane5_row48 : planeRowOK planeCentres5 planeLinear5 48 = true := by decide +kernel
theorem plane5_rows (k : ℕ) (hk : k < 49) :
    planeRowOK planeCentres5 planeLinear5 k = true := by
  interval_cases k
  · exact plane5_row0
  · exact plane5_row1
  · exact plane5_row2
  · exact plane5_row3
  · exact plane5_row4
  · exact plane5_row5
  · exact plane5_row6
  · exact plane5_row7
  · exact plane5_row8
  · exact plane5_row9
  · exact plane5_row10
  · exact plane5_row11
  · exact plane5_row12
  · exact plane5_row13
  · exact plane5_row14
  · exact plane5_row15
  · exact plane5_row16
  · exact plane5_row17
  · exact plane5_row18
  · exact plane5_row19
  · exact plane5_row20
  · exact plane5_row21
  · exact plane5_row22
  · exact plane5_row23
  · exact plane5_row24
  · exact plane5_row25
  · exact plane5_row26
  · exact plane5_row27
  · exact plane5_row28
  · exact plane5_row29
  · exact plane5_row30
  · exact plane5_row31
  · exact plane5_row32
  · exact plane5_row33
  · exact plane5_row34
  · exact plane5_row35
  · exact plane5_row36
  · exact plane5_row37
  · exact plane5_row38
  · exact plane5_row39
  · exact plane5_row40
  · exact plane5_row41
  · exact plane5_row42
  · exact plane5_row43
  · exact plane5_row44
  · exact plane5_row45
  · exact plane5_row46
  · exact plane5_row47
  · exact plane5_row48
noncomputable section
theorem plane5_census_identity (X : Finset E4) :
    (planeConstant5 : ℝ) + ((List.range 5).map fun i => (planeCounts5.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[5]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) := by
  apply affine_count_identity planeCounts5 planeConstant5
    (CensusArithmetic.planeCoeffs[5]!)
  · decide +kernel
  · intro i hi
    interval_cases i <;> decide +kernel

theorem gram_energy_ge_plane5 (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (h1 : ∀ x ∈ X, 1 ≤ ‖x‖) :
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[5]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) ≤
    gramEnergy X := by
  rw [← plane5_census_identity]
  exact gram_plane_floor planeCentres5 planeLinear5 planeCounts5 planeConstant5
    plane5_constant plane5_rows X hX hR (fun x hx => plane5_radial ‖x‖ (h1 x hx) (hR x hx))
end
end D4Bound.V7.CensusGram
