import D4Bound.V7CensusGramPlanesBasic
import D4Bound.V7CensusGramPlane3
import D4Bound.CensusArithmetic
import D4Bound.V7CensusGramCensusIdentity
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem plane3_constant : planeConstantOK planeCentres3 planeConstant3 = true := by decide +kernel
theorem plane3_row0 : planeRowOK planeCentres3 planeLinear3 0 = true := by decide +kernel
theorem plane3_row1 : planeRowOK planeCentres3 planeLinear3 1 = true := by decide +kernel
theorem plane3_row2 : planeRowOK planeCentres3 planeLinear3 2 = true := by decide +kernel
theorem plane3_row3 : planeRowOK planeCentres3 planeLinear3 3 = true := by decide +kernel
theorem plane3_row4 : planeRowOK planeCentres3 planeLinear3 4 = true := by decide +kernel
theorem plane3_row5 : planeRowOK planeCentres3 planeLinear3 5 = true := by decide +kernel
theorem plane3_row6 : planeRowOK planeCentres3 planeLinear3 6 = true := by decide +kernel
theorem plane3_row7 : planeRowOK planeCentres3 planeLinear3 7 = true := by decide +kernel
theorem plane3_row8 : planeRowOK planeCentres3 planeLinear3 8 = true := by decide +kernel
theorem plane3_row9 : planeRowOK planeCentres3 planeLinear3 9 = true := by decide +kernel
theorem plane3_row10 : planeRowOK planeCentres3 planeLinear3 10 = true := by decide +kernel
theorem plane3_row11 : planeRowOK planeCentres3 planeLinear3 11 = true := by decide +kernel
theorem plane3_row12 : planeRowOK planeCentres3 planeLinear3 12 = true := by decide +kernel
theorem plane3_row13 : planeRowOK planeCentres3 planeLinear3 13 = true := by decide +kernel
theorem plane3_row14 : planeRowOK planeCentres3 planeLinear3 14 = true := by decide +kernel
theorem plane3_row15 : planeRowOK planeCentres3 planeLinear3 15 = true := by decide +kernel
theorem plane3_row16 : planeRowOK planeCentres3 planeLinear3 16 = true := by decide +kernel
theorem plane3_row17 : planeRowOK planeCentres3 planeLinear3 17 = true := by decide +kernel
theorem plane3_row18 : planeRowOK planeCentres3 planeLinear3 18 = true := by decide +kernel
theorem plane3_row19 : planeRowOK planeCentres3 planeLinear3 19 = true := by decide +kernel
theorem plane3_row20 : planeRowOK planeCentres3 planeLinear3 20 = true := by decide +kernel
theorem plane3_row21 : planeRowOK planeCentres3 planeLinear3 21 = true := by decide +kernel
theorem plane3_row22 : planeRowOK planeCentres3 planeLinear3 22 = true := by decide +kernel
theorem plane3_row23 : planeRowOK planeCentres3 planeLinear3 23 = true := by decide +kernel
theorem plane3_row24 : planeRowOK planeCentres3 planeLinear3 24 = true := by decide +kernel
theorem plane3_row25 : planeRowOK planeCentres3 planeLinear3 25 = true := by decide +kernel
theorem plane3_row26 : planeRowOK planeCentres3 planeLinear3 26 = true := by decide +kernel
theorem plane3_row27 : planeRowOK planeCentres3 planeLinear3 27 = true := by decide +kernel
theorem plane3_row28 : planeRowOK planeCentres3 planeLinear3 28 = true := by decide +kernel
theorem plane3_row29 : planeRowOK planeCentres3 planeLinear3 29 = true := by decide +kernel
theorem plane3_row30 : planeRowOK planeCentres3 planeLinear3 30 = true := by decide +kernel
theorem plane3_row31 : planeRowOK planeCentres3 planeLinear3 31 = true := by decide +kernel
theorem plane3_row32 : planeRowOK planeCentres3 planeLinear3 32 = true := by decide +kernel
theorem plane3_row33 : planeRowOK planeCentres3 planeLinear3 33 = true := by decide +kernel
theorem plane3_row34 : planeRowOK planeCentres3 planeLinear3 34 = true := by decide +kernel
theorem plane3_row35 : planeRowOK planeCentres3 planeLinear3 35 = true := by decide +kernel
theorem plane3_row36 : planeRowOK planeCentres3 planeLinear3 36 = true := by decide +kernel
theorem plane3_row37 : planeRowOK planeCentres3 planeLinear3 37 = true := by decide +kernel
theorem plane3_row38 : planeRowOK planeCentres3 planeLinear3 38 = true := by decide +kernel
theorem plane3_row39 : planeRowOK planeCentres3 planeLinear3 39 = true := by decide +kernel
theorem plane3_row40 : planeRowOK planeCentres3 planeLinear3 40 = true := by decide +kernel
theorem plane3_row41 : planeRowOK planeCentres3 planeLinear3 41 = true := by decide +kernel
theorem plane3_row42 : planeRowOK planeCentres3 planeLinear3 42 = true := by decide +kernel
theorem plane3_row43 : planeRowOK planeCentres3 planeLinear3 43 = true := by decide +kernel
theorem plane3_row44 : planeRowOK planeCentres3 planeLinear3 44 = true := by decide +kernel
theorem plane3_row45 : planeRowOK planeCentres3 planeLinear3 45 = true := by decide +kernel
theorem plane3_row46 : planeRowOK planeCentres3 planeLinear3 46 = true := by decide +kernel
theorem plane3_row47 : planeRowOK planeCentres3 planeLinear3 47 = true := by decide +kernel
theorem plane3_row48 : planeRowOK planeCentres3 planeLinear3 48 = true := by decide +kernel
theorem plane3_rows (k : ℕ) (hk : k < 49) :
    planeRowOK planeCentres3 planeLinear3 k = true := by
  interval_cases k
  · exact plane3_row0
  · exact plane3_row1
  · exact plane3_row2
  · exact plane3_row3
  · exact plane3_row4
  · exact plane3_row5
  · exact plane3_row6
  · exact plane3_row7
  · exact plane3_row8
  · exact plane3_row9
  · exact plane3_row10
  · exact plane3_row11
  · exact plane3_row12
  · exact plane3_row13
  · exact plane3_row14
  · exact plane3_row15
  · exact plane3_row16
  · exact plane3_row17
  · exact plane3_row18
  · exact plane3_row19
  · exact plane3_row20
  · exact plane3_row21
  · exact plane3_row22
  · exact plane3_row23
  · exact plane3_row24
  · exact plane3_row25
  · exact plane3_row26
  · exact plane3_row27
  · exact plane3_row28
  · exact plane3_row29
  · exact plane3_row30
  · exact plane3_row31
  · exact plane3_row32
  · exact plane3_row33
  · exact plane3_row34
  · exact plane3_row35
  · exact plane3_row36
  · exact plane3_row37
  · exact plane3_row38
  · exact plane3_row39
  · exact plane3_row40
  · exact plane3_row41
  · exact plane3_row42
  · exact plane3_row43
  · exact plane3_row44
  · exact plane3_row45
  · exact plane3_row46
  · exact plane3_row47
  · exact plane3_row48
noncomputable section
theorem plane3_census_identity (X : Finset E4) :
    (planeConstant3 : ℝ) + ((List.range 5).map fun i => (planeCounts3.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[3]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) := by
  apply affine_count_identity planeCounts3 planeConstant3
    (CensusArithmetic.planeCoeffs[3]!)
  · decide +kernel
  · intro i hi
    interval_cases i <;> decide +kernel

theorem gram_energy_ge_plane3 (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (h1 : ∀ x ∈ X, 1 ≤ ‖x‖) :
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[3]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) ≤
    gramEnergy X := by
  rw [← plane3_census_identity]
  exact gram_plane_floor planeCentres3 planeLinear3 planeCounts3 planeConstant3
    plane3_constant plane3_rows X hX hR (fun x hx => plane3_radial ‖x‖ (h1 x hx) (hR x hx))
end
end D4Bound.V7.CensusGram
