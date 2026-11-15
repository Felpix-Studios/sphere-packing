import D4Bound.V7CensusGramPlanesBasic
import D4Bound.V7CensusGramPlane7
import D4Bound.CensusArithmetic
import D4Bound.V7CensusGramCensusIdentity
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem plane7_constant : planeConstantOK planeCentres7 planeConstant7 = true := by decide +kernel
theorem plane7_row0 : planeRowOK planeCentres7 planeLinear7 0 = true := by decide +kernel
theorem plane7_row1 : planeRowOK planeCentres7 planeLinear7 1 = true := by decide +kernel
theorem plane7_row2 : planeRowOK planeCentres7 planeLinear7 2 = true := by decide +kernel
theorem plane7_row3 : planeRowOK planeCentres7 planeLinear7 3 = true := by decide +kernel
theorem plane7_row4 : planeRowOK planeCentres7 planeLinear7 4 = true := by decide +kernel
theorem plane7_row5 : planeRowOK planeCentres7 planeLinear7 5 = true := by decide +kernel
theorem plane7_row6 : planeRowOK planeCentres7 planeLinear7 6 = true := by decide +kernel
theorem plane7_row7 : planeRowOK planeCentres7 planeLinear7 7 = true := by decide +kernel
theorem plane7_row8 : planeRowOK planeCentres7 planeLinear7 8 = true := by decide +kernel
theorem plane7_row9 : planeRowOK planeCentres7 planeLinear7 9 = true := by decide +kernel
theorem plane7_row10 : planeRowOK planeCentres7 planeLinear7 10 = true := by decide +kernel
theorem plane7_row11 : planeRowOK planeCentres7 planeLinear7 11 = true := by decide +kernel
theorem plane7_row12 : planeRowOK planeCentres7 planeLinear7 12 = true := by decide +kernel
theorem plane7_row13 : planeRowOK planeCentres7 planeLinear7 13 = true := by decide +kernel
theorem plane7_row14 : planeRowOK planeCentres7 planeLinear7 14 = true := by decide +kernel
theorem plane7_row15 : planeRowOK planeCentres7 planeLinear7 15 = true := by decide +kernel
theorem plane7_row16 : planeRowOK planeCentres7 planeLinear7 16 = true := by decide +kernel
theorem plane7_row17 : planeRowOK planeCentres7 planeLinear7 17 = true := by decide +kernel
theorem plane7_row18 : planeRowOK planeCentres7 planeLinear7 18 = true := by decide +kernel
theorem plane7_row19 : planeRowOK planeCentres7 planeLinear7 19 = true := by decide +kernel
theorem plane7_row20 : planeRowOK planeCentres7 planeLinear7 20 = true := by decide +kernel
theorem plane7_row21 : planeRowOK planeCentres7 planeLinear7 21 = true := by decide +kernel
theorem plane7_row22 : planeRowOK planeCentres7 planeLinear7 22 = true := by decide +kernel
theorem plane7_row23 : planeRowOK planeCentres7 planeLinear7 23 = true := by decide +kernel
theorem plane7_row24 : planeRowOK planeCentres7 planeLinear7 24 = true := by decide +kernel
theorem plane7_row25 : planeRowOK planeCentres7 planeLinear7 25 = true := by decide +kernel
theorem plane7_row26 : planeRowOK planeCentres7 planeLinear7 26 = true := by decide +kernel
theorem plane7_row27 : planeRowOK planeCentres7 planeLinear7 27 = true := by decide +kernel
theorem plane7_row28 : planeRowOK planeCentres7 planeLinear7 28 = true := by decide +kernel
theorem plane7_row29 : planeRowOK planeCentres7 planeLinear7 29 = true := by decide +kernel
theorem plane7_row30 : planeRowOK planeCentres7 planeLinear7 30 = true := by decide +kernel
theorem plane7_row31 : planeRowOK planeCentres7 planeLinear7 31 = true := by decide +kernel
theorem plane7_row32 : planeRowOK planeCentres7 planeLinear7 32 = true := by decide +kernel
theorem plane7_row33 : planeRowOK planeCentres7 planeLinear7 33 = true := by decide +kernel
theorem plane7_row34 : planeRowOK planeCentres7 planeLinear7 34 = true := by decide +kernel
theorem plane7_row35 : planeRowOK planeCentres7 planeLinear7 35 = true := by decide +kernel
theorem plane7_row36 : planeRowOK planeCentres7 planeLinear7 36 = true := by decide +kernel
theorem plane7_row37 : planeRowOK planeCentres7 planeLinear7 37 = true := by decide +kernel
theorem plane7_row38 : planeRowOK planeCentres7 planeLinear7 38 = true := by decide +kernel
theorem plane7_row39 : planeRowOK planeCentres7 planeLinear7 39 = true := by decide +kernel
theorem plane7_row40 : planeRowOK planeCentres7 planeLinear7 40 = true := by decide +kernel
theorem plane7_row41 : planeRowOK planeCentres7 planeLinear7 41 = true := by decide +kernel
theorem plane7_row42 : planeRowOK planeCentres7 planeLinear7 42 = true := by decide +kernel
theorem plane7_row43 : planeRowOK planeCentres7 planeLinear7 43 = true := by decide +kernel
theorem plane7_row44 : planeRowOK planeCentres7 planeLinear7 44 = true := by decide +kernel
theorem plane7_row45 : planeRowOK planeCentres7 planeLinear7 45 = true := by decide +kernel
theorem plane7_row46 : planeRowOK planeCentres7 planeLinear7 46 = true := by decide +kernel
theorem plane7_row47 : planeRowOK planeCentres7 planeLinear7 47 = true := by decide +kernel
theorem plane7_row48 : planeRowOK planeCentres7 planeLinear7 48 = true := by decide +kernel
theorem plane7_rows (k : ℕ) (hk : k < 49) :
    planeRowOK planeCentres7 planeLinear7 k = true := by
  interval_cases k
  · exact plane7_row0
  · exact plane7_row1
  · exact plane7_row2
  · exact plane7_row3
  · exact plane7_row4
  · exact plane7_row5
  · exact plane7_row6
  · exact plane7_row7
  · exact plane7_row8
  · exact plane7_row9
  · exact plane7_row10
  · exact plane7_row11
  · exact plane7_row12
  · exact plane7_row13
  · exact plane7_row14
  · exact plane7_row15
  · exact plane7_row16
  · exact plane7_row17
  · exact plane7_row18
  · exact plane7_row19
  · exact plane7_row20
  · exact plane7_row21
  · exact plane7_row22
  · exact plane7_row23
  · exact plane7_row24
  · exact plane7_row25
  · exact plane7_row26
  · exact plane7_row27
  · exact plane7_row28
  · exact plane7_row29
  · exact plane7_row30
  · exact plane7_row31
  · exact plane7_row32
  · exact plane7_row33
  · exact plane7_row34
  · exact plane7_row35
  · exact plane7_row36
  · exact plane7_row37
  · exact plane7_row38
  · exact plane7_row39
  · exact plane7_row40
  · exact plane7_row41
  · exact plane7_row42
  · exact plane7_row43
  · exact plane7_row44
  · exact plane7_row45
  · exact plane7_row46
  · exact plane7_row47
  · exact plane7_row48
noncomputable section
theorem plane7_census_identity (X : Finset E4) :
    (planeConstant7 : ℝ) + ((List.range 5).map fun i => (planeCounts7.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[7]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) := by
  apply affine_count_identity planeCounts7 planeConstant7
    (CensusArithmetic.planeCoeffs[7]!)
  · decide +kernel
  · intro i hi
    interval_cases i <;> decide +kernel

theorem gram_energy_ge_plane7 (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (h1 : ∀ x ∈ X, 1 ≤ ‖x‖) :
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[7]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) ≤
    gramEnergy X := by
  rw [← plane7_census_identity]
  exact gram_plane_floor planeCentres7 planeLinear7 planeCounts7 planeConstant7
    plane7_constant plane7_rows X hX hR (fun x hx => plane7_radial ‖x‖ (h1 x hx) (hR x hx))
end
end D4Bound.V7.CensusGram
