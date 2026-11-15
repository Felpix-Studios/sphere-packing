import D4Bound.V7CensusGramPlanesBasic
import D4Bound.V7CensusGramPlane1
import D4Bound.CensusArithmetic
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem plane1_constant : planeConstantOK planeCentres1 planeConstant1 = true := by decide +kernel
theorem plane1_row0 : planeRowOK planeCentres1 planeLinear1 0 = true := by decide +kernel
theorem plane1_row1 : planeRowOK planeCentres1 planeLinear1 1 = true := by decide +kernel
theorem plane1_row2 : planeRowOK planeCentres1 planeLinear1 2 = true := by decide +kernel
theorem plane1_row3 : planeRowOK planeCentres1 planeLinear1 3 = true := by decide +kernel
theorem plane1_row4 : planeRowOK planeCentres1 planeLinear1 4 = true := by decide +kernel
theorem plane1_row5 : planeRowOK planeCentres1 planeLinear1 5 = true := by decide +kernel
theorem plane1_row6 : planeRowOK planeCentres1 planeLinear1 6 = true := by decide +kernel
theorem plane1_row7 : planeRowOK planeCentres1 planeLinear1 7 = true := by decide +kernel
theorem plane1_row8 : planeRowOK planeCentres1 planeLinear1 8 = true := by decide +kernel
theorem plane1_row9 : planeRowOK planeCentres1 planeLinear1 9 = true := by decide +kernel
theorem plane1_row10 : planeRowOK planeCentres1 planeLinear1 10 = true := by decide +kernel
theorem plane1_row11 : planeRowOK planeCentres1 planeLinear1 11 = true := by decide +kernel
theorem plane1_row12 : planeRowOK planeCentres1 planeLinear1 12 = true := by decide +kernel
theorem plane1_row13 : planeRowOK planeCentres1 planeLinear1 13 = true := by decide +kernel
theorem plane1_row14 : planeRowOK planeCentres1 planeLinear1 14 = true := by decide +kernel
theorem plane1_row15 : planeRowOK planeCentres1 planeLinear1 15 = true := by decide +kernel
theorem plane1_row16 : planeRowOK planeCentres1 planeLinear1 16 = true := by decide +kernel
theorem plane1_row17 : planeRowOK planeCentres1 planeLinear1 17 = true := by decide +kernel
theorem plane1_row18 : planeRowOK planeCentres1 planeLinear1 18 = true := by decide +kernel
theorem plane1_row19 : planeRowOK planeCentres1 planeLinear1 19 = true := by decide +kernel
theorem plane1_row20 : planeRowOK planeCentres1 planeLinear1 20 = true := by decide +kernel
theorem plane1_row21 : planeRowOK planeCentres1 planeLinear1 21 = true := by decide +kernel
theorem plane1_row22 : planeRowOK planeCentres1 planeLinear1 22 = true := by decide +kernel
theorem plane1_row23 : planeRowOK planeCentres1 planeLinear1 23 = true := by decide +kernel
theorem plane1_row24 : planeRowOK planeCentres1 planeLinear1 24 = true := by decide +kernel
theorem plane1_row25 : planeRowOK planeCentres1 planeLinear1 25 = true := by decide +kernel
theorem plane1_row26 : planeRowOK planeCentres1 planeLinear1 26 = true := by decide +kernel
theorem plane1_row27 : planeRowOK planeCentres1 planeLinear1 27 = true := by decide +kernel
theorem plane1_row28 : planeRowOK planeCentres1 planeLinear1 28 = true := by decide +kernel
theorem plane1_row29 : planeRowOK planeCentres1 planeLinear1 29 = true := by decide +kernel
theorem plane1_row30 : planeRowOK planeCentres1 planeLinear1 30 = true := by decide +kernel
theorem plane1_row31 : planeRowOK planeCentres1 planeLinear1 31 = true := by decide +kernel
theorem plane1_row32 : planeRowOK planeCentres1 planeLinear1 32 = true := by decide +kernel
theorem plane1_row33 : planeRowOK planeCentres1 planeLinear1 33 = true := by decide +kernel
theorem plane1_row34 : planeRowOK planeCentres1 planeLinear1 34 = true := by decide +kernel
theorem plane1_row35 : planeRowOK planeCentres1 planeLinear1 35 = true := by decide +kernel
theorem plane1_row36 : planeRowOK planeCentres1 planeLinear1 36 = true := by decide +kernel
theorem plane1_row37 : planeRowOK planeCentres1 planeLinear1 37 = true := by decide +kernel
theorem plane1_row38 : planeRowOK planeCentres1 planeLinear1 38 = true := by decide +kernel
theorem plane1_row39 : planeRowOK planeCentres1 planeLinear1 39 = true := by decide +kernel
theorem plane1_row40 : planeRowOK planeCentres1 planeLinear1 40 = true := by decide +kernel
theorem plane1_row41 : planeRowOK planeCentres1 planeLinear1 41 = true := by decide +kernel
theorem plane1_row42 : planeRowOK planeCentres1 planeLinear1 42 = true := by decide +kernel
theorem plane1_row43 : planeRowOK planeCentres1 planeLinear1 43 = true := by decide +kernel
theorem plane1_row44 : planeRowOK planeCentres1 planeLinear1 44 = true := by decide +kernel
theorem plane1_row45 : planeRowOK planeCentres1 planeLinear1 45 = true := by decide +kernel
theorem plane1_row46 : planeRowOK planeCentres1 planeLinear1 46 = true := by decide +kernel
theorem plane1_row47 : planeRowOK planeCentres1 planeLinear1 47 = true := by decide +kernel
theorem plane1_row48 : planeRowOK planeCentres1 planeLinear1 48 = true := by decide +kernel
theorem plane1_rows (k : ℕ) (hk : k < 49) :
    planeRowOK planeCentres1 planeLinear1 k = true := by
  interval_cases k
  · exact plane1_row0
  · exact plane1_row1
  · exact plane1_row2
  · exact plane1_row3
  · exact plane1_row4
  · exact plane1_row5
  · exact plane1_row6
  · exact plane1_row7
  · exact plane1_row8
  · exact plane1_row9
  · exact plane1_row10
  · exact plane1_row11
  · exact plane1_row12
  · exact plane1_row13
  · exact plane1_row14
  · exact plane1_row15
  · exact plane1_row16
  · exact plane1_row17
  · exact plane1_row18
  · exact plane1_row19
  · exact plane1_row20
  · exact plane1_row21
  · exact plane1_row22
  · exact plane1_row23
  · exact plane1_row24
  · exact plane1_row25
  · exact plane1_row26
  · exact plane1_row27
  · exact plane1_row28
  · exact plane1_row29
  · exact plane1_row30
  · exact plane1_row31
  · exact plane1_row32
  · exact plane1_row33
  · exact plane1_row34
  · exact plane1_row35
  · exact plane1_row36
  · exact plane1_row37
  · exact plane1_row38
  · exact plane1_row39
  · exact plane1_row40
  · exact plane1_row41
  · exact plane1_row42
  · exact plane1_row43
  · exact plane1_row44
  · exact plane1_row45
  · exact plane1_row46
  · exact plane1_row47
  · exact plane1_row48
noncomputable section
theorem plane1_census_identity (X : Finset E4) :
    (planeConstant1 : ℝ) + ((List.range 5).map fun i => (planeCounts1.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[1]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) := by
  norm_num [planeConstant1, planeCounts1, List.range_succ, breaks,
    CensusArithmetic.affine, CensusArithmetic.planeCoeffs, CensusArithmetic.denominator,
    CensusArithmetic.ofNeighbourhood, nearCount, R1, R2, R3, R4, R5]
  ring

theorem gram_energy_ge_plane1 (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (h1 : ∀ x ∈ X, 1 ≤ ‖x‖) :
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[1]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) ≤
    gramEnergy X := by
  rw [← plane1_census_identity]
  exact gram_plane_floor planeCentres1 planeLinear1 planeCounts1 planeConstant1
    plane1_constant plane1_rows X hX hR (fun x hx => plane1_radial ‖x‖ (h1 x hx) (hR x hx))
end
end D4Bound.V7.CensusGram
