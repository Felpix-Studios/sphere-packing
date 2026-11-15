import D4Bound.V7CensusGramPlanesBasic
import D4Bound.V7CensusGramPlane0
import D4Bound.CensusArithmetic
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem plane0_constant : planeConstantOK planeCentres0 planeConstant0 = true := by decide +kernel
theorem plane0_row0 : planeRowOK planeCentres0 planeLinear0 0 = true := by decide +kernel
theorem plane0_row1 : planeRowOK planeCentres0 planeLinear0 1 = true := by decide +kernel
theorem plane0_row2 : planeRowOK planeCentres0 planeLinear0 2 = true := by decide +kernel
theorem plane0_row3 : planeRowOK planeCentres0 planeLinear0 3 = true := by decide +kernel
theorem plane0_row4 : planeRowOK planeCentres0 planeLinear0 4 = true := by decide +kernel
theorem plane0_row5 : planeRowOK planeCentres0 planeLinear0 5 = true := by decide +kernel
theorem plane0_row6 : planeRowOK planeCentres0 planeLinear0 6 = true := by decide +kernel
theorem plane0_row7 : planeRowOK planeCentres0 planeLinear0 7 = true := by decide +kernel
theorem plane0_row8 : planeRowOK planeCentres0 planeLinear0 8 = true := by decide +kernel
theorem plane0_row9 : planeRowOK planeCentres0 planeLinear0 9 = true := by decide +kernel
theorem plane0_row10 : planeRowOK planeCentres0 planeLinear0 10 = true := by decide +kernel
theorem plane0_row11 : planeRowOK planeCentres0 planeLinear0 11 = true := by decide +kernel
theorem plane0_row12 : planeRowOK planeCentres0 planeLinear0 12 = true := by decide +kernel
theorem plane0_row13 : planeRowOK planeCentres0 planeLinear0 13 = true := by decide +kernel
theorem plane0_row14 : planeRowOK planeCentres0 planeLinear0 14 = true := by decide +kernel
theorem plane0_row15 : planeRowOK planeCentres0 planeLinear0 15 = true := by decide +kernel
theorem plane0_row16 : planeRowOK planeCentres0 planeLinear0 16 = true := by decide +kernel
theorem plane0_row17 : planeRowOK planeCentres0 planeLinear0 17 = true := by decide +kernel
theorem plane0_row18 : planeRowOK planeCentres0 planeLinear0 18 = true := by decide +kernel
theorem plane0_row19 : planeRowOK planeCentres0 planeLinear0 19 = true := by decide +kernel
theorem plane0_row20 : planeRowOK planeCentres0 planeLinear0 20 = true := by decide +kernel
theorem plane0_row21 : planeRowOK planeCentres0 planeLinear0 21 = true := by decide +kernel
theorem plane0_row22 : planeRowOK planeCentres0 planeLinear0 22 = true := by decide +kernel
theorem plane0_row23 : planeRowOK planeCentres0 planeLinear0 23 = true := by decide +kernel
theorem plane0_row24 : planeRowOK planeCentres0 planeLinear0 24 = true := by decide +kernel
theorem plane0_row25 : planeRowOK planeCentres0 planeLinear0 25 = true := by decide +kernel
theorem plane0_row26 : planeRowOK planeCentres0 planeLinear0 26 = true := by decide +kernel
theorem plane0_row27 : planeRowOK planeCentres0 planeLinear0 27 = true := by decide +kernel
theorem plane0_row28 : planeRowOK planeCentres0 planeLinear0 28 = true := by decide +kernel
theorem plane0_row29 : planeRowOK planeCentres0 planeLinear0 29 = true := by decide +kernel
theorem plane0_row30 : planeRowOK planeCentres0 planeLinear0 30 = true := by decide +kernel
theorem plane0_row31 : planeRowOK planeCentres0 planeLinear0 31 = true := by decide +kernel
theorem plane0_row32 : planeRowOK planeCentres0 planeLinear0 32 = true := by decide +kernel
theorem plane0_row33 : planeRowOK planeCentres0 planeLinear0 33 = true := by decide +kernel
theorem plane0_row34 : planeRowOK planeCentres0 planeLinear0 34 = true := by decide +kernel
theorem plane0_row35 : planeRowOK planeCentres0 planeLinear0 35 = true := by decide +kernel
theorem plane0_row36 : planeRowOK planeCentres0 planeLinear0 36 = true := by decide +kernel
theorem plane0_row37 : planeRowOK planeCentres0 planeLinear0 37 = true := by decide +kernel
theorem plane0_row38 : planeRowOK planeCentres0 planeLinear0 38 = true := by decide +kernel
theorem plane0_row39 : planeRowOK planeCentres0 planeLinear0 39 = true := by decide +kernel
theorem plane0_row40 : planeRowOK planeCentres0 planeLinear0 40 = true := by decide +kernel
theorem plane0_row41 : planeRowOK planeCentres0 planeLinear0 41 = true := by decide +kernel
theorem plane0_row42 : planeRowOK planeCentres0 planeLinear0 42 = true := by decide +kernel
theorem plane0_row43 : planeRowOK planeCentres0 planeLinear0 43 = true := by decide +kernel
theorem plane0_row44 : planeRowOK planeCentres0 planeLinear0 44 = true := by decide +kernel
theorem plane0_row45 : planeRowOK planeCentres0 planeLinear0 45 = true := by decide +kernel
theorem plane0_row46 : planeRowOK planeCentres0 planeLinear0 46 = true := by decide +kernel
theorem plane0_row47 : planeRowOK planeCentres0 planeLinear0 47 = true := by decide +kernel
theorem plane0_row48 : planeRowOK planeCentres0 planeLinear0 48 = true := by decide +kernel
theorem plane0_rows (k : ℕ) (hk : k < 49) :
    planeRowOK planeCentres0 planeLinear0 k = true := by
  interval_cases k
  · exact plane0_row0
  · exact plane0_row1
  · exact plane0_row2
  · exact plane0_row3
  · exact plane0_row4
  · exact plane0_row5
  · exact plane0_row6
  · exact plane0_row7
  · exact plane0_row8
  · exact plane0_row9
  · exact plane0_row10
  · exact plane0_row11
  · exact plane0_row12
  · exact plane0_row13
  · exact plane0_row14
  · exact plane0_row15
  · exact plane0_row16
  · exact plane0_row17
  · exact plane0_row18
  · exact plane0_row19
  · exact plane0_row20
  · exact plane0_row21
  · exact plane0_row22
  · exact plane0_row23
  · exact plane0_row24
  · exact plane0_row25
  · exact plane0_row26
  · exact plane0_row27
  · exact plane0_row28
  · exact plane0_row29
  · exact plane0_row30
  · exact plane0_row31
  · exact plane0_row32
  · exact plane0_row33
  · exact plane0_row34
  · exact plane0_row35
  · exact plane0_row36
  · exact plane0_row37
  · exact plane0_row38
  · exact plane0_row39
  · exact plane0_row40
  · exact plane0_row41
  · exact plane0_row42
  · exact plane0_row43
  · exact plane0_row44
  · exact plane0_row45
  · exact plane0_row46
  · exact plane0_row47
  · exact plane0_row48
noncomputable section
theorem plane0_census_identity (X : Finset E4) :
    (planeConstant0 : ℝ) + ((List.range 5).map fun i => (planeCounts0.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[0]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) := by
  norm_num [planeConstant0, planeCounts0, List.range_succ, breaks,
    CensusArithmetic.affine, CensusArithmetic.planeCoeffs, CensusArithmetic.denominator,
    CensusArithmetic.ofNeighbourhood, nearCount, R1, R2, R3, R4, R5]
  ring

theorem gram_energy_ge_plane0 (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (h1 : ∀ x ∈ X, 1 ≤ ‖x‖) :
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[0]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) ≤
    gramEnergy X := by
  rw [← plane0_census_identity]
  exact gram_plane_floor planeCentres0 planeLinear0 planeCounts0 planeConstant0
    plane0_constant plane0_rows X hX hR (fun x hx => plane0_radial ‖x‖ (h1 x hx) (hR x hx))
end
end D4Bound.V7.CensusGram
