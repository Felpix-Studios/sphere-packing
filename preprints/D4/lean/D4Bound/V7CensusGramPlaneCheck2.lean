import D4Bound.V7CensusGramPlanesBasic
import D4Bound.V7CensusGramPlane2
import D4Bound.CensusArithmetic
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem plane2_constant : planeConstantOK planeCentres2 planeConstant2 = true := by decide +kernel
theorem plane2_row0 : planeRowOK planeCentres2 planeLinear2 0 = true := by decide +kernel
theorem plane2_row1 : planeRowOK planeCentres2 planeLinear2 1 = true := by decide +kernel
theorem plane2_row2 : planeRowOK planeCentres2 planeLinear2 2 = true := by decide +kernel
theorem plane2_row3 : planeRowOK planeCentres2 planeLinear2 3 = true := by decide +kernel
theorem plane2_row4 : planeRowOK planeCentres2 planeLinear2 4 = true := by decide +kernel
theorem plane2_row5 : planeRowOK planeCentres2 planeLinear2 5 = true := by decide +kernel
theorem plane2_row6 : planeRowOK planeCentres2 planeLinear2 6 = true := by decide +kernel
theorem plane2_row7 : planeRowOK planeCentres2 planeLinear2 7 = true := by decide +kernel
theorem plane2_row8 : planeRowOK planeCentres2 planeLinear2 8 = true := by decide +kernel
theorem plane2_row9 : planeRowOK planeCentres2 planeLinear2 9 = true := by decide +kernel
theorem plane2_row10 : planeRowOK planeCentres2 planeLinear2 10 = true := by decide +kernel
theorem plane2_row11 : planeRowOK planeCentres2 planeLinear2 11 = true := by decide +kernel
theorem plane2_row12 : planeRowOK planeCentres2 planeLinear2 12 = true := by decide +kernel
theorem plane2_row13 : planeRowOK planeCentres2 planeLinear2 13 = true := by decide +kernel
theorem plane2_row14 : planeRowOK planeCentres2 planeLinear2 14 = true := by decide +kernel
theorem plane2_row15 : planeRowOK planeCentres2 planeLinear2 15 = true := by decide +kernel
theorem plane2_row16 : planeRowOK planeCentres2 planeLinear2 16 = true := by decide +kernel
theorem plane2_row17 : planeRowOK planeCentres2 planeLinear2 17 = true := by decide +kernel
theorem plane2_row18 : planeRowOK planeCentres2 planeLinear2 18 = true := by decide +kernel
theorem plane2_row19 : planeRowOK planeCentres2 planeLinear2 19 = true := by decide +kernel
theorem plane2_row20 : planeRowOK planeCentres2 planeLinear2 20 = true := by decide +kernel
theorem plane2_row21 : planeRowOK planeCentres2 planeLinear2 21 = true := by decide +kernel
theorem plane2_row22 : planeRowOK planeCentres2 planeLinear2 22 = true := by decide +kernel
theorem plane2_row23 : planeRowOK planeCentres2 planeLinear2 23 = true := by decide +kernel
theorem plane2_row24 : planeRowOK planeCentres2 planeLinear2 24 = true := by decide +kernel
theorem plane2_row25 : planeRowOK planeCentres2 planeLinear2 25 = true := by decide +kernel
theorem plane2_row26 : planeRowOK planeCentres2 planeLinear2 26 = true := by decide +kernel
theorem plane2_row27 : planeRowOK planeCentres2 planeLinear2 27 = true := by decide +kernel
theorem plane2_row28 : planeRowOK planeCentres2 planeLinear2 28 = true := by decide +kernel
theorem plane2_row29 : planeRowOK planeCentres2 planeLinear2 29 = true := by decide +kernel
theorem plane2_row30 : planeRowOK planeCentres2 planeLinear2 30 = true := by decide +kernel
theorem plane2_row31 : planeRowOK planeCentres2 planeLinear2 31 = true := by decide +kernel
theorem plane2_row32 : planeRowOK planeCentres2 planeLinear2 32 = true := by decide +kernel
theorem plane2_row33 : planeRowOK planeCentres2 planeLinear2 33 = true := by decide +kernel
theorem plane2_row34 : planeRowOK planeCentres2 planeLinear2 34 = true := by decide +kernel
theorem plane2_row35 : planeRowOK planeCentres2 planeLinear2 35 = true := by decide +kernel
theorem plane2_row36 : planeRowOK planeCentres2 planeLinear2 36 = true := by decide +kernel
theorem plane2_row37 : planeRowOK planeCentres2 planeLinear2 37 = true := by decide +kernel
theorem plane2_row38 : planeRowOK planeCentres2 planeLinear2 38 = true := by decide +kernel
theorem plane2_row39 : planeRowOK planeCentres2 planeLinear2 39 = true := by decide +kernel
theorem plane2_row40 : planeRowOK planeCentres2 planeLinear2 40 = true := by decide +kernel
theorem plane2_row41 : planeRowOK planeCentres2 planeLinear2 41 = true := by decide +kernel
theorem plane2_row42 : planeRowOK planeCentres2 planeLinear2 42 = true := by decide +kernel
theorem plane2_row43 : planeRowOK planeCentres2 planeLinear2 43 = true := by decide +kernel
theorem plane2_row44 : planeRowOK planeCentres2 planeLinear2 44 = true := by decide +kernel
theorem plane2_row45 : planeRowOK planeCentres2 planeLinear2 45 = true := by decide +kernel
theorem plane2_row46 : planeRowOK planeCentres2 planeLinear2 46 = true := by decide +kernel
theorem plane2_row47 : planeRowOK planeCentres2 planeLinear2 47 = true := by decide +kernel
theorem plane2_row48 : planeRowOK planeCentres2 planeLinear2 48 = true := by decide +kernel
theorem plane2_rows (k : ℕ) (hk : k < 49) :
    planeRowOK planeCentres2 planeLinear2 k = true := by
  interval_cases k
  · exact plane2_row0
  · exact plane2_row1
  · exact plane2_row2
  · exact plane2_row3
  · exact plane2_row4
  · exact plane2_row5
  · exact plane2_row6
  · exact plane2_row7
  · exact plane2_row8
  · exact plane2_row9
  · exact plane2_row10
  · exact plane2_row11
  · exact plane2_row12
  · exact plane2_row13
  · exact plane2_row14
  · exact plane2_row15
  · exact plane2_row16
  · exact plane2_row17
  · exact plane2_row18
  · exact plane2_row19
  · exact plane2_row20
  · exact plane2_row21
  · exact plane2_row22
  · exact plane2_row23
  · exact plane2_row24
  · exact plane2_row25
  · exact plane2_row26
  · exact plane2_row27
  · exact plane2_row28
  · exact plane2_row29
  · exact plane2_row30
  · exact plane2_row31
  · exact plane2_row32
  · exact plane2_row33
  · exact plane2_row34
  · exact plane2_row35
  · exact plane2_row36
  · exact plane2_row37
  · exact plane2_row38
  · exact plane2_row39
  · exact plane2_row40
  · exact plane2_row41
  · exact plane2_row42
  · exact plane2_row43
  · exact plane2_row44
  · exact plane2_row45
  · exact plane2_row46
  · exact plane2_row47
  · exact plane2_row48
noncomputable section
theorem plane2_census_identity (X : Finset E4) :
    (planeConstant2 : ℝ) + ((List.range 5).map fun i => (planeCounts2.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[2]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) := by
  norm_num [planeConstant2, planeCounts2, List.range_succ, breaks,
    CensusArithmetic.affine, CensusArithmetic.planeCoeffs, CensusArithmetic.denominator,
    CensusArithmetic.ofNeighbourhood, nearCount, R1, R2, R3, R4, R5]
  ring

theorem gram_energy_ge_plane2 (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (h1 : ∀ x ∈ X, 1 ≤ ‖x‖) :
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[2]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) ≤
    gramEnergy X := by
  rw [← plane2_census_identity]
  exact gram_plane_floor planeCentres2 planeLinear2 planeCounts2 planeConstant2
    plane2_constant plane2_rows X hX hR (fun x hx => plane2_radial ‖x‖ (h1 x hx) (hR x hx))
end
end D4Bound.V7.CensusGram
