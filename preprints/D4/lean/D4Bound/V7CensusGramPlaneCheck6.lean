import D4Bound.V7CensusGramPlanesBasic
import D4Bound.V7CensusGramPlane6
import D4Bound.CensusArithmetic
import D4Bound.V7CensusGramCensusIdentity
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem plane6_constant : planeConstantOK planeCentres6 planeConstant6 = true := by decide +kernel
theorem plane6_row0 : planeRowOK planeCentres6 planeLinear6 0 = true := by decide +kernel
theorem plane6_row1 : planeRowOK planeCentres6 planeLinear6 1 = true := by decide +kernel
theorem plane6_row2 : planeRowOK planeCentres6 planeLinear6 2 = true := by decide +kernel
theorem plane6_row3 : planeRowOK planeCentres6 planeLinear6 3 = true := by decide +kernel
theorem plane6_row4 : planeRowOK planeCentres6 planeLinear6 4 = true := by decide +kernel
theorem plane6_row5 : planeRowOK planeCentres6 planeLinear6 5 = true := by decide +kernel
theorem plane6_row6 : planeRowOK planeCentres6 planeLinear6 6 = true := by decide +kernel
theorem plane6_row7 : planeRowOK planeCentres6 planeLinear6 7 = true := by decide +kernel
theorem plane6_row8 : planeRowOK planeCentres6 planeLinear6 8 = true := by decide +kernel
theorem plane6_row9 : planeRowOK planeCentres6 planeLinear6 9 = true := by decide +kernel
theorem plane6_row10 : planeRowOK planeCentres6 planeLinear6 10 = true := by decide +kernel
theorem plane6_row11 : planeRowOK planeCentres6 planeLinear6 11 = true := by decide +kernel
theorem plane6_row12 : planeRowOK planeCentres6 planeLinear6 12 = true := by decide +kernel
theorem plane6_row13 : planeRowOK planeCentres6 planeLinear6 13 = true := by decide +kernel
theorem plane6_row14 : planeRowOK planeCentres6 planeLinear6 14 = true := by decide +kernel
theorem plane6_row15 : planeRowOK planeCentres6 planeLinear6 15 = true := by decide +kernel
theorem plane6_row16 : planeRowOK planeCentres6 planeLinear6 16 = true := by decide +kernel
theorem plane6_row17 : planeRowOK planeCentres6 planeLinear6 17 = true := by decide +kernel
theorem plane6_row18 : planeRowOK planeCentres6 planeLinear6 18 = true := by decide +kernel
theorem plane6_row19 : planeRowOK planeCentres6 planeLinear6 19 = true := by decide +kernel
theorem plane6_row20 : planeRowOK planeCentres6 planeLinear6 20 = true := by decide +kernel
theorem plane6_row21 : planeRowOK planeCentres6 planeLinear6 21 = true := by decide +kernel
theorem plane6_row22 : planeRowOK planeCentres6 planeLinear6 22 = true := by decide +kernel
theorem plane6_row23 : planeRowOK planeCentres6 planeLinear6 23 = true := by decide +kernel
theorem plane6_row24 : planeRowOK planeCentres6 planeLinear6 24 = true := by decide +kernel
theorem plane6_row25 : planeRowOK planeCentres6 planeLinear6 25 = true := by decide +kernel
theorem plane6_row26 : planeRowOK planeCentres6 planeLinear6 26 = true := by decide +kernel
theorem plane6_row27 : planeRowOK planeCentres6 planeLinear6 27 = true := by decide +kernel
theorem plane6_row28 : planeRowOK planeCentres6 planeLinear6 28 = true := by decide +kernel
theorem plane6_row29 : planeRowOK planeCentres6 planeLinear6 29 = true := by decide +kernel
theorem plane6_row30 : planeRowOK planeCentres6 planeLinear6 30 = true := by decide +kernel
theorem plane6_row31 : planeRowOK planeCentres6 planeLinear6 31 = true := by decide +kernel
theorem plane6_row32 : planeRowOK planeCentres6 planeLinear6 32 = true := by decide +kernel
theorem plane6_row33 : planeRowOK planeCentres6 planeLinear6 33 = true := by decide +kernel
theorem plane6_row34 : planeRowOK planeCentres6 planeLinear6 34 = true := by decide +kernel
theorem plane6_row35 : planeRowOK planeCentres6 planeLinear6 35 = true := by decide +kernel
theorem plane6_row36 : planeRowOK planeCentres6 planeLinear6 36 = true := by decide +kernel
theorem plane6_row37 : planeRowOK planeCentres6 planeLinear6 37 = true := by decide +kernel
theorem plane6_row38 : planeRowOK planeCentres6 planeLinear6 38 = true := by decide +kernel
theorem plane6_row39 : planeRowOK planeCentres6 planeLinear6 39 = true := by decide +kernel
theorem plane6_row40 : planeRowOK planeCentres6 planeLinear6 40 = true := by decide +kernel
theorem plane6_row41 : planeRowOK planeCentres6 planeLinear6 41 = true := by decide +kernel
theorem plane6_row42 : planeRowOK planeCentres6 planeLinear6 42 = true := by decide +kernel
theorem plane6_row43 : planeRowOK planeCentres6 planeLinear6 43 = true := by decide +kernel
theorem plane6_row44 : planeRowOK planeCentres6 planeLinear6 44 = true := by decide +kernel
theorem plane6_row45 : planeRowOK planeCentres6 planeLinear6 45 = true := by decide +kernel
theorem plane6_row46 : planeRowOK planeCentres6 planeLinear6 46 = true := by decide +kernel
theorem plane6_row47 : planeRowOK planeCentres6 planeLinear6 47 = true := by decide +kernel
theorem plane6_row48 : planeRowOK planeCentres6 planeLinear6 48 = true := by decide +kernel
theorem plane6_rows (k : ℕ) (hk : k < 49) :
    planeRowOK planeCentres6 planeLinear6 k = true := by
  interval_cases k
  · exact plane6_row0
  · exact plane6_row1
  · exact plane6_row2
  · exact plane6_row3
  · exact plane6_row4
  · exact plane6_row5
  · exact plane6_row6
  · exact plane6_row7
  · exact plane6_row8
  · exact plane6_row9
  · exact plane6_row10
  · exact plane6_row11
  · exact plane6_row12
  · exact plane6_row13
  · exact plane6_row14
  · exact plane6_row15
  · exact plane6_row16
  · exact plane6_row17
  · exact plane6_row18
  · exact plane6_row19
  · exact plane6_row20
  · exact plane6_row21
  · exact plane6_row22
  · exact plane6_row23
  · exact plane6_row24
  · exact plane6_row25
  · exact plane6_row26
  · exact plane6_row27
  · exact plane6_row28
  · exact plane6_row29
  · exact plane6_row30
  · exact plane6_row31
  · exact plane6_row32
  · exact plane6_row33
  · exact plane6_row34
  · exact plane6_row35
  · exact plane6_row36
  · exact plane6_row37
  · exact plane6_row38
  · exact plane6_row39
  · exact plane6_row40
  · exact plane6_row41
  · exact plane6_row42
  · exact plane6_row43
  · exact plane6_row44
  · exact plane6_row45
  · exact plane6_row46
  · exact plane6_row47
  · exact plane6_row48
noncomputable section
theorem plane6_census_identity (X : Finset E4) :
    (planeConstant6 : ℝ) + ((List.range 5).map fun i => (planeCounts6.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[6]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) := by
  apply affine_count_identity planeCounts6 planeConstant6
    (CensusArithmetic.planeCoeffs[6]!)
  · decide +kernel
  · intro i hi
    interval_cases i <;> decide +kernel

theorem gram_energy_ge_plane6 (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (h1 : ∀ x ∈ X, 1 ≤ ‖x‖) :
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[6]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) ≤
    gramEnergy X := by
  rw [← plane6_census_identity]
  exact gram_plane_floor planeCentres6 planeLinear6 planeCounts6 planeConstant6
    plane6_constant plane6_rows X hX hR (fun x hx => plane6_radial ‖x‖ (h1 x hx) (hR x hx))
end
end D4Bound.V7.CensusGram
