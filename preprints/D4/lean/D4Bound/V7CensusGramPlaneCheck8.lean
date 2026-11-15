import D4Bound.V7CensusGramPlanesBasic
import D4Bound.V7CensusGramPlane8
import D4Bound.CensusArithmetic
import D4Bound.V7CensusGramCensusIdentity
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem plane8_constant : planeConstantOK planeCentres8 planeConstant8 = true := by decide +kernel
theorem plane8_row0 : planeRowOK planeCentres8 planeLinear8 0 = true := by decide +kernel
theorem plane8_row1 : planeRowOK planeCentres8 planeLinear8 1 = true := by decide +kernel
theorem plane8_row2 : planeRowOK planeCentres8 planeLinear8 2 = true := by decide +kernel
theorem plane8_row3 : planeRowOK planeCentres8 planeLinear8 3 = true := by decide +kernel
theorem plane8_row4 : planeRowOK planeCentres8 planeLinear8 4 = true := by decide +kernel
theorem plane8_row5 : planeRowOK planeCentres8 planeLinear8 5 = true := by decide +kernel
theorem plane8_row6 : planeRowOK planeCentres8 planeLinear8 6 = true := by decide +kernel
theorem plane8_row7 : planeRowOK planeCentres8 planeLinear8 7 = true := by decide +kernel
theorem plane8_row8 : planeRowOK planeCentres8 planeLinear8 8 = true := by decide +kernel
theorem plane8_row9 : planeRowOK planeCentres8 planeLinear8 9 = true := by decide +kernel
theorem plane8_row10 : planeRowOK planeCentres8 planeLinear8 10 = true := by decide +kernel
theorem plane8_row11 : planeRowOK planeCentres8 planeLinear8 11 = true := by decide +kernel
theorem plane8_row12 : planeRowOK planeCentres8 planeLinear8 12 = true := by decide +kernel
theorem plane8_row13 : planeRowOK planeCentres8 planeLinear8 13 = true := by decide +kernel
theorem plane8_row14 : planeRowOK planeCentres8 planeLinear8 14 = true := by decide +kernel
theorem plane8_row15 : planeRowOK planeCentres8 planeLinear8 15 = true := by decide +kernel
theorem plane8_row16 : planeRowOK planeCentres8 planeLinear8 16 = true := by decide +kernel
theorem plane8_row17 : planeRowOK planeCentres8 planeLinear8 17 = true := by decide +kernel
theorem plane8_row18 : planeRowOK planeCentres8 planeLinear8 18 = true := by decide +kernel
theorem plane8_row19 : planeRowOK planeCentres8 planeLinear8 19 = true := by decide +kernel
theorem plane8_row20 : planeRowOK planeCentres8 planeLinear8 20 = true := by decide +kernel
theorem plane8_row21 : planeRowOK planeCentres8 planeLinear8 21 = true := by decide +kernel
theorem plane8_row22 : planeRowOK planeCentres8 planeLinear8 22 = true := by decide +kernel
theorem plane8_row23 : planeRowOK planeCentres8 planeLinear8 23 = true := by decide +kernel
theorem plane8_row24 : planeRowOK planeCentres8 planeLinear8 24 = true := by decide +kernel
theorem plane8_row25 : planeRowOK planeCentres8 planeLinear8 25 = true := by decide +kernel
theorem plane8_row26 : planeRowOK planeCentres8 planeLinear8 26 = true := by decide +kernel
theorem plane8_row27 : planeRowOK planeCentres8 planeLinear8 27 = true := by decide +kernel
theorem plane8_row28 : planeRowOK planeCentres8 planeLinear8 28 = true := by decide +kernel
theorem plane8_row29 : planeRowOK planeCentres8 planeLinear8 29 = true := by decide +kernel
theorem plane8_row30 : planeRowOK planeCentres8 planeLinear8 30 = true := by decide +kernel
theorem plane8_row31 : planeRowOK planeCentres8 planeLinear8 31 = true := by decide +kernel
theorem plane8_row32 : planeRowOK planeCentres8 planeLinear8 32 = true := by decide +kernel
theorem plane8_row33 : planeRowOK planeCentres8 planeLinear8 33 = true := by decide +kernel
theorem plane8_row34 : planeRowOK planeCentres8 planeLinear8 34 = true := by decide +kernel
theorem plane8_row35 : planeRowOK planeCentres8 planeLinear8 35 = true := by decide +kernel
theorem plane8_row36 : planeRowOK planeCentres8 planeLinear8 36 = true := by decide +kernel
theorem plane8_row37 : planeRowOK planeCentres8 planeLinear8 37 = true := by decide +kernel
theorem plane8_row38 : planeRowOK planeCentres8 planeLinear8 38 = true := by decide +kernel
theorem plane8_row39 : planeRowOK planeCentres8 planeLinear8 39 = true := by decide +kernel
theorem plane8_row40 : planeRowOK planeCentres8 planeLinear8 40 = true := by decide +kernel
theorem plane8_row41 : planeRowOK planeCentres8 planeLinear8 41 = true := by decide +kernel
theorem plane8_row42 : planeRowOK planeCentres8 planeLinear8 42 = true := by decide +kernel
theorem plane8_row43 : planeRowOK planeCentres8 planeLinear8 43 = true := by decide +kernel
theorem plane8_row44 : planeRowOK planeCentres8 planeLinear8 44 = true := by decide +kernel
theorem plane8_row45 : planeRowOK planeCentres8 planeLinear8 45 = true := by decide +kernel
theorem plane8_row46 : planeRowOK planeCentres8 planeLinear8 46 = true := by decide +kernel
theorem plane8_row47 : planeRowOK planeCentres8 planeLinear8 47 = true := by decide +kernel
theorem plane8_row48 : planeRowOK planeCentres8 planeLinear8 48 = true := by decide +kernel
theorem plane8_rows (k : ℕ) (hk : k < 49) :
    planeRowOK planeCentres8 planeLinear8 k = true := by
  interval_cases k
  · exact plane8_row0
  · exact plane8_row1
  · exact plane8_row2
  · exact plane8_row3
  · exact plane8_row4
  · exact plane8_row5
  · exact plane8_row6
  · exact plane8_row7
  · exact plane8_row8
  · exact plane8_row9
  · exact plane8_row10
  · exact plane8_row11
  · exact plane8_row12
  · exact plane8_row13
  · exact plane8_row14
  · exact plane8_row15
  · exact plane8_row16
  · exact plane8_row17
  · exact plane8_row18
  · exact plane8_row19
  · exact plane8_row20
  · exact plane8_row21
  · exact plane8_row22
  · exact plane8_row23
  · exact plane8_row24
  · exact plane8_row25
  · exact plane8_row26
  · exact plane8_row27
  · exact plane8_row28
  · exact plane8_row29
  · exact plane8_row30
  · exact plane8_row31
  · exact plane8_row32
  · exact plane8_row33
  · exact plane8_row34
  · exact plane8_row35
  · exact plane8_row36
  · exact plane8_row37
  · exact plane8_row38
  · exact plane8_row39
  · exact plane8_row40
  · exact plane8_row41
  · exact plane8_row42
  · exact plane8_row43
  · exact plane8_row44
  · exact plane8_row45
  · exact plane8_row46
  · exact plane8_row47
  · exact plane8_row48
noncomputable section
theorem plane8_census_identity (X : Finset E4) :
    (planeConstant8 : ℝ) + ((List.range 5).map fun i => (planeCounts8.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[8]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) := by
  apply affine_count_identity planeCounts8 planeConstant8
    (CensusArithmetic.planeCoeffs[8]!)
  · decide +kernel
  · intro i hi
    interval_cases i <;> decide +kernel

theorem gram_energy_ge_plane8 (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (h1 : ∀ x ∈ X, 1 ≤ ‖x‖) :
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[8]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) ≤
    gramEnergy X := by
  rw [← plane8_census_identity]
  exact gram_plane_floor planeCentres8 planeLinear8 planeCounts8 planeConstant8
    plane8_constant plane8_rows X hX hR (fun x hx => plane8_radial ‖x‖ (h1 x hx) (hR x hx))
end
end D4Bound.V7.CensusGram
