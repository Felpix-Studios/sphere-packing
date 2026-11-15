import D4Bound.V7CensusGramPlanesBasic
import D4Bound.V7CensusGramPlane4
import D4Bound.CensusArithmetic
import D4Bound.V7CensusGramCensusIdentity
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem plane4_constant : planeConstantOK planeCentres4 planeConstant4 = true := by decide +kernel
theorem plane4_row0 : planeRowOK planeCentres4 planeLinear4 0 = true := by decide +kernel
theorem plane4_row1 : planeRowOK planeCentres4 planeLinear4 1 = true := by decide +kernel
theorem plane4_row2 : planeRowOK planeCentres4 planeLinear4 2 = true := by decide +kernel
theorem plane4_row3 : planeRowOK planeCentres4 planeLinear4 3 = true := by decide +kernel
theorem plane4_row4 : planeRowOK planeCentres4 planeLinear4 4 = true := by decide +kernel
theorem plane4_row5 : planeRowOK planeCentres4 planeLinear4 5 = true := by decide +kernel
theorem plane4_row6 : planeRowOK planeCentres4 planeLinear4 6 = true := by decide +kernel
theorem plane4_row7 : planeRowOK planeCentres4 planeLinear4 7 = true := by decide +kernel
theorem plane4_row8 : planeRowOK planeCentres4 planeLinear4 8 = true := by decide +kernel
theorem plane4_row9 : planeRowOK planeCentres4 planeLinear4 9 = true := by decide +kernel
theorem plane4_row10 : planeRowOK planeCentres4 planeLinear4 10 = true := by decide +kernel
theorem plane4_row11 : planeRowOK planeCentres4 planeLinear4 11 = true := by decide +kernel
theorem plane4_row12 : planeRowOK planeCentres4 planeLinear4 12 = true := by decide +kernel
theorem plane4_row13 : planeRowOK planeCentres4 planeLinear4 13 = true := by decide +kernel
theorem plane4_row14 : planeRowOK planeCentres4 planeLinear4 14 = true := by decide +kernel
theorem plane4_row15 : planeRowOK planeCentres4 planeLinear4 15 = true := by decide +kernel
theorem plane4_row16 : planeRowOK planeCentres4 planeLinear4 16 = true := by decide +kernel
theorem plane4_row17 : planeRowOK planeCentres4 planeLinear4 17 = true := by decide +kernel
theorem plane4_row18 : planeRowOK planeCentres4 planeLinear4 18 = true := by decide +kernel
theorem plane4_row19 : planeRowOK planeCentres4 planeLinear4 19 = true := by decide +kernel
theorem plane4_row20 : planeRowOK planeCentres4 planeLinear4 20 = true := by decide +kernel
theorem plane4_row21 : planeRowOK planeCentres4 planeLinear4 21 = true := by decide +kernel
theorem plane4_row22 : planeRowOK planeCentres4 planeLinear4 22 = true := by decide +kernel
theorem plane4_row23 : planeRowOK planeCentres4 planeLinear4 23 = true := by decide +kernel
theorem plane4_row24 : planeRowOK planeCentres4 planeLinear4 24 = true := by decide +kernel
theorem plane4_row25 : planeRowOK planeCentres4 planeLinear4 25 = true := by decide +kernel
theorem plane4_row26 : planeRowOK planeCentres4 planeLinear4 26 = true := by decide +kernel
theorem plane4_row27 : planeRowOK planeCentres4 planeLinear4 27 = true := by decide +kernel
theorem plane4_row28 : planeRowOK planeCentres4 planeLinear4 28 = true := by decide +kernel
theorem plane4_row29 : planeRowOK planeCentres4 planeLinear4 29 = true := by decide +kernel
theorem plane4_row30 : planeRowOK planeCentres4 planeLinear4 30 = true := by decide +kernel
theorem plane4_row31 : planeRowOK planeCentres4 planeLinear4 31 = true := by decide +kernel
theorem plane4_row32 : planeRowOK planeCentres4 planeLinear4 32 = true := by decide +kernel
theorem plane4_row33 : planeRowOK planeCentres4 planeLinear4 33 = true := by decide +kernel
theorem plane4_row34 : planeRowOK planeCentres4 planeLinear4 34 = true := by decide +kernel
theorem plane4_row35 : planeRowOK planeCentres4 planeLinear4 35 = true := by decide +kernel
theorem plane4_row36 : planeRowOK planeCentres4 planeLinear4 36 = true := by decide +kernel
theorem plane4_row37 : planeRowOK planeCentres4 planeLinear4 37 = true := by decide +kernel
theorem plane4_row38 : planeRowOK planeCentres4 planeLinear4 38 = true := by decide +kernel
theorem plane4_row39 : planeRowOK planeCentres4 planeLinear4 39 = true := by decide +kernel
theorem plane4_row40 : planeRowOK planeCentres4 planeLinear4 40 = true := by decide +kernel
theorem plane4_row41 : planeRowOK planeCentres4 planeLinear4 41 = true := by decide +kernel
theorem plane4_row42 : planeRowOK planeCentres4 planeLinear4 42 = true := by decide +kernel
theorem plane4_row43 : planeRowOK planeCentres4 planeLinear4 43 = true := by decide +kernel
theorem plane4_row44 : planeRowOK planeCentres4 planeLinear4 44 = true := by decide +kernel
theorem plane4_row45 : planeRowOK planeCentres4 planeLinear4 45 = true := by decide +kernel
theorem plane4_row46 : planeRowOK planeCentres4 planeLinear4 46 = true := by decide +kernel
theorem plane4_row47 : planeRowOK planeCentres4 planeLinear4 47 = true := by decide +kernel
theorem plane4_row48 : planeRowOK planeCentres4 planeLinear4 48 = true := by decide +kernel
theorem plane4_rows (k : ℕ) (hk : k < 49) :
    planeRowOK planeCentres4 planeLinear4 k = true := by
  interval_cases k
  · exact plane4_row0
  · exact plane4_row1
  · exact plane4_row2
  · exact plane4_row3
  · exact plane4_row4
  · exact plane4_row5
  · exact plane4_row6
  · exact plane4_row7
  · exact plane4_row8
  · exact plane4_row9
  · exact plane4_row10
  · exact plane4_row11
  · exact plane4_row12
  · exact plane4_row13
  · exact plane4_row14
  · exact plane4_row15
  · exact plane4_row16
  · exact plane4_row17
  · exact plane4_row18
  · exact plane4_row19
  · exact plane4_row20
  · exact plane4_row21
  · exact plane4_row22
  · exact plane4_row23
  · exact plane4_row24
  · exact plane4_row25
  · exact plane4_row26
  · exact plane4_row27
  · exact plane4_row28
  · exact plane4_row29
  · exact plane4_row30
  · exact plane4_row31
  · exact plane4_row32
  · exact plane4_row33
  · exact plane4_row34
  · exact plane4_row35
  · exact plane4_row36
  · exact plane4_row37
  · exact plane4_row38
  · exact plane4_row39
  · exact plane4_row40
  · exact plane4_row41
  · exact plane4_row42
  · exact plane4_row43
  · exact plane4_row44
  · exact plane4_row45
  · exact plane4_row46
  · exact plane4_row47
  · exact plane4_row48
noncomputable section
theorem plane4_census_identity (X : Finset E4) :
    (planeConstant4 : ℝ) + ((List.range 5).map fun i => (planeCounts4.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[4]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) := by
  apply affine_count_identity planeCounts4 planeConstant4
    (CensusArithmetic.planeCoeffs[4]!)
  · decide +kernel
  · intro i hi
    interval_cases i <;> decide +kernel

theorem gram_energy_ge_plane4 (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (h1 : ∀ x ∈ X, 1 ≤ ‖x‖) :
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[4]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) ≤
    gramEnergy X := by
  rw [← plane4_census_identity]
  exact gram_plane_floor planeCentres4 planeLinear4 planeCounts4 planeConstant4
    plane4_constant plane4_rows X hX hR (fun x hx => plane4_radial ‖x‖ (h1 x hx) (hR x hx))
end
end D4Bound.V7.CensusGram
