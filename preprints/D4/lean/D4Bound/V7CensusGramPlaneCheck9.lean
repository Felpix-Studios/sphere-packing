import D4Bound.V7CensusGramPlanesBasic
import D4Bound.V7CensusGramPlane9
import D4Bound.CensusArithmetic
import D4Bound.V7CensusGramCensusIdentity
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem plane9_constant : planeConstantOK planeCentres9 planeConstant9 = true := by decide +kernel
theorem plane9_row0 : planeRowOK planeCentres9 planeLinear9 0 = true := by decide +kernel
theorem plane9_row1 : planeRowOK planeCentres9 planeLinear9 1 = true := by decide +kernel
theorem plane9_row2 : planeRowOK planeCentres9 planeLinear9 2 = true := by decide +kernel
theorem plane9_row3 : planeRowOK planeCentres9 planeLinear9 3 = true := by decide +kernel
theorem plane9_row4 : planeRowOK planeCentres9 planeLinear9 4 = true := by decide +kernel
theorem plane9_row5 : planeRowOK planeCentres9 planeLinear9 5 = true := by decide +kernel
theorem plane9_row6 : planeRowOK planeCentres9 planeLinear9 6 = true := by decide +kernel
theorem plane9_row7 : planeRowOK planeCentres9 planeLinear9 7 = true := by decide +kernel
theorem plane9_row8 : planeRowOK planeCentres9 planeLinear9 8 = true := by decide +kernel
theorem plane9_row9 : planeRowOK planeCentres9 planeLinear9 9 = true := by decide +kernel
theorem plane9_row10 : planeRowOK planeCentres9 planeLinear9 10 = true := by decide +kernel
theorem plane9_row11 : planeRowOK planeCentres9 planeLinear9 11 = true := by decide +kernel
theorem plane9_row12 : planeRowOK planeCentres9 planeLinear9 12 = true := by decide +kernel
theorem plane9_row13 : planeRowOK planeCentres9 planeLinear9 13 = true := by decide +kernel
theorem plane9_row14 : planeRowOK planeCentres9 planeLinear9 14 = true := by decide +kernel
theorem plane9_row15 : planeRowOK planeCentres9 planeLinear9 15 = true := by decide +kernel
theorem plane9_row16 : planeRowOK planeCentres9 planeLinear9 16 = true := by decide +kernel
theorem plane9_row17 : planeRowOK planeCentres9 planeLinear9 17 = true := by decide +kernel
theorem plane9_row18 : planeRowOK planeCentres9 planeLinear9 18 = true := by decide +kernel
theorem plane9_row19 : planeRowOK planeCentres9 planeLinear9 19 = true := by decide +kernel
theorem plane9_row20 : planeRowOK planeCentres9 planeLinear9 20 = true := by decide +kernel
theorem plane9_row21 : planeRowOK planeCentres9 planeLinear9 21 = true := by decide +kernel
theorem plane9_row22 : planeRowOK planeCentres9 planeLinear9 22 = true := by decide +kernel
theorem plane9_row23 : planeRowOK planeCentres9 planeLinear9 23 = true := by decide +kernel
theorem plane9_row24 : planeRowOK planeCentres9 planeLinear9 24 = true := by decide +kernel
theorem plane9_row25 : planeRowOK planeCentres9 planeLinear9 25 = true := by decide +kernel
theorem plane9_row26 : planeRowOK planeCentres9 planeLinear9 26 = true := by decide +kernel
theorem plane9_row27 : planeRowOK planeCentres9 planeLinear9 27 = true := by decide +kernel
theorem plane9_row28 : planeRowOK planeCentres9 planeLinear9 28 = true := by decide +kernel
theorem plane9_row29 : planeRowOK planeCentres9 planeLinear9 29 = true := by decide +kernel
theorem plane9_row30 : planeRowOK planeCentres9 planeLinear9 30 = true := by decide +kernel
theorem plane9_row31 : planeRowOK planeCentres9 planeLinear9 31 = true := by decide +kernel
theorem plane9_row32 : planeRowOK planeCentres9 planeLinear9 32 = true := by decide +kernel
theorem plane9_row33 : planeRowOK planeCentres9 planeLinear9 33 = true := by decide +kernel
theorem plane9_row34 : planeRowOK planeCentres9 planeLinear9 34 = true := by decide +kernel
theorem plane9_row35 : planeRowOK planeCentres9 planeLinear9 35 = true := by decide +kernel
theorem plane9_row36 : planeRowOK planeCentres9 planeLinear9 36 = true := by decide +kernel
theorem plane9_row37 : planeRowOK planeCentres9 planeLinear9 37 = true := by decide +kernel
theorem plane9_row38 : planeRowOK planeCentres9 planeLinear9 38 = true := by decide +kernel
theorem plane9_row39 : planeRowOK planeCentres9 planeLinear9 39 = true := by decide +kernel
theorem plane9_row40 : planeRowOK planeCentres9 planeLinear9 40 = true := by decide +kernel
theorem plane9_row41 : planeRowOK planeCentres9 planeLinear9 41 = true := by decide +kernel
theorem plane9_row42 : planeRowOK planeCentres9 planeLinear9 42 = true := by decide +kernel
theorem plane9_row43 : planeRowOK planeCentres9 planeLinear9 43 = true := by decide +kernel
theorem plane9_row44 : planeRowOK planeCentres9 planeLinear9 44 = true := by decide +kernel
theorem plane9_row45 : planeRowOK planeCentres9 planeLinear9 45 = true := by decide +kernel
theorem plane9_row46 : planeRowOK planeCentres9 planeLinear9 46 = true := by decide +kernel
theorem plane9_row47 : planeRowOK planeCentres9 planeLinear9 47 = true := by decide +kernel
theorem plane9_row48 : planeRowOK planeCentres9 planeLinear9 48 = true := by decide +kernel
theorem plane9_rows (k : ℕ) (hk : k < 49) :
    planeRowOK planeCentres9 planeLinear9 k = true := by
  interval_cases k
  · exact plane9_row0
  · exact plane9_row1
  · exact plane9_row2
  · exact plane9_row3
  · exact plane9_row4
  · exact plane9_row5
  · exact plane9_row6
  · exact plane9_row7
  · exact plane9_row8
  · exact plane9_row9
  · exact plane9_row10
  · exact plane9_row11
  · exact plane9_row12
  · exact plane9_row13
  · exact plane9_row14
  · exact plane9_row15
  · exact plane9_row16
  · exact plane9_row17
  · exact plane9_row18
  · exact plane9_row19
  · exact plane9_row20
  · exact plane9_row21
  · exact plane9_row22
  · exact plane9_row23
  · exact plane9_row24
  · exact plane9_row25
  · exact plane9_row26
  · exact plane9_row27
  · exact plane9_row28
  · exact plane9_row29
  · exact plane9_row30
  · exact plane9_row31
  · exact plane9_row32
  · exact plane9_row33
  · exact plane9_row34
  · exact plane9_row35
  · exact plane9_row36
  · exact plane9_row37
  · exact plane9_row38
  · exact plane9_row39
  · exact plane9_row40
  · exact plane9_row41
  · exact plane9_row42
  · exact plane9_row43
  · exact plane9_row44
  · exact plane9_row45
  · exact plane9_row46
  · exact plane9_row47
  · exact plane9_row48
noncomputable section
theorem plane9_census_identity (X : Finset E4) :
    (planeConstant9 : ℝ) + ((List.range 5).map fun i => (planeCounts9.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[9]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) := by
  apply affine_count_identity planeCounts9 planeConstant9
    (CensusArithmetic.planeCoeffs[9]!)
  · decide +kernel
  · intro i hi
    interval_cases i <;> decide +kernel

theorem gram_energy_ge_plane9 (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (h1 : ∀ x ∈ X, 1 ≤ ‖x‖) :
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[9]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) ≤
    gramEnergy X := by
  rw [← plane9_census_identity]
  exact gram_plane_floor planeCentres9 planeLinear9 planeCounts9 planeConstant9
    plane9_constant plane9_rows X hX hR (fun x hx => plane9_radial ‖x‖ (h1 x hx) (hR x hx))
end
end D4Bound.V7.CensusGram
