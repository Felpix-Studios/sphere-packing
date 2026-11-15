import D4Bound.V7CensusGramPlanesBasic
import D4Bound.V7CensusGramPlane11
import D4Bound.CensusArithmetic
import D4Bound.V7CensusGramCensusIdentity
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem plane11_constant : planeConstantOK planeCentres11 planeConstant11 = true := by decide +kernel
theorem plane11_row0 : planeRowOK planeCentres11 planeLinear11 0 = true := by decide +kernel
theorem plane11_row1 : planeRowOK planeCentres11 planeLinear11 1 = true := by decide +kernel
theorem plane11_row2 : planeRowOK planeCentres11 planeLinear11 2 = true := by decide +kernel
theorem plane11_row3 : planeRowOK planeCentres11 planeLinear11 3 = true := by decide +kernel
theorem plane11_row4 : planeRowOK planeCentres11 planeLinear11 4 = true := by decide +kernel
theorem plane11_row5 : planeRowOK planeCentres11 planeLinear11 5 = true := by decide +kernel
theorem plane11_row6 : planeRowOK planeCentres11 planeLinear11 6 = true := by decide +kernel
theorem plane11_row7 : planeRowOK planeCentres11 planeLinear11 7 = true := by decide +kernel
theorem plane11_row8 : planeRowOK planeCentres11 planeLinear11 8 = true := by decide +kernel
theorem plane11_row9 : planeRowOK planeCentres11 planeLinear11 9 = true := by decide +kernel
theorem plane11_row10 : planeRowOK planeCentres11 planeLinear11 10 = true := by decide +kernel
theorem plane11_row11 : planeRowOK planeCentres11 planeLinear11 11 = true := by decide +kernel
theorem plane11_row12 : planeRowOK planeCentres11 planeLinear11 12 = true := by decide +kernel
theorem plane11_row13 : planeRowOK planeCentres11 planeLinear11 13 = true := by decide +kernel
theorem plane11_row14 : planeRowOK planeCentres11 planeLinear11 14 = true := by decide +kernel
theorem plane11_row15 : planeRowOK planeCentres11 planeLinear11 15 = true := by decide +kernel
theorem plane11_row16 : planeRowOK planeCentres11 planeLinear11 16 = true := by decide +kernel
theorem plane11_row17 : planeRowOK planeCentres11 planeLinear11 17 = true := by decide +kernel
theorem plane11_row18 : planeRowOK planeCentres11 planeLinear11 18 = true := by decide +kernel
theorem plane11_row19 : planeRowOK planeCentres11 planeLinear11 19 = true := by decide +kernel
theorem plane11_row20 : planeRowOK planeCentres11 planeLinear11 20 = true := by decide +kernel
theorem plane11_row21 : planeRowOK planeCentres11 planeLinear11 21 = true := by decide +kernel
theorem plane11_row22 : planeRowOK planeCentres11 planeLinear11 22 = true := by decide +kernel
theorem plane11_row23 : planeRowOK planeCentres11 planeLinear11 23 = true := by decide +kernel
theorem plane11_row24 : planeRowOK planeCentres11 planeLinear11 24 = true := by decide +kernel
theorem plane11_row25 : planeRowOK planeCentres11 planeLinear11 25 = true := by decide +kernel
theorem plane11_row26 : planeRowOK planeCentres11 planeLinear11 26 = true := by decide +kernel
theorem plane11_row27 : planeRowOK planeCentres11 planeLinear11 27 = true := by decide +kernel
theorem plane11_row28 : planeRowOK planeCentres11 planeLinear11 28 = true := by decide +kernel
theorem plane11_row29 : planeRowOK planeCentres11 planeLinear11 29 = true := by decide +kernel
theorem plane11_row30 : planeRowOK planeCentres11 planeLinear11 30 = true := by decide +kernel
theorem plane11_row31 : planeRowOK planeCentres11 planeLinear11 31 = true := by decide +kernel
theorem plane11_row32 : planeRowOK planeCentres11 planeLinear11 32 = true := by decide +kernel
theorem plane11_row33 : planeRowOK planeCentres11 planeLinear11 33 = true := by decide +kernel
theorem plane11_row34 : planeRowOK planeCentres11 planeLinear11 34 = true := by decide +kernel
theorem plane11_row35 : planeRowOK planeCentres11 planeLinear11 35 = true := by decide +kernel
theorem plane11_row36 : planeRowOK planeCentres11 planeLinear11 36 = true := by decide +kernel
theorem plane11_row37 : planeRowOK planeCentres11 planeLinear11 37 = true := by decide +kernel
theorem plane11_row38 : planeRowOK planeCentres11 planeLinear11 38 = true := by decide +kernel
theorem plane11_row39 : planeRowOK planeCentres11 planeLinear11 39 = true := by decide +kernel
theorem plane11_row40 : planeRowOK planeCentres11 planeLinear11 40 = true := by decide +kernel
theorem plane11_row41 : planeRowOK planeCentres11 planeLinear11 41 = true := by decide +kernel
theorem plane11_row42 : planeRowOK planeCentres11 planeLinear11 42 = true := by decide +kernel
theorem plane11_row43 : planeRowOK planeCentres11 planeLinear11 43 = true := by decide +kernel
theorem plane11_row44 : planeRowOK planeCentres11 planeLinear11 44 = true := by decide +kernel
theorem plane11_row45 : planeRowOK planeCentres11 planeLinear11 45 = true := by decide +kernel
theorem plane11_row46 : planeRowOK planeCentres11 planeLinear11 46 = true := by decide +kernel
theorem plane11_row47 : planeRowOK planeCentres11 planeLinear11 47 = true := by decide +kernel
theorem plane11_row48 : planeRowOK planeCentres11 planeLinear11 48 = true := by decide +kernel
theorem plane11_rows (k : ℕ) (hk : k < 49) :
    planeRowOK planeCentres11 planeLinear11 k = true := by
  interval_cases k
  · exact plane11_row0
  · exact plane11_row1
  · exact plane11_row2
  · exact plane11_row3
  · exact plane11_row4
  · exact plane11_row5
  · exact plane11_row6
  · exact plane11_row7
  · exact plane11_row8
  · exact plane11_row9
  · exact plane11_row10
  · exact plane11_row11
  · exact plane11_row12
  · exact plane11_row13
  · exact plane11_row14
  · exact plane11_row15
  · exact plane11_row16
  · exact plane11_row17
  · exact plane11_row18
  · exact plane11_row19
  · exact plane11_row20
  · exact plane11_row21
  · exact plane11_row22
  · exact plane11_row23
  · exact plane11_row24
  · exact plane11_row25
  · exact plane11_row26
  · exact plane11_row27
  · exact plane11_row28
  · exact plane11_row29
  · exact plane11_row30
  · exact plane11_row31
  · exact plane11_row32
  · exact plane11_row33
  · exact plane11_row34
  · exact plane11_row35
  · exact plane11_row36
  · exact plane11_row37
  · exact plane11_row38
  · exact plane11_row39
  · exact plane11_row40
  · exact plane11_row41
  · exact plane11_row42
  · exact plane11_row43
  · exact plane11_row44
  · exact plane11_row45
  · exact plane11_row46
  · exact plane11_row47
  · exact plane11_row48
noncomputable section
theorem plane11_census_identity (X : Finset E4) :
    (planeConstant11 : ℝ) + ((List.range 5).map fun i => (planeCounts11.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[11]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) := by
  apply affine_count_identity planeCounts11 planeConstant11
    (CensusArithmetic.planeCoeffs[11]!)
  · decide +kernel
  · intro i hi
    interval_cases i <;> decide +kernel

theorem gram_energy_ge_plane11 (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (h1 : ∀ x ∈ X, 1 ≤ ‖x‖) :
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[11]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) ≤
    gramEnergy X := by
  rw [← plane11_census_identity]
  exact gram_plane_floor planeCentres11 planeLinear11 planeCounts11 planeConstant11
    plane11_constant plane11_rows X hX hR (fun x hx => plane11_radial ‖x‖ (h1 x hx) (hR x hx))
end
end D4Bound.V7.CensusGram
