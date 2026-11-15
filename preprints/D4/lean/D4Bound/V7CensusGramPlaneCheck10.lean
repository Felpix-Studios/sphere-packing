import D4Bound.V7CensusGramPlanesBasic
import D4Bound.V7CensusGramPlane10
import D4Bound.CensusArithmetic
import D4Bound.V7CensusGramCensusIdentity
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem plane10_constant : planeConstantOK planeCentres10 planeConstant10 = true := by decide +kernel
theorem plane10_row0 : planeRowOK planeCentres10 planeLinear10 0 = true := by decide +kernel
theorem plane10_row1 : planeRowOK planeCentres10 planeLinear10 1 = true := by decide +kernel
theorem plane10_row2 : planeRowOK planeCentres10 planeLinear10 2 = true := by decide +kernel
theorem plane10_row3 : planeRowOK planeCentres10 planeLinear10 3 = true := by decide +kernel
theorem plane10_row4 : planeRowOK planeCentres10 planeLinear10 4 = true := by decide +kernel
theorem plane10_row5 : planeRowOK planeCentres10 planeLinear10 5 = true := by decide +kernel
theorem plane10_row6 : planeRowOK planeCentres10 planeLinear10 6 = true := by decide +kernel
theorem plane10_row7 : planeRowOK planeCentres10 planeLinear10 7 = true := by decide +kernel
theorem plane10_row8 : planeRowOK planeCentres10 planeLinear10 8 = true := by decide +kernel
theorem plane10_row9 : planeRowOK planeCentres10 planeLinear10 9 = true := by decide +kernel
theorem plane10_row10 : planeRowOK planeCentres10 planeLinear10 10 = true := by decide +kernel
theorem plane10_row11 : planeRowOK planeCentres10 planeLinear10 11 = true := by decide +kernel
theorem plane10_row12 : planeRowOK planeCentres10 planeLinear10 12 = true := by decide +kernel
theorem plane10_row13 : planeRowOK planeCentres10 planeLinear10 13 = true := by decide +kernel
theorem plane10_row14 : planeRowOK planeCentres10 planeLinear10 14 = true := by decide +kernel
theorem plane10_row15 : planeRowOK planeCentres10 planeLinear10 15 = true := by decide +kernel
theorem plane10_row16 : planeRowOK planeCentres10 planeLinear10 16 = true := by decide +kernel
theorem plane10_row17 : planeRowOK planeCentres10 planeLinear10 17 = true := by decide +kernel
theorem plane10_row18 : planeRowOK planeCentres10 planeLinear10 18 = true := by decide +kernel
theorem plane10_row19 : planeRowOK planeCentres10 planeLinear10 19 = true := by decide +kernel
theorem plane10_row20 : planeRowOK planeCentres10 planeLinear10 20 = true := by decide +kernel
theorem plane10_row21 : planeRowOK planeCentres10 planeLinear10 21 = true := by decide +kernel
theorem plane10_row22 : planeRowOK planeCentres10 planeLinear10 22 = true := by decide +kernel
theorem plane10_row23 : planeRowOK planeCentres10 planeLinear10 23 = true := by decide +kernel
theorem plane10_row24 : planeRowOK planeCentres10 planeLinear10 24 = true := by decide +kernel
theorem plane10_row25 : planeRowOK planeCentres10 planeLinear10 25 = true := by decide +kernel
theorem plane10_row26 : planeRowOK planeCentres10 planeLinear10 26 = true := by decide +kernel
theorem plane10_row27 : planeRowOK planeCentres10 planeLinear10 27 = true := by decide +kernel
theorem plane10_row28 : planeRowOK planeCentres10 planeLinear10 28 = true := by decide +kernel
theorem plane10_row29 : planeRowOK planeCentres10 planeLinear10 29 = true := by decide +kernel
theorem plane10_row30 : planeRowOK planeCentres10 planeLinear10 30 = true := by decide +kernel
theorem plane10_row31 : planeRowOK planeCentres10 planeLinear10 31 = true := by decide +kernel
theorem plane10_row32 : planeRowOK planeCentres10 planeLinear10 32 = true := by decide +kernel
theorem plane10_row33 : planeRowOK planeCentres10 planeLinear10 33 = true := by decide +kernel
theorem plane10_row34 : planeRowOK planeCentres10 planeLinear10 34 = true := by decide +kernel
theorem plane10_row35 : planeRowOK planeCentres10 planeLinear10 35 = true := by decide +kernel
theorem plane10_row36 : planeRowOK planeCentres10 planeLinear10 36 = true := by decide +kernel
theorem plane10_row37 : planeRowOK planeCentres10 planeLinear10 37 = true := by decide +kernel
theorem plane10_row38 : planeRowOK planeCentres10 planeLinear10 38 = true := by decide +kernel
theorem plane10_row39 : planeRowOK planeCentres10 planeLinear10 39 = true := by decide +kernel
theorem plane10_row40 : planeRowOK planeCentres10 planeLinear10 40 = true := by decide +kernel
theorem plane10_row41 : planeRowOK planeCentres10 planeLinear10 41 = true := by decide +kernel
theorem plane10_row42 : planeRowOK planeCentres10 planeLinear10 42 = true := by decide +kernel
theorem plane10_row43 : planeRowOK planeCentres10 planeLinear10 43 = true := by decide +kernel
theorem plane10_row44 : planeRowOK planeCentres10 planeLinear10 44 = true := by decide +kernel
theorem plane10_row45 : planeRowOK planeCentres10 planeLinear10 45 = true := by decide +kernel
theorem plane10_row46 : planeRowOK planeCentres10 planeLinear10 46 = true := by decide +kernel
theorem plane10_row47 : planeRowOK planeCentres10 planeLinear10 47 = true := by decide +kernel
theorem plane10_row48 : planeRowOK planeCentres10 planeLinear10 48 = true := by decide +kernel
theorem plane10_rows (k : ℕ) (hk : k < 49) :
    planeRowOK planeCentres10 planeLinear10 k = true := by
  interval_cases k
  · exact plane10_row0
  · exact plane10_row1
  · exact plane10_row2
  · exact plane10_row3
  · exact plane10_row4
  · exact plane10_row5
  · exact plane10_row6
  · exact plane10_row7
  · exact plane10_row8
  · exact plane10_row9
  · exact plane10_row10
  · exact plane10_row11
  · exact plane10_row12
  · exact plane10_row13
  · exact plane10_row14
  · exact plane10_row15
  · exact plane10_row16
  · exact plane10_row17
  · exact plane10_row18
  · exact plane10_row19
  · exact plane10_row20
  · exact plane10_row21
  · exact plane10_row22
  · exact plane10_row23
  · exact plane10_row24
  · exact plane10_row25
  · exact plane10_row26
  · exact plane10_row27
  · exact plane10_row28
  · exact plane10_row29
  · exact plane10_row30
  · exact plane10_row31
  · exact plane10_row32
  · exact plane10_row33
  · exact plane10_row34
  · exact plane10_row35
  · exact plane10_row36
  · exact plane10_row37
  · exact plane10_row38
  · exact plane10_row39
  · exact plane10_row40
  · exact plane10_row41
  · exact plane10_row42
  · exact plane10_row43
  · exact plane10_row44
  · exact plane10_row45
  · exact plane10_row46
  · exact plane10_row47
  · exact plane10_row48
noncomputable section
theorem plane10_census_identity (X : Finset E4) :
    (planeConstant10 : ℝ) + ((List.range 5).map fun i => (planeCounts10.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[10]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) := by
  apply affine_count_identity planeCounts10 planeConstant10
    (CensusArithmetic.planeCoeffs[10]!)
  · decide +kernel
  · intro i hi
    interval_cases i <;> decide +kernel

theorem gram_energy_ge_plane10 (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (h1 : ∀ x ∈ X, 1 ≤ ‖x‖) :
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[10]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) ≤
    gramEnergy X := by
  rw [← plane10_census_identity]
  exact gram_plane_floor planeCentres10 planeLinear10 planeCounts10 planeConstant10
    plane10_constant plane10_rows X hX hR (fun x hx => plane10_radial ‖x‖ (h1 x hx) (hR x hx))
end
end D4Bound.V7.CensusGram
