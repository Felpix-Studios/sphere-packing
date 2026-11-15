import D4Bound.V7Kernel

/-! Exact radial ownership and exterior-coordinate coverage for cyclic replay.
No coefficient or sign assertion is imported from a Python verification. -/
namespace D4Bound.V7
noncomputable section

def regionLo (p : ℕ) : ℝ := ((breaks.getD p 0 : ℚ) : ℝ)
def regionHi (p : ℕ) : ℝ := ((breaks.getD (p+1) 0 : ℚ) : ℝ)

def RegionOwns (p : ℕ) (r : ℝ) : Prop :=
  p < 7 ∧ (if p=0 then regionLo p ≤ r else regionLo p < r) ∧ r ≤ regionHi p

/-- A nonzero internal breakpoint belongs to the region on its left. -/
theorem radial_piece_of_region {p : ℕ} {r : ℝ} (h : RegionOwns p r) : radialPiece r = p := by
  rcases h with ⟨hp,hl,hh⟩
  interval_cases p
  · norm_num [regionLo,regionHi,breaks] at hl hh
    simp [radialPiece,breaks,List.findIdx_cons,hh]
  · norm_num [regionLo,regionHi,breaks] at hl hh
    have hn0 : ¬r ≤ 501473/500000 := by linarith
    simp [radialPiece,breaks,List.findIdx_cons,hh,hn0]
  · norm_num [regionLo,regionHi,breaks] at hl hh
    have hn0 : ¬r ≤ 501473/500000 := by linarith
    have hn1 : ¬r ≤ 1005643/1000000 := by linarith
    simp [radialPiece,breaks,List.findIdx_cons,hh,hn0,hn1]
  · norm_num [regionLo,regionHi,breaks] at hl hh
    have hn0 : ¬r ≤ 501473/500000 := by linarith
    have hn1 : ¬r ≤ 1005643/1000000 := by linarith
    have hn2 : ¬r ≤ 50379/50000 := by linarith
    simp [radialPiece,breaks,List.findIdx_cons,hh,hn0,hn1,hn2]
  · norm_num [regionLo,regionHi,breaks] at hl hh
    have hn0 : ¬r ≤ 501473/500000 := by linarith
    have hn1 : ¬r ≤ 1005643/1000000 := by linarith
    have hn2 : ¬r ≤ 50379/50000 := by linarith
    have hn3 : ¬r ≤ 50767/50000 := by linarith
    simp [radialPiece,breaks,List.findIdx_cons,hh,hn0,hn1,hn2,hn3]
  · norm_num [regionLo,regionHi,breaks] at hl hh
    have hn0 : ¬r ≤ 501473/500000 := by linarith
    have hn1 : ¬r ≤ 1005643/1000000 := by linarith
    have hn2 : ¬r ≤ 50379/50000 := by linarith
    have hn3 : ¬r ≤ 50767/50000 := by linarith
    have hn4 : ¬r ≤ 102597/100000 := by linarith
    simp [radialPiece,breaks,List.findIdx_cons,hh,hn0,hn1,hn2,hn3,hn4]
  · norm_num [regionLo,regionHi,breaks] at hl hh
    have hn0 : ¬r ≤ 501473/500000 := by linarith
    have hn1 : ¬r ≤ 1005643/1000000 := by linarith
    have hn2 : ¬r ≤ 50379/50000 := by linarith
    have hn3 : ¬r ≤ 50767/50000 := by linarith
    have hn4 : ¬r ≤ 102597/100000 := by linarith
    have hn5 : ¬r ≤ 3/2 := by linarith
    simp [radialPiece,breaks,List.findIdx_cons,hh,hn0,hn1,hn2,hn3,hn4,hn5]

/-- Every supported separated radius has an owning region, with closed coverage. -/
theorem region_coverage {r : ℝ} (h1 : 1 ≤ r) (hR : r ≤ 7/4) :
    ∃ p, RegionOwns p r := by
  by_cases h0 : r ≤ 501473/500000
  · exact ⟨0, by norm_num [RegionOwns,regionLo,regionHi,breaks]; exact ⟨h1,h0⟩⟩
  by_cases h1' : r ≤ 1005643/1000000
  · exact ⟨1, by norm_num [RegionOwns,regionLo,regionHi,breaks]; exact ⟨lt_of_not_ge h0,h1'⟩⟩
  by_cases h2 : r ≤ 50379/50000
  · exact ⟨2, by norm_num [RegionOwns,regionLo,regionHi,breaks]; exact ⟨lt_of_not_ge h1',h2⟩⟩
  by_cases h3 : r ≤ 50767/50000
  · exact ⟨3, by norm_num [RegionOwns,regionLo,regionHi,breaks]; exact ⟨lt_of_not_ge h2,h3⟩⟩
  by_cases h4 : r ≤ 102597/100000
  · exact ⟨4, by norm_num [RegionOwns,regionLo,regionHi,breaks]; exact ⟨lt_of_not_ge h3,h4⟩⟩
  by_cases h5 : r ≤ 3/2
  · exact ⟨5, by norm_num [RegionOwns,regionLo,regionHi,breaks]; exact ⟨lt_of_not_ge h4,h5⟩⟩
  exact ⟨6, by norm_num [RegionOwns,regionLo,regionHi,breaks]; exact ⟨lt_of_not_ge h5,hR⟩⟩

/-- Coordinate z used by stage1 exterior branches is in the unit interval. -/
theorem exterior_coordinate {r s d : ℝ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hd : 7/4 < d) (htri : d ≤ r+s) :
    let z := ((r+s)^2-d^2)/((r+s)^2-(7/4)^2)
    0 ≤ z ∧ z ≤ 1 ∧
    (r^2+s^2-d^2)/(2*r*s) = -1+z*((r+s)^2-(7/4)^2)/(2*r*s) := by
  dsimp
  have hden : 0 < (r+s)^2-(7/4)^2 := by nlinarith
  have hnum : 0 ≤ (r+s)^2-d^2 := by nlinarith
  have hup : (r+s)^2-d^2 ≤ (r+s)^2-(7/4)^2 := by nlinarith
  refine ⟨div_nonneg hnum hden.le, (div_le_one hden).mpr hup, ?_⟩
  have hr0 : r ≠ 0 := by linarith
  have hs0 : s ≠ 0 := by linarith
  rw [div_mul_cancel₀ _ (ne_of_gt hden)]
  field_simp
  ring

#print axioms radial_piece_of_region
#print axioms region_coverage
#print axioms exterior_coordinate
end
end D4Bound.V7
