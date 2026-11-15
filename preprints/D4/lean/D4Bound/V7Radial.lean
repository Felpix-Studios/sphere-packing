import D4Bound.V7Kernel

/-! Positivity of the physical Bernstein radial features, with all closed
piece boundaries handled by the actual `radialPiece` selector. -/
namespace D4Bound.V7
noncomputable section
open Classical

theorem radialPiece_on_support {r : ℝ} (hr : r ≤ 7/4) :
    radialPiece r =
      if r ≤ 501473/500000 then 0 else
      if r ≤ 1005643/1000000 then 1 else
      if r ≤ 50379/50000 then 2 else
      if r ≤ 50767/50000 then 3 else
      if r ≤ 102597/100000 then 4 else
      if r ≤ 3/2 then 5 else 6 := by
  split_ifs <;> norm_num [radialPiece, breaks, List.findIdx, List.findIdx.go, *]

theorem radialPiece_lt_seven {r : ℝ} (hr : r ≤ 7/4) : radialPiece r < 7 := by
  rw [radialPiece_on_support hr]
  split_ifs <;> norm_num

theorem radial_basis_domain {r : ℝ} (hr1 : 1 ≤ r) (hrR : r ≤ 7/4) :
    ((basisIntervals.getD (radialPiece r) (0,1)).1 : ℝ) ≤ r ∧
      r ≤ ((basisIntervals.getD (radialPiece r) (0,1)).2 : ℝ) := by
  rw [radialPiece_on_support hrR]
  split_ifs <;> norm_num [basisIntervals] at * <;> constructor <;> linarith

theorem basis_width_pos {p : ℕ} (hp : p < 7) :
    (0 : ℝ) < ((basisIntervals.getD p (0,1)).2 : ℝ) -
      ((basisIntervals.getD p (0,1)).1 : ℝ) := by
  interval_cases p <;> norm_num [basisIntervals]

theorem basisValue_nonneg {r : ℝ} (hr1 : 1 ≤ r) (hrR : r ≤ 7/4) (i : ℕ) :
    0 ≤ basisValue (radialPiece r) i r := by
  have hb := radial_basis_domain hr1 hrR
  have hw := basis_width_pos (radialPiece_lt_seven hrR)
  have hz0 : 0 ≤ (r-((basisIntervals.getD (radialPiece r) (0,1)).1 : ℝ)) /
      (((basisIntervals.getD (radialPiece r) (0,1)).2 : ℝ) -
        ((basisIntervals.getD (radialPiece r) (0,1)).1 : ℝ)) :=
    div_nonneg (sub_nonneg.mpr hb.1) hw.le
  have hz1 : (r-((basisIntervals.getD (radialPiece r) (0,1)).1 : ℝ)) /
      (((basisIntervals.getD (radialPiece r) (0,1)).2 : ℝ) -
        ((basisIntervals.getD (radialPiece r) (0,1)).1 : ℝ)) ≤ 1 := by
    apply (div_le_one hw).mpr
    linarith [hb.2]
  unfold basisValue
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz0 _))
    (pow_nonneg (sub_nonneg.mpr hz1) _)

theorem rational_getD_nonneg (v : List ℚ) (hv : ∀ a ∈ v, 0 ≤ a) (n : ℕ) :
    0 ≤ v.getD n 0 := by
  induction v generalizing n with
  | nil => simp
  | cons a v ih =>
    cases n with
    | zero => simpa using hv a (by simp)
    | succ n =>
      exact ih (fun b hb => hv b (by simp [hb])) n

theorem radialValue_nonneg (v : List ℚ) (hv : ∀ a ∈ v, 0 ≤ a)
    {r : ℝ} (hr1 : 1 ≤ r) (hrR : r ≤ 7/4) : 0 ≤ radialValue v r := by
  unfold radialValue
  apply List.sum_nonneg
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  exact mul_nonneg (Rat.cast_nonneg.mpr (rational_getD_nonneg v hv _))
    (basisValue_nonneg hr1 hrR i)

end
end D4Bound.V7
