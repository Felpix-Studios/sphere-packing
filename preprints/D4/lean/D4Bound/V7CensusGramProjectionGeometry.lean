import D4Bound.V7Radial
namespace D4Bound.V7.CensusGram
noncomputable section
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem radialPiece_le_countRadius {r : ℝ} (hr : r ≤ 7/4) (j : ℕ) (hj : j < 5) :
    radialPiece r ≤ j ↔ r ≤ ((breaks.getD (j+1) 0 : ℚ) : ℝ) := by
  interval_cases j <;> rw [radialPiece_on_support hr] <;>
    norm_num only [breaks,List.getD_cons_zero,List.getD_cons_succ,Rat.cast_div,Rat.cast_ofNat] <;>
    split_ifs <;> norm_num at * <;> (first | omega | linarith)

end
end D4Bound.V7.CensusGram
