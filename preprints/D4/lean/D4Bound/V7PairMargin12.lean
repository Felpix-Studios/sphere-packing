import D4Bound.V7PairSignBasic
import D4Bound.V7PairPolynomialDataRest
import D4Bound.V7PairMarginData1
import D4Bound.V7PairMarginData2
import D4Bound.V7CyclicRegions

/-! Quantitative gauge margins on radial pieces 1 and 2 for cyclic-sign certificates. -/
namespace D4Bound.V7
open PairPoly PairSignData PairMarginData
noncomputable section

theorem ungaugedPair_margin1 {r : ℝ} (h1 : 501473/500000 < r) (hR : r ≤ 1005643/1000000) :
    ungaugedPair r ≤ -75/10000000 := by
  have h1' : 1 ≤ r := by linarith
  have h7 : r ≤ 7/4 := by linarith
  have hp : radialPiece r = 1 := radial_piece_of_region
    ⟨by norm_num, by norm_num [regionLo, breaks]; linarith, by norm_num [regionHi, breaks]; linarith⟩
  have hu := ungaugedPair_le_upper h1' h7
  rw [← PairPoly.eval_diagonal h1' h7, hp, diagonal1_checked] at hu
  have hm := pair_upper_sign_of_normalized (501473/500000) (1005643/1000000) (by norm_num) pairMargin1
    marginD1 marginP1 marginD1Den marginP1Den (by decide +kernel) (by decide +kernel)
    (by have hw : (1005643/1000000:ℚ)-(501473/500000:ℚ)=(2697/1000000:ℚ) := by norm_num
        simpa only [hw] using marginD1_identity)
    (by have hw : (1005643/1000000:ℚ)-(501473/500000:ℚ)=(2697/1000000:ℚ) := by norm_num
        simpa only [hw] using marginP1_identity)
    marginD1_positive marginP1_positive (r := r) (by push_cast; linarith)
    (by push_cast; linarith)
  rw [pairMargin1,PairPoly.eval_add,PairPoly.eval_const] at hm
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hm
  linarith

theorem ungaugedPair_margin2 {r : ℝ} (h1 : 1005643/1000000 < r) (hR : r ≤ 50379/50000) :
    ungaugedPair r ≤ -281/100000 := by
  have h1' : 1 ≤ r := by linarith
  have h7 : r ≤ 7/4 := by linarith
  have hp : radialPiece r = 2 := radial_piece_of_region
    ⟨by norm_num, by norm_num [regionLo, breaks]; linarith, by norm_num [regionHi, breaks]; linarith⟩
  have hu := ungaugedPair_le_upper h1' h7
  rw [← PairPoly.eval_diagonal h1' h7, hp, diagonal2_checked] at hu
  have hm := pair_upper_sign_of_normalized (1005643/1000000) (50379/50000) (by norm_num) pairMargin2
    marginD2 marginP2 marginD2Den marginP2Den (by decide +kernel) (by decide +kernel)
    (by have hw : (50379/50000:ℚ)-(1005643/1000000:ℚ)=(1937/1000000:ℚ) := by norm_num
        simpa only [hw] using marginD2_identity)
    (by have hw : (50379/50000:ℚ)-(1005643/1000000:ℚ)=(1937/1000000:ℚ) := by norm_num
        simpa only [hw] using marginP2_identity)
    marginD2_positive marginP2_positive (r := r) (by push_cast; linarith)
    (by push_cast; linarith)
  rw [pairMargin2,PairPoly.eval_add,PairPoly.eval_const] at hm
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hm
  linarith

#print axioms ungaugedPair_margin1
#print axioms ungaugedPair_margin2
end
end D4Bound.V7
