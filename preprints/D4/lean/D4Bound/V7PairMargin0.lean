import D4Bound.V7PairSignBasic
import D4Bound.V7PairPolynomialData0
import D4Bound.V7PairMarginData0

/-! A quantitative first-cell gauge margin for cyclic-sign certificates. -/
namespace D4Bound.V7
open PairPoly PairSignData PairMarginData
noncomputable section

theorem ungaugedPair_first_margin {r : ℝ} (h1 : 1 ≤ r) (hR : r ≤ 501473/500000) :
    ungaugedPair r ≤ -7/100000 := by
  have h7 : r ≤ 7/4 := by linarith
  have hp : radialPiece r = 0 := by
    rw [radialPiece_on_support h7,if_pos hR]
  have hu := ungaugedPair_le_upper h1 h7
  rw [← PairPoly.eval_diagonal h1 h7,hp,diagonal0_checked] at hu
  have hm := pair_upper_sign_of_normalized 1 (501473/500000) (by norm_num) pairMargin0
    marginD0 marginP0 marginD0Den marginP0Den (by decide +kernel) (by decide +kernel)
    (by have hw : (501473/500000:ℚ)-1=(1473/500000:ℚ) := by norm_num
        simpa only [hw] using marginD0_identity)
    (by have hw : (501473/500000:ℚ)-1=(1473/500000:ℚ) := by norm_num
        simpa only [hw] using marginP0_identity)
    marginD0_positive marginP0_positive (r := r) (by simpa using h1) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hR)
  rw [pairMargin0,PairPoly.eval_add,PairPoly.eval_const] at hm
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hm
  linarith

#print axioms ungaugedPair_first_margin
end
end D4Bound.V7
