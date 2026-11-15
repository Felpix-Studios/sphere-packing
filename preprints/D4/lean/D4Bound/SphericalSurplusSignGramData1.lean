import D4Bound.SphericalSurplusSignGramLink16

import D4Bound.SphericalSurplusSignTreeData1

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign.Bernstein16

theorem gramUpper1_row0 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 0 j k ≤
      (61440*40^3)*gramUpper1 0 j k := by decide +kernel

theorem gramUpper1_row1 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 1 j k ≤
      (61440*40^3)*gramUpper1 1 j k := by decide +kernel

theorem gramUpper1_row2 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 2 j k ≤
      (61440*40^3)*gramUpper1 2 j k := by decide +kernel

theorem gramUpper1_row3 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 3 j k ≤
      (61440*40^3)*gramUpper1 3 j k := by decide +kernel

theorem gramUpper1_row4 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 4 j k ≤
      (61440*40^3)*gramUpper1 4 j k := by decide +kernel

theorem gramUpper1_row5 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 5 j k ≤
      (61440*40^3)*gramUpper1 5 j k := by decide +kernel

theorem gramUpper1_row6 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 6 j k ≤
      (61440*40^3)*gramUpper1 6 j k := by decide +kernel

theorem gramUpper1_row7 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 7 j k ≤
      (61440*40^3)*gramUpper1 7 j k := by decide +kernel

theorem gramUpper1_row8 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 8 j k ≤
      (61440*40^3)*gramUpper1 8 j k := by decide +kernel

theorem gramUpper1_row9 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 9 j k ≤
      (61440*40^3)*gramUpper1 9 j k := by decide +kernel

theorem gramUpper1_row10 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 10 j k ≤
      (61440*40^3)*gramUpper1 10 j k := by decide +kernel

theorem gramUpper1_row11 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 11 j k ≤
      (61440*40^3)*gramUpper1 11 j k := by decide +kernel

theorem gramUpper1_row12 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 12 j k ≤
      (61440*40^3)*gramUpper1 12 j k := by decide +kernel

theorem gramUpper1_row13 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 13 j k ≤
      (61440*40^3)*gramUpper1 13 j k := by decide +kernel

theorem gramUpper1_row14 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 14 j k ≤
      (61440*40^3)*gramUpper1 14 j k := by decide +kernel

theorem gramUpper1_row15 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 15 j k ≤
      (61440*40^3)*gramUpper1 15 j k := by decide +kernel

theorem gramUpper1_row16 : ∀ j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 16 j k ≤
      (61440*40^3)*gramUpper1 16 j k := by decide +kernel

theorem gramUpper1_coeff : ∀ i j k,
    (2^gramPrecision1:ℤ)*gramNum 61 40 i j k ≤ (61440*40^3)*gramUpper1 i j k := by
  intro i j k
  fin_cases i
  · exact gramUpper1_row0 j k
  · exact gramUpper1_row1 j k
  · exact gramUpper1_row2 j k
  · exact gramUpper1_row3 j k
  · exact gramUpper1_row4 j k
  · exact gramUpper1_row5 j k
  · exact gramUpper1_row6 j k
  · exact gramUpper1_row7 j k
  · exact gramUpper1_row8 j k
  · exact gramUpper1_row9 j k
  · exact gramUpper1_row10 j k
  · exact gramUpper1_row11 j k
  · exact gramUpper1_row12 j k
  · exact gramUpper1_row13 j k
  · exact gramUpper1_row14 j k
  · exact gramUpper1_row15 j k
  · exact gramUpper1_row16 j k

theorem gramUpper1_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^gramPrecision1:ℝ)*(1+2*(-1+(61:ℝ)/40*x)*(-1+(61:ℝ)/40*y)*(-1+(61:ℝ)/40*z)-
      (-1+(61:ℝ)/40*x)^2-(-1+(61:ℝ)/40*y)^2-(-1+(61:ℝ)/40*z)^2) ≤ ev gramUpper1 x y z := by
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    gram_upper_of_coeff 61 40 (by norm_num) (2^gramPrecision1) (by positivity)
      gramUpper1 gramUpper1_coeff hx hx1 hy hy1 hz hz1

#print axioms gramUpper1_correct

end D4Bound.SphericalSurplusSign.Bernstein16
