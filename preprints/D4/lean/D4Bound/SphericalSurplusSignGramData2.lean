import D4Bound.SphericalSurplusSignGramLink16

import D4Bound.SphericalSurplusSignTreeData2

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign.Bernstein16

theorem gramUpper2_row0 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 0 j k ≤
      (61440*200^3)*gramUpper2 0 j k := by decide +kernel

theorem gramUpper2_row1 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 1 j k ≤
      (61440*200^3)*gramUpper2 1 j k := by decide +kernel

theorem gramUpper2_row2 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 2 j k ≤
      (61440*200^3)*gramUpper2 2 j k := by decide +kernel

theorem gramUpper2_row3 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 3 j k ≤
      (61440*200^3)*gramUpper2 3 j k := by decide +kernel

theorem gramUpper2_row4 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 4 j k ≤
      (61440*200^3)*gramUpper2 4 j k := by decide +kernel

theorem gramUpper2_row5 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 5 j k ≤
      (61440*200^3)*gramUpper2 5 j k := by decide +kernel

theorem gramUpper2_row6 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 6 j k ≤
      (61440*200^3)*gramUpper2 6 j k := by decide +kernel

theorem gramUpper2_row7 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 7 j k ≤
      (61440*200^3)*gramUpper2 7 j k := by decide +kernel

theorem gramUpper2_row8 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 8 j k ≤
      (61440*200^3)*gramUpper2 8 j k := by decide +kernel

theorem gramUpper2_row9 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 9 j k ≤
      (61440*200^3)*gramUpper2 9 j k := by decide +kernel

theorem gramUpper2_row10 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 10 j k ≤
      (61440*200^3)*gramUpper2 10 j k := by decide +kernel

theorem gramUpper2_row11 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 11 j k ≤
      (61440*200^3)*gramUpper2 11 j k := by decide +kernel

theorem gramUpper2_row12 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 12 j k ≤
      (61440*200^3)*gramUpper2 12 j k := by decide +kernel

theorem gramUpper2_row13 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 13 j k ≤
      (61440*200^3)*gramUpper2 13 j k := by decide +kernel

theorem gramUpper2_row14 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 14 j k ≤
      (61440*200^3)*gramUpper2 14 j k := by decide +kernel

theorem gramUpper2_row15 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 15 j k ≤
      (61440*200^3)*gramUpper2 15 j k := by decide +kernel

theorem gramUpper2_row16 : ∀ j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 16 j k ≤
      (61440*200^3)*gramUpper2 16 j k := by decide +kernel

theorem gramUpper2_coeff : ∀ i j k,
    (2^gramPrecision2:ℤ)*gramNum 303 200 i j k ≤ (61440*200^3)*gramUpper2 i j k := by
  intro i j k
  fin_cases i
  · exact gramUpper2_row0 j k
  · exact gramUpper2_row1 j k
  · exact gramUpper2_row2 j k
  · exact gramUpper2_row3 j k
  · exact gramUpper2_row4 j k
  · exact gramUpper2_row5 j k
  · exact gramUpper2_row6 j k
  · exact gramUpper2_row7 j k
  · exact gramUpper2_row8 j k
  · exact gramUpper2_row9 j k
  · exact gramUpper2_row10 j k
  · exact gramUpper2_row11 j k
  · exact gramUpper2_row12 j k
  · exact gramUpper2_row13 j k
  · exact gramUpper2_row14 j k
  · exact gramUpper2_row15 j k
  · exact gramUpper2_row16 j k

theorem gramUpper2_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^gramPrecision2:ℝ)*(1+2*(-1+(303:ℝ)/200*x)*(-1+(303:ℝ)/200*y)*(-1+(303:ℝ)/200*z)-
      (-1+(303:ℝ)/200*x)^2-(-1+(303:ℝ)/200*y)^2-(-1+(303:ℝ)/200*z)^2) ≤ ev gramUpper2 x y z := by
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    gram_upper_of_coeff 303 200 (by norm_num) (2^gramPrecision2) (by positivity)
      gramUpper2 gramUpper2_coeff hx hx1 hy hy1 hz hz1

#print axioms gramUpper2_correct

end D4Bound.SphericalSurplusSign.Bernstein16
