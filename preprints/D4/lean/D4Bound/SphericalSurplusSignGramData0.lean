import D4Bound.SphericalSurplusSignGramLink16

import D4Bound.SphericalSurplusSignTreeData0

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign.Bernstein16

theorem gramUpper0_row0 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 0 j k ≤
      (61440*500000^3)*gramUpper0 0 j k := by decide +kernel

theorem gramUpper0_row1 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 1 j k ≤
      (61440*500000^3)*gramUpper0 1 j k := by decide +kernel

theorem gramUpper0_row2 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 2 j k ≤
      (61440*500000^3)*gramUpper0 2 j k := by decide +kernel

theorem gramUpper0_row3 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 3 j k ≤
      (61440*500000^3)*gramUpper0 3 j k := by decide +kernel

theorem gramUpper0_row4 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 4 j k ≤
      (61440*500000^3)*gramUpper0 4 j k := by decide +kernel

theorem gramUpper0_row5 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 5 j k ≤
      (61440*500000^3)*gramUpper0 5 j k := by decide +kernel

theorem gramUpper0_row6 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 6 j k ≤
      (61440*500000^3)*gramUpper0 6 j k := by decide +kernel

theorem gramUpper0_row7 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 7 j k ≤
      (61440*500000^3)*gramUpper0 7 j k := by decide +kernel

theorem gramUpper0_row8 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 8 j k ≤
      (61440*500000^3)*gramUpper0 8 j k := by decide +kernel

theorem gramUpper0_row9 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 9 j k ≤
      (61440*500000^3)*gramUpper0 9 j k := by decide +kernel

theorem gramUpper0_row10 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 10 j k ≤
      (61440*500000^3)*gramUpper0 10 j k := by decide +kernel

theorem gramUpper0_row11 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 11 j k ≤
      (61440*500000^3)*gramUpper0 11 j k := by decide +kernel

theorem gramUpper0_row12 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 12 j k ≤
      (61440*500000^3)*gramUpper0 12 j k := by decide +kernel

theorem gramUpper0_row13 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 13 j k ≤
      (61440*500000^3)*gramUpper0 13 j k := by decide +kernel

theorem gramUpper0_row14 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 14 j k ≤
      (61440*500000^3)*gramUpper0 14 j k := by decide +kernel

theorem gramUpper0_row15 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 15 j k ≤
      (61440*500000^3)*gramUpper0 15 j k := by decide +kernel

theorem gramUpper0_row16 : ∀ j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 16 j k ≤
      (61440*500000^3)*gramUpper0 16 j k := by decide +kernel

theorem gramUpper0_coeff : ∀ i j k,
    (2^gramPrecision0:ℤ)*gramNum 751467 500000 i j k ≤ (61440*500000^3)*gramUpper0 i j k := by
  intro i j k
  fin_cases i
  · exact gramUpper0_row0 j k
  · exact gramUpper0_row1 j k
  · exact gramUpper0_row2 j k
  · exact gramUpper0_row3 j k
  · exact gramUpper0_row4 j k
  · exact gramUpper0_row5 j k
  · exact gramUpper0_row6 j k
  · exact gramUpper0_row7 j k
  · exact gramUpper0_row8 j k
  · exact gramUpper0_row9 j k
  · exact gramUpper0_row10 j k
  · exact gramUpper0_row11 j k
  · exact gramUpper0_row12 j k
  · exact gramUpper0_row13 j k
  · exact gramUpper0_row14 j k
  · exact gramUpper0_row15 j k
  · exact gramUpper0_row16 j k

theorem gramUpper0_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^gramPrecision0:ℝ)*(1+2*(-1+(751467:ℝ)/500000*x)*(-1+(751467:ℝ)/500000*y)*(-1+(751467:ℝ)/500000*z)-
      (-1+(751467:ℝ)/500000*x)^2-(-1+(751467:ℝ)/500000*y)^2-(-1+(751467:ℝ)/500000*z)^2) ≤ ev gramUpper0 x y z := by
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    gram_upper_of_coeff 751467 500000 (by norm_num) (2^gramPrecision0) (by positivity)
      gramUpper0 gramUpper0_coeff hx hx1 hy hy1 hz hz1

#print axioms gramUpper0_correct

end D4Bound.SphericalSurplusSign.Bernstein16
