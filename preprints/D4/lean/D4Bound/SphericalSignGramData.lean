import D4Bound.SphericalSignGramLink
import D4Bound.SphericalSignTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option Elab.async false
namespace D4Bound.SphericalSign.Bernstein

theorem gramUpper24_row0 : ∀ j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 0 j k ≤ (9504*400^3)*gramUpper24 0 j k := by decide +kernel

theorem gramUpper24_row1 : ∀ j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 1 j k ≤ (9504*400^3)*gramUpper24 1 j k := by decide +kernel

theorem gramUpper24_row2 : ∀ j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 2 j k ≤ (9504*400^3)*gramUpper24 2 j k := by decide +kernel

theorem gramUpper24_row3 : ∀ j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 3 j k ≤ (9504*400^3)*gramUpper24 3 j k := by decide +kernel

theorem gramUpper24_row4 : ∀ j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 4 j k ≤ (9504*400^3)*gramUpper24 4 j k := by decide +kernel

theorem gramUpper24_row5 : ∀ j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 5 j k ≤ (9504*400^3)*gramUpper24 5 j k := by decide +kernel

theorem gramUpper24_row6 : ∀ j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 6 j k ≤ (9504*400^3)*gramUpper24 6 j k := by decide +kernel

theorem gramUpper24_row7 : ∀ j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 7 j k ≤ (9504*400^3)*gramUpper24 7 j k := by decide +kernel

theorem gramUpper24_row8 : ∀ j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 8 j k ≤ (9504*400^3)*gramUpper24 8 j k := by decide +kernel

theorem gramUpper24_row9 : ∀ j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 9 j k ≤ (9504*400^3)*gramUpper24 9 j k := by decide +kernel

theorem gramUpper24_row10 : ∀ j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 10 j k ≤ (9504*400^3)*gramUpper24 10 j k := by decide +kernel

theorem gramUpper24_row11 : ∀ j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 11 j k ≤ (9504*400^3)*gramUpper24 11 j k := by decide +kernel

theorem gramUpper24_row12 : ∀ j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 12 j k ≤ (9504*400^3)*gramUpper24 12 j k := by decide +kernel

theorem gramUpper24_coeff : ∀ i j k,
    (2^gramPrecision24:ℤ)*gramNum 603 400 i j k ≤ (9504*400^3)*gramUpper24 i j k := by
  intro i j k
  fin_cases i
  · exact gramUpper24_row0 j k
  · exact gramUpper24_row1 j k
  · exact gramUpper24_row2 j k
  · exact gramUpper24_row3 j k
  · exact gramUpper24_row4 j k
  · exact gramUpper24_row5 j k
  · exact gramUpper24_row6 j k
  · exact gramUpper24_row7 j k
  · exact gramUpper24_row8 j k
  · exact gramUpper24_row9 j k
  · exact gramUpper24_row10 j k
  · exact gramUpper24_row11 j k
  · exact gramUpper24_row12 j k

theorem gramUpper25_row0 : ∀ j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 0 j k ≤ (9504*200^3)*gramUpper25 0 j k := by decide +kernel

theorem gramUpper25_row1 : ∀ j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 1 j k ≤ (9504*200^3)*gramUpper25 1 j k := by decide +kernel

theorem gramUpper25_row2 : ∀ j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 2 j k ≤ (9504*200^3)*gramUpper25 2 j k := by decide +kernel

theorem gramUpper25_row3 : ∀ j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 3 j k ≤ (9504*200^3)*gramUpper25 3 j k := by decide +kernel

theorem gramUpper25_row4 : ∀ j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 4 j k ≤ (9504*200^3)*gramUpper25 4 j k := by decide +kernel

theorem gramUpper25_row5 : ∀ j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 5 j k ≤ (9504*200^3)*gramUpper25 5 j k := by decide +kernel

theorem gramUpper25_row6 : ∀ j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 6 j k ≤ (9504*200^3)*gramUpper25 6 j k := by decide +kernel

theorem gramUpper25_row7 : ∀ j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 7 j k ≤ (9504*200^3)*gramUpper25 7 j k := by decide +kernel

theorem gramUpper25_row8 : ∀ j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 8 j k ≤ (9504*200^3)*gramUpper25 8 j k := by decide +kernel

theorem gramUpper25_row9 : ∀ j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 9 j k ≤ (9504*200^3)*gramUpper25 9 j k := by decide +kernel

theorem gramUpper25_row10 : ∀ j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 10 j k ≤ (9504*200^3)*gramUpper25 10 j k := by decide +kernel

theorem gramUpper25_row11 : ∀ j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 11 j k ≤ (9504*200^3)*gramUpper25 11 j k := by decide +kernel

theorem gramUpper25_row12 : ∀ j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 12 j k ≤ (9504*200^3)*gramUpper25 12 j k := by decide +kernel

theorem gramUpper25_coeff : ∀ i j k,
    (2^gramPrecision25:ℤ)*gramNum 303 200 i j k ≤ (9504*200^3)*gramUpper25 i j k := by
  intro i j k
  fin_cases i
  · exact gramUpper25_row0 j k
  · exact gramUpper25_row1 j k
  · exact gramUpper25_row2 j k
  · exact gramUpper25_row3 j k
  · exact gramUpper25_row4 j k
  · exact gramUpper25_row5 j k
  · exact gramUpper25_row6 j k
  · exact gramUpper25_row7 j k
  · exact gramUpper25_row8 j k
  · exact gramUpper25_row9 j k
  · exact gramUpper25_row10 j k
  · exact gramUpper25_row11 j k
  · exact gramUpper25_row12 j k

theorem gramUpper26_row0 : ∀ j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 0 j k ≤ (9504*40^3)*gramUpper26 0 j k := by decide +kernel

theorem gramUpper26_row1 : ∀ j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 1 j k ≤ (9504*40^3)*gramUpper26 1 j k := by decide +kernel

theorem gramUpper26_row2 : ∀ j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 2 j k ≤ (9504*40^3)*gramUpper26 2 j k := by decide +kernel

theorem gramUpper26_row3 : ∀ j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 3 j k ≤ (9504*40^3)*gramUpper26 3 j k := by decide +kernel

theorem gramUpper26_row4 : ∀ j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 4 j k ≤ (9504*40^3)*gramUpper26 4 j k := by decide +kernel

theorem gramUpper26_row5 : ∀ j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 5 j k ≤ (9504*40^3)*gramUpper26 5 j k := by decide +kernel

theorem gramUpper26_row6 : ∀ j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 6 j k ≤ (9504*40^3)*gramUpper26 6 j k := by decide +kernel

theorem gramUpper26_row7 : ∀ j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 7 j k ≤ (9504*40^3)*gramUpper26 7 j k := by decide +kernel

theorem gramUpper26_row8 : ∀ j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 8 j k ≤ (9504*40^3)*gramUpper26 8 j k := by decide +kernel

theorem gramUpper26_row9 : ∀ j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 9 j k ≤ (9504*40^3)*gramUpper26 9 j k := by decide +kernel

theorem gramUpper26_row10 : ∀ j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 10 j k ≤ (9504*40^3)*gramUpper26 10 j k := by decide +kernel

theorem gramUpper26_row11 : ∀ j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 11 j k ≤ (9504*40^3)*gramUpper26 11 j k := by decide +kernel

theorem gramUpper26_row12 : ∀ j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 12 j k ≤ (9504*40^3)*gramUpper26 12 j k := by decide +kernel

theorem gramUpper26_coeff : ∀ i j k,
    (2^gramPrecision26:ℤ)*gramNum 61 40 i j k ≤ (9504*40^3)*gramUpper26 i j k := by
  intro i j k
  fin_cases i
  · exact gramUpper26_row0 j k
  · exact gramUpper26_row1 j k
  · exact gramUpper26_row2 j k
  · exact gramUpper26_row3 j k
  · exact gramUpper26_row4 j k
  · exact gramUpper26_row5 j k
  · exact gramUpper26_row6 j k
  · exact gramUpper26_row7 j k
  · exact gramUpper26_row8 j k
  · exact gramUpper26_row9 j k
  · exact gramUpper26_row10 j k
  · exact gramUpper26_row11 j k
  · exact gramUpper26_row12 j k

theorem gramUpper24_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^gramPrecision24:ℝ)*(1+2*(-1+(603:ℝ)/400*x)*(-1+(603:ℝ)/400*y)*(-1+(603:ℝ)/400*z)-
      (-1+(603:ℝ)/400*x)^2-(-1+(603:ℝ)/400*y)^2-(-1+(603:ℝ)/400*z)^2) ≤ ev gramUpper24 x y z := by
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    gram_upper_of_coeff 603 400 (by norm_num) (2^gramPrecision24) (by positivity)
      gramUpper24 gramUpper24_coeff hx hx1 hy hy1 hz hz1

#print axioms gramUpper24_correct

theorem gramUpper25_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^gramPrecision25:ℝ)*(1+2*(-1+(303:ℝ)/200*x)*(-1+(303:ℝ)/200*y)*(-1+(303:ℝ)/200*z)-
      (-1+(303:ℝ)/200*x)^2-(-1+(303:ℝ)/200*y)^2-(-1+(303:ℝ)/200*z)^2) ≤ ev gramUpper25 x y z := by
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    gram_upper_of_coeff 303 200 (by norm_num) (2^gramPrecision25) (by positivity)
      gramUpper25 gramUpper25_coeff hx hx1 hy hy1 hz hz1

#print axioms gramUpper25_correct

theorem gramUpper26_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^gramPrecision26:ℝ)*(1+2*(-1+(61:ℝ)/40*x)*(-1+(61:ℝ)/40*y)*(-1+(61:ℝ)/40*z)-
      (-1+(61:ℝ)/40*x)^2-(-1+(61:ℝ)/40*y)^2-(-1+(61:ℝ)/40*z)^2) ≤ ev gramUpper26 x y z := by
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    gram_upper_of_coeff 61 40 (by norm_num) (2^gramPrecision26) (by positivity)
      gramUpper26 gramUpper26_coeff hx hx1 hy hy1 hz hz1

#print axioms gramUpper26_correct

end D4Bound.SphericalSign.Bernstein
