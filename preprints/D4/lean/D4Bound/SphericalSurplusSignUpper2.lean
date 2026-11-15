import D4Bound.SphericalSurplusSignTransform2X

import D4Bound.SphericalSurplusSignPower2

import D4Bound.SphericalSurplusSignTreeData2

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign.Bernstein16

theorem upper2_matrix_row0 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 0 j k) ≤
      (repairDen2*affineDen2^3)*upper2 0 j k := by decide +kernel

theorem upper2_matrix_row1 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 1 j k) ≤
      (repairDen2*affineDen2^3)*upper2 1 j k := by decide +kernel

theorem upper2_matrix_row2 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 2 j k) ≤
      (repairDen2*affineDen2^3)*upper2 2 j k := by decide +kernel

theorem upper2_matrix_row3 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 3 j k) ≤
      (repairDen2*affineDen2^3)*upper2 3 j k := by decide +kernel

theorem upper2_matrix_row4 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 4 j k) ≤
      (repairDen2*affineDen2^3)*upper2 4 j k := by decide +kernel

theorem upper2_matrix_row5 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 5 j k) ≤
      (repairDen2*affineDen2^3)*upper2 5 j k := by decide +kernel

theorem upper2_matrix_row6 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 6 j k) ≤
      (repairDen2*affineDen2^3)*upper2 6 j k := by decide +kernel

theorem upper2_matrix_row7 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 7 j k) ≤
      (repairDen2*affineDen2^3)*upper2 7 j k := by decide +kernel

theorem upper2_matrix_row8 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 8 j k) ≤
      (repairDen2*affineDen2^3)*upper2 8 j k := by decide +kernel

theorem upper2_matrix_row9 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 9 j k) ≤
      (repairDen2*affineDen2^3)*upper2 9 j k := by decide +kernel

theorem upper2_matrix_row10 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 10 j k) ≤
      (repairDen2*affineDen2^3)*upper2 10 j k := by decide +kernel

theorem upper2_matrix_row11 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 11 j k) ≤
      (repairDen2*affineDen2^3)*upper2 11 j k := by decide +kernel

theorem upper2_matrix_row12 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 12 j k) ≤
      (repairDen2*affineDen2^3)*upper2 12 j k := by decide +kernel

theorem upper2_matrix_row13 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 13 j k) ≤
      (repairDen2*affineDen2^3)*upper2 13 j k := by decide +kernel

theorem upper2_matrix_row14 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 14 j k) ≤
      (repairDen2*affineDen2^3)*upper2 14 j k := by decide +kernel

theorem upper2_matrix_row15 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 15 j k) ≤
      (repairDen2*affineDen2^3)*upper2 15 j k := by decide +kernel

theorem upper2_matrix_row16 : ∀ j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X 16 j k) ≤
      (repairDen2*affineDen2^3)*upper2 16 j k := by decide +kernel

theorem upper2_matrix_coeff : ∀ i j k,
    (2^precision2:ℤ)*((transformFactor2Z*transformFactor2Y*transformFactor2X)*transform2X i j k) ≤
      (repairDen2*affineDen2^3)*upper2 i j k := by
  intro i j k
  fin_cases i
  · exact upper2_matrix_row0 j k
  · exact upper2_matrix_row1 j k
  · exact upper2_matrix_row2 j k
  · exact upper2_matrix_row3 j k
  · exact upper2_matrix_row4 j k
  · exact upper2_matrix_row5 j k
  · exact upper2_matrix_row6 j k
  · exact upper2_matrix_row7 j k
  · exact upper2_matrix_row8 j k
  · exact upper2_matrix_row9 j k
  · exact upper2_matrix_row10 j k
  · exact upper2_matrix_row11 j k
  · exact upper2_matrix_row12 j k
  · exact upper2_matrix_row13 j k
  · exact upper2_matrix_row14 j k
  · exact upper2_matrix_row15 j k
  · exact upper2_matrix_row16 j k

theorem upper2_power_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision2:ℝ)*powerEv repairPower2
      (-1+(303:ℝ)/200*x) (-1+(303:ℝ)/200*y) (-1+(303:ℝ)/200*z) ≤
        (repairDen2:ℝ)*ev upper2 x y z := by
  have hc : ∀ i j k, (2^precision2:ℤ)*
      (matrixX affine2 (matrixY affine2 (matrixZ affine2 repairPower2))) i j k ≤
        (repairDen2*affineDen2^3)*upper2 i j k := by
    rw [matrixXYZ_scaled affine2 repairPower2 transform2Z transform2Y transform2X
      transformFactor2Z transformFactor2Y transformFactor2X
      transform2Z_eq transform2Y_eq transform2X_eq]
    exact upper2_matrix_coeff
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    upper_from_matrix affine2 repairPower2 upper2 affineDen2 repairDen2
      (2^precision2) (by norm_num [affineDen2]) hc
      (-1+(303:ℝ)/200*x) (-1+(303:ℝ)/200*y) (-1+(303:ℝ)/200*z) x y z
      (fun j => affine2_exact j x) (fun j => affine2_exact j y)
      (fun j => affine2_exact j z) hx hx1 hy hy1 hz hz1

theorem upper2_raw_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision2:ℝ)*(kernel2 (-1+(303:ℝ)/200*x) (-1+(303:ℝ)/200*y) (-1+(303:ℝ)/200*z)+
      kernel2 (-1+(303:ℝ)/200*x) (-1+(303:ℝ)/200*z) (-1+(303:ℝ)/200*y)+
      kernel2 (-1+(303:ℝ)/200*y) (-1+(303:ℝ)/200*z) (-1+(303:ℝ)/200*x)-3*(epsilon2:ℝ)) ≤ ev upper2 x y z := by
  have hb := upper2_power_correct hx hx1 hy hy1 hz hz1
  rw [repairPower2_correct] at hb
  have hd : (0:ℝ)<repairDen2 := by norm_num [repairDen2]
  have hh : (repairDen2:ℝ)*((2^precision2:ℝ)*(kernel2 (-1+(303:ℝ)/200*x) (-1+(303:ℝ)/200*y) (-1+(303:ℝ)/200*z)+
      kernel2 (-1+(303:ℝ)/200*x) (-1+(303:ℝ)/200*z) (-1+(303:ℝ)/200*y)+
      kernel2 (-1+(303:ℝ)/200*y) (-1+(303:ℝ)/200*z) (-1+(303:ℝ)/200*x)-3*(epsilon2:ℝ))-ev upper2 x y z)≤0 := by nlinarith
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hh hd)

#print axioms upper2_raw_correct

end D4Bound.SphericalSurplusSign.Bernstein16
