import D4Bound.SphericalSurplusSignTransform1X

import D4Bound.SphericalSurplusSignPower1

import D4Bound.SphericalSurplusSignTreeData1

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign.Bernstein16

theorem upper1_matrix_row0 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 0 j k) ≤
      (repairDen1*affineDen1^3)*upper1 0 j k := by decide +kernel

theorem upper1_matrix_row1 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 1 j k) ≤
      (repairDen1*affineDen1^3)*upper1 1 j k := by decide +kernel

theorem upper1_matrix_row2 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 2 j k) ≤
      (repairDen1*affineDen1^3)*upper1 2 j k := by decide +kernel

theorem upper1_matrix_row3 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 3 j k) ≤
      (repairDen1*affineDen1^3)*upper1 3 j k := by decide +kernel

theorem upper1_matrix_row4 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 4 j k) ≤
      (repairDen1*affineDen1^3)*upper1 4 j k := by decide +kernel

theorem upper1_matrix_row5 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 5 j k) ≤
      (repairDen1*affineDen1^3)*upper1 5 j k := by decide +kernel

theorem upper1_matrix_row6 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 6 j k) ≤
      (repairDen1*affineDen1^3)*upper1 6 j k := by decide +kernel

theorem upper1_matrix_row7 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 7 j k) ≤
      (repairDen1*affineDen1^3)*upper1 7 j k := by decide +kernel

theorem upper1_matrix_row8 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 8 j k) ≤
      (repairDen1*affineDen1^3)*upper1 8 j k := by decide +kernel

theorem upper1_matrix_row9 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 9 j k) ≤
      (repairDen1*affineDen1^3)*upper1 9 j k := by decide +kernel

theorem upper1_matrix_row10 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 10 j k) ≤
      (repairDen1*affineDen1^3)*upper1 10 j k := by decide +kernel

theorem upper1_matrix_row11 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 11 j k) ≤
      (repairDen1*affineDen1^3)*upper1 11 j k := by decide +kernel

theorem upper1_matrix_row12 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 12 j k) ≤
      (repairDen1*affineDen1^3)*upper1 12 j k := by decide +kernel

theorem upper1_matrix_row13 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 13 j k) ≤
      (repairDen1*affineDen1^3)*upper1 13 j k := by decide +kernel

theorem upper1_matrix_row14 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 14 j k) ≤
      (repairDen1*affineDen1^3)*upper1 14 j k := by decide +kernel

theorem upper1_matrix_row15 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 15 j k) ≤
      (repairDen1*affineDen1^3)*upper1 15 j k := by decide +kernel

theorem upper1_matrix_row16 : ∀ j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X 16 j k) ≤
      (repairDen1*affineDen1^3)*upper1 16 j k := by decide +kernel

theorem upper1_matrix_coeff : ∀ i j k,
    (2^precision1:ℤ)*((transformFactor1Z*transformFactor1Y*transformFactor1X)*transform1X i j k) ≤
      (repairDen1*affineDen1^3)*upper1 i j k := by
  intro i j k
  fin_cases i
  · exact upper1_matrix_row0 j k
  · exact upper1_matrix_row1 j k
  · exact upper1_matrix_row2 j k
  · exact upper1_matrix_row3 j k
  · exact upper1_matrix_row4 j k
  · exact upper1_matrix_row5 j k
  · exact upper1_matrix_row6 j k
  · exact upper1_matrix_row7 j k
  · exact upper1_matrix_row8 j k
  · exact upper1_matrix_row9 j k
  · exact upper1_matrix_row10 j k
  · exact upper1_matrix_row11 j k
  · exact upper1_matrix_row12 j k
  · exact upper1_matrix_row13 j k
  · exact upper1_matrix_row14 j k
  · exact upper1_matrix_row15 j k
  · exact upper1_matrix_row16 j k

theorem upper1_power_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision1:ℝ)*powerEv repairPower1
      (-1+(61:ℝ)/40*x) (-1+(61:ℝ)/40*y) (-1+(61:ℝ)/40*z) ≤
        (repairDen1:ℝ)*ev upper1 x y z := by
  have hc : ∀ i j k, (2^precision1:ℤ)*
      (matrixX affine1 (matrixY affine1 (matrixZ affine1 repairPower1))) i j k ≤
        (repairDen1*affineDen1^3)*upper1 i j k := by
    rw [matrixXYZ_scaled affine1 repairPower1 transform1Z transform1Y transform1X
      transformFactor1Z transformFactor1Y transformFactor1X
      transform1Z_eq transform1Y_eq transform1X_eq]
    exact upper1_matrix_coeff
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    upper_from_matrix affine1 repairPower1 upper1 affineDen1 repairDen1
      (2^precision1) (by norm_num [affineDen1]) hc
      (-1+(61:ℝ)/40*x) (-1+(61:ℝ)/40*y) (-1+(61:ℝ)/40*z) x y z
      (fun j => affine1_exact j x) (fun j => affine1_exact j y)
      (fun j => affine1_exact j z) hx hx1 hy hy1 hz hz1

theorem upper1_raw_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision1:ℝ)*(kernel1 (-1+(61:ℝ)/40*x) (-1+(61:ℝ)/40*y) (-1+(61:ℝ)/40*z)+
      kernel1 (-1+(61:ℝ)/40*x) (-1+(61:ℝ)/40*z) (-1+(61:ℝ)/40*y)+
      kernel1 (-1+(61:ℝ)/40*y) (-1+(61:ℝ)/40*z) (-1+(61:ℝ)/40*x)-3*(epsilon1:ℝ)) ≤ ev upper1 x y z := by
  have hb := upper1_power_correct hx hx1 hy hy1 hz hz1
  rw [repairPower1_correct] at hb
  have hd : (0:ℝ)<repairDen1 := by norm_num [repairDen1]
  have hh : (repairDen1:ℝ)*((2^precision1:ℝ)*(kernel1 (-1+(61:ℝ)/40*x) (-1+(61:ℝ)/40*y) (-1+(61:ℝ)/40*z)+
      kernel1 (-1+(61:ℝ)/40*x) (-1+(61:ℝ)/40*z) (-1+(61:ℝ)/40*y)+
      kernel1 (-1+(61:ℝ)/40*y) (-1+(61:ℝ)/40*z) (-1+(61:ℝ)/40*x)-3*(epsilon1:ℝ))-ev upper1 x y z)≤0 := by nlinarith
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hh hd)

#print axioms upper1_raw_correct

end D4Bound.SphericalSurplusSign.Bernstein16
