import D4Bound.SphericalSurplusSignTransform0X

import D4Bound.SphericalSurplusSignPower0

import D4Bound.SphericalSurplusSignTreeData0

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign.Bernstein16

theorem upper0_matrix_row0 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 0 j k) ≤
      (repairDen0*affineDen0^3)*upper0 0 j k := by decide +kernel

theorem upper0_matrix_row1 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 1 j k) ≤
      (repairDen0*affineDen0^3)*upper0 1 j k := by decide +kernel

theorem upper0_matrix_row2 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 2 j k) ≤
      (repairDen0*affineDen0^3)*upper0 2 j k := by decide +kernel

theorem upper0_matrix_row3 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 3 j k) ≤
      (repairDen0*affineDen0^3)*upper0 3 j k := by decide +kernel

theorem upper0_matrix_row4 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 4 j k) ≤
      (repairDen0*affineDen0^3)*upper0 4 j k := by decide +kernel

theorem upper0_matrix_row5 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 5 j k) ≤
      (repairDen0*affineDen0^3)*upper0 5 j k := by decide +kernel

theorem upper0_matrix_row6 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 6 j k) ≤
      (repairDen0*affineDen0^3)*upper0 6 j k := by decide +kernel

theorem upper0_matrix_row7 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 7 j k) ≤
      (repairDen0*affineDen0^3)*upper0 7 j k := by decide +kernel

theorem upper0_matrix_row8 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 8 j k) ≤
      (repairDen0*affineDen0^3)*upper0 8 j k := by decide +kernel

theorem upper0_matrix_row9 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 9 j k) ≤
      (repairDen0*affineDen0^3)*upper0 9 j k := by decide +kernel

theorem upper0_matrix_row10 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 10 j k) ≤
      (repairDen0*affineDen0^3)*upper0 10 j k := by decide +kernel

theorem upper0_matrix_row11 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 11 j k) ≤
      (repairDen0*affineDen0^3)*upper0 11 j k := by decide +kernel

theorem upper0_matrix_row12 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 12 j k) ≤
      (repairDen0*affineDen0^3)*upper0 12 j k := by decide +kernel

theorem upper0_matrix_row13 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 13 j k) ≤
      (repairDen0*affineDen0^3)*upper0 13 j k := by decide +kernel

theorem upper0_matrix_row14 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 14 j k) ≤
      (repairDen0*affineDen0^3)*upper0 14 j k := by decide +kernel

theorem upper0_matrix_row15 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 15 j k) ≤
      (repairDen0*affineDen0^3)*upper0 15 j k := by decide +kernel

theorem upper0_matrix_row16 : ∀ j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X 16 j k) ≤
      (repairDen0*affineDen0^3)*upper0 16 j k := by decide +kernel

theorem upper0_matrix_coeff : ∀ i j k,
    (2^precision0:ℤ)*((transformFactor0Z*transformFactor0Y*transformFactor0X)*transform0X i j k) ≤
      (repairDen0*affineDen0^3)*upper0 i j k := by
  intro i j k
  fin_cases i
  · exact upper0_matrix_row0 j k
  · exact upper0_matrix_row1 j k
  · exact upper0_matrix_row2 j k
  · exact upper0_matrix_row3 j k
  · exact upper0_matrix_row4 j k
  · exact upper0_matrix_row5 j k
  · exact upper0_matrix_row6 j k
  · exact upper0_matrix_row7 j k
  · exact upper0_matrix_row8 j k
  · exact upper0_matrix_row9 j k
  · exact upper0_matrix_row10 j k
  · exact upper0_matrix_row11 j k
  · exact upper0_matrix_row12 j k
  · exact upper0_matrix_row13 j k
  · exact upper0_matrix_row14 j k
  · exact upper0_matrix_row15 j k
  · exact upper0_matrix_row16 j k

theorem upper0_power_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision0:ℝ)*powerEv repairPower0
      (-1+(751467:ℝ)/500000*x) (-1+(751467:ℝ)/500000*y) (-1+(751467:ℝ)/500000*z) ≤
        (repairDen0:ℝ)*ev upper0 x y z := by
  have hc : ∀ i j k, (2^precision0:ℤ)*
      (matrixX affine0 (matrixY affine0 (matrixZ affine0 repairPower0))) i j k ≤
        (repairDen0*affineDen0^3)*upper0 i j k := by
    rw [matrixXYZ_scaled affine0 repairPower0 transform0Z transform0Y transform0X
      transformFactor0Z transformFactor0Y transformFactor0X
      transform0Z_eq transform0Y_eq transform0X_eq]
    exact upper0_matrix_coeff
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    upper_from_matrix affine0 repairPower0 upper0 affineDen0 repairDen0
      (2^precision0) (by norm_num [affineDen0]) hc
      (-1+(751467:ℝ)/500000*x) (-1+(751467:ℝ)/500000*y) (-1+(751467:ℝ)/500000*z) x y z
      (fun j => affine0_exact j x) (fun j => affine0_exact j y)
      (fun j => affine0_exact j z) hx hx1 hy hy1 hz hz1

theorem upper0_raw_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision0:ℝ)*(kernel0 (-1+(751467:ℝ)/500000*x) (-1+(751467:ℝ)/500000*y) (-1+(751467:ℝ)/500000*z)+
      kernel0 (-1+(751467:ℝ)/500000*x) (-1+(751467:ℝ)/500000*z) (-1+(751467:ℝ)/500000*y)+
      kernel0 (-1+(751467:ℝ)/500000*y) (-1+(751467:ℝ)/500000*z) (-1+(751467:ℝ)/500000*x)-3*(epsilon0:ℝ)) ≤ ev upper0 x y z := by
  have hb := upper0_power_correct hx hx1 hy hy1 hz hz1
  rw [repairPower0_correct] at hb
  have hd : (0:ℝ)<repairDen0 := by norm_num [repairDen0]
  have hh : (repairDen0:ℝ)*((2^precision0:ℝ)*(kernel0 (-1+(751467:ℝ)/500000*x) (-1+(751467:ℝ)/500000*y) (-1+(751467:ℝ)/500000*z)+
      kernel0 (-1+(751467:ℝ)/500000*x) (-1+(751467:ℝ)/500000*z) (-1+(751467:ℝ)/500000*y)+
      kernel0 (-1+(751467:ℝ)/500000*y) (-1+(751467:ℝ)/500000*z) (-1+(751467:ℝ)/500000*x)-3*(epsilon0:ℝ))-ev upper0 x y z)≤0 := by nlinarith
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hh hd)

#print axioms upper0_raw_correct

end D4Bound.SphericalSurplusSign.Bernstein16
