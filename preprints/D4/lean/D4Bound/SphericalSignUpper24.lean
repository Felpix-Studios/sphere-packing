import D4Bound.SphericalSignTransform24X

import D4Bound.SphericalSignTensorData

import D4Bound.SphericalSignTransformBound

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSign.Bernstein

theorem upper24_matrix_row0 : ∀ j k,
    (2^precision24:ℤ)*transform24X 0 j k ≤ (repairDen24*affineDen24^3)*upper24 0 j k := by decide +kernel

theorem upper24_matrix_row1 : ∀ j k,
    (2^precision24:ℤ)*transform24X 1 j k ≤ (repairDen24*affineDen24^3)*upper24 1 j k := by decide +kernel

theorem upper24_matrix_row2 : ∀ j k,
    (2^precision24:ℤ)*transform24X 2 j k ≤ (repairDen24*affineDen24^3)*upper24 2 j k := by decide +kernel

theorem upper24_matrix_row3 : ∀ j k,
    (2^precision24:ℤ)*transform24X 3 j k ≤ (repairDen24*affineDen24^3)*upper24 3 j k := by decide +kernel

theorem upper24_matrix_row4 : ∀ j k,
    (2^precision24:ℤ)*transform24X 4 j k ≤ (repairDen24*affineDen24^3)*upper24 4 j k := by decide +kernel

theorem upper24_matrix_row5 : ∀ j k,
    (2^precision24:ℤ)*transform24X 5 j k ≤ (repairDen24*affineDen24^3)*upper24 5 j k := by decide +kernel

theorem upper24_matrix_row6 : ∀ j k,
    (2^precision24:ℤ)*transform24X 6 j k ≤ (repairDen24*affineDen24^3)*upper24 6 j k := by decide +kernel

theorem upper24_matrix_row7 : ∀ j k,
    (2^precision24:ℤ)*transform24X 7 j k ≤ (repairDen24*affineDen24^3)*upper24 7 j k := by decide +kernel

theorem upper24_matrix_row8 : ∀ j k,
    (2^precision24:ℤ)*transform24X 8 j k ≤ (repairDen24*affineDen24^3)*upper24 8 j k := by decide +kernel

theorem upper24_matrix_row9 : ∀ j k,
    (2^precision24:ℤ)*transform24X 9 j k ≤ (repairDen24*affineDen24^3)*upper24 9 j k := by decide +kernel

theorem upper24_matrix_row10 : ∀ j k,
    (2^precision24:ℤ)*transform24X 10 j k ≤ (repairDen24*affineDen24^3)*upper24 10 j k := by decide +kernel

theorem upper24_matrix_row11 : ∀ j k,
    (2^precision24:ℤ)*transform24X 11 j k ≤ (repairDen24*affineDen24^3)*upper24 11 j k := by decide +kernel

theorem upper24_matrix_row12 : ∀ j k,
    (2^precision24:ℤ)*transform24X 12 j k ≤ (repairDen24*affineDen24^3)*upper24 12 j k := by decide +kernel

theorem upper24_matrix_coeff : ∀ i j k,
    (2^precision24:ℤ)*transform24X i j k ≤ (repairDen24*affineDen24^3)*upper24 i j k := by
  intro i j k
  fin_cases i
  · exact upper24_matrix_row0 j k
  · exact upper24_matrix_row1 j k
  · exact upper24_matrix_row2 j k
  · exact upper24_matrix_row3 j k
  · exact upper24_matrix_row4 j k
  · exact upper24_matrix_row5 j k
  · exact upper24_matrix_row6 j k
  · exact upper24_matrix_row7 j k
  · exact upper24_matrix_row8 j k
  · exact upper24_matrix_row9 j k
  · exact upper24_matrix_row10 j k
  · exact upper24_matrix_row11 j k
  · exact upper24_matrix_row12 j k

theorem upper24_power_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision24:ℝ)*powerEv repairPower24
      (-1+(603:ℝ)/400*x) (-1+(603:ℝ)/400*y) (-1+(603:ℝ)/400*z) ≤
        (repairDen24:ℝ)*ev upper24 x y z := by
  have hc : ∀ i j k, (2^precision24:ℤ)*
      (matrixX affine24 (matrixY affine24 (matrixZ affine24 repairPower24))) i j k ≤
        (repairDen24*affineDen24^3)*upper24 i j k := by
    rw [←transform24Z_eq,←transform24Y_eq,←transform24X_eq]
    exact upper24_matrix_coeff
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    upper_from_matrix affine24 repairPower24 upper24 affineDen24 repairDen24
      (2^precision24) (by norm_num [affineDen24]) hc
      (-1+(603:ℝ)/400*x) (-1+(603:ℝ)/400*y) (-1+(603:ℝ)/400*z) x y z
      (fun j => affine24_exact j x) (fun j => affine24_exact j y)
      (fun j => affine24_exact j z) hx hx1 hy hy1 hz hz1

theorem upper24_raw_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision24:ℝ)*(SphereCertificate.kernel Finset.univ (rayDegree rays24) (rayV rays24 featureDen24)
      (-1+(603:ℝ)/400*x) (-1+(603:ℝ)/400*y) (-1+(603:ℝ)/400*z)+
    SphereCertificate.kernel Finset.univ (rayDegree rays24) (rayV rays24 featureDen24)
      (-1+(603:ℝ)/400*x) (-1+(603:ℝ)/400*z) (-1+(603:ℝ)/400*y)+
    SphereCertificate.kernel Finset.univ (rayDegree rays24) (rayV rays24 featureDen24)
      (-1+(603:ℝ)/400*y) (-1+(603:ℝ)/400*z) (-1+(603:ℝ)/400*x)-3*(epsilon24:ℝ)) ≤ ev upper24 x y z := by
  have hb := upper24_power_correct hx hx1 hy hy1 hz hz1
  rw [repairPower24_correct] at hb
  have hd : (0:ℝ)<repairDen24 := by norm_num [repairDen24]
  have hh : (repairDen24:ℝ)*((2^precision24:ℝ)*(SphereCertificate.kernel Finset.univ (rayDegree rays24) (rayV rays24 featureDen24)
      (-1+(603:ℝ)/400*x) (-1+(603:ℝ)/400*y) (-1+(603:ℝ)/400*z)+
    SphereCertificate.kernel Finset.univ (rayDegree rays24) (rayV rays24 featureDen24)
      (-1+(603:ℝ)/400*x) (-1+(603:ℝ)/400*z) (-1+(603:ℝ)/400*y)+
    SphereCertificate.kernel Finset.univ (rayDegree rays24) (rayV rays24 featureDen24)
      (-1+(603:ℝ)/400*y) (-1+(603:ℝ)/400*z) (-1+(603:ℝ)/400*x)-3*(epsilon24:ℝ))-ev upper24 x y z)≤0 := by nlinarith
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hh hd)

#print axioms upper24_raw_correct

end D4Bound.SphericalSign.Bernstein
