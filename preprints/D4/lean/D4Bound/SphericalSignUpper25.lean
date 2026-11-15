import D4Bound.SphericalSignTransform25X

import D4Bound.SphericalSignTensorData

import D4Bound.SphericalSignTransformBound

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSign.Bernstein

theorem upper25_matrix_row0 : ∀ j k,
    (2^precision25:ℤ)*transform25X 0 j k ≤ (repairDen25*affineDen25^3)*upper25 0 j k := by decide +kernel

theorem upper25_matrix_row1 : ∀ j k,
    (2^precision25:ℤ)*transform25X 1 j k ≤ (repairDen25*affineDen25^3)*upper25 1 j k := by decide +kernel

theorem upper25_matrix_row2 : ∀ j k,
    (2^precision25:ℤ)*transform25X 2 j k ≤ (repairDen25*affineDen25^3)*upper25 2 j k := by decide +kernel

theorem upper25_matrix_row3 : ∀ j k,
    (2^precision25:ℤ)*transform25X 3 j k ≤ (repairDen25*affineDen25^3)*upper25 3 j k := by decide +kernel

theorem upper25_matrix_row4 : ∀ j k,
    (2^precision25:ℤ)*transform25X 4 j k ≤ (repairDen25*affineDen25^3)*upper25 4 j k := by decide +kernel

theorem upper25_matrix_row5 : ∀ j k,
    (2^precision25:ℤ)*transform25X 5 j k ≤ (repairDen25*affineDen25^3)*upper25 5 j k := by decide +kernel

theorem upper25_matrix_row6 : ∀ j k,
    (2^precision25:ℤ)*transform25X 6 j k ≤ (repairDen25*affineDen25^3)*upper25 6 j k := by decide +kernel

theorem upper25_matrix_row7 : ∀ j k,
    (2^precision25:ℤ)*transform25X 7 j k ≤ (repairDen25*affineDen25^3)*upper25 7 j k := by decide +kernel

theorem upper25_matrix_row8 : ∀ j k,
    (2^precision25:ℤ)*transform25X 8 j k ≤ (repairDen25*affineDen25^3)*upper25 8 j k := by decide +kernel

theorem upper25_matrix_row9 : ∀ j k,
    (2^precision25:ℤ)*transform25X 9 j k ≤ (repairDen25*affineDen25^3)*upper25 9 j k := by decide +kernel

theorem upper25_matrix_row10 : ∀ j k,
    (2^precision25:ℤ)*transform25X 10 j k ≤ (repairDen25*affineDen25^3)*upper25 10 j k := by decide +kernel

theorem upper25_matrix_row11 : ∀ j k,
    (2^precision25:ℤ)*transform25X 11 j k ≤ (repairDen25*affineDen25^3)*upper25 11 j k := by decide +kernel

theorem upper25_matrix_row12 : ∀ j k,
    (2^precision25:ℤ)*transform25X 12 j k ≤ (repairDen25*affineDen25^3)*upper25 12 j k := by decide +kernel

theorem upper25_matrix_coeff : ∀ i j k,
    (2^precision25:ℤ)*transform25X i j k ≤ (repairDen25*affineDen25^3)*upper25 i j k := by
  intro i j k
  fin_cases i
  · exact upper25_matrix_row0 j k
  · exact upper25_matrix_row1 j k
  · exact upper25_matrix_row2 j k
  · exact upper25_matrix_row3 j k
  · exact upper25_matrix_row4 j k
  · exact upper25_matrix_row5 j k
  · exact upper25_matrix_row6 j k
  · exact upper25_matrix_row7 j k
  · exact upper25_matrix_row8 j k
  · exact upper25_matrix_row9 j k
  · exact upper25_matrix_row10 j k
  · exact upper25_matrix_row11 j k
  · exact upper25_matrix_row12 j k

theorem upper25_power_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision25:ℝ)*powerEv repairPower25
      (-1+(303:ℝ)/200*x) (-1+(303:ℝ)/200*y) (-1+(303:ℝ)/200*z) ≤
        (repairDen25:ℝ)*ev upper25 x y z := by
  have hc : ∀ i j k, (2^precision25:ℤ)*
      (matrixX affine25 (matrixY affine25 (matrixZ affine25 repairPower25))) i j k ≤
        (repairDen25*affineDen25^3)*upper25 i j k := by
    rw [←transform25Z_eq,←transform25Y_eq,←transform25X_eq]
    exact upper25_matrix_coeff
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    upper_from_matrix affine25 repairPower25 upper25 affineDen25 repairDen25
      (2^precision25) (by norm_num [affineDen25]) hc
      (-1+(303:ℝ)/200*x) (-1+(303:ℝ)/200*y) (-1+(303:ℝ)/200*z) x y z
      (fun j => affine25_exact j x) (fun j => affine25_exact j y)
      (fun j => affine25_exact j z) hx hx1 hy hy1 hz hz1

theorem upper25_raw_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision25:ℝ)*(SphereCertificate.kernel Finset.univ (rayDegree rays25) (rayV rays25 featureDen25)
      (-1+(303:ℝ)/200*x) (-1+(303:ℝ)/200*y) (-1+(303:ℝ)/200*z)+
    SphereCertificate.kernel Finset.univ (rayDegree rays25) (rayV rays25 featureDen25)
      (-1+(303:ℝ)/200*x) (-1+(303:ℝ)/200*z) (-1+(303:ℝ)/200*y)+
    SphereCertificate.kernel Finset.univ (rayDegree rays25) (rayV rays25 featureDen25)
      (-1+(303:ℝ)/200*y) (-1+(303:ℝ)/200*z) (-1+(303:ℝ)/200*x)-3*(epsilon25:ℝ)) ≤ ev upper25 x y z := by
  have hb := upper25_power_correct hx hx1 hy hy1 hz hz1
  rw [repairPower25_correct] at hb
  have hd : (0:ℝ)<repairDen25 := by norm_num [repairDen25]
  have hh : (repairDen25:ℝ)*((2^precision25:ℝ)*(SphereCertificate.kernel Finset.univ (rayDegree rays25) (rayV rays25 featureDen25)
      (-1+(303:ℝ)/200*x) (-1+(303:ℝ)/200*y) (-1+(303:ℝ)/200*z)+
    SphereCertificate.kernel Finset.univ (rayDegree rays25) (rayV rays25 featureDen25)
      (-1+(303:ℝ)/200*x) (-1+(303:ℝ)/200*z) (-1+(303:ℝ)/200*y)+
    SphereCertificate.kernel Finset.univ (rayDegree rays25) (rayV rays25 featureDen25)
      (-1+(303:ℝ)/200*y) (-1+(303:ℝ)/200*z) (-1+(303:ℝ)/200*x)-3*(epsilon25:ℝ))-ev upper25 x y z)≤0 := by nlinarith
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hh hd)

#print axioms upper25_raw_correct

end D4Bound.SphericalSign.Bernstein
