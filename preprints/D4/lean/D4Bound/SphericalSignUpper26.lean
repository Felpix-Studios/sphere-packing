import D4Bound.SphericalSignTransform26X

import D4Bound.SphericalSignTensorData

import D4Bound.SphericalSignTransformBound

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSign.Bernstein

theorem upper26_matrix_row0 : ∀ j k,
    (2^precision26:ℤ)*transform26X 0 j k ≤ (repairDen26*affineDen26^3)*upper26 0 j k := by decide +kernel

theorem upper26_matrix_row1 : ∀ j k,
    (2^precision26:ℤ)*transform26X 1 j k ≤ (repairDen26*affineDen26^3)*upper26 1 j k := by decide +kernel

theorem upper26_matrix_row2 : ∀ j k,
    (2^precision26:ℤ)*transform26X 2 j k ≤ (repairDen26*affineDen26^3)*upper26 2 j k := by decide +kernel

theorem upper26_matrix_row3 : ∀ j k,
    (2^precision26:ℤ)*transform26X 3 j k ≤ (repairDen26*affineDen26^3)*upper26 3 j k := by decide +kernel

theorem upper26_matrix_row4 : ∀ j k,
    (2^precision26:ℤ)*transform26X 4 j k ≤ (repairDen26*affineDen26^3)*upper26 4 j k := by decide +kernel

theorem upper26_matrix_row5 : ∀ j k,
    (2^precision26:ℤ)*transform26X 5 j k ≤ (repairDen26*affineDen26^3)*upper26 5 j k := by decide +kernel

theorem upper26_matrix_row6 : ∀ j k,
    (2^precision26:ℤ)*transform26X 6 j k ≤ (repairDen26*affineDen26^3)*upper26 6 j k := by decide +kernel

theorem upper26_matrix_row7 : ∀ j k,
    (2^precision26:ℤ)*transform26X 7 j k ≤ (repairDen26*affineDen26^3)*upper26 7 j k := by decide +kernel

theorem upper26_matrix_row8 : ∀ j k,
    (2^precision26:ℤ)*transform26X 8 j k ≤ (repairDen26*affineDen26^3)*upper26 8 j k := by decide +kernel

theorem upper26_matrix_row9 : ∀ j k,
    (2^precision26:ℤ)*transform26X 9 j k ≤ (repairDen26*affineDen26^3)*upper26 9 j k := by decide +kernel

theorem upper26_matrix_row10 : ∀ j k,
    (2^precision26:ℤ)*transform26X 10 j k ≤ (repairDen26*affineDen26^3)*upper26 10 j k := by decide +kernel

theorem upper26_matrix_row11 : ∀ j k,
    (2^precision26:ℤ)*transform26X 11 j k ≤ (repairDen26*affineDen26^3)*upper26 11 j k := by decide +kernel

theorem upper26_matrix_row12 : ∀ j k,
    (2^precision26:ℤ)*transform26X 12 j k ≤ (repairDen26*affineDen26^3)*upper26 12 j k := by decide +kernel

theorem upper26_matrix_coeff : ∀ i j k,
    (2^precision26:ℤ)*transform26X i j k ≤ (repairDen26*affineDen26^3)*upper26 i j k := by
  intro i j k
  fin_cases i
  · exact upper26_matrix_row0 j k
  · exact upper26_matrix_row1 j k
  · exact upper26_matrix_row2 j k
  · exact upper26_matrix_row3 j k
  · exact upper26_matrix_row4 j k
  · exact upper26_matrix_row5 j k
  · exact upper26_matrix_row6 j k
  · exact upper26_matrix_row7 j k
  · exact upper26_matrix_row8 j k
  · exact upper26_matrix_row9 j k
  · exact upper26_matrix_row10 j k
  · exact upper26_matrix_row11 j k
  · exact upper26_matrix_row12 j k

theorem upper26_power_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision26:ℝ)*powerEv repairPower26
      (-1+(61:ℝ)/40*x) (-1+(61:ℝ)/40*y) (-1+(61:ℝ)/40*z) ≤
        (repairDen26:ℝ)*ev upper26 x y z := by
  have hc : ∀ i j k, (2^precision26:ℤ)*
      (matrixX affine26 (matrixY affine26 (matrixZ affine26 repairPower26))) i j k ≤
        (repairDen26*affineDen26^3)*upper26 i j k := by
    rw [←transform26Z_eq,←transform26Y_eq,←transform26X_eq]
    exact upper26_matrix_coeff
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    upper_from_matrix affine26 repairPower26 upper26 affineDen26 repairDen26
      (2^precision26) (by norm_num [affineDen26]) hc
      (-1+(61:ℝ)/40*x) (-1+(61:ℝ)/40*y) (-1+(61:ℝ)/40*z) x y z
      (fun j => affine26_exact j x) (fun j => affine26_exact j y)
      (fun j => affine26_exact j z) hx hx1 hy hy1 hz hz1

theorem upper26_raw_correct {x y z : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision26:ℝ)*(SphereCertificate.kernel Finset.univ (rayDegree rays26) (rayV rays26 featureDen26)
      (-1+(61:ℝ)/40*x) (-1+(61:ℝ)/40*y) (-1+(61:ℝ)/40*z)+
    SphereCertificate.kernel Finset.univ (rayDegree rays26) (rayV rays26 featureDen26)
      (-1+(61:ℝ)/40*x) (-1+(61:ℝ)/40*z) (-1+(61:ℝ)/40*y)+
    SphereCertificate.kernel Finset.univ (rayDegree rays26) (rayV rays26 featureDen26)
      (-1+(61:ℝ)/40*y) (-1+(61:ℝ)/40*z) (-1+(61:ℝ)/40*x)-3*(epsilon26:ℝ)) ≤ ev upper26 x y z := by
  have hb := upper26_power_correct hx hx1 hy hy1 hz hz1
  rw [repairPower26_correct] at hb
  have hd : (0:ℝ)<repairDen26 := by norm_num [repairDen26]
  have hh : (repairDen26:ℝ)*((2^precision26:ℝ)*(SphereCertificate.kernel Finset.univ (rayDegree rays26) (rayV rays26 featureDen26)
      (-1+(61:ℝ)/40*x) (-1+(61:ℝ)/40*y) (-1+(61:ℝ)/40*z)+
    SphereCertificate.kernel Finset.univ (rayDegree rays26) (rayV rays26 featureDen26)
      (-1+(61:ℝ)/40*x) (-1+(61:ℝ)/40*z) (-1+(61:ℝ)/40*y)+
    SphereCertificate.kernel Finset.univ (rayDegree rays26) (rayV rays26 featureDen26)
      (-1+(61:ℝ)/40*y) (-1+(61:ℝ)/40*z) (-1+(61:ℝ)/40*x)-3*(epsilon26:ℝ))-ev upper26 x y z)≤0 := by nlinarith
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hh hd)

#print axioms upper26_raw_correct

end D4Bound.SphericalSign.Bernstein
