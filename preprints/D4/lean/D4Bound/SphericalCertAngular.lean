import D4Bound.SphericalCertLegendre
/-! Explicit homogeneous Legendre polynomials used by the spherical JSON verifier.
Each equality is proved from the normalized three-term recurrence. -/
namespace D4Bound.Schoenberg2
lemma solid_poly_0 (u v : ℝ) : solidLegendre u v 0 = (1/1)*u^0*v^0 := by
  simp [solidLegendre]
lemma solid_poly_1 (u v : ℝ) : solidLegendre u v 1 = (1/1)*u^1*v^0 := by
  simp [solidLegendre]
lemma solid_poly_2 (u v : ℝ) : solidLegendre u v 2 = (3/2)*u^2*v^0 + (-1/2)*u^0*v^1 := by
  rw [solidLegendre, solid_poly_1, solid_poly_0]
  norm_num
  <;> ring
lemma solid_poly_3 (u v : ℝ) : solidLegendre u v 3 = (5/2)*u^3*v^0 + (-3/2)*u^1*v^1 := by
  rw [solidLegendre, solid_poly_2, solid_poly_1]
  norm_num
  <;> ring
lemma solid_poly_4 (u v : ℝ) : solidLegendre u v 4 = (35/8)*u^4*v^0 + (-15/4)*u^2*v^1 + (3/8)*u^0*v^2 := by
  rw [solidLegendre, solid_poly_3, solid_poly_2]
  norm_num
  <;> ring
lemma solid_poly_5 (u v : ℝ) : solidLegendre u v 5 = (63/8)*u^5*v^0 + (-35/4)*u^3*v^1 + (15/8)*u^1*v^2 := by
  rw [solidLegendre, solid_poly_4, solid_poly_3]
  norm_num
  <;> ring
lemma solid_poly_6 (u v : ℝ) : solidLegendre u v 6 = (231/16)*u^6*v^0 + (-315/16)*u^4*v^1 + (105/16)*u^2*v^2 + (-5/16)*u^0*v^3 := by
  rw [solidLegendre, solid_poly_5, solid_poly_4]
  norm_num
  <;> ring
lemma solid_poly_7 (u v : ℝ) : solidLegendre u v 7 = (429/16)*u^7*v^0 + (-693/16)*u^5*v^1 + (315/16)*u^3*v^2 + (-35/16)*u^1*v^3 := by
  rw [solidLegendre, solid_poly_6, solid_poly_5]
  norm_num
  <;> ring
lemma solid_poly_8 (u v : ℝ) : solidLegendre u v 8 = (6435/128)*u^8*v^0 + (-3003/32)*u^6*v^1 + (3465/64)*u^4*v^2 + (-315/32)*u^2*v^3 + (35/128)*u^0*v^4 := by
  rw [solidLegendre, solid_poly_7, solid_poly_6]
  norm_num
  <;> ring
lemma solid_poly_9 (u v : ℝ) : solidLegendre u v 9 = (12155/128)*u^9*v^0 + (-6435/32)*u^7*v^1 + (9009/64)*u^5*v^2 + (-1155/32)*u^3*v^3 + (315/128)*u^1*v^4 := by
  rw [solidLegendre, solid_poly_8, solid_poly_7]
  norm_num
  <;> ring
lemma solid_poly_10 (u v : ℝ) : solidLegendre u v 10 = (46189/256)*u^10*v^0 + (-109395/256)*u^8*v^1 + (45045/128)*u^6*v^2 + (-15015/128)*u^4*v^3 + (3465/256)*u^2*v^4 + (-63/256)*u^0*v^5 := by
  rw [solidLegendre, solid_poly_9, solid_poly_8]
  norm_num
  <;> ring
lemma solid_poly_11 (u v : ℝ) : solidLegendre u v 11 = (88179/256)*u^11*v^0 + (-230945/256)*u^9*v^1 + (109395/128)*u^7*v^2 + (-45045/128)*u^5*v^3 + (15015/256)*u^3*v^4 + (-693/256)*u^1*v^5 := by
  rw [solidLegendre, solid_poly_10, solid_poly_9]
  norm_num
  <;> ring
lemma solid_poly_12 (u v : ℝ) : solidLegendre u v 12 = (676039/1024)*u^12*v^0 + (-969969/512)*u^10*v^1 + (2078505/1024)*u^8*v^2 + (-255255/256)*u^6*v^3 + (225225/1024)*u^4*v^4 + (-9009/512)*u^2*v^5 + (231/1024)*u^0*v^6 := by
  rw [solidLegendre, solid_poly_11, solid_poly_10]
  norm_num
  <;> ring

end D4Bound.Schoenberg2
