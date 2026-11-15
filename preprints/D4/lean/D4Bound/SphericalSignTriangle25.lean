import D4Bound.SphericalSignUpper25

import D4Bound.SphericalSignGramData

import D4Bound.SphericalSignFinal

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSign.Bernstein

theorem rawTriangle25_of_cube (hcheck : OnCube upper25 gramUpper25)
    (a b t : ℝ) (ha : -1≤a) (has : a≤(103:ℝ)/200)
    (hb : -1≤b) (hbs : b≤(103:ℝ)/200) (ht : -1≤t) (hts : t≤(103:ℝ)/200)
    (hdet : 0≤1+2*a*b*t-a^2-b^2-t^2) :
    SphereCertificate.kernel Finset.univ (rayDegree rays25) (rayV rays25 featureDen25) a b t+
    SphereCertificate.kernel Finset.univ (rayDegree rays25) (rayV rays25 featureDen25) a t b+
    SphereCertificate.kernel Finset.univ (rayDegree rays25) (rayV rays25 featureDen25) b t a ≤ 3*(epsilon25:ℝ) := by
  have hw : ((103:ℝ)/200+1)=(303:ℝ)/200 := by norm_num
  have hca := cube_coordinate (by norm_num : -1<(103:ℝ)/200) ha has
  have hcb := cube_coordinate (by norm_num : -1<(103:ℝ)/200) hb hbs
  have hct := cube_coordinate (by norm_num : -1<(103:ℝ)/200) ht hts
  rw [hw] at hca hcb hct
  have hp := upper25_raw_correct hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  have hg := gramUpper25_correct hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  rw [hca.2.2,hcb.2.2,hct.2.2] at hp hg
  have hh := sign_from_envelopes upper25 gramUpper25 hcheck _ _
    (2^precision25:ℝ) (2^gramPrecision25:ℝ) _ _ _ (by positivity) (by positivity)
    hdet hp hg hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  exact sub_nonpos.mp hh

#print axioms rawTriangle25_of_cube

end D4Bound.SphericalSign.Bernstein
