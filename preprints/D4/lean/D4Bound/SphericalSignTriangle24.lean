import D4Bound.SphericalSignUpper24

import D4Bound.SphericalSignGramData

import D4Bound.SphericalSignFinal

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSign.Bernstein

theorem rawTriangle24_of_cube (hcheck : OnCube upper24 gramUpper24)
    (a b t : ℝ) (ha : -1≤a) (has : a≤(203:ℝ)/400)
    (hb : -1≤b) (hbs : b≤(203:ℝ)/400) (ht : -1≤t) (hts : t≤(203:ℝ)/400)
    (hdet : 0≤1+2*a*b*t-a^2-b^2-t^2) :
    SphereCertificate.kernel Finset.univ (rayDegree rays24) (rayV rays24 featureDen24) a b t+
    SphereCertificate.kernel Finset.univ (rayDegree rays24) (rayV rays24 featureDen24) a t b+
    SphereCertificate.kernel Finset.univ (rayDegree rays24) (rayV rays24 featureDen24) b t a ≤ 3*(epsilon24:ℝ) := by
  have hw : ((203:ℝ)/400+1)=(603:ℝ)/400 := by norm_num
  have hca := cube_coordinate (by norm_num : -1<(203:ℝ)/400) ha has
  have hcb := cube_coordinate (by norm_num : -1<(203:ℝ)/400) hb hbs
  have hct := cube_coordinate (by norm_num : -1<(203:ℝ)/400) ht hts
  rw [hw] at hca hcb hct
  have hp := upper24_raw_correct hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  have hg := gramUpper24_correct hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  rw [hca.2.2,hcb.2.2,hct.2.2] at hp hg
  have hh := sign_from_envelopes upper24 gramUpper24 hcheck _ _
    (2^precision24:ℝ) (2^gramPrecision24:ℝ) _ _ _ (by positivity) (by positivity)
    hdet hp hg hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  exact sub_nonpos.mp hh

#print axioms rawTriangle24_of_cube

end D4Bound.SphericalSign.Bernstein
