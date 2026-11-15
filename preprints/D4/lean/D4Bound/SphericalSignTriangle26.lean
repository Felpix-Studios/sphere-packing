import D4Bound.SphericalSignUpper26

import D4Bound.SphericalSignGramData

import D4Bound.SphericalSignFinal

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSign.Bernstein

theorem rawTriangle26_of_cube (hcheck : OnCube upper26 gramUpper26)
    (a b t : ℝ) (ha : -1≤a) (has : a≤(21:ℝ)/40)
    (hb : -1≤b) (hbs : b≤(21:ℝ)/40) (ht : -1≤t) (hts : t≤(21:ℝ)/40)
    (hdet : 0≤1+2*a*b*t-a^2-b^2-t^2) :
    SphereCertificate.kernel Finset.univ (rayDegree rays26) (rayV rays26 featureDen26) a b t+
    SphereCertificate.kernel Finset.univ (rayDegree rays26) (rayV rays26 featureDen26) a t b+
    SphereCertificate.kernel Finset.univ (rayDegree rays26) (rayV rays26 featureDen26) b t a ≤ 3*(epsilon26:ℝ) := by
  have hw : ((21:ℝ)/40+1)=(61:ℝ)/40 := by norm_num
  have hca := cube_coordinate (by norm_num : -1<(21:ℝ)/40) ha has
  have hcb := cube_coordinate (by norm_num : -1<(21:ℝ)/40) hb hbs
  have hct := cube_coordinate (by norm_num : -1<(21:ℝ)/40) ht hts
  rw [hw] at hca hcb hct
  have hp := upper26_raw_correct hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  have hg := gramUpper26_correct hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  rw [hca.2.2,hcb.2.2,hct.2.2] at hp hg
  have hh := sign_from_envelopes upper26 gramUpper26 hcheck _ _
    (2^precision26:ℝ) (2^gramPrecision26:ℝ) _ _ _ (by positivity) (by positivity)
    hdet hp hg hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  exact sub_nonpos.mp hh

#print axioms rawTriangle26_of_cube

end D4Bound.SphericalSign.Bernstein
