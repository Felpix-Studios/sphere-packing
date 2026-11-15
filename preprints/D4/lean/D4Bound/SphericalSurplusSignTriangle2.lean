import D4Bound.SphericalSurplusSignUpper2

import D4Bound.SphericalSurplusSignGramData2

import D4Bound.SphericalSurplusSignFinal16

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign.Bernstein16

theorem rawTriangle2_of_cube (hcheck : OnCube upper2 gramUpper2)
    (a b t : ℝ) (ha : -1≤a) (has : a≤(103:ℝ)/200)
    (hb : -1≤b) (hbs : b≤(103:ℝ)/200) (ht : -1≤t) (hts : t≤(103:ℝ)/200)
    (hdet : 0≤1+2*a*b*t-a^2-b^2-t^2) :
    kernel2 a b t+kernel2 a t b+kernel2 b t a ≤ 3*(epsilon2:ℝ) := by
  have hw : ((103:ℝ)/200+1)=(303:ℝ)/200 := by norm_num
  have hca := cube_coordinate (by norm_num : -1<(103:ℝ)/200) ha has
  have hcb := cube_coordinate (by norm_num : -1<(103:ℝ)/200) hb hbs
  have hct := cube_coordinate (by norm_num : -1<(103:ℝ)/200) ht hts
  rw [hw] at hca hcb hct
  have hp := upper2_raw_correct hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  have hg := gramUpper2_correct hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  rw [hca.2.2,hcb.2.2,hct.2.2] at hp hg
  have hh := sign_from_envelopes upper2 gramUpper2 hcheck _ _
    (2^precision2:ℝ) (2^gramPrecision2:ℝ) _ _ _ (by positivity) (by positivity)
    hdet hp hg hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  exact sub_nonpos.mp hh

#print axioms rawTriangle2_of_cube

end D4Bound.SphericalSurplusSign.Bernstein16
