import D4Bound.SphericalSurplusSignUpper0

import D4Bound.SphericalSurplusSignGramData0

import D4Bound.SphericalSurplusSignFinal16

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign.Bernstein16

theorem rawTriangle0_of_cube (hcheck : OnCube upper0 gramUpper0)
    (a b t : ℝ) (ha : -1≤a) (has : a≤(251467:ℝ)/500000)
    (hb : -1≤b) (hbs : b≤(251467:ℝ)/500000) (ht : -1≤t) (hts : t≤(251467:ℝ)/500000)
    (hdet : 0≤1+2*a*b*t-a^2-b^2-t^2) :
    kernel0 a b t+kernel0 a t b+kernel0 b t a ≤ 3*(epsilon0:ℝ) := by
  have hw : ((251467:ℝ)/500000+1)=(751467:ℝ)/500000 := by norm_num
  have hca := cube_coordinate (by norm_num : -1<(251467:ℝ)/500000) ha has
  have hcb := cube_coordinate (by norm_num : -1<(251467:ℝ)/500000) hb hbs
  have hct := cube_coordinate (by norm_num : -1<(251467:ℝ)/500000) ht hts
  rw [hw] at hca hcb hct
  have hp := upper0_raw_correct hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  have hg := gramUpper0_correct hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  rw [hca.2.2,hcb.2.2,hct.2.2] at hp hg
  have hh := sign_from_envelopes upper0 gramUpper0 hcheck _ _
    (2^precision0:ℝ) (2^gramPrecision0:ℝ) _ _ _ (by positivity) (by positivity)
    hdet hp hg hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  exact sub_nonpos.mp hh

#print axioms rawTriangle0_of_cube

end D4Bound.SphericalSurplusSign.Bernstein16
