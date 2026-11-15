import D4Bound.LatitudeCertCheck

import D4Bound.LatitudeCertIdentities

set_option Elab.async false

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace D4Bound.LatitudeCheck

theorem latSign15 : LatSign s15 c15 (203/400) beta15 := by
  exact latitude_of_checked bundle15 tree15 s15 c15 (203/400) beta15
    checked15 (by norm_num [c15]) denP15 denV15 denH15 denD15
    (by norm_num [denP15]) (by norm_num [denV15]) (by norm_num [denH15]) (by norm_num [denD15])
    P_identity15 V_identity15 H_identity15 D_identity15

theorem latSign24 : LatSign s24 c24 (203/400) beta24 := by
  exact latitude_of_checked bundle24 tree24 s24 c24 (203/400) beta24
    checked24 (by norm_num [c24]) denP24 denV24 denH24 denD24
    (by norm_num [denP24]) (by norm_num [denV24]) (by norm_num [denH24]) (by norm_num [denD24])
    P_identity24 V_identity24 H_identity24 D_identity24

theorem latitude15 : LatitudeCert R1 R5 := by
  have hs : latS R1 = (s15 : ℝ) := by norm_num [latS, R1, s15]
  have hc : latC R1 R5 = (c15 : ℝ) := by norm_num [latC, R1, R5, c15]
  have hb : latBeta R1 R5 = (beta15 : ℝ) := by norm_num [latBeta, latC, R1, R5, beta15]
  unfold LatitudeCert
  rw [hs,hc,hb]
  exact latSign15

theorem latitude24 : LatitudeCert R2 R4 := by
  have hs : latS R2 = (s24 : ℝ) := by norm_num [latS, R2, s24]
  have hc : latC R2 R4 = (c24 : ℝ) := by norm_num [latC, R2, R4, c24]
  have hb : latBeta R2 R4 = (beta24 : ℝ) := by norm_num [latBeta, latC, R2, R4, beta24]
  unfold LatitudeCert
  rw [hs,hc,hb]
  exact latSign24

#print axioms latitude15

#print axioms latitude24

end D4Bound.LatitudeCheck


