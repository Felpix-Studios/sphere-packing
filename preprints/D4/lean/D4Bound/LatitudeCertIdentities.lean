import D4Bound.LatitudeCertData
import D4Bound.LatitudeCertSound
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace D4Bound.LatitudeCheck

lemma P_identity15 (x y : ℝ) : ev bundle15.P x y = (denP15 : ℝ) * latP (203/400) beta15 (((c15 : ℝ)+1)*x-1) (((c15 : ℝ)+1)*y-1) := by
  norm_num [bundle15, P15, denP15, s15, c15, beta15, ev, E, Four.map, latP, latPhi, latH]
  <;> ring

lemma V_identity15 (x y : ℝ) : ev bundle15.V x y = (denV15 : ℝ) * ((s15 : ℝ)-(((c15 : ℝ)+1)*x-1)*(((c15 : ℝ)+1)*y-1)) := by
  norm_num [bundle15, V15, denV15, s15, c15, beta15, ev, E, Four.map, latP, latPhi, latH]
  <;> ring

lemma H_identity15 (x y : ℝ) : ev bundle15.H x y = (denH15 : ℝ) * latH s15 (203/400) beta15 (((c15 : ℝ)+1)*x-1) (((c15 : ℝ)+1)*y-1) := by
  norm_num [bundle15, H15, denH15, s15, c15, beta15, ev, E, Four.map, latP, latPhi, latH]
  <;> ring

lemma D_identity15 (x y : ℝ) : ev bundle15.D x y = (denD15 : ℝ) * (1-(s15 : ℝ)^2+2*s15*((((c15 : ℝ)+1)*x-1)*(((c15 : ℝ)+1)*y-1))-(((c15 : ℝ)+1)*x-1)^2-(((c15 : ℝ)+1)*y-1)^2) := by
  norm_num [bundle15, D15, denD15, s15, c15, beta15, ev, E, Four.map, latP, latPhi, latH]
  <;> ring

lemma P_identity24 (x y : ℝ) : ev bundle24.P x y = (denP24 : ℝ) * latP (203/400) beta24 (((c24 : ℝ)+1)*x-1) (((c24 : ℝ)+1)*y-1) := by
  norm_num [bundle24, P24, denP24, s24, c24, beta24, ev, E, Four.map, latP, latPhi, latH]
  <;> ring

lemma V_identity24 (x y : ℝ) : ev bundle24.V x y = (denV24 : ℝ) * ((s24 : ℝ)-(((c24 : ℝ)+1)*x-1)*(((c24 : ℝ)+1)*y-1)) := by
  norm_num [bundle24, V24, denV24, s24, c24, beta24, ev, E, Four.map, latP, latPhi, latH]
  <;> ring

lemma H_identity24 (x y : ℝ) : ev bundle24.H x y = (denH24 : ℝ) * latH s24 (203/400) beta24 (((c24 : ℝ)+1)*x-1) (((c24 : ℝ)+1)*y-1) := by
  norm_num [bundle24, H24, denH24, s24, c24, beta24, ev, E, Four.map, latP, latPhi, latH]
  <;> ring

lemma D_identity24 (x y : ℝ) : ev bundle24.D x y = (denD24 : ℝ) * (1-(s24 : ℝ)^2+2*s24*((((c24 : ℝ)+1)*x-1)*(((c24 : ℝ)+1)*y-1))-(((c24 : ℝ)+1)*x-1)^2-(((c24 : ℝ)+1)*y-1)^2) := by
  norm_num [bundle24, D24, denD24, s24, c24, beta24, ev, E, Four.map, latP, latPhi, latH]
  <;> ring

end D4Bound.LatitudeCheck
