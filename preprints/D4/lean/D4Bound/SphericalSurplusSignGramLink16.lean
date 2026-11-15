/- Degree16 counterpart of the frozen degree12 semantic proof. -/
import D4Bound.SphericalSurplusSignGram16
set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option Elab.async false
namespace D4Bound.SphericalSurplusSign.Bernstein16

def gramNum (p q : ℤ) (i j k : I) : ℤ :=
  -4*(61440*q^3)+15360*p*q^2*((i.val:ℤ)+j.val+k.val)-
    256*p^2*q*((i.val:ℤ)*((i.val:ℤ)-1)+(j.val:ℤ)*((j.val:ℤ)-1)+(k.val:ℤ)*((k.val:ℤ)-1))-
    480*p^2*q*((i.val:ℤ)*j.val+(i.val:ℤ)*k.val+(j.val:ℤ)*k.val)+
    30*p^3*i.val*j.val*k.val

lemma gramNum_exact (p q : ℤ) (hq : q≠0) (i j k : I) :
    (gramNum p q i j k : ℝ) = 61440*(q:ℝ)^3*gramCoeffs ((p:ℝ)/q) i j k := by
  have hqR : (q:ℝ)≠0 := by exact_mod_cast hq
  unfold gramNum gramCoeffs firstMoment secondMoment
  push_cast
  field_simp
  ring

lemma gram_upper_of_coeff (p q : ℤ) (hq : 0<q) (scale : ℤ) (hs : 0<scale) (D : Tensor)
    (hc : ∀ i j k, scale*gramNum p q i j k ≤ (61440*q^3)*D i j k)
    {x y z : ℝ} (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (scale:ℝ)*(1+2*(-1+(p:ℝ)/q*x)*(-1+(p:ℝ)/q*y)*(-1+(p:ℝ)/q*z)-
      (-1+(p:ℝ)/q*x)^2-(-1+(p:ℝ)/q*y)^2-(-1+(p:ℝ)/q*z)^2) ≤ ev D x y z := by
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hC : (0:ℝ)<61440*(q:ℝ)^3 := by positivity
  have hcR : ∀ i j k, (scale:ℝ)*gramCoeffs ((p:ℝ)/q) i j k ≤ (D i j k:ℝ) := by
    intro i j k
    have hh : (scale:ℝ)*(gramNum p q i j k:ℝ) ≤ (61440*(q:ℝ)^3)*(D i j k:ℝ) := by exact_mod_cast hc i j k
    rw [gramNum_exact p q (ne_of_gt hq)] at hh
    have hnonpos : (61440*(q:ℝ)^3)*((scale:ℝ)*gramCoeffs ((p:ℝ)/q) i j k-(D i j k:ℝ)) ≤ 0 := by nlinarith
    have hh' := nonpos_of_mul_nonpos_right hnonpos hC
    linarith
  have hb : E (fun i => E (fun j => E (fun k => (scale:ℝ)*gramCoeffs ((p:ℝ)/q) i j k) z) y) x ≤ ev D x y z := by
    apply E_mono _ hx hx1
    intro i
    apply E_mono _ hy hy1
    intro j
    apply E_mono _ hz hz1
    exact hcR i j
  simpa only [E_smul,gramCoeffs_exact] using hb


end D4Bound.SphericalSurplusSign.Bernstein16
