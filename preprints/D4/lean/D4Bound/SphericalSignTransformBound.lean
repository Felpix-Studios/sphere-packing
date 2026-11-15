import D4Bound.SphericalSignTransform
import D4Bound.SphericalSignPowerAlgebra
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSign.Bernstein

lemma ev_scaleTensor (d : ℤ) (p : Tensor) (x y z : ℝ) :
    ev (scaleTensor d p) x y z=(d:ℝ)*ev p x y z := by
  simp only [ev,scaleTensor,Int.cast_mul,E_smul]

/-- The exported upper coefficients dominate the exact affine transform.
The positive integer denominators cancel only after the coefficient inequality
has been lifted through the nonnegative Bernstein basis. -/
lemma upper_from_matrix (T : I → I → ℤ) (p upper : Tensor)
    (d den scale : ℤ) (hd : 0<d)
    (hc : ∀ i j k, scale*(matrixX T (matrixY T (matrixZ T p))) i j k ≤
      (den*d^3)*upper i j k)
    (a b c x y z : ℝ)
    (hX : ∀ j, (∑ i : I,(T i j:ℝ)*basis i x)=(d:ℝ)*a^j.val)
    (hY : ∀ j, (∑ i : I,(T i j:ℝ)*basis i y)=(d:ℝ)*b^j.val)
    (hZ : ∀ j, (∑ i : I,(T i j:ℝ)*basis i z)=(d:ℝ)*c^j.val)
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (scale:ℝ)*powerEv p a b c ≤ (den:ℝ)*ev upper x y z := by
  have hb := ev_mono (scaleTensor scale (matrixX T (matrixY T (matrixZ T p))))
    (scaleTensor (den*d^3) upper) hc hx hx1 hy hy1 hz hz1
  rw [ev_scaleTensor,ev_scaleTensor,ev_matrixXYZ T d a b c x y z hX hY hZ] at hb
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hd3 : (0:ℝ)<(d:ℝ)^3 := pow_pos hdR _
  push_cast at hb
  have hn : (d:ℝ)^3*((scale:ℝ)*powerEv p a b c-(den:ℝ)*ev upper x y z)≤0 := by nlinarith
  have hn' := nonpos_of_mul_nonpos_right hn hd3
  linarith

#print axioms upper_from_matrix
end D4Bound.SphericalSign.Bernstein
