import D4Bound.SphericalConcreteU21

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
namespace D4Bound.SphericalConcrete
open AnnularCertificate

lemma U22 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (22 : ℤ)).eval t = (-1 + t * (0 + t * (264 + t * (0 + t * (-11440 + t * (0 + t * (192192 + t * (0 + t * (-1647360 + t * (0 + t * (8200192 + t * (0 + t * (-25346048 + t * (0 + t * (50135040 + t * (0 + t * (-63504384 + t * (0 + t * (49807360 + t * (0 + t * (-22020096 + t * (0 + t * (4194304 + t * 0))))))))))))))))))))))) := by
  rw [show (22 : ℤ) = 20 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]
  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  rw [U21, U20]
  ring

end D4Bound.SphericalConcrete
