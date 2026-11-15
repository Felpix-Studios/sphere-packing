import D4Bound.SphericalConcreteBasic

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
namespace D4Bound.SphericalConcrete
open AnnularCertificate

lemma U21 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (21 : ℤ)).eval t = (0 + t * (22 + t * (0 + t * (-1760 + t * (0 + t * (41184 + t * (0 + t * (-439296 + t * (0 + t * (2562560 + t * (0 + t * (-8945664 + t * (0 + t * (19496960 + t * (0 + t * (-26738688 + t * (0 + t * (22413312 + t * (0 + t * (-10485760 + t * (0 + t * (2097152 + t * 0)))))))))))))))))))))) := by
  rw [show (21 : ℤ) = 19 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]
  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  rw [U20, U19]
  ring

end D4Bound.SphericalConcrete
