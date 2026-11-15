import D4Bound.SphericalConcreteU22

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
namespace D4Bound.SphericalConcrete
open AnnularCertificate

lemma U23 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (23 : ℤ)).eval t = (0 + t * (-24 + t * (0 + t * (2288 + t * (0 + t * (-64064 + t * (0 + t * (823680 + t * (0 + t * (-5857280 + t * (0 + t * (25346048 + t * (0 + t * (-70189056 + t * (0 + t * (127008768 + t * (0 + t * (-149422080 + t * (0 + t * (110100480 + t * (0 + t * (-46137344 + t * (0 + t * (8388608 + t * 0)))))))))))))))))))))))) := by
  rw [show (23 : ℤ) = 21 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]
  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  rw [U22, U21]
  ring

end D4Bound.SphericalConcrete
