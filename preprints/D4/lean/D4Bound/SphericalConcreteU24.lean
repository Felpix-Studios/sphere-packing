import D4Bound.SphericalConcreteU23

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
namespace D4Bound.SphericalConcrete
open AnnularCertificate

lemma U24 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (24 : ℤ)).eval t = (1 + t * (0 + t * (-312 + t * (0 + t * (16016 + t * (0 + t * (-320320 + t * (0 + t * (3294720 + t * (0 + t * (-19914752 + t * (0 + t * (76038144 + t * (0 + t * (-190513152 + t * (0 + t * (317521920 + t * (0 + t * (-348651520 + t * (0 + t * (242221056 + t * (0 + t * (-96468992 + t * (0 + t * (16777216 + t * 0))))))))))))))))))))))))) := by
  rw [show (24 : ℤ) = 22 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]
  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  rw [U23, U22]
  ring

end D4Bound.SphericalConcrete
