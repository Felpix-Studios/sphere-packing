import D4Bound.SphericalSignPairData
import D4Bound.AnnularCert

/-! Small exact interfaces used to instantiate the three spherical count certificates. -/
set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign

/-- An exact integer origin numerator, retaining only degree-zero rays. -/
def originNumerator (rays : List Ray) : ℤ := (rays.map fun r => originZ r ^ 2).sum

theorem origin_eq (rays : List Ray) (od : ℤ) :
    SphereCertificate.origin Finset.univ (rayDegree rays) (rayO rays od) =
      (originNumerator rays : ℝ) / (od : ℝ)^2 := by
  change (∑ i : Fin rays.length, (fun r : Ray =>
    SphereCertificate.rayOrigin r.degree (r.originNum / od)^2) rays[i.val]) = _
  rw [Fin.sum_univ_fun_getElem rays (fun r => SphereCertificate.rayOrigin r.degree (r.originNum / od)^2)]
  simp only [originZ_cast]
  induction rays with
  | nil => simp [originNumerator]
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, originZ_cast]
    rw [ih]
    simp only [originNumerator, List.map_cons, List.sum_cons, Int.cast_add, Int.cast_pow]
    ring

end D4Bound.SphericalConcrete
