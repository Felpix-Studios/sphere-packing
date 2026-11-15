-- Generated from s0525_count26_exact.json; every arithmetic identity is kernel checked.
import D4Bound.SphericalConcreteScalar26
import D4Bound.SphericalConcreteRepair26
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign AnnularCertificate
namespace C26
theorem origin_check : originNumerator rays26 = 25801466747387072496 := by decide +kernel
theorem origin_value : SphereCertificate.origin Finset.univ (rayDegree rays26) (rayO rays26 originDen26) = (1612591671711692031/62500000000000000) := by
  rw [origin_eq, origin_check]
  norm_num [originDen26]
theorem decrease : (epsilon26:ℝ)*D + 0 < 1 := by norm_num [epsilon26, D]
theorem objective : g 1 + SphereCertificate.origin Finset.univ (rayDegree rays26) (rayO rays26 originDen26) - ((epsilon26:ℝ)*D+0) < (26+1:ℕ)*(1-((epsilon26:ℝ)*D+0)) := by
  rw [scalar_diag, origin_value]
  norm_num [epsilon26, D]
end C26
end D4Bound.SphericalConcrete
