-- Generated from s0515_count25_exact.json; every arithmetic identity is kernel checked.
import D4Bound.SphericalConcreteScalar25
import D4Bound.SphericalConcreteRepair25
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign AnnularCertificate
namespace C25
theorem origin_check : originNumerator rays25 = 24658417324019492414 := by decide +kernel
theorem origin_value : SphereCertificate.origin Finset.univ (rayDegree rays25) (rayO rays25 originDen25) = (12329208662009746207/500000000000000000) := by
  rw [origin_eq, origin_check]
  norm_num [originDen25]
theorem decrease : (epsilon25:ℝ)*D + 0 < 1 := by norm_num [epsilon25, D]
theorem objective : g 1 + SphereCertificate.origin Finset.univ (rayDegree rays25) (rayO rays25 originDen25) - ((epsilon25:ℝ)*D+0) < (25+1:ℕ)*(1-((epsilon25:ℝ)*D+0)) := by
  rw [scalar_diag, origin_value]
  norm_num [epsilon25, D]
end C25
end D4Bound.SphericalConcrete
