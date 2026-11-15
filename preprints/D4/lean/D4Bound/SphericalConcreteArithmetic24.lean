-- Generated from s05075_taper12_exact.json; every arithmetic identity is kernel checked.
import D4Bound.SphericalConcreteScalar24
import D4Bound.SphericalConcreteRepair24
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign AnnularCertificate
namespace C24
theorem origin_check : originNumerator rays24 = 23850709941097078080 := by decide +kernel
theorem origin_value : SphereCertificate.origin Finset.univ (rayDegree rays24) (rayO rays24 originDen24) = (74533468565928369/3125000000000000) := by
  rw [origin_eq, origin_check]
  norm_num [originDen24]
theorem decrease : (epsilon24:ℝ)*D + 0 < 1 := by norm_num [epsilon24, D]
theorem objective : g 1 + SphereCertificate.origin Finset.univ (rayDegree rays24) (rayO rays24 originDen24) - ((epsilon24:ℝ)*D+0) < (24+1:ℕ)*(1-((epsilon24:ℝ)*D+0)) := by
  rw [scalar_diag, origin_value]
  norm_num [epsilon24, D]
end C24
end D4Bound.SphericalConcrete
