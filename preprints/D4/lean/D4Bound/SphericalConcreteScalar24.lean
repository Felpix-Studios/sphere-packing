-- Generated from s05075_taper12_exact.json; every arithmetic identity is kernel checked.
import D4Bound.SphericalConcreteData24
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign AnnularCertificate
namespace C24
theorem scalar_identity (t : ℝ) : g t - 1 = scalarRest t := by
  norm_num [g, scalarRest, scalarWeights, Fin.sum_univ_succ, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, U17, U18, U19, U20, U21, U22, U23, U24, scalarPower24, scalarPowerDen24, evalZ]
  <;> ring
theorem scalar_diag : g 1 = (10000251317/10000000000) := by
  norm_num [g, scalarPower24, scalarPowerDen24, evalZ]
end C24
end D4Bound.SphericalConcrete
