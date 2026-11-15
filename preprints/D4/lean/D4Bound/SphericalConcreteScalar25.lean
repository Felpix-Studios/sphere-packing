-- Generated from s0515_count25_exact.json; every arithmetic identity is kernel checked.
import D4Bound.SphericalConcreteData25
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign AnnularCertificate
namespace C25
theorem scalar_identity (t : ℝ) : g t - 1 = scalarRest t := by
  norm_num [g, scalarRest, scalarWeights, Fin.sum_univ_succ, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, U17, U18, U19, U20, U21, U22, U23, U24, scalarPower25, scalarPowerDen25, evalZ]
  <;> ring
theorem scalar_diag : g 1 = (5000663387/5000000000) := by
  norm_num [g, scalarPower25, scalarPowerDen25, evalZ]
end C25
end D4Bound.SphericalConcrete
