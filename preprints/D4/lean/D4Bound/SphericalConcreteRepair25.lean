-- Generated from s0515_count25_exact.json; every arithmetic identity is kernel checked.
import D4Bound.SphericalConcreteData25
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign AnnularCertificate
namespace C25
theorem repair_identity (t : ℝ) : T t = evalZ repair25 t / repair25Den / (99999/100000) - 1 := by
  norm_num [T, repairWeights, Fin.sum_univ_succ, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, U17, U18, U19, U20, U21, U22, U23, U24, repair25, repair25Den, evalZ]
  <;> ring
theorem repair_sign (t : ℝ) (hlo : -1 ≤ t) (hhi : t ≤ (103/200)) : T t ≤ -1 := by
  rw [repair_identity]
  have h := repair25_nonpos t hlo hhi
  have hd : (0:ℝ) < repair25Den := by norm_num [repair25Den]
  have hp := div_nonpos_of_nonpos_of_nonneg h hd.le
  have hq := div_nonpos_of_nonpos_of_nonneg hp (show (0:ℝ) ≤ (99999/100000) by norm_num)
  linarith
theorem repair_diag : T 1 = D := by
  norm_num [T, repairWeights, D, Fin.sum_univ_succ, Polynomial.Chebyshev.U_eval_one]
end C25
end D4Bound.SphericalConcrete
