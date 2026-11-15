-- Generated from s05075_taper12_exact.json; every arithmetic identity is kernel checked.
import D4Bound.SphericalConcretePolynomials
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign AnnularCertificate
namespace C24
noncomputable def g (t : ℝ) : ℝ := evalZ scalarPower24 t / scalarPowerDen24
noncomputable def scalarWeights : Fin 24 → ℝ := ![(135603/20000000000), (47251/15000000000), (8917/40000000000), (621/3125000000), (211/30000000000), (0/1), (0/1), (19/11250000000), (141/20000000000), (101/110000000000), (139/60000000000), (0/1), (0/1), (0/1), (237/160000000000), (181/170000000000), (0/1), (0/1), (0/1), (0/1), (113/220000000000), (1/1437500000), (1/24000000000), (0/1)]
noncomputable def scalarRest (t : ℝ) : ℝ := ∑ i : Fin 24, scalarWeights i * (Polynomial.Chebyshev.U ℝ (i.val+1 : ℤ)).eval t
noncomputable def repairWeights : Fin 20 → ℝ := ![(18283032547/9999900000), (12482797999/5999940000), (24279916409/13333200000), (52368387037/49999500000), (493383407/1199988000), (0/1), (0/1), (0/1), (972777343/19999800000), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)]
noncomputable def T (t : ℝ) : ℝ := ∑ i : Fin 20, repairWeights i * (Polynomial.Chebyshev.U ℝ (i.val+1 : ℤ)).eval t
noncomputable def D : ℝ := (126860624209/4999950000)
theorem scalar_nonneg (i : Fin 24) : 0 ≤ scalarWeights i := by
  fin_cases i <;> norm_num [scalarWeights]
theorem repair_nonneg (i : Fin 20) : 0 ≤ repairWeights i := by
  fin_cases i <;> norm_num [repairWeights]
end C24
end D4Bound.SphericalConcrete
