-- Generated from s0525_count26_exact.json; every arithmetic identity is kernel checked.
import D4Bound.SphericalConcretePolynomials
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign AnnularCertificate
namespace C26
noncomputable def g (t : ℝ) : ℝ := evalZ scalarPower26 t / scalarPowerDen26
noncomputable def scalarWeights : Fin 24 → ℝ := ![(5002483/20000000000), (15401/625000000), (885239/20000000000), (87983/50000000000), (37753/60000000000), (0/1), (0/1), (899/90000000000), (547/3125000000), (91/5000000000), (1519/30000000000), (0/1), (0/1), (0/1), (3617/160000000000), (4853/170000000000), (1/1500000000), (0/1), (0/1), (0/1), (83/55000000000), (3573/230000000000), (13/2400000000), (0/1)]
noncomputable def scalarRest (t : ℝ) : ℝ := ∑ i : Fin 24, scalarWeights i * (Polynomial.Chebyshev.U ℝ (i.val+1 : ℤ)).eval t
noncomputable def repairWeights : Fin 24 → ℝ := ![(37126538333/19999800000), (63872893483/29999700000), (76361227069/39999600000), (55722988013/49999500000), (3448130857/7499925000), (0/1), (0/1), (0/1), (1999836707/33333000000), (290606837/36666300000), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)]
noncomputable def T (t : ℝ) : ℝ := ∑ i : Fin 24, repairWeights i * (Polynomial.Chebyshev.U ℝ (i.val+1 : ℤ)).eval t
noncomputable def D : ℝ := (133770012193/4999950000)
theorem scalar_nonneg (i : Fin 24) : 0 ≤ scalarWeights i := by
  fin_cases i <;> norm_num [scalarWeights]
theorem repair_nonneg (i : Fin 24) : 0 ≤ repairWeights i := by
  fin_cases i <;> norm_num [repairWeights]
end C26
end D4Bound.SphericalConcrete
