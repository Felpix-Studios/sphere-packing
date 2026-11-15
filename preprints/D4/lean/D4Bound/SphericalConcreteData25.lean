-- Generated from s0515_count25_exact.json; every arithmetic identity is kernel checked.
import D4Bound.SphericalConcretePolynomials
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign AnnularCertificate
namespace C25
noncomputable def g (t : ℝ) : ℝ := evalZ scalarPower25 t / scalarPowerDen25
noncomputable def scalarWeights : Fin 24 → ℝ := ![(81263/2500000000), (100013/6000000000), (107121/40000000000), (10101/10000000000), (377/5000000000), (0/1), (0/1), (149/18000000000), (5031/100000000000), (1/137500000), (899/40000000000), (0/1), (0/1), (0/1), (1553/160000000000), (1469/170000000000), (0/1), (0/1), (0/1), (0/1), (7/3437500000), (61/10000000000), (103/80000000000), (0/1)]
noncomputable def scalarRest (t : ℝ) : ℝ := ∑ i : Fin 24, scalarWeights i * (Polynomial.Chebyshev.U ℝ (i.val+1 : ℤ)).eval t
noncomputable def repairWeights : Fin 24 → ℝ := ![(18374447773/9999900000), (62934731123/29999700000), (37005817471/19999800000), (53468561599/49999500000), (8525318693/19999800000), (0/1), (0/1), (0/1), (143899621/2777750000), (94664483/54999450000), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)]
noncomputable def T (t : ℝ) : ℝ := ∑ i : Fin 24, repairWeights i * (Polynomial.Chebyshev.U ℝ (i.val+1 : ℤ)).eval t
noncomputable def D : ℝ := (258109494611/9999900000)
theorem scalar_nonneg (i : Fin 24) : 0 ≤ scalarWeights i := by
  fin_cases i <;> norm_num [scalarWeights]
theorem repair_nonneg (i : Fin 24) : 0 ≤ repairWeights i := by
  fin_cases i <;> norm_num [repairWeights]
end C25
end D4Bound.SphericalConcrete
