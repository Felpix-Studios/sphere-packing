import D4Bound.SphericalConcreteArithmetic25
import D4Bound.SphericalCertCompose
import D4Bound.SphericalSignTriangle25
import D4Bound.SphericalSignNative25
set_option maxHeartbeats 0
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign SphereCertificate
namespace C25
theorem scalar_psd : SpherePSD (fun t => g t-1) := by
  have h := harmonic_PSD Finset.univ (fun i : Fin 24 => i.val+1) scalarWeights (fun i _ => scalar_nonneg i)
  simpa only [scalar_identity, scalarRest, Nat.cast_add, Nat.cast_one] using h
theorem repair_psd : SpherePSD T := by
  exact harmonic_PSD Finset.univ (fun i : Fin 24 => i.val+1) repairWeights (fun i _ => repair_nonneg i)
theorem code_bound (hc : Bernstein.OnCube Bernstein.upper25 Bernstein.gramUpper25) :
    SphericalCodeBound (103/200) 25 := by
  apply code_bound_from_rays Finset.univ (rayDegree rays25) (rayO rays25 originDen25) (rayV rays25 featureDen25) g T (103/200) (epsilon25:ℝ) 0 D 25
  · exact scalar_psd
  · exact repair_psd
  · norm_num [epsilon25]
  · exact repair_diag
  · exact repair_sign
  · exact rawPair25_nonpos
  · exact Bernstein.rawTriangle25_of_cube hc
  · exact decrease
  · exact objective

/-- The whole-tree check (`SphericalSignNative`, run by `native_decide`) discharges the OnCube premise. -/
theorem code_bound_unconditional : SphericalCodeBound (103/200) 25 :=
  code_bound Bernstein.Native.onCube25
#print axioms code_bound_unconditional

#print axioms code_bound
end C25
end D4Bound.SphericalConcrete
