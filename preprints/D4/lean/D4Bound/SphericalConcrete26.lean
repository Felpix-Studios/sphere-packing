import D4Bound.SphericalConcreteArithmetic26
import D4Bound.SphericalCertCompose
import D4Bound.SphericalSignTriangle26
import D4Bound.SphericalSignNative26
set_option maxHeartbeats 0
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign SphereCertificate
namespace C26
theorem scalar_psd : SpherePSD (fun t => g t-1) := by
  have h := harmonic_PSD Finset.univ (fun i : Fin 24 => i.val+1) scalarWeights (fun i _ => scalar_nonneg i)
  simpa only [scalar_identity, scalarRest, Nat.cast_add, Nat.cast_one] using h
theorem repair_psd : SpherePSD T := by
  exact harmonic_PSD Finset.univ (fun i : Fin 24 => i.val+1) repairWeights (fun i _ => repair_nonneg i)
theorem code_bound (hc : Bernstein.OnCube Bernstein.upper26 Bernstein.gramUpper26) :
    SphericalCodeBound (21/40) 26 := by
  apply code_bound_from_rays Finset.univ (rayDegree rays26) (rayO rays26 originDen26) (rayV rays26 featureDen26) g T (21/40) (epsilon26:ℝ) 0 D 26
  · exact scalar_psd
  · exact repair_psd
  · norm_num [epsilon26]
  · exact repair_diag
  · exact repair_sign
  · exact rawPair26_nonpos
  · exact Bernstein.rawTriangle26_of_cube hc
  · exact decrease
  · exact objective

/-- The whole-tree check (`SphericalSignNative`, run by `native_decide`) discharges the OnCube premise. -/
theorem code_bound_unconditional : SphericalCodeBound (21/40) 26 :=
  code_bound Bernstein.Native.onCube26
#print axioms code_bound_unconditional

#print axioms code_bound
end C26
end D4Bound.SphericalConcrete
