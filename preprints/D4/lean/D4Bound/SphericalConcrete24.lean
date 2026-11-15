import D4Bound.SphericalConcreteArithmetic24
import D4Bound.SphericalCertCompose
import D4Bound.SphericalSignTriangle24
import D4Bound.SphericalSignNative24
set_option maxHeartbeats 0
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign SphereCertificate
namespace C24
theorem scalar_psd : SpherePSD (fun t => g t-1) := by
  have h := harmonic_PSD Finset.univ (fun i : Fin 24 => i.val+1) scalarWeights (fun i _ => scalar_nonneg i)
  simpa only [scalar_identity, scalarRest, Nat.cast_add, Nat.cast_one] using h
theorem repair_psd : SpherePSD T := by
  exact harmonic_PSD Finset.univ (fun i : Fin 20 => i.val+1) repairWeights (fun i _ => repair_nonneg i)
theorem code_bound (hc : Bernstein.OnCube Bernstein.upper24 Bernstein.gramUpper24) :
    SphericalCodeBound (203/400) 24 := by
  apply code_bound_from_rays Finset.univ (rayDegree rays24) (rayO rays24 originDen24) (rayV rays24 featureDen24) g T (203/400) (epsilon24:ℝ) 0 D 24
  · exact scalar_psd
  · exact repair_psd
  · norm_num [epsilon24]
  · exact repair_diag
  · exact repair_sign
  · exact rawPair24_nonpos
  · exact Bernstein.rawTriangle24_of_cube hc
  · exact decrease
  · exact objective

/-- The whole-tree check (`SphericalSignNative`, run by `native_decide`) discharges the OnCube premise. -/
theorem code_bound_unconditional : SphericalCodeBound (203/400) 24 :=
  code_bound Bernstein.Native.onCube24
#print axioms code_bound_unconditional

#print axioms code_bound
end C24
end D4Bound.SphericalConcrete
