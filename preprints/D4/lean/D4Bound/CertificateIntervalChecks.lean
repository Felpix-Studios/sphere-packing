import D4Bound.CertificateIntervalTree
import D4Bound.CertificateIntervalKinks
import D4Bound.CertificateIntervalCentered

/-! Kernel-evaluated acceptance and rejection controls for interval certificates. -/
namespace D4Bound.CertificateInterval

example : invOK ⟨-1,1⟩ ⟨-100,100⟩ = false := by decide +kernel
example : sqrtOK ⟨2,2⟩ ⟨7/5,3/2⟩ = true := by decide +kernel
example : sqrtOK ⟨2,2⟩ ⟨3/2,2⟩ = false := by decide +kernel
example : expOK 12 ⟨-1/2,1/2⟩ ⟨3/5,5/3⟩ = true := by decide +kernel
example : expOK 0 ⟨-1/2,1/2⟩ ⟨3/5,5/3⟩ = false := by decide +kernel
example : expOK 12 ⟨-2,1/2⟩ ⟨0,5/3⟩ = false := by decide +kernel
example : indicatorLEOK ⟨0,0⟩ ⟨1,1⟩ = true := by decide +kernel
example : indicatorLTOK ⟨0,0⟩ ⟨0,0⟩ = true := by decide +kernel
example : indicatorLEOK ⟨0,0⟩ ⟨0,0⟩ = false := by decide +kernel

def exampleInputs : ℕ → Interval
  | 0 => ⟨-1/2,1/2⟩
  | _ => ⟨0,0⟩

def exampleProgram : List Row :=
  [⟨.var 0, ⟨-1/2,1/2⟩⟩,
   ⟨.mul 0 0, ⟨-1/4,1/4⟩⟩,
   ⟨.exp 12 1, ⟨3/5,5/3⟩⟩,
   ⟨.add 1 0, ⟨7/20,23/12⟩⟩]

/-- The kernel accepts a nonpolynomial, input-dependent interval program. -/
theorem example_program_pass : nonnegOK 1 exampleInputs exampleProgram = true := by decide +kernel

/-- A forward register reference is rejected even when its default value is zero. -/
theorem forward_reference_rejected :
    nonnegOK 1 exampleInputs [⟨.add 0 0, ⟨0,0⟩⟩] = false := by decide +kernel

/-- A falsely elevated lower endpoint is rejected. -/
theorem false_lower_rejected :
    nonnegOK 1 exampleInputs
      [⟨.var 0, ⟨-1/2,1/2⟩⟩, ⟨.mul 0 0, ⟨1,2⟩⟩] = false := by decide +kernel

/-- Algebraic interpretation of the checked program, proved independently of intervals. -/
lemma example_program_eval (xs : ℕ → ℝ) :
    eval xs exampleProgram = xs 0 * xs 0 + Real.exp (xs 0) := by
  simp [eval, exampleProgram, evalFrom, evalOp]

theorem example_program_sound (xs : ℕ → ℝ) (hx : InDomain exampleInputs xs) :
    0 ≤ xs 0 * xs 0 + Real.exp (xs 0) := by
  simpa [example_program_eval] using nonneg_sound example_program_pass hx

/-- Split points must lie in the parent interval. -/
theorem invalid_split_rejected :
    checkTree 1 (exampleProgram.map Row.op) exampleInputs
      (.split 0 2 (.leaf exampleProgram) (.leaf exampleProgram)) = false := by decide +kernel

/-- Both children are checked: a failing child cannot be hidden by a passing sibling. -/
theorem missing_leaf_rejected :
    checkTree 1 (exampleProgram.map Row.op) exampleInputs
      (.split 0 0 (.leaf exampleProgram) (.leaf [])) = false := by decide +kernel

def centeredExample : CenteredData 1 :=
  {center := ⟨3,3⟩, gradient := fun _ => ⟨-1,1⟩,
   hessian := fun _ _ => ⟨-2,2⟩, radius := fun _ => 1}
example : centerLower centeredExample = 1 := by decide +kernel
example : centeredOK centeredExample = true := by decide +kernel
example : centeredOK {centeredExample with center := ⟨0,0⟩} = false := by decide +kernel

#print axioms D4Bound.CertificateInterval.centered_lower_sound
#print axioms D4Bound.CertificateInterval.centered_nonnegative
#print axioms D4Bound.CertificateInterval.mul_sound
#print axioms D4Bound.CertificateInterval.inv_sound
#print axioms D4Bound.CertificateInterval.sqrt_sound
#print axioms D4Bound.CertificateInterval.exp_sound
#print axioms D4Bound.CertificateInterval.exp_scaled_sound
#print axioms D4Bound.CertificateInterval.indicatorLE_sound
#print axioms D4Bound.CertificateInterval.indicatorLT_sound
#print axioms D4Bound.CertificateInterval.nonneg_sound
#print axioms D4Bound.CertificateInterval.checkTree_sound
#print axioms D4Bound.CertificateInterval.example_program_sound
#print axioms D4Bound.CertificateInterval.taylor_lower_01
#print axioms D4Bound.CertificateInterval.lower_surrogate_nonnegative

end D4Bound.CertificateInterval
