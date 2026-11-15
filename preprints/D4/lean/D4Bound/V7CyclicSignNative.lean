import D4Bound.V7CyclicNativeSign
import D4Bound.V7CyclicOutsideNative

/-! The cyclic sign condition for the V7 kernel, with no premises.

`v7_cyclic_sign_of_outside` reduces it to the 84 full cases (one `native_decide` each) and the
exterior statement; `outside_native` proves the exterior statement from the 28 exterior cases. -/
namespace D4Bound.V7

theorem cyclicSign_kernel : CyclicSign kernel :=
  v7_cyclic_sign_of_outside outside_native

end D4Bound.V7

#print axioms D4Bound.V7.cyclicSign_kernel
