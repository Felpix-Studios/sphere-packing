import D4Bound.SphericalSurplusSignArray16
import D4Bound.SphericalSurplusSignTreeData0

/-! Whole-tree degree-sixteen surplus sign check for index 0 (7921 nodes).

`ArrayData.checkData` replays the complete subdivision tree from the root
tensors and `ArrayData.checkData_sound` proves that a successful run gives
`OnCube`. Only the run `check0` uses `native_decide`, so `onCube0` depends
on the Lean compiler (`Lean.ofReduceBool`, `Lean.trustCompiler`) in addition
to the three standard axioms. -/
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSurplusSign.Bernstein16.Native
open ArrayData

theorem check0 : checkData (tab upper0) (tab gramUpper0) triangleTree0 = true := by
  native_decide

theorem onCube0 : OnCube upper0 gramUpper0 := by
  have h := checkData_sound _ _ _ check0
  rwa [tensor_tab, tensor_tab] at h

#print axioms onCube0

end D4Bound.SphericalSurplusSign.Bernstein16.Native
