import D4Bound.SphericalSurplusSignArray16
import D4Bound.SphericalSurplusSignTreeData1

/-! Whole-tree degree-sixteen surplus sign check for index 1 (8747 nodes).

`ArrayData.checkData` replays the complete subdivision tree from the root
tensors and `ArrayData.checkData_sound` proves that a successful run gives
`OnCube`. Only the run `check1` uses `native_decide`, so `onCube1` depends
on the Lean compiler (`Lean.ofReduceBool`, `Lean.trustCompiler`) in addition
to the three standard axioms. -/
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSurplusSign.Bernstein16.Native
open ArrayData

theorem check1 : checkData (tab upper1) (tab gramUpper1) triangleTree1 = true := by
  native_decide

theorem onCube1 : OnCube upper1 gramUpper1 := by
  have h := checkData_sound _ _ _ check1
  rwa [tensor_tab, tensor_tab] at h

#print axioms onCube1

end D4Bound.SphericalSurplusSign.Bernstein16.Native
