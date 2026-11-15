import D4Bound.SphericalSurplusSignArray16
import D4Bound.SphericalSurplusSignTreeData2

/-! Whole-tree degree-sixteen surplus sign check for index 2 (6041 nodes).

`ArrayData.checkData` replays the complete subdivision tree from the root
tensors and `ArrayData.checkData_sound` proves that a successful run gives
`OnCube`. Only the run `check2` uses `native_decide`, so `onCube2` depends
on the Lean compiler (`Lean.ofReduceBool`, `Lean.trustCompiler`) in addition
to the three standard axioms. -/
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSurplusSign.Bernstein16.Native
open ArrayData

theorem check2 : checkData (tab upper2) (tab gramUpper2) triangleTree2 = true := by
  native_decide

theorem onCube2 : OnCube upper2 gramUpper2 := by
  have h := checkData_sound _ _ _ check2
  rwa [tensor_tab, tensor_tab] at h

#print axioms onCube2

end D4Bound.SphericalSurplusSign.Bernstein16.Native
