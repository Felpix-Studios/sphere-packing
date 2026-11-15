import D4Bound.SphericalSignArrayData

/-! Whole-tree degree-twelve sign check for the 26-point near-code certificate.

`ArrayData.checkData` replays the complete subdivision tree from the root
tensors, and `ArrayData.checkData_sound` proves that a successful run gives
`OnCube`.  Only the run itself uses `native_decide`, so `onCube26` depends on
the Lean compiler in addition to the three standard axioms.
-/
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSign.Bernstein.Native
open ArrayData

theorem check26 : checkData upper26Data gramUpper26Data triangleTree26 = true := by
  native_decide

theorem onCube26 : OnCube upper26 gramUpper26 := by
  have h := checkData_sound _ _ _ check26
  rwa [upper26_eq, gramUpper26_eq] at h

#print axioms onCube26

end D4Bound.SphericalSign.Bernstein.Native
