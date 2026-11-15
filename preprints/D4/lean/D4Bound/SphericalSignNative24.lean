import D4Bound.SphericalSignArrayData

/-! Whole-tree degree-twelve sign check for the 24-point near-code certificate.

`ArrayData.checkData` replays the complete subdivision tree from the root
tensors, and `ArrayData.checkData_sound` proves that a successful run gives
`OnCube`.  Only the run itself uses `native_decide`, so `onCube24` depends on
the Lean compiler in addition to the three standard axioms.
-/
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSign.Bernstein.Native
open ArrayData

theorem check24 : checkData upper24Data gramUpper24Data triangleTree24 = true := by
  native_decide

theorem onCube24 : OnCube upper24 gramUpper24 := by
  have h := checkData_sound _ _ _ check24
  rwa [upper24_eq, gramUpper24_eq] at h

#print axioms onCube24

end D4Bound.SphericalSign.Bernstein.Native
