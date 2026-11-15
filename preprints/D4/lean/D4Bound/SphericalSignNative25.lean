import D4Bound.SphericalSignArrayData

/-! Whole-tree degree-twelve sign check for the 25-point near-code certificate.

`ArrayData.checkData` replays the complete subdivision tree from the root
tensors, and `ArrayData.checkData_sound` proves that a successful run gives
`OnCube`.  Only the run itself uses `native_decide`, so `onCube25` depends on
the Lean compiler in addition to the three standard axioms.
-/
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSign.Bernstein.Native
open ArrayData

theorem check25 : checkData upper25Data gramUpper25Data triangleTree25 = true := by
  native_decide

theorem onCube25 : OnCube upper25 gramUpper25 := by
  have h := checkData_sound _ _ _ check25
  rwa [upper25_eq, gramUpper25_eq] at h

#print axioms onCube25

end D4Bound.SphericalSign.Bernstein.Native
