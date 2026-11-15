import D4Bound.V7CensusFromCubes
import D4Bound.SphericalSurplusSignNative0
import D4Bound.SphericalSurplusSignNative1
import D4Bound.SphericalSurplusSignNative2

/-! `CensusFloor V7.kernel` with no premises. The three degree-16 cube
certificates come from the whole-tree runs `SphericalSurplusSignNative{0,1,2}`,
which use `native_decide`. -/
namespace D4Bound.V7

theorem censusFloor_kernel : CensusFloor kernel :=
  censusFloor_of_cubes SphericalSurplusSign.Bernstein16.Native.onCube0
    SphericalSurplusSign.Bernstein16.Native.onCube1
    SphericalSurplusSign.Bernstein16.Native.onCube2

end D4Bound.V7

#print axioms D4Bound.V7.censusFloor_kernel
