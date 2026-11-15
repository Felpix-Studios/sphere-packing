import D4Bound.V7CyclicNativeFullG

/-! Shared parameters of the native cyclic case checks. Any choice is sound. -/
namespace D4Bound.V7
open CyclicNative

/-- Caps with weight times largest radial coefficient below 1e-11 get lower bound 0. -/
def capUse (c : Cap) : Bool := decide ((1:ℚ)/10^11 ≤ c.weight * c.vector.foldl max 0)

def caseUnit : ℚ := 1/2^40
def caseFuel : ℕ := 64

end D4Bound.V7
