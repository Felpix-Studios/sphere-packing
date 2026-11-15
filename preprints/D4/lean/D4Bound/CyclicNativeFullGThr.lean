import D4Bound.CyclicNativeCorr

/-!
# Threshold of the full cases with diagonal caps (Init only)

For the gauge-in-polynomial route (`V7CyclicNativeFullG`). On pieces 5 and 6 the gauge
polynomial `KBN.Ugen` drops the diagonal caps correction `capsCorrection x x 1`; this
threshold adds a box lower bound of it back, with a nonnegative weight per side. Soundness:
`V7CyclicNativeFullG`. Compiled to a native library together with Core, Poly and Corr.
-/
namespace D4Bound.CyclicNative

/-- A full case with per-side weights of the diagonal caps term. -/
structure FullCaseG where
  base : FullCase
  wr : Rat
  ws : Rat
  wd : Rat

/-- Lower bound of the diagonal caps correction `capsCorrection x x 1`, `x ∈ [lo,hi]`, piece `k`. -/
def diagCapsLo (D : CData) (k : Nat) (lo hi : Rat) : Rat := capsLo D k k lo hi lo hi 1 1

def fullCorrLoG (D : CData) (F : FullCaseG) (B : Box) : Rat :=
  fullCorrLo D F.base B +
    F.wr * diagCapsLo D F.base.p (coordLo F.base.ir B.a) (coordHi F.base.ir B.a) +
    F.ws * diagCapsLo D F.base.q (coordLo F.base.is B.b) (coordHi F.base.is B.b) +
    F.wd * diagCapsLo D F.base.k (coordLo F.base.id B.c) (coordHi F.base.id B.c)

/-- Threshold `(2 rlo slo dlo)^18 * max 0 corrLoG`. -/
def fullThrG (D : CData) (F : FullCaseG) (B : Box) : Rat :=
  (2 * coordLo F.base.ir B.a * coordLo F.base.is B.b * coordLo F.base.id B.c)^18 *
    max 0 (fullCorrLoG D F B)

end D4Bound.CyclicNative
