import D4Bound.CyclicNativeCorr
import D4Bound.CyclicNativeAllocLo

/-!
# Exterior threshold with diagonal caps and the sharper allocation profile (Init only)

For the exterior cases with the gauge inside the polynomial (`V7CyclicNativeExtG`). Two
changes to `extThr`:

* On pieces 5 and 6 the gauge polynomial `KBN.Ugen` drops the diagonal caps correction
  `capsCorrection x x 1`; a box lower bound of it is added back with a nonnegative weight per
  side (`wr`, `ws`), as in `CyclicNativeFullGThr` for the full cases.
* Allocations use `allocProfLo2` (square-root branch of the classical profile).

Soundness: `V7CyclicOutsideExtW`. Compiled to a native library (with `CyclicNativeAllocLo`).
-/
namespace D4Bound.CyclicNative

/-- An exterior case with per-side weights of the diagonal caps term. -/
structure ExtCaseW where
  base : ExtCase
  wr : Rat
  ws : Rat

def allocTermLo2 (BI : List (Rat × Rat)) (c : AllocN) (p q : Nat) (rl rh sl sh qh : Rat) : Rat :=
  if 0 ≤ c.weight then
    c.weight * (max 0 (radialLo BI c.vector p rl rh) + max 0 (radialLo BI c.vector q sl sh)) *
      allocProfLo2 c qh / 2
  else 0

def extCorrLoW (D : CData) (X : XData) (W : ExtCaseW) (B : Box) : Rat :=
  let E := W.base
  let rl := coordLo E.ir B.a
  let rh := coordHi E.ir B.a
  let sl := coordLo E.is B.b
  let sh := coordHi E.is B.b
  let zl := B.c.lo
  let zh := B.c.hi
  let tl := extTLo rl rh sl sh zl
  let th := extTHi rl rh sl sh zh
  capsLo D E.p E.q rl rh sl sh tl th +
  (X.tents.map fun c => tentTermLo D.basisIntervals c E.p E.q rl rh sl sh tl th).sum +
  (X.graphs.map fun g => graphTermLo g rl rh sl sh tl th).sum +
  (X.allocs.map fun c => allocTermLo2 D.basisIntervals c E.p E.q rl rh sl sh (sqDistHi rl rh sl sh zh)).sum +
  E.gauge +
  W.wr * capsLo D E.p E.p rl rh rl rh 1 1 +
  W.ws * capsLo D E.q E.q sl sh sl sh 1 1

/-- Threshold `(2 rlo slo)^18 * max 0 corrLoW`. -/
def extThrW (D : CData) (X : XData) (W : ExtCaseW) (B : Box) : Rat :=
  (2 * coordLo W.base.ir B.a * coordLo W.base.is B.b)^18 * max 0 (extCorrLoW D X W B)

end D4Bound.CyclicNative
