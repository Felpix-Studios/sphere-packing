import D4Bound.CyclicNativeCorr

/-!
# Sharper allocation profile lower bound (Init only)

`allocProfLo2` agrees with `allocProfLo` except for the classical profile at `qh < 1/4`, where
it uses `min 1 (2 (1 - sqrtUp qh)^2)` (at least 1/2) instead of the constant 1/2. Near
antipodal pairs at large radii (`|y+z|^2 < 1/4`) the difference is up to half the term.
Soundness: `CyclicNativeAllocLoSound.allocProfLo2_sound` (same statement as
`allocProfLo_sound`).
-/
namespace D4Bound.CyclicNative

def allocProfLo2 (c : AllocN) (qh : Rat) : Rat :=
  if c.twoLevel then allocProfLo c qh
  else if 1/4 ≤ qh then allocProfLo c qh
  else
    let su := sqrtUp qh
    if 0 ≤ su ∧ su ≤ 1 ∧ qh ≤ su^2 then max (1/2) (min 1 (2*(1-su)^2)) else allocProfLo c qh

end D4Bound.CyclicNative
