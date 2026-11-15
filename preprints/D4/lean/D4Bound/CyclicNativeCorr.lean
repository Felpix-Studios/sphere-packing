import D4Bound.CyclicNativeCore
import D4Bound.CyclicNativePoly

/-!
# Executable correction lower bounds for the native cyclic checker

Init-only. Rational interval lower bounds, on a box, for the nonnegative
correction terms that the cyclic sign subtracts from its polynomial part.
Soundness: `CyclicNativeCorrSound`.
-/
namespace D4Bound.CyclicNative

/-- A pointed cap; `use = false` drops it from the lower bound (always sound). -/
structure CapN where
  d : Rat
  a2 : Rat
  sigma : Rat
  weight : Rat
  vector : List Rat
  cutoff : Option Rat
  use : Bool

structure CData where
  basisIntervals : List (Rat × Rat)
  caps : List CapN

/-- Lower bound of `radialValue v r` for `r ∈ [lo,hi]` inside the basis interval of piece `p`. -/
def radialLo (BI : List (Rat × Rat)) (v : List Rat) (p : Nat) (lo hi : Rat) : Rat :=
  let ab := BI.getD p (0,1)
  let w := ab.2 - ab.1
  let zl := (lo - ab.1)/w
  let zh := (hi - ab.1)/w
  if 0 < w ∧ 0 ≤ zl ∧ zl ≤ zh ∧ zh ≤ 1 ∧ ((List.range 7).all fun i => decide (0 ≤ v.getD (7*p+i) 0))
  then ((List.range 7).map fun i =>
      v.getD (7*p+i) 0 * (NPoly.choose 6 i : Rat) * zl^i * (1-zh)^(6-i)).sum
  else 0

def capWeightLo (BI : List (Rat × Rat)) (c : CapN) (p : Nat) (lo hi : Rat) : Rat :=
  match c.cutoff with
  | none => radialLo BI c.vector p lo hi
  | some C => if C < lo then radialLo BI c.vector p lo hi else 0

/-- Integer square root by Newton iteration with fuel; correctness is checked by callers. -/
def isqrtAux : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | k+1, n, x => let y := (x + n / x) / 2; if y < x then isqrtAux k n y else x

def isqrt (n : Nat) : Nat := if n = 0 then 0 else isqrtAux 200 n n

/-- Candidate `floor(sqrt q * 2^40)/2^40` for `q ≥ 0`. -/
def sqrtDown (q : Rat) : Rat :=
  if q ≤ 0 then 0 else
  let s := isqrt ((q.num.toNat * 4^40) / q.den)
  (s : Rat) / (2^40 : Nat)

def sqrtUp (q : Rat) : Rat := sqrtDown q + 1 / (2^40 : Nat)

/-- Upper bound of `A = c(r) - sigma t` on a box. -/
def capAmax (c : CapN) (rlo rhi tlo thi : Rat) : Rat :=
  rhi/(2*c.d) + (if 0 ≤ c.d^2 - c.a2 then (c.d^2 - c.a2)/(2*c.d*rlo)
    else (c.d^2 - c.a2)/(2*c.d*rhi)) + max (-c.sigma*tlo) (-c.sigma*thi)

/-- Upper bound of `S = (1-sigma^2)(1-t^2)`. -/
def capSmax (c : CapN) (tlo thi : Rat) : Rat :=
  (1 - c.sigma^2) * (if tlo ≤ 0 ∧ 0 ≤ thi then 1 else max (1-tlo^2) (1-thi^2))

/-- Lower bound of `S`. -/
def capSmin (c : CapN) (tlo thi : Rat) : Rat :=
  (1 - c.sigma^2) * min (1-tlo^2) (1-thi^2)

/-- Lower bound of `capProbability c r t` on `[rlo,rhi] × [tlo,thi]`, valid when `|t| ≤ 1`. -/
def capProbLo (c : CapN) (rlo rhi tlo thi : Rat) : Rat :=
  if 0 < c.d ∧ 0 < rlo ∧ rlo ≤ rhi ∧ tlo ≤ thi ∧ c.sigma^2 ≤ 1 then
    if capAmax c rlo rhi tlo thi ≤ 0 then
      if 0 ≤ sqrtUp (capSmax c tlo thi) ∧ capSmax c tlo thi ≤ sqrtUp (capSmax c tlo thi)^2 then
        (if 0 < sqrtUp (capSmax c tlo thi) then
          min 1 ((1 - capAmax c rlo rhi tlo thi/sqrtUp (capSmax c tlo thi))/2) else 1)
      else 0
    else
      if 0 < sqrtDown (capSmin c tlo thi) ∧ sqrtDown (capSmin c tlo thi)^2 ≤ capSmin c tlo thi then
        max 0 ((1 - capAmax c rlo rhi tlo thi/sqrtDown (capSmin c tlo thi))/2)
      else 0
  else 0

/-- Lower bound of one cap's contribution to `capsCorrection r s t`. -/
def capTermLo (BI : List (Rat × Rat)) (c : CapN) (p q : Nat)
    (rlo rhi slo shi tlo thi : Rat) : Rat :=
  if c.use ∧ 0 ≤ c.weight then
    c.weight * (max 0 (capWeightLo BI c q slo shi) * capProbLo c rlo rhi tlo thi +
      max 0 (capWeightLo BI c p rlo rhi) * capProbLo c slo shi tlo thi) / 2
  else 0

def capsLo (D : CData) (p q : Nat) (rlo rhi slo shi tlo thi : Rat) : Rat :=
  (D.caps.map fun c => capTermLo D.basisIntervals c p q rlo rhi slo shi tlo thi).sum

/-! ## Interval helpers -/

/-- Lower and upper bounds of `n/d` for `n ∈ [n1,n2]`, `d ∈ [d1,d2]`, `d1 > 0`. -/
def quotLo (n1 d1 d2 : Rat) : Rat := if 0 ≤ n1 then n1/d2 else n1/d1
def quotHi (n2 d1 d2 : Rat) : Rat := if 0 ≤ n2 then n2/d1 else n2/d2

/-- Side cosine `(r^2+s^2-d^2)/(2rs)` enclosure for positive radii. -/
def cosLo (rl rh sl sh dl dh : Rat) : Rat := quotLo (rl^2+sl^2-dh^2) (2*rl*sl) (2*rh*sh)
def cosHi (rl rh sl sh dl dh : Rat) : Rat := quotHi (rh^2+sh^2-dl^2) (2*rl*sl) (2*rh*sh)

/-- Real interval of a box coordinate inside the case interval `[a,b]`. -/
def coordLo (ab : Rat × Rat) (d : Dy) : Rat := ab.1 + (ab.2 - ab.1) * d.lo
def coordHi (ab : Rat × Rat) (d : Dy) : Rat := ab.1 + (ab.2 - ab.1) * d.hi

/-! ## Full cases -/

/-- A full case: regions `p ≤ q ≤ k`, their closed intervals, and the constant gauge credit. -/
structure FullCase where
  p : Nat
  q : Nat
  k : Nat
  ir : Rat × Rat
  is : Rat × Rat
  id : Rat × Rat
  gauge : Rat

/-- Correction lower bound on a box (full case, caps and gauge). -/
def fullCorrLo (D : CData) (F : FullCase) (B : Box) : Rat :=
  let rl := coordLo F.ir B.a
  let rh := coordHi F.ir B.a
  let sl := coordLo F.is B.b
  let sh := coordHi F.is B.b
  let dl := coordLo F.id B.c
  let dh := coordHi F.id B.c
  capsLo D F.p F.q rl rh sl sh (cosLo rl rh sl sh dl dh) (cosHi rl rh sl sh dl dh) +
  capsLo D F.p F.k rl rh dl dh (cosLo rl rh dl dh sl sh) (cosHi rl rh dl dh sl sh) +
  capsLo D F.q F.k sl sh dl dh (cosLo sl sh dl dh rl rh) (cosHi sl sh dl dh rl rh) +
  F.gauge

/-- Threshold `(2 rlo slo dlo)^18 * max 0 corrLo`. -/
def fullThr (D : CData) (F : FullCase) (B : Box) : Rat :=
  (2 * coordLo F.ir B.a * coordLo F.is B.b * coordLo F.id B.c)^18 * max 0 (fullCorrLo D F B)

def fullWidths (F : FullCase) : Rat × Rat × Rat :=
  (F.ir.2 - F.ir.1, F.is.2 - F.is.1, F.id.2 - F.id.1)

/-- Gauge weight lower bound on region `p` (pair margins on pieces 0, 1, 2). -/
def gaugeLo (p : Nat) : Rat :=
  if p = 0 then 24/23 * (7/100000) else if p = 1 then 24/23 * (75/10000000)
  else if p = 2 then 24/23 * (281/100000) else 0

/-- Gauge indicator `psi` on region `p`. -/
def gaugePsiN (p : Nat) : Rat := if p ≤ 2 then 1/24 else 0

def gaugeConst (p q k : Nat) : Rat :=
  (gaugeLo p * (gaugePsiN q + gaugePsiN k) + gaugeLo q * (gaugePsiN p + gaugePsiN k) +
    gaugeLo k * (gaugePsiN p + gaugePsiN q)) / 2

def mkFull (br : List Rat) (p q k : Nat) : FullCase :=
  ⟨p, q, k, (br.getD p 0, br.getD (p+1) 0), (br.getD q 0, br.getD (q+1) 0),
    (br.getD k 0, br.getD (k+1) 0), gaugeConst p q k⟩

/-! ## Exterior cases -/

structure TentN where
  d : Rat
  weight : Rat
  vector : List Rat

structure GraphN where
  weight : Rat
  lo1 : Rat
  hi1 : Rat
  lo2 : Rat
  hi2 : Rat
  tlo : Rat
  thi : Rat
  firstOpen : Bool
  mixed : Bool

structure AllocN where
  weight : Rat
  vector : List Rat
  twoLevel : Bool
  inner : Rat
  outer : Rat

structure XData where
  tents : List TentN
  graphs : List GraphN
  allocs : List AllocN

/-- Upper bound of `r*t` for `r ∈ [rl,rh]`, `t ∈ [tl,th]`. -/
def prodHi (rl rh tl th : Rat) : Rat := max (max (rl*tl) (rl*th)) (max (rh*tl) (rh*th))
def prodLo (rl rh tl th : Rat) : Rat := min (min (rl*tl) (rl*th)) (min (rh*tl) (rh*th))

/-- Lower bound of `tentProfile d r t = max 0 (1-2(r^2+d^2+2drt))`, `r ≥ 0`. -/
def tentProfLo (d rl rh tl th : Rat) : Rat :=
  max 0 (1 - 2*(rh^2 + d^2 + (if 0 ≤ d then 2*d*prodHi rl rh tl th else 2*d*prodLo rl rh tl th)))

def tentTermLo (BI : List (Rat × Rat)) (c : TentN) (p q : Nat) (rl rh sl sh tl th : Rat) : Rat :=
  if 0 ≤ c.weight then
    c.weight * (max 0 (radialLo BI c.vector q sl sh) * tentProfLo c.d rl rh tl th +
      max 0 (radialLo BI c.vector p rl rh) * tentProfLo c.d sl sh tl th) / 2
  else 0

def inFirst (g : GraphN) (a b : Rat) : Bool := decide (g.lo1 ≤ a ∧ b ≤ g.hi1)
def inSecond (g : GraphN) (a b : Rat) : Bool :=
  (if g.firstOpen then decide (g.lo2 < a) else decide (g.lo2 ≤ a)) && decide (b ≤ g.hi2)

def graphTermLo (g : GraphN) (rl rh sl sh tl th : Rat) : Rat :=
  if 0 ≤ g.weight ∧ g.tlo ≤ tl ∧ th ≤ g.thi ∧
      ((inFirst g rl rh && inSecond g sl sh) ||
        (g.mixed && inFirst g sl sh && inSecond g rl rh)) = true
  then g.weight else 0

/-- Upper bound of `|x+y|^2 = (r-s)^2 + z((r+s)^2-49/16)` on an exterior box. -/
def sqDistHi (rl rh sl sh zh : Rat) : Rat :=
  max ((rl-sh)^2) ((rh-sl)^2) + zh*((rh+sh)^2 - 49/16)

/-- Lower bound of `allocationProfile c q` for `0 ≤ q ≤ qh`. -/
def allocProfLo (c : AllocN) (qh : Rat) : Rat :=
  if c.twoLevel then
    (if qh < c.inner^2 then 1 else if qh ≤ c.outer^2 then 1/2 else 0)
  else if 1/2 ≤ qh then 0 else if 1/4 ≤ qh then 1 - 2*qh else 1/2

def allocTermLo (BI : List (Rat × Rat)) (c : AllocN) (p q : Nat) (rl rh sl sh qh : Rat) : Rat :=
  if 0 ≤ c.weight then
    c.weight * (max 0 (radialLo BI c.vector p rl rh) + max 0 (radialLo BI c.vector q sl sh)) *
      allocProfLo c qh / 2
  else 0

/-- An exterior case: regions `p ≤ q`, their intervals, and the constant gauge credit. -/
structure ExtCase where
  p : Nat
  q : Nat
  ir : Rat × Rat
  is : Rat × Rat
  gauge : Rat

/-- `t = -1 + z h(r,s)` enclosure with `h = ((r+s)^2-49/16)/(2rs)`. -/
def extTLo (rl rh sl sh zl : Rat) : Rat := -1 + zl * quotLo ((rl+sl)^2 - 49/16) (2*rl*sl) (2*rh*sh)
def extTHi (rl rh sl sh zh : Rat) : Rat := -1 + zh * quotHi ((rh+sh)^2 - 49/16) (2*rl*sl) (2*rh*sh)

def extCorrLo (D : CData) (X : XData) (E : ExtCase) (B : Box) : Rat :=
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
  (X.allocs.map fun c => allocTermLo D.basisIntervals c E.p E.q rl rh sl sh (sqDistHi rl rh sl sh zh)).sum +
  E.gauge

def extThr (D : CData) (X : XData) (E : ExtCase) (B : Box) : Rat :=
  (2 * coordLo E.ir B.a * coordLo E.is B.b)^18 * max 0 (extCorrLo D X E B)

def extWidths (E : ExtCase) : Rat × Rat × Rat := (E.ir.2 - E.ir.1, E.is.2 - E.is.1, 1)

def gaugeConstExt (p q : Nat) : Rat := (gaugeLo p * gaugePsiN q + gaugeLo q * gaugePsiN p) / 2

def mkExt (br : List Rat) (p q : Nat) : ExtCase :=
  ⟨p, q, (br.getD p 0, br.getD (p+1) 0), (br.getD q 0, br.getD (q+1) 0), gaugeConstExt p q⟩

/-- Exterior numerator `A = -B + z((a+b)^2-49/16)` and denominator `B = 2ab`. -/
def extB (a b : NPoly.Poly) : NPoly.Poly := NPoly.scale 2 (NPoly.fastMul a b)
def extA (a b : NPoly.Poly) : NPoly.Poly :=
  NPoly.fastAdd (NPoly.scale (-1) (extB a b))
    (NPoly.fastMul (NPoly.coordinate 2)
      (NPoly.fastAdd (NPoly.fastPower (NPoly.fastAdd a b) 2) (NPoly.constant (-49/16))))

end D4Bound.CyclicNative
