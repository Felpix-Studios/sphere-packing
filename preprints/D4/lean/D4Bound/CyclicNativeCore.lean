/-!
# Executable core of the native cyclic-sign checker

This module imports only `Init`, so it can be compiled to native code and
loaded with `--load-dynlib`. It contains no proofs. Soundness of every
function is proved in `D4Bound.CyclicNativeSound` on the three standard axioms.

Tensors hold Bernstein coefficients of a trivariate polynomial on the unit
cube, as integers times a fixed positive rational unit. Splits use a
ceil-rounded midpoint de Casteljau triangle, so the integer coefficients
stay upper bounds for the exact real coefficients.
-/
namespace D4Bound.CyclicNative

/-- Ceil of the average `(a+b)/2`. -/
def cavg (a b : Int) : Int := (a + b + 1) / 2

/-- One row of the de Casteljau triangle. -/
def triStep (row : Array Int) : Array Int :=
  Array.ofFn (n := row.size - 1) fun i => cavg (row.getD i.val 0) (row.getD (i.val+1) 0)

/-- Collect the first and last entry of each triangle row. -/
def triLoop : Nat → Array Int → Array Int → Array Int → Array Int × Array Int
  | 0, row, L, R => (L.push (row.getD 0 0), R.push (row.getD (row.size-1) 0))
  | k+1, row, L, R =>
    triLoop k (triStep row) (L.push (row.getD 0 0)) (R.push (row.getD (row.size-1) 0))

/-- Left and right halves of one fiber of length `n+1`. -/
def splitFiber (n : Nat) (g : Array Int) : Array Int × Array Int :=
  let p := triLoop n g #[] #[]
  (p.1, p.2.reverse)

/-- A dense tensor of degrees `n0,n1,n2`. -/
structure Tens where
  n0 : Nat
  n1 : Nat
  n2 : Nat
  data : Array Int

def Tens.idx (T : Tens) (i j k : Nat) : Nat := (i*(T.n1+1)+j)*(T.n2+1)+k
def Tens.get (T : Tens) (i j k : Nat) : Int := T.data.getD (T.idx i j k) 0

/-- The fiber along the last axis with index `f = i*(n1+1)+j`. -/
def Tens.fiber (T : Tens) (f : Nat) : Array Int :=
  Array.ofFn (n := T.n2+1) fun k => T.data.getD (f*(T.n2+1)+k.val) 0

/-- Split along the last axis at its midpoint. -/
def splitLast (T : Tens) : Tens × Tens :=
  let m := T.n2+1
  let nf := (T.n0+1)*(T.n1+1)
  let fs : Array (Array Int × Array Int) :=
    Array.ofFn (n := nf) fun f => splitFiber T.n2 (T.fiber f.val)
  let L := Array.ofFn (n := nf*m) fun q => (fs.getD (q.val/m) (#[],#[])).1.getD (q.val%m) 0
  let R := Array.ofFn (n := nf*m) fun q => (fs.getD (q.val/m) (#[],#[])).2.getD (q.val%m) 0
  (⟨T.n0,T.n1,T.n2,L⟩, ⟨T.n0,T.n1,T.n2,R⟩)

/-- Rotation `new(a,b,c) = old(c,a,b)`: the old first axis becomes the last. -/
def rot (T : Tens) : Tens :=
  let m0 := T.n0+1
  let m2 := T.n2+1
  ⟨T.n1, T.n2, T.n0, Array.ofFn (n := (T.n1+1)*m2*m0) fun q =>
    let c := q.val % m0
    let ab := q.val / m0
    T.get c (ab / m2) (ab % m2)⟩

/-- Largest coefficient, at least zero. -/
def Tens.top (T : Tens) : Int := T.data.foldl max 0

/-- One dyadic coordinate interval `[num/2^lev, (num+1)/2^lev]` of the unit interval. -/
structure Dy where
  num : Nat
  lev : Nat

structure Box where
  a : Dy
  b : Dy
  c : Dy

def Dy.lo (d : Dy) : Rat := (d.num : Rat) / (2^d.lev : Nat)
def Dy.hi (d : Dy) : Rat := ((d.num+1 : Nat) : Rat) / (2^d.lev : Nat)
def Dy.left (d : Dy) : Dy := ⟨2*d.num, d.lev+1⟩
def Dy.right (d : Dy) : Dy := ⟨2*d.num+1, d.lev+1⟩

def rootBox : Box := ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩

/-- Split one tensor axis: 0, 1 or 2. Axes 0 and 1 are rotated to the end and back. -/
def splitAxis (T : Tens) : Nat → Tens × Tens
  | 0 => let p := splitLast (rot T); (rot (rot p.1), rot (rot p.2))
  | 1 => let p := splitLast (rot (rot T)); (rot p.1, rot p.2)
  | _ => splitLast T

def Box.splitAxis (B : Box) : Nat → Box × Box
  | 0 => (⟨B.a.left,B.b,B.c⟩, ⟨B.a.right,B.b,B.c⟩)
  | 1 => (⟨B.a,B.b.left,B.c⟩, ⟨B.a,B.b.right,B.c⟩)
  | _ => (⟨B.a,B.b,B.c.left⟩, ⟨B.a,B.b,B.c.right⟩)

/-- Widest coordinate in real units; `w` are the case widths. -/
def chooseAxis (w : Rat × Rat × Rat) (B : Box) : Nat :=
  let x := w.1 / (2^B.a.lev : Nat)
  let y := w.2.1 / (2^B.b.lev : Nat)
  let z := w.2.2 / (2^B.c.lev : Nat)
  if y ≤ x then (if z ≤ x then 0 else 2) else (if z ≤ y then 1 else 2)

/-- Self-subdividing check. A box passes when every upper coefficient times the
unit is at most the threshold of that box. -/
def check (thr : Box → Rat) (unit : Rat) (w : Rat × Rat × Rat) : Nat → Tens → Box → Bool
  | 0, T, B => T.top == 0 || decide ((T.top : Rat) * unit ≤ thr B)
  | fuel+1, T, B =>
    T.top == 0 || decide ((T.top : Rat) * unit ≤ thr B) ||
      (let ax := chooseAxis w B
       let p := splitAxis T ax
       let q := B.splitAxis ax
       check thr unit w fuel p.1 q.1 && check thr unit w fuel p.2 q.2)

/-! ## Initial Bernstein tensor from a sparse rational polynomial -/

/-- Pascal row `n`. -/
def pascal : Nat → Array Nat
  | 0 => #[1]
  | n+1 => let r := pascal n
    Array.ofFn (n := n+2) fun k => (if k.val = 0 then 0 else r.getD (k.val-1) 0) + r.getD k.val 0

/-- Pascal rows 0..127, a closed constant evaluated once. -/
def pascalTab : Array (Array Nat) := Array.ofFn (n := 128) fun n => pascal n.val

def binom (n k : Nat) : Nat :=
  if n < 128 then (pascalTab.getD n #[]).getD k 0 else (pascal n).getD k 0

/-- Power-to-Bernstein transform of one fiber: `out_i = sum_{l<=i} C(n-l,i-l) g_l`. -/
def convFiber (n : Nat) (g : Array Int) : Array Int :=
  Array.ofFn (n := n+1) fun i =>
    (List.range (i.val+1)).foldl (fun s l => s + (binom (n-l) (i.val-l) : Int) * g.getD l 0) 0

def convLast (T : Tens) : Tens :=
  let m := T.n2+1
  let nf := (T.n0+1)*(T.n1+1)
  let fs : Array (Array Int) := Array.ofFn (n := nf) fun f => convFiber T.n2 (T.fiber f.val)
  ⟨T.n0,T.n1,T.n2, Array.ofFn (n := nf*m) fun q => (fs.getD (q.val/m) #[]).getD (q.val%m) 0⟩

/-- Transform all three axes; the result has the same axis order. -/
def convAll (T : Tens) : Tens := rot (convLast (rot (convLast (rot (convLast T)))))

/-- Dense integer power tensor `A` with `p = A / D` coefficientwise. -/
def denseOf (n0 n1 n2 : Nat) (D : Nat) (p : List ((Nat × Nat × Nat) × Rat)) : Tens :=
  let T0 : Tens := ⟨n0,n1,n2, Array.replicate ((n0+1)*(n1+1)*(n2+1)) 0⟩
  p.foldl (fun T t =>
    let q := t.2 * (D : Rat)
    ⟨T.n0,T.n1,T.n2, T.data.modify (T.idx t.1.1 t.1.2.1 t.1.2.2) (· + q.num)⟩) T0

/-- Common denominator of the coefficients. -/
def commonDen (p : List ((Nat × Nat × Nat) × Rat)) : Nat :=
  p.foldl (fun d t => Nat.lcm d t.2.den) 1

/-- Ceil of a rational. -/
def rceil (q : Rat) : Int := -((-q.num) / (q.den : Int))

/-- Scale transformed coefficients: `hi_ijk = ceil(B'_ijk / (D * C * unit))`. -/
def scaleUp (T : Tens) (D : Nat) (unit : Rat) : Tens :=
  ⟨T.n0,T.n1,T.n2, Array.ofFn (n := (T.n0+1)*(T.n1+1)*(T.n2+1)) fun q =>
    let k := q.val % (T.n2+1)
    let ij := q.val / (T.n2+1)
    let j := ij % (T.n1+1)
    let i := ij / (T.n1+1)
    rceil ((T.get i j k : Rat) /
      ((D * binom T.n0 i * binom T.n1 j * binom T.n2 k : Nat) * unit))⟩

/-- Exponent and coefficient sanity: every exponent within the degrees. -/
def degreesOK (n0 n1 n2 : Nat) (p : List ((Nat × Nat × Nat) × Rat)) : Bool :=
  p.all fun t => decide (t.1.1 ≤ n0 ∧ t.1.2.1 ≤ n1 ∧ t.1.2.2 ≤ n2)

/-- Maximal exponents per variable. -/
def degrees (p : List ((Nat × Nat × Nat) × Rat)) : Nat × Nat × Nat :=
  p.foldl (fun d t => (max d.1 t.1.1, max d.2.1 t.1.2.1, max d.2.2 t.1.2.2)) (0,0,0)

def initial (p : List ((Nat × Nat × Nat) × Rat)) (unit : Rat) : Tens :=
  let d := degrees p
  let D := commonDen p
  scaleUp (convAll (denseOf d.1 d.2.1 d.2.2 D p)) D unit

/-- Every coefficient becomes an integer after multiplying by `D`. -/
def intOK (D : Nat) (p : List ((Nat × Nat × Nat) × Rat)) : Bool :=
  p.all fun t => (t.2 * (D : Rat)).den == 1

/-- Full case check from a sparse unit-cube polynomial. -/
def checkPoly (thr : Box → Rat) (unit : Rat) (w : Rat × Rat × Rat) (fuel : Nat)
    (p : List ((Nat × Nat × Nat) × Rat)) : Bool :=
  let d := degrees p
  degreesOK d.1 d.2.1 d.2.2 p && intOK (commonDen p) p && decide (0 < unit) &&
    check thr unit w fuel (initial p unit) rootBox

/-! ## Affine maps applied inside the checker -/

/-- Integer affine shift of one power fiber:
`out_i = ω^i * Σ_{m ≤ n-i} C(i+m,i) α^m e^(n-i-m) g_(i+m)`, so that
`Σ out_i x^i = e^n Σ g_l ((α + ω x)/e)^l`. -/
def shiftFiber (n e : Nat) (α ω : Int) (g : Array Int) : Array Int :=
  Array.ofFn (n := n+1) fun i =>
    ω^i.val * (List.range (n+1-i.val)).foldl (fun s m =>
      s + (binom (i.val+m) i.val : Int) * α^m * (e : Int)^(n-(i.val+m)) * g.getD (i.val+m) 0) 0

def shiftLast (T : Tens) (e : Nat) (α ω : Int) : Tens :=
  let m := T.n2+1
  let nf := (T.n0+1)*(T.n1+1)
  let fs : Array (Array Int) := Array.ofFn (n := nf) fun f => shiftFiber T.n2 e α ω (T.fiber f.val)
  ⟨T.n0,T.n1,T.n2, Array.ofFn (n := nf*m) fun q => (fs.getD (q.val/m) #[]).getD (q.val%m) 0⟩

/-- Affine data `(e, α, ω)` of `x ↦ a + (b-a) x = (α + ω x)/e`. -/
def affOf (ab : Rat × Rat) : Nat × Int × Int :=
  (ab.1.den * ab.2.den, ab.1.num * ab.2.den, ab.2.num * ab.1.den - ab.1.num * ab.2.den)

/-- Shift all three axes; the result has the same axis order. -/
def shiftAll (T : Tens) (A0 A1 A2 : Nat × Int × Int) : Tens :=
  rot (shiftLast (rot (shiftLast (rot (shiftLast T A2.1 A2.2.1 A2.2.2)) A0.1 A0.2.1 A0.2.2))
    A1.1 A1.2.1 A1.2.2)

def initialAff (p : List ((Nat × Nat × Nat) × Rat)) (A0 A1 A2 : Nat × Int × Int) (unit : Rat) : Tens :=
  let d := degrees p
  let D := commonDen p
  scaleUp (convAll (shiftAll (denseOf d.1 d.2.1 d.2.2 D p) A0 A1 A2))
    (D * A0.1^d.1 * A1.1^d.2.1 * A2.1^d.2.2) unit

/-- Case check from a sparse polynomial in the original radii and the three affine maps. -/
def checkPolyAff (thr : Box → Rat) (unit : Rat) (w : Rat × Rat × Rat) (fuel : Nat)
    (p : List ((Nat × Nat × Nat) × Rat)) (A0 A1 A2 : Nat × Int × Int) : Bool :=
  let d := degrees p
  degreesOK d.1 d.2.1 d.2.2 p && intOK (commonDen p) p && decide (0 < unit) &&
    decide (0 < A0.1 ∧ 0 < A1.1 ∧ 0 < A2.1) &&
    check thr unit w fuel (initialAff p A0 A1 A2 unit) rootBox

end D4Bound.CyclicNative
