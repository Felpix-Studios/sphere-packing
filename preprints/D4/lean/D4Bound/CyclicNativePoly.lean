/-!
# Native clone of the cyclic polynomial construction

Init-only copy of `V7.CyclicPoly` (modules `V7CyclicPolynomialBasic`, `Fast`,
`Homogeneous`, `Substitution`, `Def`), with the kernel data passed as an argument
instead of read from `V7Data`. `CyclicNativePolyEq` proves that, on the actual
data, every function equals its original. No proofs here.
-/
namespace D4Bound.CyclicNative.NPoly

abbrev Exponent := Nat × Nat × Nat
abbrev Term := Exponent × Rat
abbrev Poly := List Term

def before (a b : Exponent) : Bool :=
  decide (a.1 < b.1 ∨ a.1 = b.1 ∧
    (a.2.1 < b.2.1 ∨ a.2.1 = b.2.1 ∧ a.2.2 < b.2.2))

def insert (t : Term) : Poly → Poly
  | [] => if t.2 = 0 then [] else [t]
  | u :: p =>
    if t.1 = u.1 then
      if t.2 + u.2 = 0 then p else (t.1,t.2+u.2) :: p
    else if before t.1 u.1 then
      if t.2 = 0 then u :: p else t :: u :: p
    else u :: insert t p

def scale (a : Rat) (p : Poly) : Poly :=
  p.foldr (fun t q => insert (t.1,a*t.2) q) []
def termMul (a b : Term) : Term :=
  ((a.1.1+b.1.1,a.1.2.1+b.1.2.1,a.1.2.2+b.1.2.2),a.2*b.2)
def mulTerm (a : Term) (p : Poly) : Poly := p.map (termMul a)
def constant (a : Rat) : Poly := if a = 0 then [] else [((0,0,0),a)]
def coordinate (i : Fin 3) : Poly :=
  [((if i=0 then 1 else 0,if i=1 then 1 else 0,if i=2 then 1 else 0),1)]

def merge : Nat → Poly → Poly → Poly
  | 0,p,q => p++q
  | _+1,[],q => q
  | _+1,p,[] => p
  | n+1,a::p,b::q =>
    if a.1 = b.1 then
      if a.2+b.2 = 0 then merge n p q else (a.1,a.2+b.2)::merge n p q
    else if before a.1 b.1 then a::merge n p (b::q)
    else b::merge n (a::p) q

def fastAdd (p q : Poly) : Poly := merge (p.length+q.length) p q
def fastMul (p q : Poly) : Poly := p.foldr (fun a z => fastAdd (mulTerm a q) z) []
def fastPower (p : Poly) : Nat → Poly
  | 0 => constant 1
  | n+1 => fastMul (fastPower p n) p
def fastSum (ps : List Poly) : Poly := ps.foldr fastAdd []

def homogeneousU (A B : Poly) : Nat → Poly
  | 0 => constant 1
  | 1 => scale 2 A
  | n+2 => fastAdd (scale 2 (fastMul A (homogeneousU A B (n+1))))
      (scale (-1) (fastMul (fastPower B 2) (homogeneousU A B n)))

def clearedZonal (N n : Nat) (A B : Poly) : Poly :=
  scale (1/(n+1 : Rat)) (fastMul (fastPower B (N-n)) (homogeneousU A B n))

def sideNumerator (r s d : Poly) : Poly :=
  fastAdd (fastAdd (fastPower r 2) (fastPower s 2)) (scale (-1) (fastPower d 2))

def affine (a b : Rat) (i : Fin 3) : Poly :=
  fastAdd (constant a) (scale (b-a) (coordinate i))

/-- Pascal row, used for `Nat.choose 6 i`. -/
def pascal : Nat → Array Nat
  | 0 => #[1]
  | n+1 => let r := pascal n
    Array.ofFn (n := n+2) fun k => (if k.val = 0 then 0 else r.getD (k.val-1) 0) + r.getD k.val 0

def choose (n k : Nat) : Nat := (pascal n).getD k 0

/-- Kernel data needed by the polynomial part. -/
structure KData where
  breaks : List Rat
  basisIntervals : List (Rat × Rat)
  gramRays : List (List (Rat × List Rat))
  gramDenominator : Rat
  conditionalRays : List (Rat × Rat × Rat)
  countPolynomials : List (List Rat × Rat × List (List Rat))
  sphericalRays : List (Rat × Rat × List Rat)

section
variable (K : KData)

def flag (R : Rat) (p : Nat) : Rat := if K.breaks.getD (p+1) 0 ≤ R then 1 else 0

def basis (p i : Nat) (a : Poly) : Poly :=
  let ab := K.basisIntervals.getD p (0,1)
  let z := scale (1/(ab.2-ab.1)) (fastAdd a (constant (-ab.1)))
  scale (choose 6 i)
    (fastMul (fastPower z i) (fastPower (fastAdd (constant 1) (scale (-1) z)) (6-i)))

def radial (v : List Rat) (p : Nat) (a : Poly) : Poly :=
  fastSum ((List.range 7).map fun i => scale (v.getD (7*p+i) 0) (basis K p i a))

def gramRadial (ell p q : Nat) (a b : Poly) : Poly :=
  fastSum ((K.gramRays.getD ell []).map fun ray =>
    scale ray.1 (fastMul (radial K ray.2 p a) (radial K ray.2 q b)))

def gramBlock (ell p q : Nat) (a b A B : Poly) : Poly :=
  scale (1/K.gramDenominator)
    (fastMul (clearedZonal 18 ell A B) (gramRadial K ell p q a b))

def gram (p q : Nat) (a b A B : Poly) : Poly :=
  fastSum ((List.range K.gramRays.length).map fun ell => gramBlock K ell p q a b A B)

def conditional (p q : Nat) : Rat :=
  (K.conditionalRays.map fun c => -c.2.2 *
    (flag K c.1 p * (flag K c.2.1 q-flag K c.1 q) +
      (flag K c.2.1 p-flag K c.1 p)*flag K c.1 q)/2).sum

def count (c : List Rat × Rat × List (List Rat)) (p q : Nat) : Rat :=
  c.2.1*((List.range c.1.length).map fun i =>
    ((List.range c.1.length).map fun j =>
      (c.2.2.getD i []).getD j 0 * flag K (c.1.getD i 0) p *
        flag K (c.1.getD j 0) q).sum).sum

def sphericalBlock (c : Rat × Rat × List Rat) (p q : Nat) (A B : Poly) : Poly :=
  fastSum ((List.range c.2.2.length).map fun ell =>
    scale (-c.2.1*flag K c.1 p*flag K c.1 q*
      c.2.2.getD ell 0) (clearedZonal 18 ell A B))

def spherical (p q : Nat) (A B : Poly) : Poly :=
  fastSum (K.sphericalRays.map fun c => sphericalBlock K c p q A B)

def pair (p q : Nat) (a b A B : Poly) : Poly :=
  fastAdd (fastAdd (gram K p q a b A B) (spherical K p q A B))
    (scale (conditional K p q+(K.countPolynomials.map fun c => count K c p q).sum)
      (fastPower B 18))

def fullFactor (a b c : Poly) : Poly := scale 2 (fastMul (fastMul a b) c)
def fullNumerator (a b c : Poly) : Poly := fastMul (sideNumerator a b c) c

def cyclic (p q k : Nat) (a b c : Poly) : Poly :=
  let B := fullFactor a b c
  fastAdd
    (fastAdd (pair K p q a b (fullNumerator a b c) B)
      (pair K p k a c (fullNumerator a c b) B))
    (pair K q k b c (fullNumerator b c a) B)

end

end D4Bound.CyclicNative.NPoly
