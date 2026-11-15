import D4Bound.V7Data
import D4Bound.ScalarData
import Mathlib.Data.Nat.Choose.Basic

/-! Computable rational coefficient arithmetic for the concrete pair upper. -/
namespace D4Bound.V7.PairPoly
abbrev Poly := List ℚ

def add : Poly → Poly → Poly
  | [],q => q
  | p,[] => p
  | a::p,b::q => (a+b)::add p q

def scale (a : ℚ) (p : Poly) : Poly := p.map (a*·)
def mul : Poly → Poly → Poly
  | [],_ => []
  | a::p,q => add (scale a q) (0::mul p q)
def pow (p : Poly) : ℕ → Poly
  | 0 => [1]
  | n+1 => mul (pow p n) p

def sum : List Poly → Poly
  | [] => []
  | p::ps => add p (sum ps)

def basis (p i : ℕ) : Poly :=
  let ab := basisIntervals.getD p (0,1)
  let z := [-ab.1/(ab.2-ab.1),1/(ab.2-ab.1)]
  scale (Nat.choose 6 i) (mul (pow z i) (pow (add [1] (scale (-1) z)) (6-i)))

def radial (v : List ℚ) (p : ℕ) : Poly :=
  sum ((List.range 7).map fun i => scale (v.getD (7*p+i) 0) (basis p i))

def flag (R : ℚ) (p : ℕ) : ℚ := if breaks.getD (p+1) 0 ≤ R then 1 else 0

def gram (p : ℕ) : Poly :=
  sum (gramRays.map fun block => sum (block.map fun ray =>
    scale (ray.weight/gramDenominator) (mul (radial ray.vector p) (radial ray.vector p))))

def countLin (c : CountPolynomial) (p : ℕ) : ℚ := c.weight *
  ((List.range c.radii.length).map fun i => c.linear.getD i 0 * flag (c.radii.getD i 0) p).sum

def countDiag (c : CountPolynomial) (p : ℕ) : ℚ := c.weight *
  ((List.range c.radii.length).map fun i => ((List.range c.radii.length).map fun j =>
    (c.matrix.getD i []).getD j 0 * flag (c.radii.getD i 0) p * flag (c.radii.getD j 0) p).sum).sum

def uncut (p : ℕ) : Poly :=
  add (radial originVector p)
  (add (sum (caps.map fun c => scale (c.weight*c.multiplicity/2) (radial c.vector p)))
  (add (sum (tents.map fun c => scale (c.weight*c.capacity/2) (radial c.vector p)))
  (add (sum (allocations.map fun c => scale (c.weight/2) (radial c.vector p)))
  [(sphericalRays.map fun c => c.weight*c.bound*flag c.radius p/2).sum +
    (conditionalRays.map fun c => 23*c.weight*(flag c.outer p-flag c.inner p)/2).sum +
    (countPolynomials.map fun c => countLin c p).sum])))

def diagonal (p : ℕ) : Poly :=
  add (scale 2 (uncut p)) (add (gram p)
    [ (sphericalRays.map fun c => -c.weight*flag c.radius p*flag c.radius p*c.coefficients.sum).sum +
      (conditionalRays.map fun c => -c.weight*(flag c.inner p*(flag c.outer p-flag c.inner p)+
        (flag c.outer p-flag c.inner p)*flag c.inner p)/2).sum +
      (countPolynomials.map fun c => countDiag c p).sum ])


def comp : Poly → Poly → Poly
  | [],_ => []
  | a::p,q => add [a] (mul q (comp p q))

def taylor (n : ℕ) : Poly :=
  sum ((List.range n).map fun i => scale (1/i.factorial) (pow [0,0,2] i))

end D4Bound.V7.PairPoly
