import D4Bound.V7CyclicPolynomialHomogeneous
import D4Bound.V7PairPolynomialDef

/-! Polynomial expressions for the actual Gram, spherical, conditional and
count terms. The common homogeneous denominator has degree eighteen. -/
namespace D4Bound.V7.CyclicPoly

def basis (p i : ℕ) (a : Poly) : Poly :=
  let ab := basisIntervals.getD p (0,1)
  let z := scale (1/(ab.2-ab.1)) (fastAdd a (constant (-ab.1)))
  scale (Nat.choose 6 i)
    (fastMul (fastPower z i) (fastPower (fastAdd (constant 1) (scale (-1) z)) (6-i)))

def radial (v : List ℚ) (p : ℕ) (a : Poly) : Poly :=
  fastSum ((List.range 7).map fun i => scale (v.getD (7*p+i) 0) (basis p i a))

def gramRadial (ell p q : ℕ) (a b : Poly) : Poly :=
  fastSum ((gramRays.getD ell []).map fun ray =>
    scale ray.weight (fastMul (radial ray.vector p a) (radial ray.vector q b)))

def gramBlock (ell p q : ℕ) (a b A B : Poly) : Poly :=
  scale (1/gramDenominator)
    (fastMul (clearedZonal 18 ell A B) (gramRadial ell p q a b))

def gram (p q : ℕ) (a b A B : Poly) : Poly :=
  fastSum ((List.range gramRays.length).map fun ell => gramBlock ell p q a b A B)

def conditional (p q : ℕ) : ℚ :=
  (conditionalRays.map fun c => -c.weight *
    (PairPoly.flag c.inner p * (PairPoly.flag c.outer q-PairPoly.flag c.inner q) +
      (PairPoly.flag c.outer p-PairPoly.flag c.inner p)*PairPoly.flag c.inner q)/2).sum

def count (c : CountPolynomial) (p q : ℕ) : ℚ :=
  c.weight*((List.range c.radii.length).map fun i =>
    ((List.range c.radii.length).map fun j =>
      (c.matrix.getD i []).getD j 0 * PairPoly.flag (c.radii.getD i 0) p *
        PairPoly.flag (c.radii.getD j 0) q).sum).sum

def sphericalBlock (c : SphericalRay) (p q : ℕ) (A B : Poly) : Poly :=
  fastSum ((List.range c.coefficients.length).map fun ell =>
    scale (-c.weight*PairPoly.flag c.radius p*PairPoly.flag c.radius q*
      c.coefficients.getD ell 0) (clearedZonal 18 ell A B))

def spherical (p q : ℕ) (A B : Poly) : Poly :=
  fastSum (sphericalRays.map fun c => sphericalBlock c p q A B)

def pair (p q : ℕ) (a b A B : Poly) : Poly :=
  fastAdd (fastAdd (gram p q a b A B) (spherical p q A B))
    (scale (conditional p q+(countPolynomials.map fun c => count c p q).sum)
      (fastPower B 18))

def fullFactor (a b c : Poly) : Poly := scale 2 (fastMul (fastMul a b) c)
def fullNumerator (a b c : Poly) : Poly := fastMul (sideNumerator a b c) c

def cyclic (p q k : ℕ) (a b c : Poly) : Poly :=
  let B := fullFactor a b c
  fastAdd
    (fastAdd (pair p q a b (fullNumerator a b c) B)
      (pair p k a c (fullNumerator a c b) B))
    (pair q k b c (fullNumerator b c a) B)

end D4Bound.V7.CyclicPoly
