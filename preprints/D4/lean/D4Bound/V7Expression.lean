import D4Bound.V7Kernel
import D4Bound.CertificateIntervalKinks
import D4Bound.CertificateIntervalExp

/-! Exact expression syntax for the concrete V7 kernel. Conditionals retain
closed, strict and equality branches, including degenerate cap probabilities.
No data from an external equality checker enters these semantic theorems. -/
namespace D4Bound.V7Expression

inductive Expr where
  | rat (q : ℚ)
  | var (i : ℕ)
  | add (a b : Expr)
  | neg (a : Expr)
  | mul (a b : Expr)
  | inv (a : Expr)
  | sqrt (a : Expr)
  | exp (a : Expr)
  | max (a b : Expr)
  | min (a b : Expr)
  | ifLE (a b yes no : Expr)
  | ifLT (a b yes no : Expr)
  | ifEQ (a b yes no : Expr)
  deriving Repr, DecidableEq

namespace Expr
noncomputable def eval (xs : ℕ → ℝ) : Expr → ℝ
  | .rat q => q
  | .var i => xs i
  | .add a b => eval xs a + eval xs b
  | .neg a => -eval xs a
  | .mul a b => eval xs a * eval xs b
  | .inv a => (eval xs a)⁻¹
  | .sqrt a => Real.sqrt (eval xs a)
  | .exp a => Real.exp (eval xs a)
  | .max a b => Max.max (eval xs a) (eval xs b)
  | .min a b => Min.min (eval xs a) (eval xs b)
  | .ifLE a b yes no => if eval xs a ≤ eval xs b then eval xs yes else eval xs no
  | .ifLT a b yes no => if eval xs a < eval xs b then eval xs yes else eval xs no
  | .ifEQ a b yes no => if eval xs a = eval xs b then eval xs yes else eval xs no

instance : Add Expr := ⟨Expr.add⟩
instance : Neg Expr := ⟨Expr.neg⟩
instance : Sub Expr := ⟨fun a b => Expr.add a (Expr.neg b)⟩
instance : Mul Expr := ⟨Expr.mul⟩
instance : Div Expr := ⟨fun a b => Expr.mul a (Expr.inv b)⟩
instance (n : ℕ) : OfNat Expr n := ⟨Expr.rat n⟩

def pow (a : Expr) : ℕ → Expr
  | 0 => 1
  | n+1 => pow a n * a
instance : Pow Expr ℕ := ⟨Expr.pow⟩

def sum (es : List Expr) : Expr := es.foldr Expr.add 0

@[simp] theorem eval_rat (xs) (q) : eval xs (.rat q) = (q : ℝ) := rfl
@[simp] theorem eval_var (xs) (i) : eval xs (.var i) = xs i := rfl
@[simp] theorem eval_add (xs) (a b : Expr) : eval xs (a+b) = eval xs a+eval xs b := rfl
@[simp] theorem eval_neg (xs) (a : Expr) : eval xs (-a) = -eval xs a := rfl
@[simp] theorem eval_sub (xs) (a b : Expr) : eval xs (a-b) = eval xs a-eval xs b := by
  change eval xs a + -eval xs b = eval xs a-eval xs b
  exact (sub_eq_add_neg _ _).symm
@[simp] theorem eval_mul (xs) (a b : Expr) : eval xs (a*b) = eval xs a*eval xs b := rfl
@[simp] theorem eval_div (xs) (a b : Expr) : eval xs (a/b) = eval xs a/eval xs b := by
  change eval xs a * (eval xs b)⁻¹ = eval xs a/eval xs b
  exact (div_eq_mul_inv _ _).symm
@[simp] theorem eval_nat (xs) (n : ℕ) : eval xs (OfNat.ofNat n : Expr) = (n : ℝ) := by
  change ((n : ℚ) : ℝ) = (n : ℝ)
  exact Rat.cast_natCast n
@[simp] theorem eval_pow (xs) (a : Expr) (n : ℕ) : eval xs (a^n) = eval xs a ^ n := by
  induction n with
  | zero => change ((1 : ℚ) : ℝ) = _; simp only [Rat.cast_one, pow_zero]
  | succ n ih =>
    change eval xs (a^n) * eval xs a = eval xs a ^ (n+1)
    rw [ih, pow_succ]
@[simp] theorem eval_sum (xs) (es : List Expr) : eval xs (sum es) = (es.map (eval xs)).sum := by
  induction es with
  | nil => change ((0 : ℚ) : ℝ) = 0; exact Rat.cast_zero
  | cons e es ih =>
    change eval xs e + eval xs (sum es) = eval xs e + (es.map (eval xs)).sum
    rw [ih]

end Expr

open Expr

def basisE (p i : ℕ) (r : Expr) : Expr :=
  let ab := V7.basisIntervals.getD p (0,1)
  let z := (r-.rat ab.1)/(.rat ab.2-.rat ab.1)
  .rat (Nat.choose 6 i) * z^i * (1-z)^(6-i)

def radialE (v : List ℚ) (p : ℕ) (r : Expr) : Expr :=
  Expr.sum ((List.range 7).map fun i => .rat (v.getD (7*p+i) 0) * basisE p i r)

def chebE : ℕ → Expr → Expr
  | 0, _ => 1
  | 1, t => 2*t
  | n+2, t => 2*t*chebE (n+1) t-chebE n t

def zonalE (n : ℕ) (t : Expr) : Expr := chebE n t / .rat (n+1)
def indicatorE (R : ℚ) (r : Expr) : Expr := .ifLE r (.rat R) 1 0

def gramE (p q : ℕ) (r s t : Expr) : Expr :=
  Expr.sum ((List.range V7.gramRays.length).map fun ell =>
    zonalE ell t * Expr.sum ((V7.gramRays.getD ell []).map fun ray =>
      .rat ray.weight * radialE ray.vector p r * radialE ray.vector q s) /
        .rat V7.gramDenominator)

def capWeightE (c : V7.Cap) (p : ℕ) (r : Expr) : Expr :=
  match c.cutoff with
  | none => radialE c.vector p r
  | some C => .ifLT (.rat C) r (radialE c.vector p r) 0

def capProbabilityE (c : V7.Cap) (r t : Expr) : Expr :=
  let A := (r*r + (.rat c.d)^2 - .rat c.a2)/(2*(.rat c.d)*r)-(.rat c.sigma)*t
  let S := (1-(.rat c.sigma)^2)*(1-t*t)
  .ifEQ S 0 (.ifLE A 0 1 0) (.max 0 (.min 1 ((1-A/(.sqrt S))/2)))

def capsE (p q : ℕ) (r s t : Expr) : Expr :=
  Expr.sum (V7.caps.map fun c => .rat c.weight *
    (capWeightE c q s * capProbabilityE c r t + capWeightE c p r * capProbabilityE c s t)/2)

def tentProfileE (d : ℚ) (r t : Expr) : Expr := .max 0 (1-2*(r*r+(.rat d)*(.rat d)+2*(.rat d)*r*t))
def tentsE (p q : ℕ) (r s t : Expr) : Expr :=
  Expr.sum (V7.tents.map fun c => .rat c.weight *
    (radialE c.vector q s * tentProfileE c.d r t + radialE c.vector p r * tentProfileE c.d s t)/2)

def allocationProfileE (c : V7.AllocationData) (v : Expr) : Expr :=
  if c.twoLevel then .ifLT v ((.rat c.inner)^2) 1 (.ifLE v ((.rat c.outer)^2) (1/2) 0)
  else .ifLE (1/2) v 0 (.ifLE (1/4) v (1-2*v) (.min 1 (2*(1-.sqrt v)^2)))
def allocationsE (p q : ℕ) (r s t : Expr) : Expr :=
  Expr.sum (V7.allocations.map fun c => .rat c.weight *
    (radialE c.vector p r + radialE c.vector q s) * allocationProfileE c (r*r+s*s+2*r*s*t)/2)

def conditionalE (r s : Expr) : Expr :=
  Expr.sum (V7.conditionalRays.map fun c => -(.rat c.weight) *
    (indicatorE c.inner r*(indicatorE c.outer s-indicatorE c.inner s) +
      (indicatorE c.outer r-indicatorE c.inner r)*indicatorE c.inner s)/2)

def countPairE (c : V7.CountPolynomial) (r s : Expr) : Expr :=
  .rat c.weight * Expr.sum ((List.range c.radii.length).map fun i =>
    Expr.sum ((List.range c.radii.length).map fun j =>
      .rat ((c.matrix.getD i []).getD j 0) *
        indicatorE (c.radii.getD i 0) r * indicatorE (c.radii.getD j 0) s))

def sphericalE (r s t : Expr) : Expr :=
  Expr.sum (V7.sphericalRays.map fun c => -(.rat c.weight)*indicatorE c.radius r*indicatorE c.radius s *
    Expr.sum ((List.range c.coefficients.length).map fun j =>
      .rat (c.coefficients.getD j 0)*zonalE j t))

/-- Select a branch by an indicator expression which is exactly zero or one. -/
def branch (condition yes no : Expr) : Expr := .ifEQ condition 1 yes no

def firstE (g : V7.Graph) (r : Expr) : Expr := .ifLE (.rat g.lo1) r (.ifLE r (.rat g.hi1) 1 0) 0
def secondE (g : V7.Graph) (r : Expr) : Expr :=
  if g.firstOpen then .ifLT (.rat g.lo2) r (.ifLE r (.rat g.hi2) 1 0) 0
  else .ifLE (.rat g.lo2) r (.ifLE r (.rat g.hi2) 1 0) 0

def graphRadialE (g : V7.Graph) (r s : Expr) : Expr :=
  if g.mixed then branch (firstE g r) (branch (secondE g s) 1 (firstE g s*secondE g r))
    (firstE g s*secondE g r)
  else firstE g r*secondE g s

def graphsE (r s t : Expr) : Expr :=
  Expr.sum (V7.graphs.map fun g => branch (graphRadialE g r s)
    (.ifLE (.rat g.tlo) t (.ifLE t (.rat g.thi) (.rat g.weight) 0) 0) 0)

def rawPairE (p q : ℕ) (r s t : Expr) : Expr :=
  gramE p q r s t+sphericalE r s t+conditionalE r s+
    Expr.sum (V7.countPolynomials.map fun c => countPairE c r s)-capsE p q r s t-
    tentsE p q r s t-allocationsE p q r s t-graphsE r s t

def countLinearE (c : V7.CountPolynomial) (r : Expr) : Expr :=
  .rat c.weight * Expr.sum ((List.range c.radii.length).map fun i =>
    .rat (c.linear.getD i 0)*indicatorE (c.radii.getD i 0) r)

def rawLinearE (p : ℕ) (r : Expr) : Expr :=
  radialE V7.originVector p r+
  Expr.sum (V7.caps.map fun c => .rat c.weight*.rat c.multiplicity*capWeightE c p r/2)+
  Expr.sum (V7.tents.map fun c => .rat c.weight*.rat c.capacity*radialE c.vector p r/2)+
  Expr.sum (V7.allocations.map fun c => .rat c.weight*radialE c.vector p r/2)+
  Expr.sum (V7.sphericalRays.map fun c => .rat c.weight*.rat c.bound*indicatorE c.radius r/2)+
  Expr.sum (V7.conditionalRays.map fun c => 23*.rat c.weight*(indicatorE c.outer r-indicatorE c.inner r)/2)+
  Expr.sum (V7.countPolynomials.map fun c => countLinearE c r)

def polyE (cs : List ℚ) (x : Expr) : Expr := cs.foldr (fun c tail => .rat c+x*tail) 0

def scalarE (r : Expr) : Expr := .exp (-2*r^2) * polyE Fq (2*r^2)
def ungaugedE (p : ℕ) (r : Expr) : Expr := scalarE r+2*rawLinearE p r+rawPairE p p r r 1
def gaugePsiE (r : Expr) : Expr := indicatorE V7.gaugeRadius r / .rat V7.gaugeCount
def gaugeWeightE (p : ℕ) (r : Expr) : Expr := -ungaugedE p r/(1-gaugePsiE r)
def pairE (p q : ℕ) (r s t : Expr) : Expr := rawPairE p q r s t-
  (gaugeWeightE p r*gaugePsiE s+gaugeWeightE q s*gaugePsiE r)/2

end D4Bound.V7Expression
