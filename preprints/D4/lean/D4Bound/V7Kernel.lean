import D4Bound.Main
import D4Bound.V7Data

/-!
# The concrete V7 kernel

The definitions below retain each component of the published kernel. They use
the exact arrays in `V7Data.lean`, generated from `data/v7`. Closed upper radial
endpoints select the lower piece; the radius-one endpoint selects piece zero.
The extension to nonzero radii below one is zero (those arguments never occur
in an admissible packing neighbourhood).

This file defines the mathematical kernel. Its continuum cyclic signs, census
floor and box estimates are separate statements, not fields of this definition.
-/

open scoped RealInnerProductSpace

namespace D4Bound.V7

noncomputable section
open Classical

def radialPiece (r : ℝ) : ℕ :=
  breaks.tail.findIdx (fun b => decide (r ≤ (b : ℝ)))

def basisValue (p i : ℕ) (r : ℝ) : ℝ :=
  let ab := basisIntervals.getD p (0, 1)
  let z := (r - (ab.1 : ℝ)) / ((ab.2 : ℝ) - (ab.1 : ℝ))
  (Nat.choose 6 i : ℝ) * z ^ i * (1-z) ^ (6-i)

def radialValue (v : List ℚ) (r : ℝ) : ℝ :=
  ((List.range 7).map fun i =>
    ((v.getD (7 * radialPiece r + i) 0 : ℚ) : ℝ) * basisValue (radialPiece r) i r).sum

def chebU : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, t => 2*t
  | n+2, t => 2*t*chebU (n+1) t - chebU n t

def zonal (n : ℕ) (t : ℝ) : ℝ := chebU n t / (n+1)

def indicator (R : ℚ) (r : ℝ) : ℝ := if r ≤ (R : ℝ) then 1 else 0

def gramPair (r s t : ℝ) : ℝ :=
  ((List.range gramRays.length).map fun ell =>
    zonal ell t * (((gramRays.getD ell []).map fun ray =>
      (ray.weight : ℝ) * radialValue ray.vector r * radialValue ray.vector s).sum) /
        (gramDenominator : ℝ)).sum

def capWeight (c : Cap) (r : ℝ) : ℝ :=
  match c.cutoff with
  | none => radialValue c.vector r
  | some C => if (C : ℝ) < r then radialValue c.vector r else 0

/-- The closed-ball convention is retained at a degenerate probe angle. -/
def capProbability (c : Cap) (r t : ℝ) : ℝ :=
  let A := (r*r + (c.d : ℝ)^2 - (c.a2 : ℝ)) / (2*(c.d : ℝ)*r) - (c.sigma : ℝ)*t
  let S := (1-(c.sigma : ℝ)^2)*(1-t*t)
  if S = 0 then (if A ≤ 0 then 1 else 0)
  else max 0 (min 1 ((1-A / Real.sqrt S)/2))

def capsCorrection (r s t : ℝ) : ℝ :=
  (caps.map fun c => (c.weight : ℝ) *
    (capWeight c s * capProbability c r t + capWeight c r * capProbability c s t)/2).sum

def tentProfile (d r t : ℝ) : ℝ := max 0 (1-2*(r*r+d*d+2*d*r*t))

def tentsCorrection (r s t : ℝ) : ℝ :=
  (tents.map fun c => (c.weight : ℝ) *
    (radialValue c.vector s * tentProfile c.d r t +
      radialValue c.vector r * tentProfile c.d s t)/2).sum

def allocationProfile (c : AllocationData) (q : ℝ) : ℝ :=
  if c.twoLevel then
    if q < (c.inner : ℝ)^2 then 1 else if q ≤ (c.outer : ℝ)^2 then 1/2 else 0
  else if 1/2 ≤ q then 0 else if 1/4 ≤ q then 1-2*q
  else min 1 (2*(1-Real.sqrt q)^2)

def allocationsCorrection (r s t : ℝ) : ℝ :=
  (allocations.map fun c => (c.weight : ℝ) *
    (radialValue c.vector r + radialValue c.vector s) *
      allocationProfile c (r*r+s*s+2*r*s*t)/2).sum

def conditionalPair (r s : ℝ) : ℝ :=
  (conditionalRays.map fun c => -(c.weight : ℝ) *
    (indicator c.inner r * (indicator c.outer s - indicator c.inner s) +
      (indicator c.outer r - indicator c.inner r) * indicator c.inner s)/2).sum

def countPair (c : CountPolynomial) (r s : ℝ) : ℝ :=
  (c.weight : ℝ) * ((List.range c.radii.length).map fun i =>
    ((List.range c.radii.length).map fun j =>
      (((c.matrix.getD i []).getD j 0 : ℚ) : ℝ) *
        indicator (c.radii.getD i 0) r * indicator (c.radii.getD j 0) s).sum).sum

def sphericalPair (r s t : ℝ) : ℝ :=
  (sphericalRays.map fun c => -(c.weight : ℝ) * indicator c.radius r * indicator c.radius s *
    (((List.range c.coefficients.length).map fun j =>
      ((c.coefficients.getD j 0 : ℚ) : ℝ) * zonal j t).sum)).sum

def graphRadial (g : Graph) (r s : ℝ) : Prop :=
  let first := fun x : ℝ => (g.lo1 : ℝ) ≤ x ∧ x ≤ (g.hi1 : ℝ)
  let second := fun x : ℝ =>
    (if g.firstOpen then (g.lo2 : ℝ) < x else (g.lo2 : ℝ) ≤ x) ∧ x ≤ (g.hi2 : ℝ)
  if g.mixed then (first r ∧ second s) ∨ (first s ∧ second r) else first r ∧ second s

def graphsCorrection (r s t : ℝ) : ℝ :=
  (graphs.map fun g => if graphRadial g r s ∧ (g.tlo : ℝ) ≤ t ∧ t ≤ (g.thi : ℝ)
    then (g.weight : ℝ) else 0).sum

/-- Every non-gauge component of the nonorigin pair kernel. -/
def rawPair (r s t : ℝ) : ℝ :=
  gramPair r s t + sphericalPair r s t + conditionalPair r s +
    (countPolynomials.map fun c => countPair c r s).sum -
    capsCorrection r s t - tentsCorrection r s t -
    allocationsCorrection r s t - graphsCorrection r s t

def countLinear (c : CountPolynomial) (r : ℝ) : ℝ :=
  (c.weight : ℝ) * ((List.range c.radii.length).map fun i =>
    ((c.linear.getD i 0 : ℚ) : ℝ) * indicator (c.radii.getD i 0) r).sum

/-- Origin row before the pair gauge. Graphs have no origin row. -/
def rawLinear (r : ℝ) : ℝ :=
  radialValue originVector r +
  (caps.map fun c => (c.weight : ℝ)*(c.multiplicity : ℝ)*capWeight c r/2).sum +
  (tents.map fun c => (c.weight : ℝ)*(c.capacity : ℝ)*radialValue c.vector r/2).sum +
  (allocations.map fun c => (c.weight : ℝ)*radialValue c.vector r/2).sum +
  (sphericalRays.map fun c => (c.weight : ℝ)*(c.bound : ℝ)*indicator c.radius r/2).sum +
  (conditionalRays.map fun c => 23*(c.weight : ℝ)*
    (indicator c.outer r-indicator c.inner r)/2).sum +
  (countPolynomials.map fun c => countLinear c r).sum

/-- Only Gram, count and graph components contribute at the origin. -/
def rawOriginQ : ℚ := gramOrigin +
  (countPolynomials.map fun c => c.weight*c.constant).sum +
  (graphs.map fun g => g.weight*g.capacity).sum

def scalarRadius (r : ℝ) : ℝ := Real.exp (-2*r^2)*F (2*r^2)

def ungaugedPair (r : ℝ) : ℝ := scalarRadius r + 2*rawLinear r + rawPair r r 1

def gaugePsi (r : ℝ) : ℝ := indicator gaugeRadius r / (gaugeCount : ℝ)

def gaugeWeight (r : ℝ) : ℝ := -ungaugedPair r / (1-gaugePsi r)

def linear (r : ℝ) : ℝ := rawLinear r + gaugeWeight r/2

def pair (r s t : ℝ) : ℝ := rawPair r s t -
  (gaugeWeight r*gaugePsi s + gaugeWeight s*gaugePsi r)/2

/-- Concrete V7 kernel on R4; all component data are fixed in `V7Data`. -/
def kernel (x y : E4) : ℝ :=
  if 7/4 < ‖x‖ ∨ 7/4 < ‖y‖ then 0
  else if x = 0 then
    if y = 0 then (rawOriginQ : ℝ) else if 1 ≤ ‖y‖ then linear ‖y‖ else 0
  else if y = 0 then
    if 1 ≤ ‖x‖ then linear ‖x‖ else 0
  else if 1 ≤ ‖x‖ ∧ 1 ≤ ‖y‖ then pair ‖x‖ ‖y‖ (⟪x,y⟫/(‖x‖*‖y‖)) else 0

theorem kernel_supported : SupportedIn kernel := by
  intro x y h
  simp only [kernel, if_pos h]

theorem kernel_origin : kernel 0 0 = (rawOriginQ : ℝ) := by
  norm_num [kernel]

theorem gauge_denominator_ne (r : ℝ) : 1-gaugePsi r ≠ 0 := by
  unfold gaugePsi indicator gaugeCount
  split_ifs <;> norm_num

theorem pair_cancellation (r : ℝ) : scalarRadius r + 2*linear r + pair r r 1 = 0 := by
  have h : gaugeWeight r * (1-gaugePsi r) = -ungaugedPair r := by
    unfold gaugeWeight
    exact div_mul_cancel₀ _ (gauge_denominator_ne r)
  unfold ungaugedPair at h
  unfold linear pair
  linarith

theorem kernel_zero_right {x : E4} (h1 : 1 ≤ ‖x‖) (hR : ‖x‖ ≤ 7/4) :
    kernel x 0 = linear ‖x‖ := by
  have hx : x ≠ 0 := by intro h; subst x; norm_num at h1
  have h0 : ¬ (7/4 : ℝ) < ‖(0 : E4)‖ := by norm_num
  simp only [kernel, if_neg (not_or.mpr ⟨not_lt.mpr hR, h0⟩), if_neg hx,
    if_pos h1, ite_true]

theorem kernel_diag {x : E4} (h1 : 1 ≤ ‖x‖) (hR : ‖x‖ ≤ 7/4) :
    kernel x x = pair ‖x‖ ‖x‖ 1 := by
  have hx : x ≠ 0 := by intro h; subst x; norm_num at h1
  have hn : ‖x‖ ≠ 0 := by linarith
  have hc : ⟪x,x⟫/(‖x‖*‖x‖) = 1 := by
    rw [real_inner_self_eq_norm_sq, pow_two]
    exact div_self (mul_ne_zero hn hn)
  simp only [kernel, if_neg (not_or.mpr ⟨not_lt.mpr hR, not_lt.mpr hR⟩),
    if_neg hx, if_pos (And.intro h1 h1), hc]

theorem kernel_pair : PairSign kernel := by
  intro x hx
  by_cases hR : ‖x‖ ≤ 7/4
  · rw [kernel_zero_right hx hR, kernel_diag hx hR]
    exact (pair_cancellation ‖x‖).le
  · have h : 7/4 < ‖x‖ := lt_of_not_ge hR
    rw [kernel_supported x 0 (Or.inl h), kernel_supported x x (Or.inl h)]
    simpa using f_nonpos h.le

/-- Exact objective comparison, checked in the Lean kernel on rational data. -/
theorem raw_objective_rational : Fq.headD 0 + rawOriginQ ≤ 8*urawUp := by
  decide +kernel

theorem scalar_origin : f (0 : E4) = ((Fq.headD 0 : ℚ) : ℝ) := by
  simp [f, F, Fq, evalQ]

theorem kernel_raw : RawObjective kernel := by
  unfold RawObjective
  rw [kernel_origin, scalar_origin]
  exact_mod_cast raw_objective_rational

end
end D4Bound.V7
