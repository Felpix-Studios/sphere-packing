import D4Bound.CyclicNativeSound
import D4Bound.CyclicNativePolyEq
import D4Bound.V7CyclicUpper
import D4Bound.V7PairMargin0
import D4Bound.V7CyclicPolynomialFull

/-!
# Linking native cyclic checks to the actual V7 kernel

`full000_of_check`: a successful native check of the full000 polynomial on the
first-shell cube proves `sideCyclic r s d ≤ 0` there. The check itself is a
separate `native_decide` module.
-/
namespace D4Bound.V7
open CyclicNative

noncomputable section

def shellR1 : ℚ := 501473/500000

/-- The full000 cyclic polynomial on the unit cube, built by the native clone. -/
def full000Poly : List ((ℕ × ℕ × ℕ) × ℚ) :=
  NPoly.cyclic NPoly.kdata 0 0 0 (NPoly.affine 1 shellR1 0) (NPoly.affine 1 shellR1 1)
    (NPoly.affine 1 shellR1 2)

/-- Threshold `2^18 * 9/10^6` for the whole first-shell cube. -/
def full000Thr : ℚ := 262144 * (9/1000000)

theorem full000_poly_eval {x y z : ℝ} :
    CyclicPoly.eval full000Poly x y z =
      CyclicPoly.eval (CyclicPoly.cyclic 0 0 0 (CyclicPoly.affine 1 shellR1 0)
        (CyclicPoly.affine 1 shellR1 1) (CyclicPoly.affine 1 shellR1 2)) x y z := by
  rw [full000Poly, NPoly.cyclic_eq, NPoly.affine_eq]

theorem full000_of_check (unit : ℚ) (w : ℚ × ℚ × ℚ) (fuel : ℕ)
    (h : checkPoly (fun _ => full000Thr) unit w fuel full000Poly = true)
    {r s d : ℝ} (hr1 : 1 ≤ r) (hr : r ≤ 501473/500000) (hs1 : 1 ≤ s) (hs : s ≤ 501473/500000)
    (hd1 : 1 ≤ d) (hd : d ≤ 501473/500000) : sideCyclic r s d ≤ 0 := by
  have hc := checkPoly_sound (fun _ => full000Thr) unit w fuel full000Poly (fun _ _ _ => (full000Thr : ℝ)) h
    (by intro B _ x y z _; exact le_refl _) (by intro x y z _; norm_num [full000Thr])
  have hw : ((shellR1 : ℚ) : ℝ) - 1 = 1473/500000 := by norm_num [shellR1]
  set x := (r-1)/(1473/500000) with hx
  set y := (s-1)/(1473/500000) with hy
  set z := (d-1)/(1473/500000) with hz
  have hcube : Cube x y z := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (apply div_nonneg <;> linarith)
    | (rw [div_le_one (by norm_num)]; linarith)
  have hb := hc x y z hcube
  rw [full000_poly_eval] at hb
  have ea : CyclicPoly.eval (CyclicPoly.affine 1 shellR1 0) x y z = r := by
    rw [CyclicPoly.eval_affine0, Rat.cast_one, hw, hx]; field_simp; ring
  have eb : CyclicPoly.eval (CyclicPoly.affine 1 shellR1 1) x y z = s := by
    rw [CyclicPoly.eval_affine1, Rat.cast_one, hw, hy]; field_simp; ring
  have ec : CyclicPoly.eval (CyclicPoly.affine 1 shellR1 2) x y z = d := by
    rw [CyclicPoly.eval_affine2, Rat.cast_one, hw, hz]; field_simp; ring
  have hp : ∀ t : ℝ, t ≤ 501473/500000 → radialPiece t = 0 := by
    intro t ht
    simp [radialPiece, breaks, List.findIdx_cons, ht]
  have he := CyclicPoly.eval_cyclic (CyclicPoly.affine 1 shellR1 0) (CyclicPoly.affine 1 shellR1 1)
    (CyclicPoly.affine 1 shellR1 2) x y z
    (by rw [ea]; exact hr1) (by rw [ea]; linarith) (by rw [eb]; exact hs1) (by rw [eb]; linarith)
    (by rw [ec]; exact hd1) (by rw [ec]; linarith)
  rw [ea, eb, ec, hp r hr, hp s hs, hp d hd] at he
  rw [he] at hb
  have hf := CyclicPoly.full_factor_lower hr1 hs1 hd1
  have hpoly : polynomialSideCyclic r s d ≤ 9/1000000 := by
    by_contra hcon
    push_neg at hcon
    have h1 : (262144 : ℝ) * (9/1000000) < (2*r*s*d)^18 * polynomialSideCyclic r s d := by
      calc (262144 : ℝ) * (9/1000000) ≤ (2*r*s*d)^18 * (9/1000000) := by nlinarith
        _ < (2*r*s*d)^18 * polynomialSideCyclic r s d := by
          apply mul_lt_mul_of_pos_left hcon; linarith
    have h2 : ((full000Thr : ℚ) : ℝ) = 262144 * (9/1000000) := by norm_num [full000Thr]
    linarith
  exact sideCyclic_near_nonpos_of_polynomial (c := 7/100000) hr1 hs1 hd1 (by linarith)
    (by linarith) (by linarith) hpoly (by have := ungaugedPair_first_margin hr1 hr; linarith)
    (by have := ungaugedPair_first_margin hs1 hs; linarith)
    (by have := ungaugedPair_first_margin hd1 hd; linarith) (by norm_num)

end
end D4Bound.V7

#print axioms D4Bound.V7.full000_of_check
