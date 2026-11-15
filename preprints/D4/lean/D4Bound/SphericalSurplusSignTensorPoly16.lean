/- Degree16 counterpart of the frozen degree12 semantic proof. -/
import D4Bound.SphericalSignPoly3
import D4Bound.SphericalSurplusSignTensor16
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSurplusSign.Bernstein16
open SphericalSign

lemma evalH_finite {α : Type*} (f : α → ℝ) (zero : α) (hz : f zero=0)
    (p : List α) (n : ℕ) (hn : p.length≤n) (x : ℝ) :
    evalH f x p=∑ i : Fin n, f ((p[i.val]?).getD zero)*x^i.val := by
  induction n generalizing p with
  | zero =>
    have hp : p=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst p
    simp [evalH]
  | succ n ih =>
    cases p with
    | nil => simp [evalH,hz]
    | cons a p =>
      have hp : p.length≤n := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hn
      rw [evalH,Fin.sum_univ_succ,ih p hp]
      simp only [Fin.val_zero,List.getElem?_cons_zero,Option.getD_some,pow_zero,mul_one,
        Fin.val_succ,List.getElem?_cons_succ,pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

def bounded3 (p : Poly3) : Prop := p.length≤17 ∧ ∀ q∈p,
  q.length≤17 ∧ ∀ r∈q, r.length≤17
instance (p : Poly3) : Decidable (bounded3 p) := inferInstanceAs
  (Decidable (p.length≤17 ∧ ∀ q∈p, q.length≤17 ∧ ∀ r∈q, r.length≤17))

def coeff3 (p : Poly3) (i j k : ℕ) : ℤ :=
  (((p[i]?.getD [])[j]?.getD [])[k]?).getD 0
def powerTensor (p : Poly3) : Tensor := fun i j k => coeff3 p i.val j.val k.val
noncomputable def powerEv (p : Tensor) (x y z : ℝ) : ℝ :=
  ∑ i : I, ∑ j : I, ∑ k : I,
    (p i j k:ℝ)*x^i.val*y^j.val*z^k.val

lemma getD_property {α : Type*} (p : List α) (zero : α) (P : α → Prop)
    (hz : P zero) (hp : ∀ a∈p, P a) (i : ℕ) : P (p[i]?.getD zero) := by
  cases he : p[i]? with
  | none => simpa only [he,Option.getD_none] using hz
  | some a =>
    simpa only [he,Option.getD_some] using hp a (List.mem_of_getElem? he)

lemma eval3_powerTensor (p : Poly3) (hp : bounded3 p) (x y z : ℝ) :
    eval3 p x y z=powerEv (powerTensor p) x y z := by
  rw [eval3,evalH_finite (fun q => eval2 q y z) [] rfl p 17 hp.1]
  unfold powerEv
  apply Finset.sum_congr rfl
  intro i _
  have hq : (p[i.val]?.getD []).length≤17 ∧ ∀ r∈p[i.val]?.getD [],r.length≤17 :=
    getD_property p [] (fun q => q.length≤17 ∧ ∀ r∈q,r.length≤17)
      (by simp) hp.2 i.val
  rw [eval2,evalH_finite (fun r => evalZ r z) [] rfl _ 17 hq.1,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hr : ((p[i.val]?.getD [])[j.val]?.getD []).length≤17 :=
    getD_property (p[i.val]?.getD []) [] (fun r : List ℤ => r.length≤17)
      (by simp) hq.2 j.val
  have he (r : List ℤ) : evalZ r z=evalH (fun a : ℤ => (a:ℝ)) z r := by
    induction r with
    | nil => rfl
    | cons a r ih => simp only [evalZ,evalH,ih]
  rw [he,evalH_finite (fun a : ℤ => (a:ℝ)) 0 (by simp) _ 17 hr,
    Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp only [powerTensor,coeff3]
  ring

#print axioms eval3_powerTensor
end D4Bound.SphericalSurplusSign.Bernstein16
