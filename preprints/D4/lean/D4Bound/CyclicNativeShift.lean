import D4Bound.CyclicNativeSound

/-!
# Soundness of the affine-shift entry point of the native checker

`checkPolyAff_sound`: the check of a polynomial `p` in the original radii, with affine maps
`x ↦ (α + ω x)/e` on the three axes, bounds `p` at the mapped point for every point of the
unit cube.
-/
namespace D4Bound.CyclicNative
open Finset

noncomputable section

/-- Fiber identity of the integer affine shift. -/
lemma shift_identity (n : ℕ) (e α ω : ℝ) (he : e ≠ 0) (g : ℕ → ℝ) (x : ℝ) :
    ∑ i ∈ range (n+1), (ω^i * ∑ m ∈ range (n-i+1), ((i+m).choose i : ℝ) * α^m * e^(n-(i+m)) * g (i+m)) * x^i
      = e^n * ∑ l ∈ range (n+1), g l * ((α + ω*x)/e)^l := by
  rw [mul_sum]
  have hx : ∀ l ∈ range (n+1), e^n * (g l * ((α + ω*x)/e)^l) = ∑ i ∈ range (n+1),
      (if i ≤ l then ω^i * (((l.choose i : ℝ) * α^(l-i) * e^(n-l) * g l)) * x^i else 0) := by
    intro l hl
    have hl' : l ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hl)
    have hpow : e^n * ((α + ω*x)/e)^l = e^(n-l) * (ω*x + α)^l := by
      rw [div_pow, show n = (n-l)+l by omega, pow_add]
      field_simp
      ring_nf
      rw [show n - l + l - l = n - l by omega]
    have e2 := add_pow (ω*x) α l
    rw [show e^n * (g l * ((α + ω*x)/e)^l) = g l * (e^n * ((α + ω*x)/e)^l) by ring, hpow, e2,
      mul_sum, mul_sum, sum_trunc_le (fun i => ω^i * (((l.choose i : ℝ) * α^(l-i) * e^(n-l) * g l)) * x^i) hl']
    apply sum_congr rfl
    intro i _
    rw [mul_pow]; ring
  rw [sum_congr rfl hx, sum_comm]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [sum_trunc_ge (fun l => ω^i * (((l.choose i : ℝ) * α^(l-i) * e^(n-l) * g l)) * x^i) hi',
    mul_sum, sum_mul]
  apply sum_congr rfl
  intro m _
  simp only [show i + m - i = m by omega]

lemma shiftLast_get (T : Tens) (e : ℕ) (α ω : ℤ) {i j k : ℕ} (hi : i ≤ T.n0) (hj : j ≤ T.n1)
    (hk : k ≤ T.n2) : (shiftLast T e α ω).get i j k = ω^k * ∑ m ∈ range (T.n2+1-k),
      (((k+m).choose k : ℕ) : ℤ) * α^m * (e : ℤ)^(T.n2-(k+m)) * T.get i j (k+m) := by
  have hlt := idx_lt T hi hj hk
  obtain ⟨hd, hm⟩ := idx_div T (i := i) (j := j) hk
  have hf : i*(T.n1+1)+j < (T.n0+1)*(T.n1+1) := by nlinarith
  show (Array.ofFn _).getD (T.idx i j k) 0 = _
  rw [getD_ofFn _ (by simpa [Tens.idx] using hlt)]
  simp only [hd, hm]
  rw [getD_ofFn _ hf]
  unfold shiftFiber
  rw [getD_ofFn _ (by omega)]
  simp only
  rw [foldl_range_sum]
  congr 1
  refine sum_congr rfl fun m hm' => ?_
  have hm'' : m < T.n2+1-k := mem_range.mp hm'
  rw [binom_eq, fiber_getD T (by omega)]

@[simp] lemma shiftLast_dims (T : Tens) (e : ℕ) (α ω : ℤ) : (shiftLast T e α ω).n0 = T.n0 ∧
    (shiftLast T e α ω).n1 = T.n1 ∧ (shiftLast T e α ω).n2 = T.n2 := by simp [shiftLast]

lemma S_shiftLast (T : Tens) (e : ℕ) (he : 0 < e) (α ω : ℤ) (φ0 φ1 : ℕ → ℝ → ℝ) (x y z : ℝ) :
    S (shiftLast T e α ω) φ0 φ1 pw x y z =
      (e : ℝ)^T.n2 * S T φ0 φ1 pw x y (((α : ℝ) + (ω : ℝ)*z)/(e : ℝ)) := by
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  unfold S
  simp only [shiftLast_dims]
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hi' : i ≤ T.n0 := by simp at hi; omega
  have hj' : j ≤ T.n1 := by simp at hj; omega
  have h1 : ∀ k ∈ range (T.n2+1), ((shiftLast T e α ω).get i j k : ℝ) * (φ0 i x * φ1 j y * pw k z) =
      (φ0 i x * φ1 j y) * (((ω:ℝ)^k * ∑ m ∈ range (T.n2-k+1), (((k+m).choose k : ℕ) : ℝ) * (α:ℝ)^m *
        (e:ℝ)^(T.n2-(k+m)) * (T.get i j (k+m) : ℝ)) * z^k) := by
    intro k hk
    rw [shiftLast_get T e α ω hi' hj' (by simp at hk; omega), show T.n2+1-k = T.n2-k+1 by
      simp at hk; omega]
    push_cast
    unfold pw; ring
  have hid := shift_identity T.n2 (e:ℝ) (α:ℝ) (ω:ℝ) he' (fun l => (T.get i j l : ℝ)) z
  beta_reduce at hid
  push_cast at hid ⊢
  rw [sum_congr rfl h1, ← mul_sum, hid]
  simp only [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  unfold pw; ring

lemma S_shiftAll (T : Tens) (A0 A1 A2 : ℕ × ℤ × ℤ) (h0 : 0 < A0.1) (h1 : 0 < A1.1) (h2 : 0 < A2.1)
    (x y z : ℝ) : S (shiftAll T A0 A1 A2) pw pw pw x y z =
      (A0.1 : ℝ)^T.n0 * (A1.1 : ℝ)^T.n1 * (A2.1 : ℝ)^T.n2 *
      S T pw pw pw (((A0.2.1 : ℝ) + (A0.2.2 : ℝ)*x)/(A0.1 : ℝ)) (((A1.2.1 : ℝ) + (A1.2.2 : ℝ)*y)/(A1.1 : ℝ))
        (((A2.2.1 : ℝ) + (A2.2.2 : ℝ)*z)/(A2.1 : ℝ)) := by
  unfold shiftAll
  have e1 := S_shiftLast T A2.1 h2 A2.2.1 A2.2.2 pw pw
    (((A0.2.1 : ℝ) + (A0.2.2 : ℝ)*x)/(A0.1 : ℝ)) (((A1.2.1 : ℝ) + (A1.2.2 : ℝ)*y)/(A1.1 : ℝ)) z
  have e2 := S_shiftLast (rot (shiftLast T A2.1 A2.2.1 A2.2.2)) A0.1 h0 A0.2.1 A0.2.2 pw pw
    (((A1.2.1 : ℝ) + (A1.2.2 : ℝ)*y)/(A1.1 : ℝ)) z x
  have e3 := S_shiftLast (rot (shiftLast (rot (shiftLast T A2.1 A2.2.1 A2.2.2)) A0.1 A0.2.1 A0.2.2))
    A1.1 h1 A1.2.1 A1.2.2 pw pw z x y
  simp only [rot_n0, rot_n1, rot_n2, shiftLast_dims] at e2 e3
  rw [S_rot, e3, S_rot, e2, S_rot, e1]
  try ring

lemma affOf_eval (ab : ℚ × ℚ) (x : ℝ) :
    (((affOf ab).2.1 : ℝ) + ((affOf ab).2.2 : ℝ)*x)/((affOf ab).1 : ℝ) =
      (ab.1 : ℝ) + ((ab.2 : ℝ) - ab.1) * x := by
  unfold affOf
  have h1 : (ab.1 : ℝ) = (ab.1.num : ℝ) / (ab.1.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have h2 : (ab.2 : ℝ) = (ab.2.num : ℝ) / (ab.2.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have d1 : (ab.1.den : ℝ) ≠ 0 := by exact_mod_cast ab.1.den_pos.ne'
  have d2 : (ab.2.den : ℝ) ≠ 0 := by exact_mod_cast ab.2.den_pos.ne'
  rw [h1, h2]
  push_cast
  field_simp
  try ring

lemma affOf_pos (ab : ℚ × ℚ) : 0 < (affOf ab).1 := by
  unfold affOf; exact Nat.mul_pos ab.1.den_pos ab.2.den_pos

/-- Rounded scaled Bernstein tensor bounds `S C bp bp bp / Dn`. -/
lemma scaleUp_bound (C : Tens) (Dn : ℕ) (hD : 0 < Dn) (unit : ℚ) (hu : 0 < unit) {x y z : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    S C (bp C.n0) (bp C.n1) (bp C.n2) x y z / Dn ≤ (unit : ℝ) * E3 (scaleUp C Dn unit) x y z := by
  have hDr : (0:ℝ) < Dn := by exact_mod_cast hD
  unfold E3 S
  simp only [scaleUp_dims]
  rw [div_eq_mul_inv, sum_mul, mul_sum]
  refine sum_le_sum fun i hi => ?_
  rw [sum_mul, mul_sum]
  refine sum_le_sum fun j hj => ?_
  rw [sum_mul, mul_sum]
  refine sum_le_sum fun k hk => ?_
  have hi' : i ≤ C.n0 := by simp at hi; omega
  have hj' : j ≤ C.n1 := by simp at hj; omega
  have hk' : k ≤ C.n2 := by simp at hk; omega
  rw [scaleUp_get _ Dn unit hi' hj' hk']
  simp only [binom_eq]
  set c := C.get i j k
  have hb0 : (0:ℝ) < (C.n0.choose i : ℝ) := by exact_mod_cast Nat.choose_pos hi'
  have hb1 : (0:ℝ) < (C.n1.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj'
  have hb2 : (0:ℝ) < (C.n2.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk'
  have hur : (0:ℝ) < (unit : ℝ) := by exact_mod_cast hu
  set q : ℚ := (c : ℚ) / ((Dn * C.n0.choose i * C.n1.choose j * C.n2.choose k : ℕ) * unit) with hqdef
  have hr := rceil_ge q
  have hqc : (q : ℝ) = (c : ℝ) / ((Dn:ℝ) * (C.n0.choose i : ℝ) * (C.n1.choose j : ℝ) *
      (C.n2.choose k : ℝ) * (unit : ℝ)) := by rw [hqdef]; push_cast; ring
  rw [hqc] at hr
  have hprod : 0 ≤ B C.n0 i x * B C.n1 j y * B C.n2 k z :=
    mul_nonneg (mul_nonneg (B_nonneg _ _ hx0 hx1) (B_nonneg _ _ hy0 hy1)) (B_nonneg _ _ hz0 hz1)
  have hq : (c : ℝ) / (Dn * C.n0.choose i * C.n1.choose j * C.n2.choose k * unit) * unit *
      (B C.n0 i x * B C.n1 j y * B C.n2 k z) =
      (c : ℝ) * (bp C.n0 i x * bp C.n1 j y * bp C.n2 k z) * (Dn:ℝ)⁻¹ := by
    unfold B bp; field_simp
  calc (c : ℝ) * (bp C.n0 i x * bp C.n1 j y * bp C.n2 k z) * (Dn:ℝ)⁻¹
      = (c : ℝ) / (Dn * C.n0.choose i * C.n1.choose j * C.n2.choose k * unit) * unit *
          (B C.n0 i x * B C.n1 j y * B C.n2 k z) := hq.symm
    _ ≤ (unit : ℝ) * ((rceil q : ℝ) * (B C.n0 i x * B C.n1 j y * B C.n2 k z)) := by
        rw [show (unit : ℝ) * ((rceil q : ℝ) * (B C.n0 i x * B C.n1 j y * B C.n2 k z)) =
          (rceil q : ℝ) * unit * (B C.n0 i x * B C.n1 j y * B C.n2 k z) by ring]
        apply mul_le_mul_of_nonneg_right _ hprod
        apply mul_le_mul_of_nonneg_right _ hur.le
        exact hr

lemma convAll_dims (T : Tens) : (convAll T).n0 = T.n0 ∧ (convAll T).n1 = T.n1 ∧ (convAll T).n2 = T.n2 := by
  simp [convAll]

lemma shiftAll_dims (T : Tens) (A0 A1 A2 : ℕ × ℤ × ℤ) : (shiftAll T A0 A1 A2).n0 = T.n0 ∧
    (shiftAll T A0 A1 A2).n1 = T.n1 ∧ (shiftAll T A0 A1 A2).n2 = T.n2 := by
  simp [shiftAll]

theorem checkPolyAff_sound (thr : Box → ℚ) (unit : ℚ) (w : ℚ × ℚ × ℚ) (fuel : ℕ)
    (p : List ((ℕ × ℕ × ℕ) × ℚ)) (A0 A1 A2 : ℕ × ℤ × ℤ) (G : ℝ → ℝ → ℝ → ℝ)
    (h : checkPolyAff thr unit w fuel p A0 A1 A2 = true)
    (hthr : ∀ (B : Box), B.Valid → ∀ x y z, Cube x y z →
      ((thr B : ℚ) : ℝ) ≤ G (B.a.pt x) (B.b.pt y) (B.c.pt z))
    (hG : ∀ x y z, Cube x y z → 0 ≤ G x y z) :
    ∀ x y z, Cube x y z → V7.CyclicPoly.eval p (((A0.2.1 : ℝ) + (A0.2.2 : ℝ)*x)/(A0.1 : ℝ))
      (((A1.2.1 : ℝ) + (A1.2.2 : ℝ)*y)/(A1.1 : ℝ)) (((A2.2.1 : ℝ) + (A2.2.2 : ℝ)*z)/(A2.1 : ℝ)) ≤
        G x y z := by
  simp only [checkPolyAff, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hdeg, hint⟩, hu⟩, ⟨h0, h1, h2⟩⟩, hc⟩ := h
  have hG' : ∀ (B : Box), B.Valid → ∀ x y z, Cube x y z → 0 ≤ G (B.a.pt x) (B.b.pt y) (B.c.pt z) := by
    intro B hB x y z hc
    obtain ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩ := hc
    obtain ⟨ha, hb, hcc⟩ := hB
    exact hG _ _ _ ⟨(Dy.pt_unit ha hx0 hx1).1, (Dy.pt_unit ha hx0 hx1).2, (Dy.pt_unit hb hy0 hy1).1,
      (Dy.pt_unit hb hy0 hy1).2, (Dy.pt_unit hcc hz0 hz1).1, (Dy.pt_unit hcc hz0 hz1).2⟩
  set d := degrees p
  set D := commonDen p
  set A := denseOf d.1 d.2.1 d.2.2 D p
  have hDpos : 0 < D := by
    simp only [D, commonDen]
    have key : ∀ (l : List ((ℕ × ℕ × ℕ) × ℚ)) (a : ℕ), 0 < a →
        0 < l.foldl (fun d t => Nat.lcm d t.2.den) a := by
      intro l
      induction l with
      | nil => intro a ha; simpa using ha
      | cons t l ih => intro a ha; exact ih _ (Nat.lcm_pos ha t.2.den_pos)
    exact key p 1 (by norm_num)
  have hdeg' : ∀ t ∈ p, t.1.1 ≤ d.1 ∧ t.1.2.1 ≤ d.2.1 ∧ t.1.2.2 ≤ d.2.2 := by
    intro t ht; have := List.all_eq_true.mp hdeg t ht; simpa using this
  have hden : ∀ t ∈ p, (t.2 * (D : ℚ)).den = 1 := by
    intro t ht; have := List.all_eq_true.mp hint t ht; simpa using this
  have hinv : Inv (fun x y z => V7.CyclicPoly.eval p (((A0.2.1 : ℝ) + (A0.2.2 : ℝ)*x)/(A0.1 : ℝ))
      (((A1.2.1 : ℝ) + (A1.2.2 : ℝ)*y)/(A1.1 : ℝ)) (((A2.2.1 : ℝ) + (A2.2.2 : ℝ)*z)/(A2.1 : ℝ)))
      unit (initialAff p A0 A1 A2 unit) rootBox := by
    intro x y z hc
    obtain ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩ := hc
    dsimp only
    rw [(rootBox_pt x).1, (rootBox_pt y).2.1, (rootBox_pt z).2.2]
    set X := ((A0.2.1 : ℝ) + (A0.2.2 : ℝ)*x)/(A0.1 : ℝ)
    set Y := ((A1.2.1 : ℝ) + (A1.2.2 : ℝ)*y)/(A1.1 : ℝ)
    set Z := ((A2.2.1 : ℝ) + (A2.2.2 : ℝ)*z)/(A2.1 : ℝ)
    have hA := S_foldl D p ⟨d.1, d.2.1, d.2.2, Array.replicate ((d.1+1)*(d.2.1+1)*(d.2.2+1)) 0⟩
      (by simp) hdeg' hden X Y Z
    rw [S_zero_dims ⟨d.1, d.2.1, d.2.2, Array.replicate ((d.1+1)*(d.2.1+1)*(d.2.2+1)) 0⟩
      (by intro i j k; simp only [Tens.get, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
          split_ifs <;> rfl), zero_add, ← denseOf_eq] at hA
    have hS := S_shiftAll A A0 A1 A2 h0 h1 h2 x y z
    have hC := S_convAll (shiftAll A A0 A1 A2) x y z
    have hsd := shiftAll_dims A A0 A1 A2
    rw [hsd.1, hsd.2.1, hsd.2.2] at hC
    have hAd : A.n0 = d.1 ∧ A.n1 = d.2.1 ∧ A.n2 = d.2.2 := by
      simp only [A]
      have : ∀ (l : List ((ℕ × ℕ × ℕ) × ℚ)) (T : Tens), (l.foldl (denseStep D) T).n0 = T.n0 ∧
          (l.foldl (denseStep D) T).n1 = T.n1 ∧ (l.foldl (denseStep D) T).n2 = T.n2 := by
        intro l
        induction l with
        | nil => intro T; simp
        | cons t l ih => intro T; simp only [List.foldl_cons]; exact ih _
      rw [denseOf_eq]; exact this p _
    have hD' : 0 < D * A0.1^d.1 * A1.1^d.2.1 * A2.1^d.2.2 := by positivity
    have hb := scaleUp_bound (convAll (shiftAll A A0 A1 A2)) (D * A0.1^d.1 * A1.1^d.2.1 * A2.1^d.2.2)
      hD' unit hu hx0 hx1 hy0 hy1 hz0 hz1
    have hcd := convAll_dims (shiftAll A A0 A1 A2)
    rw [hcd.1, hcd.2.1, hcd.2.2, hsd.1, hsd.2.1, hsd.2.2, hC, hS, hAd.1, hAd.2.1, hAd.2.2, hA] at hb
    have e0 : (0:ℝ) < (A0.1:ℝ) := by exact_mod_cast h0
    have e1 : (0:ℝ) < (A1.1:ℝ) := by exact_mod_cast h1
    have e2 : (0:ℝ) < (A2.1:ℝ) := by exact_mod_cast h2
    have hDr : (0:ℝ) < (D:ℝ) := by exact_mod_cast hDpos
    have key : (A0.1:ℝ)^d.1 * (A1.1:ℝ)^d.2.1 * (A2.1:ℝ)^d.2.2 * ((D:ℝ) * V7.CyclicPoly.eval p X Y Z) /
        ((D * A0.1^d.1 * A1.1^d.2.1 * A2.1^d.2.2 : ℕ) : ℝ) = V7.CyclicPoly.eval p X Y Z := by
      push_cast; field_simp
    rw [key] at hb
    exact hb
  intro x y z hcube
  have := check_sound thr unit w (by exact_mod_cast hu.le) _ G hthr hG' fuel _ rootBox rootBox_valid hc
    hinv x y z hcube
  simpa only [(rootBox_pt x).1, (rootBox_pt y).2.1, (rootBox_pt z).2.2] using this

end
end D4Bound.CyclicNative

#print axioms D4Bound.CyclicNative.checkPolyAff_sound
