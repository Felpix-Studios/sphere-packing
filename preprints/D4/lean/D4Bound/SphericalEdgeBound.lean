import D4Bound.SphericalCertBasic

/-! A spherical energy certificate bounds the number of ordered pairs in a
closed angular band. Symmetry supplies the evenness needed for integer rounding.
-/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound
noncomputable section
open Classical

def relationCount {α : Type*} (s : Finset α) (r : α → α → Prop) : ℕ :=
  ∑ x ∈ s, ∑ y ∈ s, if r x y then 1 else 0

theorem relationCount_even {α : Type*} (s : Finset α) (r : α → α → Prop)
    (hsy : ∀ x y, r x y ↔ r y x) (hii : ∀ x ∈ s, ¬ r x x) : Even (relationCount s r) := by
  induction s using Finset.induction_on with
  | empty => simp [relationCount]
  | @insert a s ha ih =>
    have hsa := hii a (Finset.mem_insert_self _ _)
    have hs := ih (fun x hx => hii x (Finset.mem_insert_of_mem hx))
    have he : (∑ x ∈ s, if r x a then 1 else 0) =
        (∑ x ∈ s, if r a x then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hsy x a]
    obtain ⟨k,hk⟩ := hs
    refine ⟨k + ∑ x ∈ s, if r a x then 1 else 0, ?_⟩
    simp only [relationCount, Finset.sum_insert ha, if_neg hsa, zero_add,
      Finset.sum_add_distrib, he] at hk ⊢
    omega

def angularBandCount (C : Finset (EuclideanSpace ℝ (Fin 4))) (lo hi : ℝ) : ℕ :=
  relationCount C (fun x y => lo ≤ ⟪x,y⟫ ∧ ⟪x,y⟫ ≤ hi)

theorem angularBandCount_even (C : Finset (EuclideanSpace ℝ (Fin 4)))
    (hC : ∀ u ∈ C, ‖u‖ = 1) (lo hi : ℝ) (hhi : hi < 1) :
    Even (angularBandCount C lo hi) := by
  apply relationCount_even
  · intro x y
    rw [real_inner_comm x y]
  · intro x hx h
    have := h.2
    rw [real_inner_self_eq_norm_sq, hC x hx] at this
    nlinarith

theorem spherical_band_bound (C : Finset (EuclideanSpace ℝ (Fin 4)))
    (hC : ∀ u ∈ C, ‖u‖ = 1) (s A B lo hi : ℝ) (h : ℝ → ℝ)
    (hhi : hi < 1) (henergy : SphereEnergyNonneg h)
    (hdiag : A+h 1=B)
    (hsign : ∀ t : ℝ, -1 ≤ t → t ≤ s → A+h t ≤ 0)
    (hband : ∀ t : ℝ, lo ≤ t → t ≤ hi → A+h t ≤ -1)
    (hsep : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ⟪u,v⟫ ≤ s) :
    (angularBandCount C lo hi : ℝ) ≤ (C.card : ℝ)*B-A*(C.card : ℝ)^2 := by
  have hlow : (C.card : ℝ)^2*A ≤ ∑ u ∈ C, ∑ v ∈ C, (A+h ⟪u,v⟫) := by
    have he := henergy C hC
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    nlinarith
  have hhigh : (∑ u ∈ C, ∑ v ∈ C, (A+h ⟪u,v⟫)) ≤
      (C.card : ℝ)*B-(angularBandCount C lo hi : ℝ) := by
    calc
      _ ≤ ∑ u ∈ C, ∑ v ∈ C,
          ((if u=v then B else 0) - (if lo ≤ ⟪u,v⟫ ∧ ⟪u,v⟫ ≤ hi then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        by_cases he : u=v
        · subst v
          have huu : ⟪u,u⟫ = (1 : ℝ) := by
            rw [real_inner_self_eq_norm_sq,hC u hu]; norm_num
          simp only [if_true,huu,hdiag]
          rw [if_neg (by intro h; exact (not_le.mpr hhi) h.2), sub_zero]
        · rw [if_neg he, zero_sub]
          split_ifs with hb
          · exact hband _ hb.1 hb.2
          · simp only [neg_zero]
            apply hsign
            · have hl := (abs_le.mp (abs_real_inner_le_norm u v)).1
              simpa [hC u hu,hC v hv] using hl
            · exact hsep u hu v hv he
      _ = _ := by
        simp only [Finset.sum_sub_distrib]
        simp [angularBandCount,relationCount,Finset.sum_ite_eq',Nat.cast_sum,Nat.cast_ite]
  nlinarith

end
end D4Bound
