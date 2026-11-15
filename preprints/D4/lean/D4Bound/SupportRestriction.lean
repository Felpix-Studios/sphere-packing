import D4Bound.Main

/-! Restricting an arbitrary admissible neighbourhood to the kernel support
preserves its energy and every census count. This covers exterior neighbours
when component identities are stated on the closed support interval. -/
open Finset
namespace D4Bound
noncomputable section
open Classical

def supportPart (X : Finset E4) : Finset E4 := X.filter (fun x => ‖x‖ ≤ 7/4)

theorem supported_energy_restrict {K : E4 → E4 → ℝ} (hK : SupportedIn K) (X : Finset E4) :
    nbhdEnergy K (supportPart X) = nbhdEnergy K X := by
  have hlinear : (∑ x ∈ supportPart X, K x 0) = ∑ x ∈ X, K x 0 := by
    rw [supportPart, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rfl
    · exact (hK x 0 (Or.inl (lt_of_not_ge hx))).symm
  have hpair : (∑ x ∈ supportPart X, ∑ y ∈ supportPart X, K x y) =
      ∑ x ∈ X, ∑ y ∈ X, K x y := by
    rw [supportPart, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : ‖x‖ ≤ 7/4
    · rw [if_pos hx, Finset.sum_filter]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs with hy
      · rfl
      · exact (hK x y (Or.inr (lt_of_not_ge hy))).symm
    · rw [if_neg hx]
      exact (Finset.sum_eq_zero fun y _ => hK x y (Or.inl (lt_of_not_ge hx))).symm
  unfold nbhdEnergy
  rw [hlinear, hpair]

theorem Kg_supported : SupportedIn Kg := by
  intro x y h
  have hzero : ¬ (x = 0 ∧ y = 0) := by
    rintro ⟨rfl, rfl⟩
    norm_num at h
  have hedge : ¬ broadEdge x y := by
    intro he
    rcases h with hx | hy
    · exact (not_lt_of_ge he.2.1) hx
    · exact (not_lt_of_ge he.2.2.2.1) hy
  simp only [Kg, if_neg hzero, if_neg hedge]

theorem supported_sub_graph {K : E4 → E4 → ℝ} (hK : SupportedIn K) :
    SupportedIn (fun x y => K x y - Kg x y) := by
  intro x y h
  change K x y - Kg x y = 0
  rw [hK x y h, Kg_supported x y h, sub_self]

theorem supportPart_admissible {X : Finset E4} (hX : Admissible X) :
    Admissible (supportPart X) := by
  constructor
  · intro x hx
    exact hX.1 x (Finset.mem_filter.mp hx).1
  · intro x hx y hy hxy
    exact hX.2 x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy

theorem countWithin_supportPart (X : Finset E4) {r : ℝ} (hr : r ≤ 7/4) :
    countWithin (supportPart X) r = countWithin X r := by
  unfold countWithin
  congr 1
  ext x
  simp only [supportPart, Finset.mem_filter]
  exact ⟨fun ⟨⟨hx, _⟩, hrx⟩ => ⟨hx, hrx⟩,
    fun ⟨hx, hrx⟩ => ⟨⟨hx, hrx.trans hr⟩, hrx⟩⟩

theorem supportPart_radii {X : Finset E4} (hX : Admissible X) :
    ∀ x ∈ supportPart X, 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 7/4 := by
  intro x hx
  exact ⟨hX.1 x (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

theorem countWithin_supportPart_R1 (X : Finset E4) :
    countWithin (supportPart X) R1 = countWithin X R1 :=
  countWithin_supportPart X (by norm_num [R1])

theorem countWithin_supportPart_R2 (X : Finset E4) :
    countWithin (supportPart X) R2 = countWithin X R2 :=
  countWithin_supportPart X (by norm_num [R2])

theorem countWithin_supportPart_R3 (X : Finset E4) :
    countWithin (supportPart X) R3 = countWithin X R3 :=
  countWithin_supportPart X (by norm_num [R3])

theorem countWithin_supportPart_R4 (X : Finset E4) :
    countWithin (supportPart X) R4 = countWithin X R4 :=
  countWithin_supportPart X (by norm_num [R4])

theorem countWithin_supportPart_R5 (X : Finset E4) :
    countWithin (supportPart X) R5 = countWithin X R5 :=
  countWithin_supportPart X (by norm_num [R5])

theorem nearCount_supportPart (X : Finset E4) :
    nearCount (supportPart X) = nearCount X := countWithin_supportPart_R5 X

theorem firstRadius_supportPart (X : Finset E4) :
    firstRadius (supportPart X) = firstRadius X := by
  simp only [firstRadius, countWithin_supportPart_R1, countWithin_supportPart_R2,
    countWithin_supportPart_R3, countWithin_supportPart_R4, nearCount_supportPart]

theorem inCountDomain_supportPart (X : Finset E4) :
    InCountDomain (supportPart X) ↔ InCountDomain X := by
  simp only [InCountDomain, countWithin_supportPart_R1, countWithin_supportPart_R2,
    countWithin_supportPart_R3, countWithin_supportPart_R4, countWithin_supportPart_R5]

/-- It suffices to prove the census estimate for points in the closed support.
The restricted configuration preserves admissibility and its exact group key. -/
theorem censusFloor_of_supported {K : E4 → E4 → ℝ} (hK : SupportedIn K)
    (hfloor : ∀ X : Finset E4, Admissible X →
      (∀ x ∈ X, ‖x‖ ≤ 7/4) → InCountDomain X →
      ∀ g ∈ groups, g.1 = nearCount X → g.2.1 = firstRadius X →
        (g.2.2 : ℝ) ≤ nbhdEnergy (fun x y => K x y - Kg x y) X) :
    CensusFloor K := by
  intro X hX hD g hg hN hj
  rw [← supported_energy_restrict (supported_sub_graph hK) X]
  apply hfloor (supportPart X) (supportPart_admissible hX)
    (fun x hx => (Finset.mem_filter.mp hx).2)
    ((inCountDomain_supportPart X).mpr hD) g hg
  · simpa only [nearCount_supportPart] using hN
  · simpa only [firstRadius_supportPart] using hj

end
end D4Bound
