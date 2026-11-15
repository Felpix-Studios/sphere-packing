import D4Bound.V7CyclicRegions
import D4Bound.V7CyclicSymmetry

/-! The exact 84+28 canonical case interface. This is coverage and reduction,
not an assertion that the case signs have been formally replayed. -/
namespace D4Bound.V7
noncomputable section
open Classical

def fullCases : Finset (Fin 7 × Fin 7 × Fin 7) :=
  Finset.univ.filter fun p => p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2

def outsideCases : Finset (Fin 7 × Fin 7) :=
  Finset.univ.filter fun p => p.1 ≤ p.2

theorem fullCases_card : fullCases.card = 84 := by decide +kernel
theorem outsideCases_card : outsideCases.card = 28 := by decide +kernel

theorem region_index_mono {p q : ℕ} {r s : ℝ}
    (hp : RegionOwns p r) (hq : RegionOwns q s) (hrs : r ≤ s) : p ≤ q := by
  rcases hp with ⟨hp,hl,hh⟩
  rcases hq with ⟨hq,kl,kh⟩
  interval_cases p <;> interval_cases q <;>
    norm_num [regionLo,regionHi,breaks] at hl hh kl kh ⊢ <;> linarith

/-- Literal case proof obligations, with actual fixed data and exact endpoint ownership. -/
theorem cyclicSign_of_112_cases
    (full : ∀ p ∈ fullCases, ∀ r s d : ℝ,
      RegionOwns p.1.val r → RegionOwns p.2.1.val s → RegionOwns p.2.2.val d →
      r ≤ s → s ≤ d → sideCyclic r s d ≤ 0)
    (outside : ∀ p ∈ outsideCases, ∀ r s d : ℝ,
      RegionOwns p.1.val r → RegionOwns p.2.val s →
      r ≤ s → 7/4 < d → d ≤ r+s → pair r s (sideCos r s d) ≤ 0) :
    CyclicSign kernel := by
  apply cyclicSign_of_ordered_side_certificates
  · intro r s d hr hrs hsd hd
    obtain ⟨p,hp⟩ := region_coverage hr (hrs.trans (hsd.trans hd))
    obtain ⟨q,hq⟩ := region_coverage (hr.trans hrs) (hsd.trans hd)
    obtain ⟨k,hk⟩ := region_coverage (hr.trans (hrs.trans hsd)) hd
    let pi : Fin 7 := ⟨p,hp.1⟩
    let qi : Fin 7 := ⟨q,hq.1⟩
    let ki : Fin 7 := ⟨k,hk.1⟩
    have hm : (pi,qi,ki) ∈ fullCases := by
      simp only [fullCases,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨region_index_mono hp hq hrs,region_index_mono hq hk hsd⟩
    exact full _ hm r s d hp hq hk hrs hsd
  · intro r s d hr hrs hs hd htri
    obtain ⟨p,hp⟩ := region_coverage hr (hrs.trans hs)
    obtain ⟨q,hq⟩ := region_coverage (hr.trans hrs) hs
    let pi : Fin 7 := ⟨p,hp.1⟩
    let qi : Fin 7 := ⟨q,hq.1⟩
    have hm : (pi,qi) ∈ outsideCases := by
      simp only [outsideCases,Finset.mem_filter,Finset.mem_univ,true_and]
      exact region_index_mono hp hq hrs
    exact outside _ hm r s d hp hq hrs hd htri

#print axioms fullCases_card
#print axioms outsideCases_card
#print axioms cyclicSign_of_112_cases
end
end D4Bound.V7
