import D4Bound.Bernstein2
import D4Bound.CountDomain

namespace D4Bound.LatitudeCheck

/-- A checked bicubic sign certificate gives the latitude predicate after the affine
coordinate change. The four exact polynomial identities are checked separately. -/
theorem latitude_of_checked (p : Bundle) (t : Tree) (s c S β : ℝ)
    (hcheck : check p t = true) (hc : -1 < c)
    (dP dV dH dD : ℝ) (hdP : 0 < dP) (hdV : 0 < dV) (hdH : 0 < dH) (hdD : 0 < dD)
    (hP : ∀ x y, ev p.P x y = dP * latP S β ((c+1)*x-1) ((c+1)*y-1))
    (hV : ∀ x y, ev p.V x y = dV * (s - ((c+1)*x-1)*((c+1)*y-1)))
    (hH : ∀ x y, ev p.H x y = dH * latH s S β ((c+1)*x-1) ((c+1)*y-1))
    (hD : ∀ x y, ev p.D x y = dD * (1-s^2+2*s*(((c+1)*x-1)*((c+1)*y-1))-((c+1)*x-1)^2-((c+1)*y-1)^2)) :
    LatSign s c S β := by
  intro a b ha hac hb hbc hdet
  let x := (a+1)/(c+1)
  let y := (b+1)/(c+1)
  have hcpos : 0 < c+1 := by linarith
  have hx : 0 ≤ x := div_nonneg (by linarith) hcpos.le
  have hy : 0 ≤ y := div_nonneg (by linarith) hcpos.le
  have hx1 : x ≤ 1 := (div_le_one hcpos).mpr (by linarith)
  have hy1 : y ≤ 1 := (div_le_one hcpos).mpr (by linarith)
  have hxa : (c+1)*x-1 = a := by dsimp [x]; field_simp; ring
  have hyb : (c+1)*y-1 = b := by dsimp [y]; field_simp; ring
  have hh := check_sound t p hcheck hx hx1 hy hy1
  unfold Good at hh
  rw [hP, hV, hH, hD, hxa, hyb] at hh
  rcases hh with hd | ⟨hp,hv⟩ | ⟨hp,hh⟩ | ⟨hv,hh⟩
  · have : 0 ≤ dD * (1-s^2+2*s*(a*b)-a^2-b^2) := mul_nonneg hdD.le hdet
    linarith
  · exact Or.inl ⟨(mul_nonneg_iff_of_pos_left hdP).mp hp, (by nlinarith)⟩
  · exact Or.inr (Or.inl ⟨(mul_nonneg_iff_of_pos_left hdP).mp hp, (mul_nonneg_iff_of_pos_left hdH).mp hh⟩)
  · exact Or.inr (Or.inr ⟨(by nlinarith), (by nlinarith)⟩)

end D4Bound.LatitudeCheck
