import D4Bound.V7PairPolynomial
import D4Bound.V7PairPolynomialTrim

namespace D4Bound.V7.PairPoly
noncomputable section

lemma eval_trim (p : Poly) (r : ℝ) : eval (trim p) r = eval p r := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    unfold trim
    dsimp only
    split_ifs with h
    · obtain ⟨ha,hp⟩ := h
      have hz : eval p r = 0 := by rw [← ih,hp]; rfl
      simp [eval,ha,hz]
    · simp only [eval,ih]

end
end D4Bound.V7.PairPoly
