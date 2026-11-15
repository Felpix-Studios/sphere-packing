/- Degree16 counterpart of the frozen degree12 semantic proof. -/
import D4Bound.SphericalSurplusSignTree16
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSurplusSign.Bernstein16

lemma cube_coordinate {s a : ℝ} (hs : -1<s) (ha : -1≤a) (has : a≤s) :
    0≤(a+1)/(s+1) ∧ (a+1)/(s+1)≤1 ∧ -1+(s+1)*((a+1)/(s+1))=a := by
  have hw : 0<s+1 := by linarith
  have hw0 : s+1≠0 := ne_of_gt hw
  refine ⟨div_nonneg (by linarith) hw.le, (div_le_one hw).mpr (by linarith), ?_⟩
  field_simp
  ring

lemma sign_from_envelopes (upper gram : Tensor) (hcheck : OnCube upper gram)
    (raw determinant scale gramScale x y z : ℝ) (hs : 0<scale) (hgs : 0≤gramScale)
    (hdet : 0≤determinant) (hp : scale*raw≤ev upper x y z)
    (hg : gramScale*determinant≤ev gram x y z)
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) : raw≤0 := by
  have hd : 0≤ev gram x y z := le_trans (mul_nonneg hgs hdet) hg
  rcases hcheck x y z hx hx1 hy hy1 hz hz1 with h | h
  · exact False.elim (not_lt_of_ge hd h)
  · exact nonpos_of_mul_nonpos_right (le_trans hp h) hs

#print axioms sign_from_envelopes
end D4Bound.SphericalSurplusSign.Bernstein16
