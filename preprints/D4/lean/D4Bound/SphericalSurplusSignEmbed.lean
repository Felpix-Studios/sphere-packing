import D4Bound.SphericalSignPoly3
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSurplusSign
open SphericalSign

def embedX (p : List ℤ) : Poly3 := p.map (fun a => [[a]])
def embedY (p : List ℤ) : Poly3 := [p.map (fun a => [a])]

lemma eval_embedX (p : List ℤ) (x y z : ℝ) : eval3 (embedX p) x y z=evalZ p x := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change eval2 [[a]] y z + x*eval3 (embedX p) x y z=evalZ (a::p) x
    rw [ih]
    simp [eval2,evalH,evalZ]

lemma eval_embedY (p : List ℤ) (x y z : ℝ) : eval3 (embedY p) x y z=evalZ p y := by
  have h : eval2 (p.map (fun a => [a])) y z=evalZ p y := by
    induction p with
    | nil => rfl
    | cons a p ih =>
      change evalZ [a] z+y*eval2 (p.map (fun a => [a])) y z=evalZ (a::p) y
      rw [ih]
      simp [evalZ]
  simpa [embedY,eval3,evalH] using h

lemma eval_const3 (a : ℤ) (x y z : ℝ) : eval3 [[[a]]] x y z=a := by
  simp [eval3,eval2,evalH,evalZ]

#print axioms eval_embedX
#print axioms eval_embedY
end D4Bound.SphericalSurplusSign
