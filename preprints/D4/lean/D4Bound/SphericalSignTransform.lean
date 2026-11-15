import D4Bound.SphericalSignTensorPoly
import D4Bound.SphericalSignConvert
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSign.Bernstein

def matrixX (T : I → I → ℤ) (p : Tensor) : Tensor := fun i j k => ∑ a : I, T i a*p a j k
def matrixY (T : I → I → ℤ) (p : Tensor) : Tensor := fun i j k => ∑ b : I, T j b*p i b k
def matrixZ (T : I → I → ℤ) (p : Tensor) : Tensor := fun i j k => ∑ c : I, T k c*p i j c

lemma E_matrix (T : I → I → ℤ) (d a x : ℝ)
    (hT : ∀ j, (∑ i : I, (T i j:ℝ)*basis i x)=d*a^j.val) (p : I → ℝ) :
    E (fun i => ∑ j : I,(T i j:ℝ)*p j) x=d*powerEval p a := by
  simp only [E,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc,mul_comm (p _) (basis _ x),←mul_assoc,←Finset.sum_mul,hT]
  rw [powerEval,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma ev_matrixXYZ (T : I → I → ℤ) (d a b c x y z : ℝ)
    (hX : ∀ j, (∑ i : I, (T i j:ℝ)*basis i x)=d*a^j.val)
    (hY : ∀ j, (∑ i : I, (T i j:ℝ)*basis i y)=d*b^j.val)
    (hZ : ∀ j, (∑ i : I, (T i j:ℝ)*basis i z)=d*c^j.val) (p : Tensor) :
    ev (matrixX T (matrixY T (matrixZ T p))) x y z=d^3*powerEv p a b c := by
  have he : ev (matrixX T (matrixY T (matrixZ T p))) x y z =
      E (fun i => ∑ ia : I,(T i ia:ℝ)*
        E (fun j => ∑ ib : I,(T j ib:ℝ)*
          E (fun k => ∑ ic : I,(T k ic:ℝ)*(p ia ib ic:ℝ)) z) y) x := by
    simp only [ev,matrixX,matrixY,matrixZ,Int.cast_sum,Int.cast_mul]
    simp_rw [E_sum,E_smul,E_sum,E_smul,E_sum]
  rw [he]
  simp_rw [E_matrix T d c z hZ,E_matrix T d b y hY,E_matrix T d a x hX]
  simp only [powerEval,powerEv,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

#print axioms ev_matrixXYZ
end D4Bound.SphericalSign.Bernstein
