/- Degree16 counterpart of the frozen degree12 semantic proof. -/
import D4Bound.SphericalSurplusSignTensor16
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSurplusSign.Bernstein16

noncomputable def firstMoment (i : I) : ℝ := (i.val:ℝ)/16
noncomputable def secondMoment (i : I) : ℝ := (i.val:ℝ)*((i.val:ℝ)-1)/240

lemma E_firstMoment (x : ℝ) : E firstMoment x = x := by
  norm_num [E,firstMoment,basis,Fin.sum_univ_succ,Nat.choose]
  ring
lemma E_secondMoment (x : ℝ) : E secondMoment x = x^2 := by
  norm_num [E,secondMoment,basis,Fin.sum_univ_succ,Nat.choose]
  ring
lemma E_sub (p q : I → ℝ) (x : ℝ) : E (fun i => p i-q i) x = E p x-E q x := by
  simp only [E,sub_mul,Finset.sum_sub_distrib]
lemma E_mul (p : I → ℝ) (c x : ℝ) : E (fun i => p i*c) x = E p x*c := by
  simp only [E,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact Bernstein coefficients of the Gram determinant after
(a,b,t)=(-1+w*x,-1+w*y,-1+w*z), in degree16 in each variable. -/
noncomputable def gramCoeffs (w : ℝ) (i j k : I) : ℝ :=
  -4+4*w*(firstMoment i+firstMoment j+firstMoment k)-
    w^2*(secondMoment i+secondMoment j+secondMoment k+
      2*(firstMoment i*firstMoment j+firstMoment i*firstMoment k+firstMoment j*firstMoment k))+
    2*w^3*firstMoment i*firstMoment j*firstMoment k

lemma gramCoeffs_exact (w x y z : ℝ) :
    E (fun i => E (fun j => E (gramCoeffs w i j) z) y) x =
      1+2*(-1+w*x)*(-1+w*y)*(-1+w*z)-(-1+w*x)^2-(-1+w*y)^2-(-1+w*z)^2 := by
  unfold gramCoeffs
  simp only [E_add,E_sub,E_smul,E_mul,E_const,E_firstMoment,E_secondMoment]
  ring

#print axioms gramCoeffs_exact
end D4Bound.SphericalSurplusSign.Bernstein16
