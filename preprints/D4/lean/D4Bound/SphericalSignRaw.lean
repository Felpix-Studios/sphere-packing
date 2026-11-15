import D4Bound.SphericalSignPoly3
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSign

noncomputable def rawList (rs : List Ray) (scale : ℤ) (a b t : ℝ) : ℝ :=
  (rs.map (fun r => SphereCertificate.rayKernel r.degree
    (fun x => evalZ r.coeffs x/scale) a b t)).sum

lemma rawList_append (rs ss : List Ray) (scale : ℤ) (a b t : ℝ) :
    rawList (rs++ss) scale a b t=rawList rs scale a b t+rawList ss scale a b t := by
  simp [rawList,List.map_append,List.sum_append]

lemma rawList_kernel (rs : List Ray) (scale : ℤ) (a b t : ℝ) :
    rawList rs scale a b t=SphereCertificate.kernel Finset.univ
      (rayDegree rs) (rayV rs scale) a b t := by
  change _=∑ i : Fin rs.length,
    (fun r : Ray => SphereCertificate.rayKernel r.degree
      (fun x => evalZ r.coeffs x/scale) a b t) rs[i.val]
  exact (Fin.sum_univ_fun_getElem rs _).symm

def blockNum (l : ℕ) (rs : List Ray) : Poly3 := mul3 (radialSum3 rs) (angular3 l)

lemma rawList_scaled (rs : List Ray) (l : ℕ) (scale : ℤ) (hs : scale≠0)
    (hl : rs.all (fun r => r.degree==l)=true) (a b t : ℝ) :
    (scale:ℝ)^2*rawList rs scale a b t =
      (rs.map (fun r => evalZ r.coeffs a*evalZ r.coeffs b)).sum *
        Schoenberg2.solidLegendre (t-a*b) ((1-a^2)*(1-b^2)) l := by
  have hsR : (scale:ℝ)≠0 := by exact_mod_cast hs
  induction rs with
  | nil => simp [rawList]
  | cons r rs ih =>
    have hh : r.degree=l ∧ rs.all (fun r => r.degree==l)=true := by simpa using hl
    have ht := ih hh.2
    simp only [rawList,List.map_cons,List.sum_cons] at ht ⊢
    rw [mul_add,ht]
    unfold SphereCertificate.rayKernel
    rw [hh.1]
    field_simp

lemma eval_blockNum (l : ℕ) (rs : List Ray) (scale : ℤ) (hs : scale≠0)
    (hl : rs.all (fun r => r.degree==l)=true) (a b t : ℝ) :
    eval3 (blockNum l rs) a b t=(Nat.factorial l:ℝ)*(scale:ℝ)^2*rawList rs scale a b t := by
  rw [blockNum,eval_mul3,eval_radialSum3,eval_angular3]
  rw [mul_assoc,rawList_scaled rs l scale hs hl]
  ring

#print axioms eval_blockNum
end D4Bound.SphericalSign
