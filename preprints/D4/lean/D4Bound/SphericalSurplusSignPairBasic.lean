import D4Bound.SphericalSignPair

set_option maxHeartbeats 0
set_option Elab.async false

namespace D4Bound.SphericalSurplusSign
open SphericalSign

def correctedPairNum (scalar correction : List ℤ) (rays : List Ray)
    (sd od fd cd : ℤ) : List ℤ :=
  addL ((pairNum scalar rays sd od fd).map (cd*·))
    (correction.map ((sd*od*fd^2)*·))

lemma corrected_pair_nonpos (scalar correction p : List ℤ) (rays : List Ray)
    (sd od fd cd pd : ℤ)
    (hsd : 0<sd) (hod : 0<od) (hfd : 0<fd) (hcd : 0<cd) (hpd : 0<pd)
    (hid : p.map ((sd*od*fd^2*cd)*·) =
      (correctedPairNum scalar correction rays sd od fd cd).map (pd*·))
    (x : ℝ) (hP : evalZ p x ≤ 0) :
    evalZ scalar x/sd +
      2*SphereCertificate.coupling Finset.univ (rayDegree rays)
        (rayO rays od) (rayV rays fd) x +
      SphereCertificate.kernel Finset.univ (rayDegree rays) (rayV rays fd) x x 1 +
      evalZ correction x/cd ≤ 0 := by
  rw [rawPair_list (fun a => evalZ scalar a/sd)]
  have he := congrArg (fun q => evalZ q x) hid
  simp only [correctedPairNum,evalZ_addL,evalZ_map_mul,Int.cast_mul,Int.cast_pow] at he
  rw [eval_pairNum scalar rays sd od fd (ne_of_gt hsd) (ne_of_gt hod) (ne_of_gt hfd)] at he
  have hsdR : (0:ℝ)<sd := by exact_mod_cast hsd
  have hodR : (0:ℝ)<od := by exact_mod_cast hod
  have hfdR : (0:ℝ)<fd := by exact_mod_cast hfd
  have hcdR : (0:ℝ)<cd := by exact_mod_cast hcd
  have hpdR : (0:ℝ)<pd := by exact_mod_cast hpd
  have hC : (0:ℝ)<(sd:ℝ)*od*fd^2 := by positivity
  have hp := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hC.le hcdR.le) hP
  rw [he] at hp
  have h1 := nonpos_of_mul_nonpos_right hp hpdR
  have h2 : (sd:ℝ)*od*fd^2*((cd:ℝ)*
      (evalZ scalar x/sd + (rays.map (fun r => rawRayPair r od fd x)).sum) +
      evalZ correction x) ≤ 0 := by nlinarith
  have h3 := nonpos_of_mul_nonpos_right h2 hC
  have h4 : (cd:ℝ)*
      (evalZ scalar x/sd + (rays.map (fun r => rawRayPair r od fd x)).sum +
      evalZ correction x/cd) ≤ 0 := by
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hcdR)]
    exact h3
  exact nonpos_of_mul_nonpos_right h4 hcdR

#print axioms corrected_pair_nonpos
end D4Bound.SphericalSurplusSign
