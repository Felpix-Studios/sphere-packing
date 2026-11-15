import D4Bound.SphericalSignPoly
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSign

def originZ (r : Ray) : ℤ := if r.degree=0 then r.originNum else 0

def rayPairNum (r : Ray) (sd od fd : ℤ) : List ℤ :=
  addL (r.coeffs.map ((2*originZ r*sd*fd)*·)) ((diagP r).map ((sd*od)*·))

def pairNum (scalar : List ℤ) (rays : List Ray) (sd od fd : ℤ) : List ℤ :=
  addL (scalar.map ((od*fd^2)*·)) (sumP (rays.map (fun r => rayPairNum r sd od fd)))

noncomputable def rawRayPair (r : Ray) (od fd : ℤ) (x : ℝ) : ℝ :=
  2*SphereCertificate.rayOrigin r.degree (r.originNum/od)*(evalZ r.coeffs x/fd) +
    SphereCertificate.rayKernel r.degree (fun a => evalZ r.coeffs a/fd) x x 1

lemma originZ_cast (r : Ray) (od : ℤ) :
    SphereCertificate.rayOrigin r.degree (r.originNum/od) = (originZ r:ℝ)/od := by
  simp only [originZ,SphereCertificate.rayOrigin]
  split_ifs <;> simp

lemma eval_rayPairNum (r : Ray) (sd od fd : ℤ) (hod : od≠0) (hfd : fd≠0) (x : ℝ) :
    evalZ (rayPairNum r sd od fd) x = (sd:ℝ)*od*fd^2*rawRayPair r od fd x := by
  rw [rayPairNum,evalZ_addL,evalZ_map_mul,evalZ_map_mul]
  simp only [rawRayPair,rayKernel_diag,originZ_cast]
  have hodR : (od:ℝ)≠0 := by exact_mod_cast hod
  have hfdR : (fd:ℝ)≠0 := by exact_mod_cast hfd
  push_cast
  field_simp

lemma eval_pairNum (scalar : List ℤ) (rays : List Ray) (sd od fd : ℤ)
    (hsd : sd≠0) (hod : od≠0) (hfd : fd≠0) (x : ℝ) :
    evalZ (pairNum scalar rays sd od fd) x = (sd:ℝ)*od*fd^2 *
      (evalZ scalar x/sd + (rays.map (fun r => rawRayPair r od fd x)).sum) := by
  have hs : evalZ (sumP (rays.map (fun r => rayPairNum r sd od fd))) x =
      (sd:ℝ)*od*fd^2*(rays.map (fun r => rawRayPair r od fd x)).sum := by
    induction rays with
    | nil => simp [sumP,evalZ]
    | cons r rs ih =>
      simp only [List.map_cons,sumP,evalZ_addL,eval_rayPairNum r sd od fd hod hfd,ih,List.sum_cons]
      ring
  rw [pairNum,evalZ_addL,evalZ_map_mul,hs]
  have hsdR : (sd:ℝ)≠0 := by exact_mod_cast hsd
  push_cast
  field_simp

lemma rawPair_list (scalar : ℝ → ℝ) (rays : List Ray) (od fd : ℤ) (x : ℝ) :
    scalar x + 2*SphereCertificate.coupling Finset.univ (rayDegree rays)
      (rayO rays od) (rayV rays fd) x +
      SphereCertificate.kernel Finset.univ (rayDegree rays) (rayV rays fd) x x 1 =
    scalar x + (rays.map (fun r => rawRayPair r od fd x)).sum := by
  change scalar x + 2*(∑ i : Fin rays.length,
      (fun r : Ray => SphereCertificate.rayOrigin r.degree (r.originNum/od)*(evalZ r.coeffs x/fd)) rays[i.val]) +
      (∑ i : Fin rays.length, (fun r : Ray => SphereCertificate.rayKernel r.degree (fun a => evalZ r.coeffs a/fd) x x 1) rays[i.val]) = _
  rw [Fin.sum_univ_fun_getElem rays (fun r => SphereCertificate.rayOrigin r.degree (r.originNum/od)*(evalZ r.coeffs x/fd)),
    Fin.sum_univ_fun_getElem rays (fun r => SphereCertificate.rayKernel r.degree (fun a => evalZ r.coeffs a/fd) x x 1)]
  have hsum : (rays.map (fun r => rawRayPair r od fd x)).sum =
      2*(rays.map (fun r => SphereCertificate.rayOrigin r.degree (r.originNum/od)*(evalZ r.coeffs x/fd))).sum +
        (rays.map (fun r => SphereCertificate.rayKernel r.degree (fun a => evalZ r.coeffs a/fd) x x 1)).sum := by
    induction rays with
    | nil => simp
    | cons r rs ih => simp only [List.map_cons,List.sum_cons,rawRayPair] at *; rw [ih]; ring
  rw [hsum]
  ring

lemma rawPair_nonpos_of_identity (scalar p : List ℤ) (rays : List Ray) (sd od fd pd : ℤ)
    (hsd : 0<sd) (hod : 0<od) (hfd : 0<fd) (hpd : 0<pd)
    (hid : p.map ((sd*od*fd^2)*·) = (pairNum scalar rays sd od fd).map (pd*·))
    (x : ℝ) (hP : evalZ p x≤0) :
    evalZ scalar x/sd + 2*SphereCertificate.coupling Finset.univ (rayDegree rays)
      (rayO rays od) (rayV rays fd) x +
      SphereCertificate.kernel Finset.univ (rayDegree rays) (rayV rays fd) x x 1 ≤ 0 := by
  rw [rawPair_list (fun a => evalZ scalar a/sd)]
  have he := congrArg (fun q => evalZ q x) hid
  simp only [evalZ_map_mul,Int.cast_mul,Int.cast_pow] at he
  rw [eval_pairNum scalar rays sd od fd (ne_of_gt hsd) (ne_of_gt hod) (ne_of_gt hfd)] at he
  have hsdR : (0:ℝ)<sd := by exact_mod_cast hsd
  have hodR : (0:ℝ)<od := by exact_mod_cast hod
  have hfdR : (0:ℝ)<fd := by exact_mod_cast hfd
  have hpdR : (0:ℝ)<pd := by exact_mod_cast hpd
  have hC : (0:ℝ)<(sd:ℝ)*od*fd^2 := by positivity
  have hh := mul_nonpos_of_nonneg_of_nonpos hC.le hP
  rw [he] at hh
  have h1 := nonpos_of_mul_nonpos_right hh hpdR
  exact nonpos_of_mul_nonpos_right h1 hC

end D4Bound.SphericalSign
