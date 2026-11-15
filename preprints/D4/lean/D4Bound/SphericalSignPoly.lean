import D4Bound.SphericalSignRays
import D4Bound.SphericalCertAngular
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSign

def mulP : List ℤ → List ℤ → List ℤ
  | [],_ => []
  | a::p,q => addL (q.map (a*·)) (0::mulP p q)

lemma eval_mulP (p q : List ℤ) (x : ℝ) : evalZ (mulP p q) x = evalZ p x*evalZ q x := by
  induction p with
  | nil => simp [mulP,evalZ]
  | cons a p ih => simp only [mulP,evalZ_addL,evalZ_map_mul,evalZ,ih]; ring

def powP (p : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n+1 => mulP p (powP p n)
lemma eval_powP (p : List ℤ) (n : ℕ) (x : ℝ) : evalZ (powP p n) x = (evalZ p x)^n := by
  induction n with
  | zero => simp [powP,evalZ]
  | succ n ih => simp [powP,eval_mulP,ih,pow_succ,mul_comm]

def sumP : List (List ℤ) → List ℤ
  | [] => []
  | p::ps => addL p (sumP ps)
lemma eval_sumP (ps : List (List ℤ)) (x : ℝ) : evalZ (sumP ps) x = (ps.map (fun p => evalZ p x)).sum := by
  induction ps with
  | nil => simp [sumP,evalZ]
  | cons p ps ih => simp [sumP,evalZ_addL,ih]

def diagP (r : Ray) : List ℤ := mulP (mulP r.coeffs r.coeffs) (powP [1,0,-1] r.degree)
lemma eval_diagP (r : Ray) (x : ℝ) : evalZ (diagP r) x = (evalZ r.coeffs x)^2*(1-x^2)^r.degree := by
  simp only [diagP,eval_mulP,eval_powP,evalZ]
  have he : (1:ℝ)+x*(0+x*(-1+x*0))=1-x^2 := by ring
  norm_num only [Int.cast_one,Int.cast_zero,Int.cast_neg]
  rw [he]
  ring

lemma solidLegendre_diag (u : ℝ) : ∀ l : ℕ, Schoenberg2.solidLegendre u (u^2) l = u^l
  | 0 => by simp [Schoenberg2.solidLegendre]
  | 1 => by simp [Schoenberg2.solidLegendre]
  | l+2 => by
    rw [Schoenberg2.solidLegendre,solidLegendre_diag u (l+1),solidLegendre_diag u l]
    have hn : (l:ℝ)+2 ≠ 0 := by positivity
    rw [pow_succ,pow_succ]
    field_simp
    ring

lemma rayKernel_diag (r : Ray) (scale : ℤ) (x : ℝ) :
    SphereCertificate.rayKernel r.degree (fun a => evalZ r.coeffs a/scale) x x 1 =
      evalZ (diagP r) x/(scale:ℝ)^2 := by
  unfold SphereCertificate.rayKernel
  have h1 : 1-x*x=1-x^2 := by ring
  have h2 : (1-x^2)*(1-x^2)=(1-x^2)^2 := by ring
  rw [h1,h2,solidLegendre_diag,eval_diagP]
  ring

end D4Bound.SphericalSign
