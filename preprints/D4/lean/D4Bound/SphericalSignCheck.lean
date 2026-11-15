import D4Bound.ScalarCheck

namespace D4Bound.SphericalSign

/-- Polynomial substitution x ↦ c*x, on integer power coefficients. -/
def scaleX (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: rest => a :: ((scaleX c rest).map (c*·))

lemma eval_scaleX (c : ℤ) (p : List ℤ) (x : ℝ) : evalZ (scaleX c p) x = evalZ p ((c : ℝ)*x) := by
  induction p with
  | nil => simp [scaleX,evalZ]
  | cons a p ih => simp only [scaleX,evalZ,evalZ_map_mul,ih]; ring

/-- A positive multiple of -P((p+q)*x/q-1). -/
def normalized (p q : ℤ) (P : List ℤ) : List ℤ := (scaleX (p+q) (comp (-q) q P)).map (- ·)

lemma normalized_value (p q : ℤ) (P : List ℤ) (hq : q ≠ 0) (x : ℝ) :
    (q : ℝ) * evalZ (normalized p q P) x =
      -(q : ℝ)^P.length * evalZ P (((p+q : ℤ) : ℝ)*x/q-1) := by
  have hc := evalZ_comp (-q) q (by exact_mod_cast hq) P (((p+q : ℤ) : ℝ)*x)
  have hn : evalZ (normalized p q P) x = -evalZ (comp (-q) q P) (((p+q : ℤ) : ℝ)*x) := by
    unfold normalized
    have hmap : (scaleX (p+q) (comp (-q) q P)).map (- ·) =
        (scaleX (p+q) (comp (-q) q P)).map ((-1 : ℤ)*·) := by congr 1; funext z; ring
    rw [hmap,evalZ_map_mul,eval_scaleX]; norm_num
  have harg : (((-q : ℤ) : ℝ)+((p+q : ℤ) : ℝ)*x)/(q : ℝ) = ((p+q : ℤ) : ℝ)*x/q-1 := by
    have : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    push_cast; field_simp; ring
  rw [harg] at hc
  rw [hn]
  linear_combination -hc

inductive Tree where
  | leaf
  | split (left right : Tree)
  deriving Repr

def leafOK (P : List ℤ) (a k : ℕ) : Bool := decide (0 ≤ lb 1 (comp a (2^k) P))
def check (P : List ℤ) : ℕ → ℕ → Tree → Bool
  | a,k,.leaf => leafOK P a k
  | a,k,.split l r => check P (2*a) (k+1) l && check P (2*a+1) (k+1) r

lemma leaf_sound (P : List ℤ) (a k : ℕ) (h : leafOK P a k = true) (x : ℝ)
    (hlo : (a : ℝ)/2^k ≤ x) (hhi : x ≤ ((a : ℝ)+1)/2^k) : 0 ≤ evalZ P x := by
  have hnonneg : 0 ≤ lb 1 (comp a (2^k) P) := by simpa [leafOK] using h
  have hD : (0 : ℝ) < 2^k := by positivity
  let w := 2^k*x-a
  have hw0 : 0 ≤ w := by rw [div_le_iff₀ hD] at hlo; dsimp [w]; linarith
  have hw1 : w ≤ (1 : ℤ) := by rw [le_div_iff₀ hD] at hhi; dsimp [w]; norm_num; linarith
  have hb := lb_le 1 (comp a (2^k) P) hw0 hw1
  have hc := evalZ_comp a (2^k) (by positivity) P w
  have harg : ((a : ℤ)+w)/((2^k : ℤ) : ℝ) = x := by push_cast; dsimp [w]; field_simp; ring
  rw [harg] at hc
  have hh : (0 : ℝ) ≤ evalZ (comp a (2^k) P) w := le_trans (by exact_mod_cast hnonneg) hb
  have hp : (0 : ℝ) < ((2^k : ℤ) : ℝ)^P.length := by positivity
  have hprod : (0 : ℝ) ≤ ((2^k : ℤ) : ℝ)^P.length * evalZ P x := by rw [←hc]; exact mul_nonneg (by positivity) hh
  exact nonneg_of_mul_nonneg_right hprod hp

lemma check_sound (tree : Tree) (P : List ℤ) (a k : ℕ) (h : check P a k tree = true) (x : ℝ)
    (hlo : (a : ℝ)/2^k ≤ x) (hhi : x ≤ ((a : ℝ)+1)/2^k) : 0 ≤ evalZ P x := by
  induction tree generalizing a k with
  | leaf => exact leaf_sound P a k h x hlo hhi
  | split l r ihl ihr =>
    simp only [check,Bool.and_eq_true] at h
    have hd : (0 : ℝ) < 2^k := by positivity
    have hleft : ((2*a : ℕ) : ℝ)/2^(k+1) = (a : ℝ)/2^k := by push_cast; rw [pow_succ]; ring
    have hright : (((2*a+1 : ℕ) : ℝ)+1)/2^(k+1) = ((a : ℝ)+1)/2^k := by push_cast; rw [pow_succ]; ring
    by_cases hm : x ≤ ((2*a : ℝ)+1)/2^(k+1)
    · apply ihl (2*a) (k+1) h.1
      · simpa only [hleft] using hlo
      · simpa using hm
    · apply ihr (2*a+1) (k+1) h.2
      · push_cast; exact le_of_lt (lt_of_not_ge hm)
      · simpa only [hright] using hhi

lemma raw_nonpos_of_checked (P : List ℤ) (p q : ℤ) (hq : 0 < q) (hw : 0 < p+q) (tree : Tree)
    (h : check (normalized p q P) 0 0 tree = true) (t : ℝ) (hlo : -1 ≤ t) (hhi : t ≤ (p : ℝ)/q) :
    evalZ P t ≤ 0 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hwR : (0 : ℝ) < ((p+q : ℤ) : ℝ) := by exact_mod_cast hw
  let x := ((q : ℝ)*t+q)/((p+q : ℤ) : ℝ)
  have hx0 : 0 ≤ x := div_nonneg (by nlinarith) hwR.le
  have hx1 : x ≤ 1 := by
    apply (div_le_one hwR).mpr
    rw [le_div_iff₀ hqR] at hhi
    push_cast; nlinarith
  have hn := check_sound tree (normalized p q P) 0 0 h x (by simpa using hx0) (by simpa using hx1)
  have hv := normalized_value p q P (ne_of_gt hq) x
  have ha : ((p+q : ℤ) : ℝ)*x/(q : ℝ)-1 = t := by
    dsimp [x]; field_simp; ring
  rw [ha] at hv
  have hp : (0 : ℝ) < (q : ℝ)^P.length := pow_pos hqR _
  have hh : (q : ℝ)^P.length * evalZ P t ≤ 0 := by nlinarith [mul_nonneg hqR.le hn]
  exact nonpos_of_mul_nonpos_right hh hp

end D4Bound.SphericalSign
