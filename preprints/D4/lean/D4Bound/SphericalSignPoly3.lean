import D4Bound.SphericalSignPoly
set_option maxHeartbeats 0
set_option Elab.async false
/-! Executable integer Horner polynomials in three variables, with evaluation
soundness proved algebraically. No external arithmetic acceptance is used. -/
namespace D4Bound.SphericalSign

def addH {α : Type*} (add : α → α → α) : List α → List α → List α
  | [],q => q
  | p,[] => p
  | a::p,b::q => add a b::addH add p q

def mulH {α : Type*} (zero : α) (add mul : α → α → α) : List α → List α → List α
  | [],_ => []
  | a::p,q => addH add (q.map (mul a)) (zero::mulH zero add mul p q)

noncomputable def evalH {α : Type*} (f : α → ℝ) (x : ℝ) : List α → ℝ
  | [] => 0
  | a::p => f a+x*evalH f x p

lemma evalH_add {α : Type*} (add : α → α → α) (f : α → ℝ)
    (hf : ∀ a b, f (add a b)=f a+f b) (p q : List α) (x : ℝ) :
    evalH f x (addH add p q)=evalH f x p+evalH f x q := by
  induction p generalizing q with
  | nil => simp [addH,evalH]
  | cons a p ih =>
    cases q with
    | nil => simp [addH,evalH]
    | cons b q => simp only [addH,evalH,hf,ih]; ring

lemma evalH_map {α : Type*} (f : α → ℝ) (g : α → α) (c : ℝ)
    (hf : ∀ a, f (g a)=c*f a) (p : List α) (x : ℝ) :
    evalH f x (p.map g)=c*evalH f x p := by
  induction p with
  | nil => simp [evalH]
  | cons a p ih => simp only [List.map_cons,evalH,hf,ih]; ring

lemma evalH_mul {α : Type*} (zero : α) (add mul : α → α → α) (f : α → ℝ)
    (hz : f zero=0) (ha : ∀ a b, f (add a b)=f a+f b)
    (hm : ∀ a b, f (mul a b)=f a*f b) (p q : List α) (x : ℝ) :
    evalH f x (mulH zero add mul p q)=evalH f x p*evalH f x q := by
  induction p with
  | nil => simp [mulH,evalH]
  | cons a p ih =>
    rw [mulH,evalH_add add f ha,evalH_map f (mul a) (f a) (hm a)]
    simp only [evalH,hz,ih]
    ring

abbrev Poly2 := List (List ℤ)
abbrev Poly3 := List Poly2
def add2 : Poly2 → Poly2 → Poly2 := addH addL
def mul2 : Poly2 → Poly2 → Poly2 := mulH [] addL mulP
def add3 : Poly3 → Poly3 → Poly3 := addH add2
def mul3 : Poly3 → Poly3 → Poly3 := mulH [] add2 mul2
noncomputable def eval2 (p : Poly2) (x y : ℝ) : ℝ := evalH (fun c => evalZ c y) x p
noncomputable def eval3 (p : Poly3) (x y z : ℝ) : ℝ := evalH (fun c => eval2 c y z) x p

lemma eval_add2 (p q : Poly2) (x y : ℝ) : eval2 (add2 p q) x y=eval2 p x y+eval2 q x y :=
  evalH_add addL (fun c => evalZ c y) (fun a b => evalZ_addL a b y) p q x
lemma eval_mul2 (p q : Poly2) (x y : ℝ) : eval2 (mul2 p q) x y=eval2 p x y*eval2 q x y :=
  evalH_mul [] addL mulP (fun c => evalZ c y) rfl (fun a b => evalZ_addL a b y)
    (fun a b => eval_mulP a b y) p q x
lemma eval_add3 (p q : Poly3) (x y z : ℝ) : eval3 (add3 p q) x y z=eval3 p x y z+eval3 q x y z :=
  evalH_add add2 (fun c => eval2 c y z) (fun a b => eval_add2 a b y z) p q x
lemma eval_mul3 (p q : Poly3) (x y z : ℝ) : eval3 (mul3 p q) x y z=eval3 p x y z*eval3 q x y z :=
  evalH_mul [] add2 mul2 (fun c => eval2 c y z) rfl (fun a b => eval_add2 a b y z)
    (fun a b => eval_mul2 a b y z) p q x

def smul3 (a : ℤ) (p : Poly3) : Poly3 := p.map (fun q => q.map (fun r => r.map (a*·)))
lemma eval_smul3 (a : ℤ) (p : Poly3) (x y z : ℝ) :
    eval3 (smul3 a p) x y z=(a:ℝ)*eval3 p x y z := by
  apply evalH_map
  intro q
  apply evalH_map
  intro r
  exact evalZ_map_mul a r z

def one3 : Poly3 := [[[1]]]
def u3 : Poly3 := [[[0,1]],[[0],[-1]]]
def v3 : Poly3 := [[[1],[0],[-1]],[],[[-1],[0],[1]]]
lemma eval_one3 (x y z : ℝ) : eval3 one3 x y z=1 := by norm_num [one3,eval3,eval2,evalH,evalZ]
lemma eval_u3 (x y z : ℝ) : eval3 u3 x y z=z-x*y := by norm_num [u3,eval3,eval2,evalH,evalZ]; ring
lemma eval_v3 (x y z : ℝ) : eval3 v3 x y z=(1-x^2)*(1-y^2) := by norm_num [v3,eval3,eval2,evalH,evalZ]; ring

/-- `l!` times the solid Legendre polynomial; division-free recurrence. -/
def angular3 : ℕ → Poly3
  | 0 => one3
  | 1 => u3
  | l+2 => add3 (smul3 (2*(l:ℤ)+3) (mul3 u3 (angular3 (l+1))))
      (smul3 (-((l:ℤ)+1)^2) (mul3 v3 (angular3 l)))

lemma eval_angular3 (x y z : ℝ) : ∀ l,
    eval3 (angular3 l) x y z=(Nat.factorial l:ℝ)*Schoenberg2.solidLegendre (z-x*y) ((1-x^2)*(1-y^2)) l
  | 0 => by simp [angular3,eval_one3,Schoenberg2.solidLegendre]
  | 1 => by simp [angular3,eval_u3,Schoenberg2.solidLegendre]
  | l+2 => by
    rw [angular3,eval_add3,eval_smul3,eval_smul3,eval_mul3,eval_mul3,
      eval_u3,eval_v3,eval_angular3 x y z (l+1),eval_angular3 x y z l,
      Schoenberg2.solidLegendre]
    have h : (l:ℝ)+2≠0 := by positivity
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_natCast,Int.cast_ofNat]
    field_simp
    ring

def outer3 (p q : List ℤ) : Poly3 := p.map (fun a => q.map (fun b => [a*b]))
lemma eval_outer3 (p q : List ℤ) (x y z : ℝ) :
    eval3 (outer3 p q) x y z=evalZ p x*evalZ q y := by
  have hq (a : ℤ) : eval2 (q.map (fun b => [a*b])) y z=(a:ℝ)*evalZ q y := by
    induction q with
    | nil => simp [eval2,evalH,evalZ]
    | cons b q ih => simp only [List.map_cons,eval2,evalH,evalZ,Int.cast_mul] at *; rw [ih]; ring
  induction p with
  | nil => simp [outer3,eval3,evalH,evalZ]
  | cons a p ih => simp only [outer3,List.map_cons,eval3,evalH,evalZ] at *; rw [hq,ih]; ring

def radialSum3 : List Ray → Poly3
  | [] => []
  | r::rs => add3 (outer3 r.coeffs r.coeffs) (radialSum3 rs)

lemma eval_radialSum3 (rs : List Ray) (x y z : ℝ) :
    eval3 (radialSum3 rs) x y z=(rs.map (fun r => evalZ r.coeffs x*evalZ r.coeffs y)).sum := by
  induction rs with
  | nil => simp [radialSum3,eval3,evalH]
  | cons r rs ih => simp only [radialSum3,eval_add3,eval_outer3,ih,List.map_cons,List.sum_cons]

#print axioms eval_angular3
end D4Bound.SphericalSign
