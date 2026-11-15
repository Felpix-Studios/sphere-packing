import D4Bound.CountDomain

/-!
Finite-domain checker for the D4 count census. Its Boolean evaluation is certified
by the Lean kernel, not imported from a Python acceptance report. The separate
analytic statement that the concrete kernel energy dominates the evaluated
formula is deliberately not claimed by this arithmetic module.
-/
namespace D4Bound.CensusArithmetic

structure Counts where
  n0 : ℕ
  n1 : ℕ
  n2 : ℕ
  n3 : ℕ
  n4 : ℕ
  deriving DecidableEq, Repr

def Valid (v : Counts) : Prop :=
  v.n0 ≤ v.n1 ∧ v.n1 ≤ v.n2 ∧ v.n2 ≤ v.n3 ∧ v.n3 ≤ v.n4 ∧
  v.n2 ≤ 24 ∧ v.n3 ≤ 25 ∧ v.n4 ≤ 26 ∧
  (v.n0 = 24 → v.n4 = 24) ∧ (v.n1 = 24 → v.n3 = 24)

instance (v : Counts) : Decidable (Valid v) := inferInstanceAs (Decidable (_ ∧ _))

def first (v : Counts) : ℕ :=
  if v.n0 = v.n4 then 1 else if v.n1 = v.n4 then 2
  else if v.n2 = v.n4 then 3 else if v.n3 = v.n4 then 4 else 5

def allAt (N : ℕ) (test : Counts → Bool) : Bool :=
  (List.range (min N 25 + 1)).all fun n3 =>
  (List.range (min n3 24 + 1)).all fun n2 =>
  (List.range (n2 + 1)).all fun n1 =>
  (List.range (n1 + 1)).all fun n0 =>
    if (n0 = 24 → N = 24) ∧ (n1 = 24 → n3 = 24)
    then test ⟨n0,n1,n2,n3,N⟩ else true

/-- A small independently reducible census block. Splitting the proof here bounds
the memory used by kernel evaluation without changing the enumerated domain. -/
def atPair (N n3 n2 : ℕ) (test : Counts → Bool) : Bool :=
  (List.range (n2 + 1)).all fun n1 =>
  (List.range (n1 + 1)).all fun n0 =>
    if (n0 = 24 → N = 24) ∧ (n1 = 24 → n3 = 24)
    then test ⟨n0,n1,n2,n3,N⟩ else true

/-- A block of at most eight consecutive values of the second inner count.
This bounds reduction memory for the largest census cases. -/
def atPairChunk (N n3 n2 block : ℕ) (test : Counts → Bool) : Bool :=
  (List.range 8).all fun k =>
    let n1 := 8*block+k
    if n1 ≤ n2 then
      (List.range (n1+1)).all fun n0 =>
        if (n0 = 24 → N = 24) ∧ (n1 = 24 → n3 = 24)
        then test ⟨n0,n1,n2,n3,N⟩ else true
    else true

theorem atPair_of_chunks {N n3 n2 : ℕ} {test : Counts → Bool} (hn2 : n2 ≤ 24)
    (h : ∀ block, block < 4 → atPairChunk N n3 n2 block test = true) :
    atPair N n3 n2 test = true := by
  simp only [atPair, List.all_eq_true]
  intro n1 h1 n0 h0
  have h1le : n1 ≤ n2 := by simpa only [List.mem_range, Nat.lt_succ_iff] using h1
  have hc := h (n1/8) (by omega)
  simp only [atPairChunk, List.all_eq_true] at hc
  have hk : n1%8 ∈ List.range 8 := by simp only [List.mem_range]; omega
  have hh := hc (n1%8) hk
  have he : 8*(n1/8)+n1%8 = n1 := by omega
  simp only [he, if_pos h1le, List.all_eq_true] at hh
  exact hh n0 h0

theorem allAt_of_pairs {N : ℕ} {test : Counts → Bool}
    (h : ∀ n3, n3 ≤ min N 25 → ∀ n2, n2 ≤ min n3 24 →
      atPair N n3 n2 test = true) : allAt N test = true := by
  simp only [allAt, List.all_eq_true]
  intro n3 h3 n2 h2
  have hr := h n3 (by simpa only [List.mem_range, Nat.lt_succ_iff] using h3)
    n2 (by simpa only [List.mem_range, Nat.lt_succ_iff] using h2)
  simpa only [atPair, List.all_eq_true] using hr

theorem allAt_sound {N : ℕ} {test : Counts → Bool} (h : allAt N test = true)
    (v : Counts) (hv : Valid v) (hN : v.n4 = N) : test v = true := by
  rcases v with ⟨n0,n1,n2,n3,n4⟩
  simp only at hN
  subst n4
  dsimp only [Valid] at hv
  rcases hv with ⟨h01,h12,h23,h34,h2,h3,h4,ha,hb⟩
  simp only [allAt, List.all_eq_true] at h
  have hm3 : n3 ∈ List.range (min N 25 + 1) := by
    simp only [List.mem_range]; omega
  have hm2 : n2 ∈ List.range (min n3 24 + 1) := by
    simp only [List.mem_range]; omega
  have hm1 : n1 ∈ List.range (n2 + 1) := by simp; omega
  have hm0 : n0 ∈ List.range (n1 + 1) := by simp; omega
  have hh := h n3 hm3 n2 hm2 n1 hm1 n0 hm0
  have hc : (n0 = 24 → N = 24) ∧ (n1 = 24 → n3 = 24) := ⟨ha,hb⟩
  simpa only [if_pos hc] using hh

noncomputable def ofNeighbourhood (X : Finset E4) : Counts :=
  ⟨countWithin X R1, countWithin X R2, countWithin X R3,
    countWithin X R4, nearCount X⟩

@[simp] theorem first_ofNeighbourhood (X : Finset E4) :
    first (ofNeighbourhood X) = firstRadius X := rfl

theorem valid_of_countDomain {a b c d e : ℕ} (h : CountDomain a b c d e) :
    Valid ⟨a,b,c,d,e⟩ := by
  rcases h with ⟨hab,hbc,hcd,hde,ha,hb,hc,hd,he,hac,hbd⟩
  refine ⟨hab,hbc,hcd,hde,hc,hd,he,?_,?_⟩
  · intro ha24
    change a = 24 at ha24
    change e = 24
    subst a
    norm_num at hac
    omega
  · intro hb24
    change b = 24 at hb24
    change d = 24
    subst b
    norm_num at hbd
    omega

theorem ofNeighbourhood_valid {X : Finset E4} (h : InCountDomain X) :
    Valid (ofNeighbourhood X) := valid_of_countDomain h

end D4Bound.CensusArithmetic
