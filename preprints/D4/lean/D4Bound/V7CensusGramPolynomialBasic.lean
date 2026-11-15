import D4Bound.CensusEnvelope

/-! Algebraic coefficient expansion for the actual five-count projection.
Finite rational coefficient identities are checked in separate modules. -/
namespace D4Bound.V7.CensusGram
open CensusArithmetic

def projectionEval {A : Type*} [CommRing A] (c : ℕ → A) (n : ℕ → A) : A :=
  c 0 + 2*(c 1*n 0+c 2*n 1+c 3*n 2+c 4*n 3+c 5*n 4) +
  c 6*n 0*n 0+2*c 7*n 0*n 1+2*c 8*n 0*n 2+2*c 9*n 0*n 3+2*c 10*n 0*n 4+
  c 11*n 1*n 1+2*c 12*n 1*n 2+2*c 13*n 1*n 3+2*c 14*n 1*n 4+
  c 15*n 2*n 2+2*c 16*n 2*n 3+2*c 17*n 2*n 4+
  c 18*n 3*n 3+2*c 19*n 3*n 4+c 20*n 4*n 4

def countsAt (v : Counts) : ℕ → ℕ :=
  fun i => [v.n0,v.n1,v.n2,v.n3,v.n4].getD i 0

theorem projectionEval_congr {A : Type*} [CommRing A] (c d n : ℕ → A)
    (h : ∀ i, i < 21 → c i = d i) : projectionEval c n = projectionEval d n := by
  unfold projectionEval
  rw [h 0 (by omega),h 1 (by omega),h 2 (by omega),h 3 (by omega),h 4 (by omega),
    h 5 (by omega),h 6 (by omega),h 7 (by omega),h 8 (by omega),h 9 (by omega),
    h 10 (by omega),h 11 (by omega),h 12 (by omega),h 13 (by omega),
    h 14 (by omega),h 15 (by omega),h 16 (by omega),h 17 (by omega),
    h 18 (by omega),h 19 (by omega),h 20 (by omega)]

theorem projectionPart_eval (v : Counts) :
    projectionPart v = projectionEval
      (fun i => ((totalCoeffs[i]! : ℝ)-(countCoeffs[i]! : ℝ))/(denominator : ℝ))
      (fun i => (countsAt v i : ℝ)) := by
  unfold projectionPart projectionEval quadratic countsAt
  simp only [List.getD_cons_zero,List.getD_cons_succ]
  push_cast
  ring

def matrixProjection {A : Type*} [CommRing A]
    (G : ℕ → ℕ → A) (o n : ℕ → A) : A :=
  ((List.range 5).map fun j => ((List.range 5).map fun k =>
    (n j+o j)*G j k*(n k+o k)).sum).sum

def projectionCoefficients {A : Type*} [CommRing A]
    (G : ℕ → ℕ → A) (o : ℕ → A) : ℕ → A :=
  fun i => [matrixProjection G o (fun _ => 0),
    ((List.range 5).map fun k => G 0 k*o k).sum,
    ((List.range 5).map fun k => G 1 k*o k).sum,
    ((List.range 5).map fun k => G 2 k*o k).sum,
    ((List.range 5).map fun k => G 3 k*o k).sum,
    ((List.range 5).map fun k => G 4 k*o k).sum,
    G 0 0,G 0 1,G 0 2,G 0 3,G 0 4,G 1 1,G 1 2,G 1 3,G 1 4,
    G 2 2,G 2 3,G 2 4,G 3 3,G 3 4,G 4 4].getD i 0

theorem matrixProjection_expand {A : Type*} [CommRing A]
    (G : ℕ → ℕ → A) (o n : ℕ → A)
    (hs : ∀ j k, j < 5 → k < 5 → G j k = G k j) :
    matrixProjection G o n = projectionEval (projectionCoefficients G o) n := by
  unfold matrixProjection projectionEval projectionCoefficients
  simp only [matrixProjection,List.range_succ,List.range_zero,List.cons_append,
    List.nil_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,List.getD_cons_zero,List.getD_cons_succ]
  rw [hs 1 0 (by omega) (by omega),hs 2 0 (by omega) (by omega),
    hs 2 1 (by omega) (by omega),hs 3 0 (by omega) (by omega),
    hs 3 1 (by omega) (by omega),hs 3 2 (by omega) (by omega),
    hs 4 0 (by omega) (by omega),hs 4 1 (by omega) (by omega),
    hs 4 2 (by omega) (by omega),hs 4 3 (by omega) (by omega)]
  ring

end D4Bound.V7.CensusGram
