"""Generate the stronger first-cell pair upper q<=-7/100000 for cyclic signs."""
from gen_v7_pair_sign import *

def emit_margin():
    K=Kernel(D4/'data/v7');D=K.pair_poly(0);D[0]+=Q(7,100000)
    T=[Q(0)]*49
    for i in range(25):T[2*i]=Q(2**i,factorial(i))
    P=flint.fmpq_poly(list(map(fq,K.F_of_alpha_r2())))+flint.fmpq_poly(list(map(fq,D)))*flint.fmpq_poly(list(map(fq,T)))
    lo,hi=K.breaks[:2]
    out=['import D4Bound.V7PairPolynomialTrim\nimport D4Bound.V7PairSignData0\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 8192\nset_option Elab.async false\n\nnamespace D4Bound.V7.PairMarginData\nopen PairPoly PairSignData\n']
    out.append('def pairMargin0 : Poly := PairPoly.add pairD0 [7/100000]\n')
    for name,cs in [('marginD0',[-c for c in D]),('marginP0',[-qf(c) for c in P.coeffs()])]:
        z,den=normalized(cs,lo,hi);leaves=chain(z)
        out.append(f'def {name} : List ℤ := {z}\n')
        out.append(f'def {name}Den : ℕ := {den}\n')
        ss='['+', '.join('('+','.join(map(str,c))+')' for c in leaves)+']'
        out.append(f'def {name}Chain : List (ℕ × ℕ × ℕ) := {ss}\n')
        A,k,h=leaves[-1]
        out.append(f'''theorem {name}_positive (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < evalZ {name} x := by
  by_cases hx : x < 1
  · exact chainOK_sound {name} {name}Chain 0 0 1 0 (by decide +kernel) x
      (by simpa using hx0) (by simpa using hx)
  · have he : x = 1 := by linarith
    subst x
    exact leafOK_sound (P := {name}) (A := {A}) (k := {k}) (h := {h})
      (by decide +kernel) 1 (by norm_num) (by norm_num)
''')
    affine='['+lean_rational(lo)+', '+lean_rational(hi-lo)+']'
    out.append(f'''theorem marginD0_identity : PairPoly.trim (PairPoly.comp pairMargin0 {affine}) =
    PairPoly.trim (PairPoly.scale (-1/(marginD0Den : ℚ)) (marginD0.map Int.cast)) := by decide +kernel

theorem marginP0_identity : PairPoly.trim (PairPoly.comp (PairPoly.add (PairPoly.comp Fq [0,0,2]) (PairPoly.mul pairMargin0 (PairPoly.taylor 25))) {affine}) =
    PairPoly.trim (PairPoly.scale (-1/(marginP0Den : ℚ)) (marginP0.map Int.cast)) := by decide +kernel

end D4Bound.V7.PairMarginData
''')
    (HERE.parent/'D4Bound/V7PairMarginData0.lean').write_text('\n'.join(out))

if __name__=='__main__':emit_margin()
