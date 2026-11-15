"""Generate pair-margin data q <= -m on radial pieces 1 and 2 (cyclic gauge credit).

Same certificate format as gen_v7_pair_margin.py (piece 0). Usage:
  python3 gen_v7_pair_margin_more.py
"""
from gen_v7_pair_sign import *

MARGINS = {1: Q(75, 10000000), 2: Q(281, 100000), 3: Q(5, 10000000), 4: Q(8, 10000000), 5: Q(11, 10000000)}

def emit(p, m):
    K=Kernel(D4/'data/v7');D=K.pair_poly(p);D[0]+=m
    T=[Q(0)]*49
    for i in range(25):T[2*i]=Q(2**i,factorial(i))
    P=flint.fmpq_poly(list(map(fq,K.F_of_alpha_r2())))+flint.fmpq_poly(list(map(fq,D)))*flint.fmpq_poly(list(map(fq,T)))
    lo,hi=K.breaks[p:p+2]
    out=[f'import D4Bound.V7PairPolynomialTrim\nimport D4Bound.V7PairSignData{p if p<2 else "Rest"}\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 8192\nset_option Elab.async false\n\nnamespace D4Bound.V7.PairMarginData\nopen PairPoly PairSignData\n']
    out.append(f'def pairMargin{p} : Poly := PairPoly.add pairD{p} [{lean_rational(m)}]\n')
    for name,cs in [(f'marginD{p}',[-c for c in D]),(f'marginP{p}',[-qf(c) for c in P.coeffs()])]:
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
    out.append(f'''theorem marginD{p}_identity : PairPoly.trim (PairPoly.comp pairMargin{p} {affine}) =
    PairPoly.trim (PairPoly.scale (-1/(marginD{p}Den : ℚ)) (marginD{p}.map Int.cast)) := by decide +kernel

theorem marginP{p}_identity : PairPoly.trim (PairPoly.comp (PairPoly.add (PairPoly.comp Fq [0,0,2]) (PairPoly.mul pairMargin{p} (PairPoly.taylor 25))) {affine}) =
    PairPoly.trim (PairPoly.scale (-1/(marginP{p}Den : ℚ)) (marginP{p}.map Int.cast)) := by decide +kernel

end D4Bound.V7.PairMarginData
''')
    (HERE.parent/f'D4Bound/V7PairMarginData{p}.lean').write_text('\n'.join(out))

if __name__=='__main__':
    for p,m in MARGINS.items(): emit(p,m)
