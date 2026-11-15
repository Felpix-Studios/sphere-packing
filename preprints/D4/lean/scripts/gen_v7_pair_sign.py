"""Exact univariate diagnostic/certificate generation for the ungauged pair upper.

The retained upper drops nonnegative self corrections and restores truncated
cap weights. Certificates prove -D and -(F(2r^2)+D*T_N(2r^2)) positive on each
piece. The Python result is data only; Lean must replay it and prove linkage.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial,lcm
import argparse,json,sys,time
import flint
HERE=Path(__file__).resolve().parent
D4=HERE.parents[1]
sys.path.insert(0,str(D4/'verify/kernel_independent'))
from kernel import Kernel, fq,qf

def normalized(poly,lo,hi):
    x=flint.fmpq_poly([fq(lo),fq(hi-lo)])
    ans=flint.fmpq_poly([])
    for c in reversed(poly): ans=ans*x+fq(c)
    cs=[qf(c) for c in ans.coeffs()]
    den=lcm(*(a.denominator for a in cs))
    return [int(c*den) for c in cs],den

def transform(P,A,k):
    # P((A+w)/2^k), retaining positive common scale 2^(k*degree).
    n=len(P)-1;D=2**k
    # Direct FLINT transformation keeps implementation independent of Lean Horner.
    p=flint.fmpz_poly(P); x=flint.fmpz_poly([A,1]);out=flint.fmpz_poly([])
    for i in range(n,-1,-1):out=out*x+int(P[i])*D**(n-i)
    return list(map(int,out.coeffs()))

def lower(P,A,k):
    cs=transform(P,A,k)
    lo=0
    for c in reversed(cs):lo=c+min(lo,0)
    return lo

def chain(P,maxdepth=24):
    stack=[(0,0)];out=[]
    while stack:
        A,k=stack.pop()
        if lower(P,A,k)>0:out.append((A,k,1));continue
        if k>=maxdepth:raise RuntimeError(('not proved',A,k))
        stack.extend([(2*A+1,k+1),(2*A,k+1)])
    return out

def run(order):
    K=Kernel(D4/'data/v7');F=K.F_of_alpha_r2()
    T=[Q(0)]*(2*order+1)
    for i in range(order+1):T[2*i]=Q(2**i,factorial(i))
    tp=flint.fmpq_poly(list(map(fq,T)));fp=flint.fmpq_poly(list(map(fq,F)))
    out=[]
    for p in range(7):
        D=K.pair_poly(p);dp=flint.fmpq_poly(list(map(fq,D)));P=fp+dp*tp
        a,b=K.breaks[p:p+2]
        dz,dd=normalized([-c for c in D],a,b)
        pz,pd=normalized([-qf(c) for c in P.coeffs()],a,b)
        dc=chain(dz);pc=chain(pz)
        out.append(dict(piece=p,left=str(a),right=str(b),D=[str(c) for c in D],negative_D=dz,D_denominator=dd,D_chain=dc,negative_majorant=pz,majorant_denominator=pd,majorant_chain=pc))
        print(json.dumps(dict(piece=p,degree=len(pz)-1,D_leaves=len(dc),majorant_leaves=len(pc),depth=max(k for _,k,_ in pc))),flush=True)
    return dict(order=order,status='EXACT_DATA_GENERATED_NOT_LEAN_PROVED',pieces=out)


def lean_rational(x):
    x=Q(x)
    return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator}:ℚ)'

def emit_lean(data):
    dst=HERE.parent/'D4Bound'
    remainder=[]
    for p in data['pieces']:
        i=p['piece']
        out=['import D4Bound.ScalarCheck\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 4096\nset_option Elab.async false\n\nnamespace D4Bound.V7.PairSignData\n']
        out.append(f'def pairD{i} : List ℚ := ['+', '.join(map(lean_rational,p['D']))+']\n')
        for tag,key,den,ck in [('negativeD','negative_D','D_denominator','D_chain'),('negativeP','negative_majorant','majorant_denominator','majorant_chain')]:
            name=f'{tag}{i}'
            out.append(f'def {name} : List ℤ := '+str(p[key]).replace('-','-')+'\n')
            out.append(f'def {name}Den : ℕ := {p[den]}\n')
            cs='['+', '.join('('+','.join(map(str,c))+')' for c in p[ck])+']'
            out.append(f'def {name}Chain : List (ℕ × ℕ × ℕ) := {cs}\n')
            out.append(f'theorem {name}_check : chainOK {name} 0 0 {name}Chain 1 0 = true := by decide +kernel\n')
            A,k,h=p[ck][-1]
            out.append(f'''theorem {name}_positive (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < evalZ {name} x := by
  by_cases hx : x < 1
  · exact chainOK_sound {name} {name}Chain 0 0 1 0 {name}_check x (by simpa using hx0) (by simpa using hx)
  · have he : x = 1 := by linarith
    subst x
    exact leafOK_sound (P := {name}) (A := {A}) (k := {k}) (h := {h})
      (by decide +kernel) 1 (by norm_num) (by norm_num)
''')
        out.append('end D4Bound.V7.PairSignData\n')
        rendered='\n'.join(out)
        if i < 2:
            (dst/f'V7PairSignData{i}.lean').write_text(rendered)
        else:
            remainder.append(rendered.replace('import D4Bound.ScalarCheck\n',''))
    (dst/'V7PairSignDataRest.lean').write_text('import D4Bound.ScalarCheck\n'+'\n'.join(remainder))


# Kept separate from interval sign replay so coefficient computation is reviewable.
def emit_links(data):
    dst=HERE.parent/'D4Bound'
    remainder=[]
    for p in data['pieces']:
        i=p['piece'];a=Q(p['left']);w=Q(p['right'])-a
        affine='['+lean_rational(a)+', '+lean_rational(w)+']'
        data_module=str(i) if i < 2 else 'Rest'
        gram_module='0' if i == 0 else 'Rest'
        text=f'''import D4Bound.V7PairPolynomialTrim
import D4Bound.V7PairGramData{gram_module}
import D4Bound.V7PairSignData{data_module}

set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option Elab.async false
namespace D4Bound.V7.PairPoly
open PairSignData

/-- The uncut diagonal polynomial is computed from the actual component data. -/
theorem diagonal{i}_checked : diagonal {i} = pairD{i} := by
  unfold diagonal
  rw [gram{i}_checked]
  decide +kernel

/-- Exact change of coordinates to the closed unit interval. -/
theorem negativeD{i}_identity :
    trim (comp pairD{i} {affine}) =
      trim (scale (-1/(negativeD{i}Den : ℚ)) (negativeD{i}.map Int.cast)) := by decide +kernel

/-- The complete scalar-plus-Taylor polynomial, including every scalar coefficient. -/
theorem negativeP{i}_identity :
    trim (comp (add (comp Fq [0,0,2]) (mul pairD{i} (taylor {data['order']+1}))) {affine}) =
      trim (scale (-1/(negativeP{i}Den : ℚ)) (negativeP{i}.map Int.cast)) := by decide +kernel

end D4Bound.V7.PairPoly
'''
        if i == 0:
            (dst/'V7PairPolynomialData0.lean').write_text(text)
        else:
            remainder.append('\n'.join(line for line in text.splitlines() if not line.startswith('import ')))
    if remainder:
        imports = 'import D4Bound.V7PairPolynomialTrim\nimport D4Bound.V7PairGramDataRest\nimport D4Bound.V7PairSignData1\nimport D4Bound.V7PairSignDataRest\n'
        (dst/'V7PairPolynomialDataRest.lean').write_text(imports+'\n'.join(remainder)+'\n')

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--order',type=int,default=24)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--lean',action='store_true')
    a=ap.parse_args()
    data=run(a.order)
    a.output.write_text(json.dumps(data,indent=2)+'\n')
    if a.lean:
        emit_lean(data)
        emit_links(data)
