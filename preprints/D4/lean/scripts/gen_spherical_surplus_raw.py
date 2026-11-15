"""Emit bounded groups of kernel-checked integer raw-ray polynomial identities.

The degree16 physical correction and the triangle tree are separate steps.
Every file is at most 1MiB; these coefficients are untrusted until Lean checks.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import ast
import importlib.util
import json
import math
import sys

sys.dont_write_bytecode=True
PKG=Path(__file__).resolve().parents[2]
OUT=PKG/'lean/D4Bound'
ap=argparse.ArgumentParser()
ap.add_argument('--check',action='store_true')
args=ap.parse_args()


def add(n,p,q):
    if n==0:return p+q
    return [add(n-1,p[i],q[i]) if i<len(p) and i<len(q) else p[i] if i<len(p) else q[i]
            for i in range(max(len(p),len(q)))]


def mul(n,p,q):
    if n==0:return p*q
    v=[]
    for a in reversed(p):v=add(n,[mul(n-1,a,b)for b in q],[(0 if n==1 else [])]+v)
    return v


def smul(n,a,p):return a*p if n==0 else [smul(n-1,a,q)for q in p]


def render(p):return '['+', '.join(map(render,p))+']' if isinstance(p,list)else str(int(p))


def emit(name,lines):
    text='\n\n'.join(lines)+'\n'
    assert len(text.encode())<1024**2,(name,len(text))
    p=OUT/f'{name}.lean'
    if args.check:assert p.read_text()==text,p
    else:p.write_text(text)
    print(name,len(text),flush=True)


head=['set_option maxHeartbeats 0','set_option maxRecDepth 20000','set_option Elab.async false',
      'namespace D4Bound.SphericalSurplusSign','open SphericalSign']
angular=(OUT/'SphericalSignAngularData.lean').read_text()
ANG=[ast.literal_eval(angular.split(f'def angularData{l} : Poly3 := ')[1].split('\n\n')[0])for l in range(9)]
SOURCE=PKG/'verify/stage2_origin/source'
registry=json.loads((SOURCE/'target625/origin_completion/FINAL_ORIGIN_REGISTRY.json').read_text())
for n in range(3):
    data=(OUT/f'SphericalSurplusSignData{n}.lean').read_text()
    rays=ast.literal_eval(data.split(f'def rays{n} : List Ray := ')[1].split('\n\n')[0].replace('⟨','[').replace('⟩',']'))
    total=[]
    start=0
    for group in range(3):
        lines=['import D4Bound.SphericalSignAngularData',f'import D4Bound.SphericalSurplusSignData{n}']+head
        for l in range(group*3,group*3+3):
            selected=[r for r in rays if r[0]==l]
            rpoly=[]
            for _,_,c in selected:rpoly=add(3,rpoly,[[[a*b]for b in c]for a in c])
            num=mul(3,rpoly,ANG[l])
            total=add(3,total,smul(3,40320//math.factorial(l),num))
            lines += [f'def block{n}_{l} : List Ray := (rays{n}.drop {start}).take {len(selected)}',
              f'theorem block{n}_{l}_degree : (block{n}_{l}.all (fun r => r.degree=={l}))=true := by decide +kernel',
              f'def radialData{n}_{l} : Poly3 := {render(rpoly)}',
              f'theorem radialData{n}_{l}_eq : radialSum3 block{n}_{l}=radialData{n}_{l} := by decide +kernel',
              f'def numData{n}_{l} : Poly3 := {render(num)}',
              f'''theorem numData{n}_{l}_eq : blockNum {l} block{n}_{l}=numData{n}_{l} := by
  rw [blockNum,radialData{n}_{l}_eq,angularData{l}_eq]
  decide +kernel''']
            start += len(selected)
        lines += ['end D4Bound.SphericalSurplusSign']
        emit(f'SphericalSurplusSignRaw{n}Part{group}',lines)
    lines=[f'import D4Bound.SphericalSurplusSignRaw{n}Part{k}'for k in range(3)]+head
    addexpr='[]'
    for l in reversed(range(9)):addexpr=f'(add3 (smul3 {40320//math.factorial(l)} numData{n}_{l}) {addexpr})'
    lines += [f'theorem rays{n}_blocks : rays{n}='+' ++ '.join(f'block{n}_{l}'for l in range(9))+' := by rfl',
      f'def numAll{n} : Poly3 := {render(total)}',
      f'theorem numAll{n}_eq : numAll{n}={addexpr} := by decide +kernel',
      f'''theorem numAll{n}_correct (a b t : ℝ) :
    eval3 numAll{n} a b t=40320*(featureDen{n}:ℝ)^2*
      SphereCertificate.kernel Finset.univ (rayDegree rays{n}) (rayV rays{n} featureDen{n}) a b t := by
  rw [numAll{n}_eq]
  simp only [eval_add3,eval_smul3]
  rw ['''+', '.join(f'←numData{n}_{l}_eq'for l in range(9))+''']
  simp only ['''+', '.join(f'eval_blockNum {l} block{n}_{l} featureDen{n} (by norm_num [featureDen{n}]) block{n}_{l}_degree'for l in range(9))+f''']
  rw [←rawList_kernel,rays{n}_blocks]
  simp only [rawList_append]
  norm_num [Nat.factorial,eval3,evalH]
  ring''', f'#print axioms numAll{n}_correct','end D4Bound.SphericalSurplusSign']
    emit(f'SphericalSurplusSignRaw{n}',lines)
    # Independent full physical cyclic coefficient comparison, including the
    # indefinite fixed-count rank-two correction absent from the PSD rays.
    source=json.loads((SOURCE/registry['common_g_certificates'][n]['certificate']).read_text())
    path=SOURCE/('target625/geometry/fixed_cardinality_spherical_algebra.py'if source.get('fixed_count')else
        'optimization/continuation_20261018/base/new_work/spherical_sdp/certify.py')
    spec=importlib.util.spec_from_file_location(f'surplus_algebra_{n}',path)
    algebra=importlib.util.module_from_spec(spec);spec.loader.exec_module(algebra)
    tri,td,*_=algebra.polynomials(source)
    def integer(name):return int(data.split(f'def {name} : ℤ := ')[1].split('\n')[0])
    fd,od=integer(f'featureDen{n}'),integer(f'originDen{n}')
    correction=ast.literal_eval(data.split(f'def correction{n} : List ℤ := ')[1].split('\n')[0])
    cd,b=integer(f'correctionDen{n}'),integer(f'bNum{n}')
    def c(i,j,k):return total[i][j][k]if i<len(total)and j<len(total[i])and k<len(total[i][j])else 0
    for i in range(17):
        for j in range(17):
            for k in range(17):
                v=Q(c(i,j,k)+c(i,k,j)+c(j,k,i),40320*fd**2)
                if i==j==k==0:v+=Q(3*b,od**2)
                for x,y,z in [(i,j,k),(j,i,k),(k,i,j)]:
                    if y==z==0 and x<len(correction):v+=Q(2*correction[x],cd)
                assert v==Q(int(tri[i,j,k]),td),(n,i,j,k)
print('PASS generation only; Lean replay and physical correction still required.')
