"""Export compact roots and complete multiplier trees, never materialized states.

The generated trees are untrusted. Their leaves and all subdivisions must be
replayed in Lean against the physical-kernel polynomial identities.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import importlib.util
import json
import math
import sys
import time
import numpy as np

sys.dont_write_bytecode=True
PKG=Path(__file__).resolve().parents[2]
SOURCE=PKG/'verify/stage2_origin/source'
OUT=PKG/'lean/D4Bound'
ap=argparse.ArgumentParser()
ap.add_argument('--check',action='store_true')
ap.add_argument('--index',type=int,choices=range(3),required=True)
args=ap.parse_args()


def possible(p,g):
    lo,hi=Q(0),None
    for pv,gv in zip(p.flat,g.flat):
        pv,gv=int(pv),int(gv)
        if gv==0:
            if pv>0:return None
        elif gv>0:
            if pv>0:return None
            r=Q(-pv,gv)
            hi=r if hi is None else min(hi,r)
        elif pv>0:lo=max(lo,Q(pv,-gv))
        if hi is not None and lo>hi:return None
    return lo


registry=json.loads((SOURCE/'target625/origin_completion/FINAL_ORIGIN_REGISTRY.json').read_text())
item=registry['common_g_certificates'][args.index]
data=json.loads((SOURCE/item['certificate']).read_text())
path=SOURCE/('target625/geometry/fixed_cardinality_spherical_algebra.py'if data.get('fixed_count')else
    'optimization/continuation_20261018/base/new_work/spherical_sdp/certify.py')
spec=importlib.util.spec_from_file_location('surplus_tree_algebra',path)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
p,pd,_,_,g,_,s=m.polynomials(data)
assert p.shape==(17,17,17)
repair=data.get('repair',data.get('bounded_cardinality_common_g_repair'))
eps=Q(repair['scale']);den=math.lcm(pd,(3*eps).denominator)
p*=den//pd;p[0,0,0]-=int(3*eps*den)
ge=np.zeros(p.shape,dtype=object);ge[:3,:3,:3]=g
_,pu,pp=m.bernstein(p,den,[(Q(-1),s)]*3)
_,gu,gp=m.bernstein(ge,1,[(Q(-1),s)]*3)
counts=dict(nodes=0,ordinary=0,excluded=0,multiplier=0)


def build(p,g,depth):
    counts['nodes']+=1
    assert counts['nodes']<=10000 and depth<=66
    if g.max()<0:
        counts['excluded']+=1;return '(.leaf 0 0)'
    if p.max()<=0:
        counts['ordinary']+=1;return '(.leaf 0 1)'
    mu=possible(p,g)
    if mu is not None:
        counts['multiplier']+=1;return f'(.leaf {mu.numerator} {mu.denominator})'
    axis=depth%3
    pl,pr=m.split(p,axis,True);gl,gr=m.split(g,axis,True)
    return f'(.{"xyz"[axis]} {build(pl,gl,depth+1)} {build(pr,gr,depth+1)})'


started=time.time();tree=build(pu,gu,0)
lines=['-- Compact untrusted roots and full tree; no accepted outcome flags.',
    'import D4Bound.SphericalSurplusSignTree16','set_option maxHeartbeats 0',
    'set_option maxRecDepth 20000','set_option Elab.async false',
    'namespace D4Bound.SphericalSurplusSign.Bernstein16']
for label,tensor in [('upper',pu),('gramUpper',gu)]:
    value='!['+', '.join('!['+', '.join('!['+', '.join(str(int(tensor[i,j,k]))for k in range(17))+']'
        for j in range(17))+']'for i in range(17))+']'
    lines += [f'def {label}{args.index} : Tensor := {value}']
lines += [f'def precision{args.index} : ℕ := {pp}',f'def gramPrecision{args.index} : ℕ := {gp}',
    f'def triangleTree{args.index} : Tree := {tree}', 'end D4Bound.SphericalSurplusSign.Bernstein16']
text='\n\n'.join(lines)+'\n'
assert len(text.encode())<1024**2
out=OUT/f'SphericalSurplusSignTreeData{args.index}.lean'
if args.check:assert out.read_text()==text
else:out.write_text(text)
print(json.dumps(dict(index=args.index,counts=counts,seconds=time.time()-started,bytes=len(text),
    status='GENERATED_UNTRUSTED_COMPLETE_TREE'),indent=2))
