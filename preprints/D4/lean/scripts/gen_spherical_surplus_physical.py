"""Export exact fixed-count physical corrections on the proved ray polynomial."""
from pathlib import Path
import argparse
import ast

PKG=Path(__file__).resolve().parents[2];OUT=PKG/'lean/D4Bound'
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()


def add(n,p,q):
    if n==0:return p+q
    return [add(n-1,p[i],q[i])if i<len(p)and i<len(q)else p[i]if i<len(p)else q[i]
            for i in range(max(len(p),len(q)))]


def smul(n,c,p):return c*p if n==0 else[smul(n-1,c,q)for q in p]


for n in range(3):
    data=(OUT/f'SphericalSurplusSignData{n}.lean').read_text()
    raw=(OUT/f'SphericalSurplusSignRaw{n}.lean').read_text()
    num=ast.literal_eval(raw.split(f'def numAll{n} : Poly3 := ')[1].split('\n\n')[0])
    def integer(name):return int(data.split(f'def {name} : ℤ := ')[1].split('\n')[0])
    fd,od=integer(f'featureDen{n}'),integer(f'originDen{n}')
    assert fd%od==0
    rd=fd//od
    b=integer(f'bNum{n}')
    corr=ast.literal_eval(data.split(f'def correction{n} : List ℤ := ')[1].split('\n')[0])
    physical=add(3,num,add(3,[[[40320*rd**2*b]]],
        smul(3,40320*rd,add(3,[[[a]]for a in corr],[[[a]for a in corr]]))))
    text=f'''-- Generated exact physical kernel numerator; all integer arithmetic is replayed.
import D4Bound.SphericalSurplusSignRaw{n}
import D4Bound.SphericalSurplusSignEmbed
set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option Elab.async false
namespace D4Bound.SphericalSurplusSign
open SphericalSign

def physicalNum{n} : Poly3 := {physical}

theorem physicalNum{n}_eq : physicalNum{n} = add3 numAll{n}
    (add3 [[[{40320*rd**2*b}]]] (smul3 {40320*rd} (add3 (embedX correction{n}) (embedY correction{n})))) := by
  decide +kernel

theorem physicalNum{n}_correct (a b t : ℝ) :
    eval3 physicalNum{n} a b t=40320*(featureDen{n}:ℝ)^2*kernel{n} a b t := by
  rw [physicalNum{n}_eq,eval_add3,eval_add3,eval_const3,eval_smul3,eval_add3,
    eval_embedX,eval_embedY,numAll{n}_correct]
  dsimp [kernel{n},b{n},F{n}]
  norm_num only [featureDen{n},originDen{n},bNum{n},correctionDen{n}]
  ring

#print axioms physicalNum{n}_correct
end D4Bound.SphericalSurplusSign
'''
    assert len(text.encode())<1024**2
    p=OUT/f'SphericalSurplusSignPhysical{n}.lean'
    if args.check:assert p.read_text()==text,p
    else:p.write_text(text)
    print(p.name,len(text))
