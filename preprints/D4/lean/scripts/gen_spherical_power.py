"""Generate repaired cyclic power tensors from the kernel-checked Horner data.

All list-to-tensor and repair coefficient equalities are proved by the emitted
Lean source. Reading the generated integer lists is not a trusted operation.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse, ast, json, math
PKG=Path(__file__).resolve().parents[2]
OUT=PKG/'lean/D4Bound'
SRC=PKG/'verify/stage1_v7/record/current/base/new_work/spherical_sdp'
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
for n,fn in [(24,'s05075_taper12_exact.json'),(25,'s0515_count25_exact.json'),(26,'s0525_count26_exact.json')]:
    txt=(OUT/f'SphericalSignRaw{n}Data.lean').read_text()
    num=ast.literal_eval(txt.split(f'def numAll{n} : Poly3 := ')[1].split('\n\n')[0])
    assert len(num)<=13 and all(len(p)<=13 and all(len(q)<=13 for q in p) for p in num)
    data=json.loads((SRC/fn).read_text());eps=Q(data['uniform_repair']['scale'])
    raytext=(OUT/'SphericalSignRays.lean').read_text()
    fd=int(raytext.split(f'def featureDen{n} : ℤ := ')[1].split('\n')[0])
    den=math.factorial(12)*fd**2*eps.denominator
    repair=3*eps.numerator*math.factorial(12)*fd**2
    def at(i,j,k):
        return num[i][j][k] if i<len(num) and j<len(num[i]) and k<len(num[i][j]) else 0
    P=[[[eps.denominator*(at(i,j,k)+at(i,k,j)+at(j,k,i))-(repair if i==j==k==0 else 0)
         for k in range(13)] for j in range(13)] for i in range(13)]
    def vec(p):
        return '!['+', '.join(vec(x) if isinstance(x,list) else str(x) for x in p)+']'
    lines=[f'import D4Bound.SphericalSignRaw{n}Data','import D4Bound.SphericalSignPowerAlgebra',
      'set_option maxHeartbeats 0','set_option maxRecDepth 20000','set_option Elab.async false',
      'namespace D4Bound.SphericalSign',f'def rawPower{n} : Bernstein.Tensor := powerTensor numAll{n}',
      f'theorem numAll{n}_bounded : bounded3 numAll{n} := by decide +kernel',
      f'''theorem rawPower{n}_correct (a b t : ℝ) :
    powerEv rawPower{n} a b t=479001600*(featureDen{n}:ℝ)^2*
      SphereCertificate.kernel Finset.univ (rayDegree rays{n}) (rayV rays{n} featureDen{n}) a b t := by
  rw [rawPower{n},←eval3_powerTensor numAll{n} numAll{n}_bounded,numAll{n}_correct]''',
      f'def repairPower{n} : Bernstein.Tensor := {vec(P)}',f'def repairDen{n} : ℤ := {den}']
    expr=f'addTensor (scaleTensor {eps.denominator} (cyclicTensor rawPower{n})) (constTensor (-{repair}))'
    for i in range(13):
        lines.append(f'''theorem repairPower{n}_row{i} : ∀ j k, repairPower{n} {i} j k=({expr}) {i} j k := by decide +kernel''')
    lines.extend([f'''theorem repairPower{n}_eq : repairPower{n}={expr} := by
  funext i j k
  fin_cases i
'''+ '\n'.join(f'  · exact repairPower{n}_row{i} j k' for i in range(13)),
      f'''theorem repairPower{n}_correct (a b t : ℝ) :
    powerEv repairPower{n} a b t=(repairDen{n}:ℝ)*
      (SphereCertificate.kernel Finset.univ (rayDegree rays{n}) (rayV rays{n} featureDen{n}) a b t+
       SphereCertificate.kernel Finset.univ (rayDegree rays{n}) (rayV rays{n} featureDen{n}) a t b+
       SphereCertificate.kernel Finset.univ (rayDegree rays{n}) (rayV rays{n} featureDen{n}) b t a-3*(epsilon{n}:ℝ)) := by
  rw [repairPower{n}_eq,powerEv_add,powerEv_scale,powerEv_cyclic,powerEv_const]
  simp only [rawPower{n}_correct]
  norm_num [repairDen{n},featureDen{n},epsilon{n}]
  ring''',f'#print axioms repairPower{n}_correct','end D4Bound.SphericalSign'])
    text='\n\n'.join(lines)+'\n';dest=OUT/f'SphericalSignPower{n}Data.lean'
    assert len(text.encode())<1024**2
    if args.check:assert dest.read_text()==text
    else:dest.write_text(text)
    print(dest.name,len(text))
print('PASS generation; Lean coefficient and semantic checks remain required.')
