"""Export repaired degree16 physical cyclic tensors with Lean identities."""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import ast

PKG=Path(__file__).resolve().parents[2];OUT=PKG/'lean/D4Bound'
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
for n in range(3):
    raw=(OUT/f'SphericalSurplusSignPhysical{n}.lean').read_text()
    data=(OUT/f'SphericalSurplusSignData{n}.lean').read_text()
    num=ast.literal_eval(raw.split(f'def physicalNum{n} : Poly3 := ')[1].split('\n\n')[0])
    assert len(num)<=17 and all(len(p)<=17 and all(len(q)<=17 for q in p)for p in num)
    fd=int(data.split(f'def featureDen{n} : ℤ := ')[1].split('\n')[0])
    eps=Q(data.split(f'def epsilon{n} : ℚ := ')[1].split('\n')[0])
    den=40320*fd**2*eps.denominator
    repair=3*eps.numerator*40320*fd**2
    def at(i,j,k):return num[i][j][k]if i<len(num)and j<len(num[i])and k<len(num[i][j])else 0
    p=[[[eps.denominator*(at(i,j,k)+at(i,k,j)+at(j,k,i))-(repair if i==j==k==0 else 0)
         for k in range(17)]for j in range(17)]for i in range(17)]
    def vec(v):return '!['+', '.join(vec(x)if isinstance(x,list)else str(x)for x in v)+']'
    datalines=['-- Exact tensor literals; semantic linkage is in the companion proof module.',
      'import D4Bound.SphericalSurplusSignTensor16',
      'set_option maxRecDepth 20000','set_option Elab.async false',
      'namespace D4Bound.SphericalSurplusSign','open Bernstein16',
      f'def repairPower{n} : Tensor := {vec(p)}',f'def repairDen{n} : ℤ := {den}',
      'end D4Bound.SphericalSurplusSign']
    datatext='\n\n'.join(datalines)+'\n'
    datapath=OUT/f'SphericalSurplusSignPower{n}Data.lean'
    assert len(datatext.encode())<1024**2
    if args.check:assert datapath.read_text()==datatext
    else:datapath.write_text(datatext)
    print(datapath.name,len(datatext))
    lines=[f'import D4Bound.SphericalSurplusSignPhysical{n}',
      f'import D4Bound.SphericalSurplusSignPower{n}Data',
      'import D4Bound.SphericalSurplusSignPowerAlgebra16','set_option maxHeartbeats 0',
      'set_option maxRecDepth 20000','set_option Elab.async false',
      'namespace D4Bound.SphericalSurplusSign','open SphericalSign Bernstein16',
      f'def rawPower{n} : Tensor := powerTensor physicalNum{n}',
      f'theorem physicalNum{n}_bounded : bounded3 physicalNum{n} := by decide +kernel',
      f'''theorem rawPower{n}_correct (a b t : ℝ) :
    powerEv rawPower{n} a b t=40320*(featureDen{n}:ℝ)^2*kernel{n} a b t := by
  rw [rawPower{n},←eval3_powerTensor physicalNum{n} physicalNum{n}_bounded,physicalNum{n}_correct]''']
    expression=f'addTensor (scaleTensor {eps.denominator} (cyclicTensor rawPower{n})) (constTensor (-{repair}))'
    for i in range(17):lines.append(f'theorem repairPower{n}_row{i} : ∀ j k, repairPower{n} {i} j k=({expression}) {i} j k := by decide +kernel')
    lines += [f'''theorem repairPower{n}_eq : repairPower{n}={expression} := by
  funext i j k
  fin_cases i
'''+ '\n'.join(f'  · exact repairPower{n}_row{i} j k'for i in range(17)),
      f'''theorem repairPower{n}_correct (a b t : ℝ) :
    powerEv repairPower{n} a b t=(repairDen{n}:ℝ)*
      (kernel{n} a b t+kernel{n} a t b+kernel{n} b t a-3*(epsilon{n}:ℝ)) := by
  rw [repairPower{n}_eq,powerEv_add,powerEv_scale,powerEv_cyclic,powerEv_const]
  simp only [rawPower{n}_correct]
  norm_num [repairDen{n},featureDen{n},epsilon{n}]
  ring''',f'#print axioms repairPower{n}_correct','end D4Bound.SphericalSurplusSign']
    text='\n\n'.join(lines)+'\n'
    assert len(text.encode())<1024**2
    path=OUT/f'SphericalSurplusSignPower{n}.lean'
    if args.check:assert path.read_text()==text
    else:path.write_text(text)
    print(path.name,len(text))
