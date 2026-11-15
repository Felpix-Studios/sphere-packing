"""Materialize exact matrix products and their kernel-checked upper inequalities.

This is untrusted proof-data generation. Every product and inequality is replayed
in Lean, and generic lemmas prove its real-polynomial meaning.
"""
from pathlib import Path
import argparse, ast, numpy as np
PKG=Path(__file__).resolve().parents[2];OUT=PKG/'lean/D4Bound'
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
def readvalue(text,marker):
    return ast.literal_eval(text.split(marker)[1].split('\n\n')[0].replace('![','['))
def vec(p):
    if isinstance(p,np.ndarray):p=p.tolist()
    return '!['+', '.join(vec(x) if isinstance(x,list) else str(int(x)) for x in p)+']'
def emit(name,lines):
    text='\n\n'.join(lines)+'\n';path=OUT/(name+'.lean')
    assert len(text.encode())<1024**2,(name,len(text))
    if args.check:assert path.read_text()==text
    else:path.write_text(text)
    print(name,len(text))
header=['set_option maxHeartbeats 0','set_option maxRecDepth 20000',
        'set_option Elab.async false','namespace D4Bound.SphericalSign.Bernstein']
aff=(OUT/'SphericalSignAffine.lean').read_text()
trees=(OUT/'SphericalSignTensorData.lean').read_text()
for n,p,q in [(24,603,400),(25,303,200),(26,61,40)]:
    power=(OUT/f'SphericalSignPower{n}Data.lean').read_text()
    P=np.array(readvalue(power,f'def repairPower{n} : Bernstein.Tensor := '),dtype=object)
    den=int(readvalue(power,f'def repairDen{n} : ℤ := '))
    T=np.array(readvalue(aff,f'def affine{n} : I → I → ℤ := '),dtype=object)
    td=int(readvalue(aff,f'def affineDen{n} : ℤ := '))
    prev=f'repairPower{n}';previousmodule=f'SphericalSignPower{n}Data'
    for axis,label in [(2,'Z'),(1,'Y'),(0,'X')]:
        moved=np.moveaxis(P,axis,0)
        P=np.moveaxis((T@moved.reshape(13,-1)).reshape(moved.shape),0,axis)
        name=f'SphericalSignTransform{n}{label}';value=f'transform{n}{label}'
        lines=[f'import D4Bound.{previousmodule}','import D4Bound.SphericalSignAffine']+header
        lines.append(f'def {value} : Tensor := {vec(P)}')
        for i in range(13):
            lines.append(f'theorem {value}_row{i} : ∀ j k, {value} {i} j k=matrix{label} affine{n} {prev} {i} j k := by decide +kernel')
        lines.append(f'''theorem {value}_eq : {value}=matrix{label} affine{n} {prev} := by
  funext i j k
  fin_cases i
'''+ '\n'.join(f'  · exact {value}_row{i} j k' for i in range(13)))
        lines+=['end D4Bound.SphericalSign.Bernstein'];emit(name,lines)
        prev=value;previousmodule=name
    U=np.array(readvalue(trees,f'def upper{n} : Tensor := '),dtype=object)
    precision=int(readvalue(trees,f'def precision{n} : ℕ := '))
    D=den*td**3
    for x,y in zip(P.flat,U.flat):
        assert -((-int(x)*2**precision)//D)==int(y)
    lines=[f'import D4Bound.{previousmodule}','import D4Bound.SphericalSignTensorData',
           'import D4Bound.SphericalSignTransformBound']+header
    for i in range(13):
        lines.append(f'''theorem upper{n}_matrix_row{i} : ∀ j k,
    (2^precision{n}:ℤ)*transform{n}X {i} j k ≤ (repairDen{n}*affineDen{n}^3)*upper{n} {i} j k := by decide +kernel''')
    lines.append(f'''theorem upper{n}_matrix_coeff : ∀ i j k,
    (2^precision{n}:ℤ)*transform{n}X i j k ≤ (repairDen{n}*affineDen{n}^3)*upper{n} i j k := by
  intro i j k
  fin_cases i
'''+ '\n'.join(f'  · exact upper{n}_matrix_row{i} j k' for i in range(13)))
    lines.append(f'''theorem upper{n}_power_correct {{x y z : ℝ}}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision{n}:ℝ)*powerEv repairPower{n}
      (-1+({p}:ℝ)/{q}*x) (-1+({p}:ℝ)/{q}*y) (-1+({p}:ℝ)/{q}*z) ≤
        (repairDen{n}:ℝ)*ev upper{n} x y z := by
  have hc : ∀ i j k, (2^precision{n}:ℤ)*
      (matrixX affine{n} (matrixY affine{n} (matrixZ affine{n} repairPower{n}))) i j k ≤
        (repairDen{n}*affineDen{n}^3)*upper{n} i j k := by
    rw [←transform{n}Z_eq,←transform{n}Y_eq,←transform{n}X_eq]
    exact upper{n}_matrix_coeff
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    upper_from_matrix affine{n} repairPower{n} upper{n} affineDen{n} repairDen{n}
      (2^precision{n}) (by norm_num [affineDen{n}]) hc
      (-1+({p}:ℝ)/{q}*x) (-1+({p}:ℝ)/{q}*y) (-1+({p}:ℝ)/{q}*z) x y z
      (fun j => affine{n}_exact j x) (fun j => affine{n}_exact j y)
      (fun j => affine{n}_exact j z) hx hx1 hy hy1 hz hz1''')
    raw=f'''(SphereCertificate.kernel Finset.univ (rayDegree rays{n}) (rayV rays{n} featureDen{n})
      (-1+({p}:ℝ)/{q}*x) (-1+({p}:ℝ)/{q}*y) (-1+({p}:ℝ)/{q}*z)+
    SphereCertificate.kernel Finset.univ (rayDegree rays{n}) (rayV rays{n} featureDen{n})
      (-1+({p}:ℝ)/{q}*x) (-1+({p}:ℝ)/{q}*z) (-1+({p}:ℝ)/{q}*y)+
    SphereCertificate.kernel Finset.univ (rayDegree rays{n}) (rayV rays{n} featureDen{n})
      (-1+({p}:ℝ)/{q}*y) (-1+({p}:ℝ)/{q}*z) (-1+({p}:ℝ)/{q}*x)-3*(epsilon{n}:ℝ))'''
    lines.append(f'''theorem upper{n}_raw_correct {{x y z : ℝ}}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision{n}:ℝ)*{raw} ≤ ev upper{n} x y z := by
  have hb := upper{n}_power_correct hx hx1 hy hy1 hz hz1
  rw [repairPower{n}_correct] at hb
  have hd : (0:ℝ)<repairDen{n} := by norm_num [repairDen{n}]
  have hh : (repairDen{n}:ℝ)*((2^precision{n}:ℝ)*{raw}-ev upper{n} x y z)≤0 := by nlinarith
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hh hd)''')
    lines += [f'#print axioms upper{n}_raw_correct','end D4Bound.SphericalSign.Bernstein']
    emit(f'SphericalSignUpper{n}',lines)
    lines=[f'import D4Bound.SphericalSignUpper{n}','import D4Bound.SphericalSignGramData',
           'import D4Bound.SphericalSignFinal']+header
    lines.append(f'''theorem rawTriangle{n}_of_cube (hcheck : OnCube upper{n} gramUpper{n})
    (a b t : ℝ) (ha : -1≤a) (has : a≤({p-q}:ℝ)/{q})
    (hb : -1≤b) (hbs : b≤({p-q}:ℝ)/{q}) (ht : -1≤t) (hts : t≤({p-q}:ℝ)/{q})
    (hdet : 0≤1+2*a*b*t-a^2-b^2-t^2) :
    SphereCertificate.kernel Finset.univ (rayDegree rays{n}) (rayV rays{n} featureDen{n}) a b t+
    SphereCertificate.kernel Finset.univ (rayDegree rays{n}) (rayV rays{n} featureDen{n}) a t b+
    SphereCertificate.kernel Finset.univ (rayDegree rays{n}) (rayV rays{n} featureDen{n}) b t a ≤ 3*(epsilon{n}:ℝ) := by
  have hw : (({p-q}:ℝ)/{q}+1)=({p}:ℝ)/{q} := by norm_num
  have hca := cube_coordinate (by norm_num : -1<({p-q}:ℝ)/{q}) ha has
  have hcb := cube_coordinate (by norm_num : -1<({p-q}:ℝ)/{q}) hb hbs
  have hct := cube_coordinate (by norm_num : -1<({p-q}:ℝ)/{q}) ht hts
  rw [hw] at hca hcb hct
  have hp := upper{n}_raw_correct hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  have hg := gramUpper{n}_correct hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  rw [hca.2.2,hcb.2.2,hct.2.2] at hp hg
  have hh := sign_from_envelopes upper{n} gramUpper{n} hcheck _ _
    (2^precision{n}:ℝ) (2^gramPrecision{n}:ℝ) _ _ _ (by positivity) (by positivity)
    hdet hp hg hca.1 hca.2.1 hcb.1 hcb.2.1 hct.1 hct.2.1
  exact sub_nonpos.mp hh''')
    lines += [f'#print axioms rawTriangle{n}_of_cube','end D4Bound.SphericalSign.Bernstein']
    emit(f'SphericalSignTriangle{n}',lines)
print('PASS exact affine products and existing outward ceilings; Lean replay required.')
