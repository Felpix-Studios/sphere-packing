"""Generate the checked initial Gram envelope and physical triangle interface."""
from pathlib import Path
import argparse

PKG = Path(__file__).resolve().parents[2]
OUT = PKG / 'lean/D4Bound'
ap = argparse.ArgumentParser()
ap.add_argument('--check', action='store_true')
args = ap.parse_args()


def emit(name, lines):
    text = '\n\n'.join(lines) + '\n'
    path = OUT / (name + '.lean')
    assert len(text.encode()) < 1024**2
    if args.check:
        assert path.read_text() == text
    else:
        path.write_text(text)
    print(name, len(text))


header = ['set_option maxHeartbeats 0', 'set_option maxRecDepth 20000',
          'set_option Elab.async false', 'namespace D4Bound.SphericalSurplusSign.Bernstein16']
for n, p, q in [(0, 751467, 500000), (1, 61, 40), (2, 303, 200)]:
    lines = ['import D4Bound.SphericalSurplusSignGramLink16',
             f'import D4Bound.SphericalSurplusSignTreeData{n}'] + header
    for i in range(17):
        lines.append(f'''theorem gramUpper{n}_row{i} : ∀ j k,
    (2^gramPrecision{n}:ℤ)*gramNum {p} {q} {i} j k ≤
      (61440*{q}^3)*gramUpper{n} {i} j k := by decide +kernel''')
    lines.append(f'''theorem gramUpper{n}_coeff : ∀ i j k,
    (2^gramPrecision{n}:ℤ)*gramNum {p} {q} i j k ≤ (61440*{q}^3)*gramUpper{n} i j k := by
  intro i j k
  fin_cases i
''' + '\n'.join(f'  · exact gramUpper{n}_row{i} j k' for i in range(17)))
    lines.append(f'''theorem gramUpper{n}_correct {{x y z : ℝ}}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^gramPrecision{n}:ℝ)*(1+2*(-1+({p}:ℝ)/{q}*x)*(-1+({p}:ℝ)/{q}*y)*(-1+({p}:ℝ)/{q}*z)-
      (-1+({p}:ℝ)/{q}*x)^2-(-1+({p}:ℝ)/{q}*y)^2-(-1+({p}:ℝ)/{q}*z)^2) ≤ ev gramUpper{n} x y z := by
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    gram_upper_of_coeff {p} {q} (by norm_num) (2^gramPrecision{n}) (by positivity)
      gramUpper{n} gramUpper{n}_coeff hx hx1 hy hy1 hz hz1''')
    lines += [f'#print axioms gramUpper{n}_correct', 'end D4Bound.SphericalSurplusSign.Bernstein16']
    emit(f'SphericalSurplusSignGramData{n}', lines)

    lines = [f'import D4Bound.SphericalSurplusSignUpper{n}',
             f'import D4Bound.SphericalSurplusSignGramData{n}',
             'import D4Bound.SphericalSurplusSignFinal16'] + header
    lines.append(f'''theorem rawTriangle{n}_of_cube (hcheck : OnCube upper{n} gramUpper{n})
    (a b t : ℝ) (ha : -1≤a) (has : a≤({p-q}:ℝ)/{q})
    (hb : -1≤b) (hbs : b≤({p-q}:ℝ)/{q}) (ht : -1≤t) (hts : t≤({p-q}:ℝ)/{q})
    (hdet : 0≤1+2*a*b*t-a^2-b^2-t^2) :
    kernel{n} a b t+kernel{n} a t b+kernel{n} b t a ≤ 3*(epsilon{n}:ℝ) := by
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
    lines += [f'#print axioms rawTriangle{n}_of_cube', 'end D4Bound.SphericalSurplusSign.Bernstein16']
    emit(f'SphericalSurplusSignTriangle{n}', lines)
