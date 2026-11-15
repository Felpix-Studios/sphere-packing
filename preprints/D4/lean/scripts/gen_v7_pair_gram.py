"""Generate separate kernel checks for the 19 Gram-block pair polynomials."""
from gen_v7_pair_sign import *

def emit_gram(pieces=range(7)):
    K=Kernel(D4/'data/v7')
    remainder=[]
    for p in pieces:
        out=['import D4Bound.V7PairPolynomialDef\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 8192\nset_option Elab.async false\n\nnamespace D4Bound.V7.PairPoly\n']
        total=flint.fmpq_poly([])
        for ell in range(19):
            poly=flint.fmpq_poly([])
            for i in range(7):
                for j in range(7):
                    bi=flint.fmpq_poly(list(map(fq,K.phi_power[p][i])))
                    bj=flint.fmpq_poly(list(map(fq,K.phi_power[p][j])))
                    poly+=fq(Q(int(K.M[ell][7*p+i,7*p+j]),K.D))*bi*bj
            total+=poly
            cs=list(map(qf,poly.coeffs()));cs += [Q(0)]*(13-len(cs))
            name=f'gramBlock{p}_{ell}'
            out.append(f'def {name} : Poly := ['+', '.join(map(lean_rational,cs))+']\n')
            out.append(f'''theorem {name}_checked :
    sum (gramRays{ell}.map fun ray => scale (ray.weight/gramDenominator)
      (mul (radial ray.vector {p}) (radial ray.vector {p}))) = {name} := by decide +kernel
''')
        cs=list(map(qf,total.coeffs()));cs += [Q(0)]*(13-len(cs))
        out.append(f'def gramValue{p} : Poly := ['+', '.join(map(lean_rational,cs))+']\n')
        out.append(f'''theorem gram{p}_checked : gram {p} = gramValue{p} := by
  unfold gram gramRays
  simp only [List.map_cons,List.map_nil,sum]
  rw ['''+', '.join(f'gramBlock{p}_{ell}_checked' for ell in range(19))+''']
  decide +kernel

end D4Bound.V7.PairPoly
''')
        rendered='\n'.join(out)
        if p == 0:
            (HERE.parent/'D4Bound/V7PairGramData0.lean').write_text(rendered)
        else:
            remainder.append(rendered.replace('import D4Bound.V7PairPolynomialDef\n',''))
    if remainder:
        (HERE.parent/'D4Bound/V7PairGramDataRest.lean').write_text('import D4Bound.V7PairPolynomialDef\n'+'\n'.join(remainder))

if __name__=='__main__':emit_gram()
