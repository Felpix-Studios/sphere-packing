import D4Bound.V7Kernel
import D4Bound.SphericalConcrete24
import D4Bound.SphericalConcrete25
import D4Bound.SphericalConcrete26
import D4Bound.KernelBoxNativeCheck1
import D4Bound.KernelBoxNativeCheck5
import D4Bound.V7CensusNative
import D4Bound.V7CyclicSignNative

/-!
# Specialization to the concrete V7 kernel

All fourteen certificate premises of `d4_density_bound` are discharged for the V7 kernel:
support, pair sign, cyclic sign, raw objective, both latitude certificates, annular
cardinality, the graph's projected degree bound, the three near-code count bounds
`A(4,203/400) ≤ 24`, `A(4,103/200) ≤ 25`, `A(4,21/40) ≤ 26`, both far-pair kernel boxes,
and the census energy floor. The theorem below takes only a packing.

Finite certificate checks run proved checkers with `native_decide`:
* the three degree-12 near-code sign trees (`SphericalSignNative24/25/26`);
* the kernel boxes (`KernelBoxNativeCheckScalar/1/5`) and the gauge table (`KBNGaugeCheck`);
* the three degree-16 surplus sign trees behind the census floor
  (`SphericalSurplusSignNative0/1/2`);
* the cyclic sign: 84 full cases (`V7CyclicNativeF*`) and 28 exterior cases
  (`V7CyclicNativeXO*`, `XW*`, and four sub-boxes `XS55*`).
So this theorem depends on the Lean compiler through 125 native axioms in addition to
`propext`, `Classical.choice` and `Quot.sound`; every soundness proof is kernel-checked.
-/
namespace D4Bound

theorem d4_density_bound_concrete
    (P : Set E4) (hP : IsUnitPacking P) :
    upperDensity P < ENNReal.ofReal (629521681653 / 1000000000000) :=
  d4_density_bound V7.kernel V7.kernel_supported V7.kernel_pair V7.cyclicSign_kernel V7.kernel_raw
    V7.censusFloor_kernel KBN.kernel_box_1_native KBN.kernel_box_5_native
    SphericalConcrete.C24.code_bound_unconditional
    SphericalConcrete.C25.code_bound_unconditional
    SphericalConcrete.C26.code_bound_unconditional P hP

#print axioms d4_density_bound_concrete

end D4Bound
