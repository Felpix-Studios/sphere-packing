# Formal component energy lemmas

The component modules below supplement the main density theorem. `V7Kernel.lean`
now defines the concrete kernel separately; these general and specialized energy
lemmas do not by themselves prove its seven remaining certificate premises or
replace the external interval programs. Individual components have compilation
evidence, while the expanded project's final clean build remains pending; see
[REVIEW.md](../REVIEW.md#current-formalization-status).

| Module | Proved statements | V7 component |
|---|---|---|
| `D4Bound/SchoenbergS3.lean` | `schoenberg_S3`: for every natural degree `l`, every finite weighted family of unit vectors in R4 has nonnegative energy for `U_l(inner(x,y))` | Gegenbauer parameter 1 on S3; rows 1, 2 and S3 graph bounds |
| `D4Bound/SchoenbergS2.lean` | `schoenberg_S2`: weighted positivity of normalized Legendre kernels on S² for every degree | Transverse spherical blocks and the projected graph bound |
| `D4Bound/ComponentsGram.lean` | `gram_energy_nonneg`, the block/ray equivalence, `origin_credit_identity`, `gram_origin_credit`, `gram_energy_ge_credit` | Harmonic Gram kernel, degree-zero origin coupling, completed-square origin credit; rows 1, 2, 16 |
| `D4Bound/ComponentsGauge.lean` | `usage_energy_eq`, `usage_energy_nonneg`, `gauge_energy_eq`, `gauge_pair_term`, `pair_count_gauge_nonneg` | Capacity-minus-usage kernel and the count gauge; row 15 |
| `D4Bound/ComponentsCapacity.lean` | `card_le_of_ball`, `blichfeldt_translate`, `pstar_capacity`, `step_capacity`, `pstar_allocation_nonneg`, `step_allocation_nonneg` | Pair-distance ball count, basic tent occupancy, both antipodal allocations; rows 3, 4, 5 |

Row numbers refer to [`../verify/stage1_v7/COMPONENTS.md`](../verify/stage1_v7/COMPONENTS.md).

Schoenberg's theorem is proved here for S3 by the Fischer inner product on polynomials in
four variables. Multiplication by a coordinate is adjoint to differentiation. The solid
zonal polynomial is harmonic and its Fischer product with another zonal polynomial is
`2^l l!` times its evaluation. Restriction to unit vectors gives the Chebyshev polynomial
`U_l`; division by the positive number `l+1` gives the normalized Gegenbauer kernel.
No integration, spherical harmonic basis or cited positive-definiteness assumption enters
this S³ proof. The separate `SchoenbergS2.lean` supplies the Legendre/S² proof by the corresponding three-variable Fischer construction.

The Gram theorem admits arbitrary nonnegative ray weights and arbitrary radial features.
The origin contributes only in degree zero. The origin-credit theorem verifies the full
completed-square identity, including the linear sum that must be nonnegative. The gauge
module proves both the anchored-energy identity and the cancellation of the original pair
term. The usage-kernel identity includes diagonal terms and requires the neighbourhood to
exclude the origin.

The capacity proofs apply in every real inner product space. The classical-improvement
profile uses the closed breakpoint `r <= 1/2`; the step profile uses `r < a`, then `r <= b`.
The exact certificate parameters `a=8453/20000`, `b=11547/20000` satisfy the step hypotheses
(`step_params_ok`). The ball-count theorem covers the strict pair-distance condition
`2(T+1)r^2 < T`. The five-point strictly-obtuse branch for R4 is now formalized in
`ComponentsObtuse.lean` and `ComponentsBall.lean`; strictness lies in the squared
radius bound, while containment is closed. `ComponentsTent.lean` proves the refined
shifted-tent capacity. The pointed-cap probability-averaging bridge is now
proved separately by `SphereMeasureCap.lean`, `SphereMeasureTransport.lean`
and `V7CapsFinal.lean`, using an actual normalized spherical measure.

The concrete JSON coefficients are generated into Lean data, and support, pair cancellation
and the raw objective are proved for `V7.kernel`. The external implementation identities
remain checked by `verify/`. In particular these modules do not discharge
`CensusFloor V7.kernel`, its cyclic sign or its kernel-box hypotheses by themselves.
The main Lean theorem and these component lemmas together support the mixed written,
exact-computation and formal proof described in the package documentation.

The source of the four modules was recovered from the interrupted lean-energy build. The
recovery repaired an implicit erased-point argument in `sep_sum_ge`, added the general
pair-distance ball count and translated tent inequality, and rebuilt the dependency chain.

## Later concrete component bridges

| Module | Formal scope |
|---|---|
| `V7Energy.lean` | Decomposition of the supported kernel energy into its component groups; gauge positivity still requires the indicated pair/count assumptions |
| `V7Conditional.lean` | Exact conditional count-ray energies and their signs on the count domain |
| `V7Allocations.lean`, `V7Tents.lean` | The actual two allocations and four tents, including the profile boundaries and nonnegative exact data weights |
| `V7CapsFinal.lean` | All 98 actual cap energies are nonnegative; includes the origin subtraction, degenerate cap cases, closed boundaries and proved S² coordinate law |
| `SphereMeasureCap.lean`, `SphereMeasureTransport.lean` | Normalized S² closed-cap probability in every direction and at every threshold, proved by disk-slice integration and transported into each transverse E4 subspace |
| `V7GramEnergy.lean`, `V7CensusGramOriginSound.lean` | Actual harmonic ray energies and exact degree-zero completed squares, with the concrete origin identities proved |
| `V7CensusGramProjection.lean` | The actual Gram energy dominates the census projection, from checked range, origin and polynomial identities; only admissibility and closed support are assumed |
| `V7CensusCount.lean`, `V7Graphs.lean` | Actual count-polynomial identity, exact broad-graph energy identity and nonnegative residual graph energies |
| `V7CensusGramPlanes.lean` | All twelve actual affine floors, including 588 coefficient equations and 84 closed radial interval bounds |
| `V7PairSign.lean`, `V7PairMargin0.lean` | Actual ungauged pair sign throughout closed support and the first-shell margin; gauge energy needs only the geometric count cap |
| `V7SphericalSurplus.lean` | Actual spherical energy dominates the census surplus assuming the three physical triangle-sign statements |
| `V7Census.lean`, `V7CensusFromSigns.lean` | Composition with all 165,503 checked count cases, Gram projection, twelve affine floors and gauge sign; the final concrete census interface retains exactly three spherical triangle-sign inputs |
| `SupportRestriction.lean` | Restricting to the closed support preserves the kernel energy, admissibility, counts and group key |
| `ComponentsObtuse.lean`, `ComponentsBall.lean` | Strict-negative-inner-product cardinality and its translated closed-ball corollary |

These are ingredients of the concrete census-energy comparison. A finite table
check alone does not prove that the actual kernel energy dominates that table's
expression. The latter remains distinct from the arithmetic census and is not
removed from `ConcreteMain.lean` by this inventory.
