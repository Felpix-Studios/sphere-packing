# Proof dependencies of the D4 upper bound

This is a source audit of the argument for **upper density less than
0.629521681653 for every packing of congruent balls in R4**. It is not a
proof that the D4 lattice is optimal. All certificate inputs and programs
needed for this bound are in this directory. The non-Lean proof path combines
the written proofs with exact/interval certificate verification. It is
self-contained in `paper.tex`, `data/`, and
`verify/`; it does not require the separate Lean project. The Lean material
described below is a parallel formalization and is not a prerequisite for the
non-Lean result.

The separate Lean concrete specialization is in
[ConcreteMain.lean](lean/D4Bound/ConcreteMain.lean).
It has seven remaining certificate premises: cyclic sign, census floor, two
kernel boxes, and three near-code bounds. Seven of the original fourteen
premises are now supplied by Lean proofs. `P` and its unit-separation premise
are packing inputs, not certificate hypotheses. The original inventory below
records which obligations have been discharged.
The earlier eight-hypothesis discussion in
[HYPOTHESIS_AUDIT.md](lean/HYPOTHESIS_AUDIT.md) is historical. Its new addendum
explains the change.

## Current execution status

The seven-premise concrete specialization and several component modules have
individual successful compilation receipts. A final clean build of **all**
expanded publication sources and the full concrete spherical sign-tree replay in Lean
remain pending. The 22-module/53-axiom receipt in [REVIEW.md](REVIEW.md) is for
the earlier recovery snapshot; it must not be read as verification of later
sources. The stages below describe the complete external computer-assisted
argument and its previously recorded replay, not a claim that all those
checks have been converted into Lean proofs.

## Mathematical chain

1. The scalar function is the concrete Gaussian times a degree-49 rational
   polynomial in [scalar.json](data/v7/scalar.json). Its Fourier transform,
   positive Fourier sign, negative physical tail, and integral `pi²/4`
   are proved in [Scalar.lean](lean/D4Bound/Scalar.lean), using
   [Fourier.lean](lean/D4Bound/Fourier.lean) and the kernel-checked scalar
   certificates. Stage 1 also checks these independently by polynomial
   coefficient identities and Sturm sequences. Balls have radius `1/2`,
   hence volume `pi²/32`: division by the scalar integral gives the factor
   `1/8` in every density objective.
2. The complete V7 anchored energy has nonnegative components on actual
   unit-separated neighbourhoods. These need not be positive-definite
   kernels on arbitrary point sets. The source-by-source inventory is
   [COMPONENTS.md](verify/stage1_v7/COMPONENTS.md); the useful analytic
   arguments are identified below. Stage 1 checks the complete pair sign,
   all 112 cyclic branches, and the raw objective, with every component's
   origin constant included.
3. Stages 2 and 3 improve the energy floor, without spending an origin
   credit twice. [Stage 2's proof](verify/stage2_origin/PROOF.md) projects
   the degree-zero Gram energy onto five counts and takes the maximum with
   twelve affine floors. It adds the three count polynomials and the best
   applicable spherical surplus. The two conditional count rays and all
   other components have nonnegative energy and can be discarded. The
   census covers all 165,503 integer vectors satisfying the proved caps
   and implications, without assuming each vector is realizable.
   [Stage 3's proof](verify/stage3_census/finite_count_gain.md) uses the
   exact numbers of pairs and triples, refining all 124 group floors.
4. The broad graph term is explicitly separated as `Kg`. The census
   floor bounds `E_(K-Kg)`, so adding `E_Kg >= 3/10^6` does not count a
   credit twice. [The graph proof](verify/stage4_graph_slack/proofs/graph_slack.md)
   has at most 151 vertices and degree at most 8, hence 1208 ordered edges.
   Its origin already paid for 1358 edges at weight `1/50000000`.
5. The allocation `H` adds no origin or pair cost and cancels the summed
   cyclic slack. The far-pair argument in
   [Allocation.lean](lean/D4Bound/Allocation.lean) and
   [the written lemma](verify/stage5_kernelbox/proofs/far_pair_lemma.md)
   raises a group `(N,j)` by `lambda(j) max(Q_N,0)`, with
   `Q_N = N(13561N-179244)/250000`. Stage 5 certifies the two needed
   kernel inequalities on the closed domains `B_1` and `B_5` by replaying
   every leaf of the saved trees. The [exact symbolic link](verify/kernel_link/README.md) binds those
   formulas to the same V7 kernel checked in stage 1 on all 25 radial
   cells and 25 singular angular faces. The [independent reconstruction](verify/kernel_independent/README.md)
   additionally compares all 112 polynomial branches, the seven pair
   pieces, and the origin/objective. Its [written component identities](verify/kernel_independent/COMPONENT_IDENTITIES.md)
   and exact parameter contracts handle nonpolynomial corrections.
   Numerical overlap at sample points alone is not used as an identity proof.
6. [Ledger.lean](lean/D4Bound/Ledger.lean) minimizes the raised floors over
   all groups. The binding group is `(24,1)`. The finite local-energy
   theorem and [Transfer.lean](lean/D4Bound/Transfer.lean) cover arbitrary
   infinite packings, with no lattice or periodicity premise. The final
   exact comparison is

       U_raw - a_new/8 - 3/8000000 < 629521681653/10^12.

The conventional occupied-volume upper density agrees with the centre-count
definition used in Lean: for a unit-separated packing, disjoint radius-1/2
balls centred in the width-1 boundary annulus have total volume `O(R³)`.
Thus the discrepancy between covered volume in `B(0,R)` and the volume per
ball times the number of centres there, divided by `vol(B(0,R))`, tends to
zero. Rescaling a packing of any positive congruent radius to radius `1/2`
preserves density. These two elementary convention changes are written
arguments, not additional numerical inputs.

## Original Lean obligations and current status

| Hypothesis | Exact meaning and discharge outside the main Lean theorem |
|---|---|
| `v7_support` — proved | `K(x,y)=0` when either norm exceeds `7/4`. This is the definition of every component, including both arguments of allocations and gauges. The value at radius exactly `7/4` is retained. |
| `v7_pair` — proved | `f(x)+2K(x,0)+K(x,x)<=0` for every norm at least 1. Stage 1 proves all seven unlifted pieces; the complete count gauge makes the lifted pair zero inside support. The scalar tail handles the exterior. |
| `v7_cyclic` | The sum over the three rooted vertices is nonpositive whenever all three side lengths are at least 1. Stage 1 covers 84 interior and 28 exterior branches; if two sides exceed support, every rooted term vanishes. |
| `v7_raw` — proved | `f(0)+K(0,0)<=8 urawUp`. The stage drivers reconstruct the same rational raw objective from the scalar, origin, count constants and all graph charges. The Lean bridge checks outward rounding. |
| `census` | For an admissible neighbourhood in `InCountDomain`, every matching ledger group has its floor at most `E_(K-Kg)`. Stages 2 and 3 check the census and floors. The count-domain premise is explicit. Given the three near-code bounds and the proved latitude certificates, Lean proves that each admissible neighbourhood lies in that domain; it does not thereby prove the energy-floor inequality. |
| `kernel_box_1` | `-K>=3/10^6 (t^4-a²t²)` on radii `[1,R1]` and `t<=-a`, with `a=133/250`. Stage 5 replays 286 leaves. |
| `kernel_box_5` | The same statement with `1/10^6`, radii `[1,R5]`, and 4663 leaves. |
| `code_24` | `A(4,203/400)<=24`, from `s05075_taper12_exact.json` and its spherical verifier. The original certificate can exclude exactly 25 points; a larger code contains a 25-point subset. |
| `code_25` | `A(4,103/200)<=25`, from `s0515_count25_exact.json`. |
| `code_26` | `A(4,21/40)<=26`, from `s0525_count26_exact.json`. |
| `latitude_15` — proved | `LatSign` with `(r,R)=(R1,R5)`, checked by exact bivariate Bernstein subdivision. |
| `latitude_24` — proved | The same with `(r,R)=(R2,R4)`. `LatSign`, `latP`, `latH`, `latS`, `latC` and `latBeta` match the rational polynomials in `affine_latitude_counts.py`. |
| `annular_151` — proved | `A(4,41/49)<=151`, from the degree-20 polynomial in stage 4. Its rational bound is `151196972764393/999999000000<152`; integrality supplies 151. |
| `svdw` — replaced | The full classical theorem is no longer required. `projected_eight_proved` proves `A(3,223/735) ≤ 8`; `GraphSlackExact.lean` proves that this is sufficient. |

The three near-code inputs are checked by `certify.py` in the stage-1
record and replayed by stage 2. Their exact theorem and cardinality-specific
PSD reduction are in
[the spherical theorem](verify/stage1_v7/proofs/current/base/new_work/spherical_sdp/THEOREM.md).
The latitude formulas and meridian reduction are in
[the affine-latitude proof](verify/stage1_v7/proofs/current/base/new_work/conditional/AFFINE_LATITUDE_THEOREM.md).
The executable is
[affine_latitude_counts.py](verify/stage1_v7/record/current/base/new_work/conditional/affine_latitude_counts.py);
the executable location, rather than that historical note's same-directory
link, is the publication location.

`CountDomain.lean` proves the caps, the two conditional implications, and
the fact that exactly one of the 124 keys covers the neighbourhood.
`GraphSlackExact.lean` proves the exact projected-cosine reduction. The two
latitude certificates, annular151 and projected8 are kernel-checked in their
respective concrete certificate modules. The three near-code count assemblies
now compile with only their respective `OnCube` inputs; complete concrete
sign-tree replay remains. The actual census energy composition similarly
reduces to three physical spherical triangle-sign proofs.

## Analytic component proofs and their scope

These are proofs, not assumptions inferred from successful sampling.

| Component | Analytic basis |
|---|---|
| Gram and spherical kernels | Positive-definiteness of normalized Gegenbauer polynomials on S3 and Legendre polynomials on S2; positive sums of integer outer products; the origin range equation completes a square. |
| Pointed caps | The pair-distance/variance identity bounds occupancy of a ball, followed by averaging over probe directions. The probability is obtained from a uniform coordinate on S2. Its degenerate denominator uses the **closed** ball indicator. [Complete derivation and enclosure argument](verify/stage1_v7/proofs/current/base/new_work/audit/POINTED_VERIFICATION.md). |
| Tents | `sum (1-2|x-c|²)_+ <= 1` follows from the same variance identity. The sharper anchored capacity uses at most four active neighbours and a one-variable monotonicity argument. [Proof](verify/stage1_v7/proofs/current/base/new_work/copositive/TENT_CAPACITY_THEOREM.md). |
| Classical allocation | The modified Blichfeldt profile has capacity at most 1. Its complete elementary proof is included, so the original Blichfeldt paper is attribution, not a missing proof input. [Proof](verify/stage1_v7/proofs/current/base/new_work/copositive/CLASSICAL_SHIFTED_ANTIPODAL_CAPACITY.md). |
| Two-level allocation | With `a+b=1` and `3b²<1`, a closed `b`-ball contains at most two centres; a centre strictly inside radius `a` excludes every other support point. Hence weights 1 on `[0,a)` and 1/2 on `[a,b]` have total at most 1. The exact parameters and endpoint predicate are in [the helper](verify/stage1_v7/record/current/base/new_work/pointed/two_capacity_antipodal_allocation_exact.py). |
| Count gauge | `w=-q0/(1-psi)>=0`, `sum psi<=1` imply `(sum w)(1-sum psi)>=0`; polarization gives pair correction `-q0` and zero origin constant. [Proof](verify/stage1_v7/proofs/current/base/new_work/copositive/ADAPTIVE_COUNT_GAUGES.md). |
| Spherical surplus | Each auxiliary anchor energy is nonnegative; summing yields the scalar bound with exact pair/triple multiplicities. Fixed-cardinality positivity is used only at its declared count, and the uniform certificate only through count 26. [Stage 2](verify/stage2_origin/PROOF.md), [stage 3](verify/stage3_census/finite_count_gain.md). |
| Kernel-box enclosure | Taylor's theorem applies to a smooth lower surrogate; every unresolved kink enters `-K` monotonically with nonnegative coefficient and is replaced by a whole-box lower bound. [Soundness argument](verify/stage5_kernelbox/proofs/kernel_box_method.md). |

The imported proof notes also contain historical diagnostics, unsuccessful
candidates, and references to research logs. Those histories are not inputs
to this bound. In particular graph A and graph B have weight zero here.
The executable read set and current exact data determine the certificate;
no historical numerical search file is needed to verify it.

## Classical mathematical inputs

The two former cited prerequisites now have formal replacements. `SchoenbergS3.lean`
and `SchoenbergS2.lean` prove weighted positivity for every degree; the normalized
Legendre recurrence and value at one are also proved. `ProjectedEightCert.lean`
proves the sufficient projected code bound using six positive Legendre terms,
constant `99999/100000`, and value at one `89804130521/10^10 < 9·99999/100000`.
Its nonpositive sign is checked on the entire closed interval `[-1,223/735]`
using 46 dyadic leaves plus the endpoint. `GraphSlackExact.lean` proves the
geometric reduction to that interval. The full nine-point theorem at `1/3`
is retained below for attribution and as an alternative written argument;
its proof is not needed by the current Lean density theorem.


**Sphere positivity.** The version needed is: for unit vectors on S3,
`U_l(<u,v>)/(l+1)` is positive definite, and on S2 the normalized Legendre
polynomial `P_l(<u,v>)` is positive definite, for every nonnegative degree.
This is the addition theorem/Schoenberg theorem; see I. J. Schoenberg,
*Positive definite functions on spheres*, Duke Math. J. 9 (1942), 96–108,
[DOI](https://doi.org/10.1215/S0012-7094-42-00908-6).
The S2 case is used in the transverse blocks of the spherical certificates
and in the original broad-graph degree-nine argument. The package now includes separate Lean proofs of both instances; proving
only the S3 case would not remove the S2 dependency. The two Gegenbauer
parameters are respectively 1 and 1/2. Polynomial identities alone do not
prove positive definiteness.

**Nine points on S2.** K. Schütte and B. L. van der Waerden,
*Auf welcher Kugel haben 5, 6, 7, 8 oder 9 Punkte mit Mindestabstand Eins
Platz?*, Math. Ann. 123 (1951), 96–124, is cited through the explicit
statement in A. Barg and O. R. Musin, *Codes in spherical caps*, Adv. Math.
Commun. 1 (2007), 131–149,
[arXiv:math/0606734v2](https://arxiv.org/abs/math/0606734v2), article pages
8–9, item 2 after Corollary 2. Page 8 defines `phi_n(M)` as the largest
possible minimum angular separation of an `M`-point code on `S^(n-1)`;
page 9 states `phi_3(9)=arccos(1/3)`.
The saved v2 text was opened during the original source audit; the 1951
article was not opened and its proof is not reproduced here. The current
projected8 certificate supplies the needed conclusion independently.

Only the upper bound on separation is needed. It says that nine **distinct**
unit vectors have a pair with cosine at least `1/3`. The historical Lean nine-point interface permits
repeated vectors as well: two repeated entries have cosine 1, which gives
the same conclusion. In the graph proof the projected cosines are at most
`223/735`, and

    1/3 - 223/735 = 22/735 > 0.

Thus there is a strict contradiction for nine neighbours. No uniqueness,
classification of equality cases, unproved numerical Tammes value, or
claim about a strict inequality at `1/3` is used. The zero-projection case
has degree at most one and is treated before normalization.

## Verification versus source review

This document records the mathematical dependency audit, not a substitute
for replay. A fresh full run must exit zero, certify every stage and exact
kernel comparison, and recompute the final rational inequality. A clean
Lean build and the printed axiom list are separate evidence. Compiler or
interpreter failures, missing result files, partial branch runs, and
sampled comparisons are not successful certification. The current run
receipt belongs with the publication's verification report.
