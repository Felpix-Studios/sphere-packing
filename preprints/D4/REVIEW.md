# D4 publication verification review

## Current formalization status

Documentation audit: 2026-11-13. The current
[concrete theorem](lean/D4Bound/ConcreteMain.lean) defines `V7.kernel` and has
**seven remaining certificate premises**: cyclic sign, census floor, two
kernel-box inequalities, and the three near-code bounds. The support, pair
sign, raw objective, both latitude certificates, annular151 and sufficient
projected-eight bound have individual compiled proofs. S² and S³ positivity
are also formalized. The [dependency map](PROOF_DEPENDENCIES.md) and
[Lean README](lean/README.md) describe the current interfaces.

**The final clean build of the expanded project is pending.** The full
concrete spherical sign-tree replay in Lean is also unfinished; its generic soundness
lemmas, polynomial identities and partial checks do not establish the three
near-code premises. Finite census checks and component-energy identities do
not by themselves establish `CensusFloor V7.kernel`; the concrete analytic
comparison remains a separate obligation. The cyclic and kernel-box premises
also remain explicit. Successful compilation of this theorem therefore still
checks a conditional implication, not an unconditional formal packing bound.

At the requested pause, the actual twelve affine census floors and ungauged
pair sign have been integrated. `D4Bound.V7.censusFloor_of_triangles`, defined
in `V7CensusFromSigns.lean`, requires only the three physical spherical
triangle-sign statements. A separate coordinator compilation checked that
interface and six associated axiom reports; all use only the allowed three
axioms. The three near-code count-bound assemblies also compile with only
their respective `OnCube` inputs. These component results reduce the remaining
work but do not change the seven-premise concrete density theorem.

The dated recovery record below is preserved as historical evidence. Its
22-module/53-axiom build, source comparison and driver-composition receipt
refer to the earlier recovery snapshot, **not** the subsequently expanded
Lean tree. Its statements that the concrete kernel was outside Lean and two
classical inputs remained cited describe that earlier state. The previous
five-stage exact/interval replay remains evidence for the external
computer-assisted route; this documentation audit did not repeat it or claim
a completed build of the new formalization.

## Historical recovery record

Date: 2026-11-13. Scope: the existing global upper bound **0.629521681653**, for all sphere packings in R4. This is publication recovery and certification, not a new bound or a proof that D4 is optimal.

## Proof and dependency review

The [dependency audit](PROOF_DEPENDENCIES.md) reviews the written reductions and maps the current fourteen Lean hypotheses to exact certificate statements or cited theorems. A separate agent reviewed these reductions; this is source review, not a certificate rerun. The omitted pointed-cap derivation was restored verbatim and included in the stage-1 manifest. The original pinned files under the stage-1 `record/` are unchanged.

The complete proof consists of the written arguments, all five certificate stages, the two kernel links, and Lean. It is not an unconditional end-to-end Lean proof: the concrete V7 kernel and the external certificate checkers remain outside Lean. Schoenberg positivity on S2 and the Schütte–van der Waerden nine-point theorem remain cited. The S3 instance is proved in Lean for every degree.

## Completed clean-build checks

A clean copy omitted all project build products. Its Lean build used the pinned third-party Mathlib v4.33.1 cache; no publication `.olean` files were reused. The copied publication has no dependency on private mathematical source files.

| Check | Result |
|---|---|
| Serial Lean build | PASS: 22 publication modules, 334.15 seconds |
| Lean axiom audit | PASS: all 53 listed theorems use only `propext`, `Classical.choice`, `Quot.sound` |
| Stage-1/stage-5 exact link | PASS: 25 radial cells, 25 singular endpoint faces, 213,550 polynomial coefficients, 1,655 nonpolynomial monomials |
| Kernel-link failure controls | PASS: all five deliberate corruptions rejected |
| Driver rejection tests | PASS: seven tests, including fractional/float counts, missing/duplicate groups, negative or inexact floors, incomplete/unapproved axiom reports, optimized Python, and OS-metadata versus unlisted-code handling |
| Lean scalar/ledger input checks | PASS: exact generated scalar sources and outward-rounded ledger constants; an isolated nonintegral-count corruption was rejected |
| Preprint | Rebuilt from included LaTeX source; all 12 pages rendered and visually reviewed; no overfull boxes or undefined references |

[Lean result](verify/recorded/lean.json) and [exact kernel link result](verify/recorded/kernel_link.json) retain the machine-readable outcomes. The clean Lean guard measured 3,502,325,760 bytes aggregate peak RSS, mostly mapped Mathlib code; serial compilation avoids parallel memory multiplication. The clean kernel-link replay used 277,692,416 bytes aggregate peak RSS.

## Certificate replay

All five core stages passed together from the clean copy, with terminal exit 0 (1,971.7 seconds in the driver; 1,975.6 seconds including the guard). The exact objective is retained in [core.json](verify/recorded/core.json); its displayed approximation is 0.629521681652092, strictly below **629521681653/1000000000000**.

| Stage | Fresh result | Seconds |
|---|---|---:|
| V7 signs | PASS: all 112 cyclic branches | 1,475.0 |
| Origin credit | PASS: 165,503 count vectors | 102.0 |
| Census | PASS: 124 group floors | 0.2 |
| Graph slack | PASS: exact count/slack checks | 0.12 |
| Far-pair kernel boxes | PASS: both trees, 286 and 4,663 leaves | 394.1 |
| Independent kernel reconstruction | PASS: 112 branches, 1,059,688 polynomial coefficients, seven pair pieces, 775 exact component equations | 622.8 |

The independent reconstruction was rerun by its author on the final hardened implementation; its [result](verify/kernel_independent/evidence/RESULT.json), [terminal receipts](verify/kernel_independent/evidence/TERMINATION.json), and [failure controls](verify/kernel_independent/evidence/CONTROLS.json) are included. Both deliberate mutations and all fourteen malformed-input cases were rejected. The coordinator separately reran the stage-5 controls: excessive lambda and merged leaves both failed closed ([result](verify/recorded/kernel_box_controls.json)).

The final extended driver was checked by composing these separately fresh, terminal passing outputs with the clean kernel-link and Lean outputs, and rerunning its scalar/ledger gates. [composition.json](verify/recorded/composition.json) records this integration check explicitly. This was not one uninterrupted execution of the extended driver, and the composition step did not rerun certificate signs.

The [source comparison](verify/recorded/source_comparison.json) found no mathematical checker, certificate-data, or Lean-source changes between the tested clean copy and the release. Reviewed wrapper differences ignore only Finder `.DS_Store` metadata in stage 1 and isolate stage-5 negative-control fixtures from build caches; those behaviors were tested separately. Manifests and documentation were updated accordingly. The final driver wiring was checked by the composition above. The core guard measured 1,001,324,544 bytes aggregate peak RSS.

## Reproduction commands

From this D4 folder, after installing the dependencies in the READMEs:

```sh
python3 verify/verify_all.py --out /tmp/d4-full --mode full --workers 2 --lean
python3 -m unittest discover -s verify -p test_driver.py -v
python3 verify/kernel_independent/negative_controls.py --out /tmp/d4-independent-controls
python3 verify/stage5_kernelbox/negative_controls.py --work /tmp/d4-box-controls --workers 2
```

All output directories must be new. The normal driver runs the exact kernel-link controls internally. Quick mode omits the 112 cyclic subdivisions and is not a fresh global-certificate replay.

## Trust and attribution

The independent assembler was written separately from stage 1/5, with the earlier source inspected to resolve conventions; it is not clean-room code. Exact coefficient equality covers the polynomial assembly. Its nonpolynomial components are identified by [written formulas](verify/kernel_independent/COMPONENT_IDENTITIES.md), checked exact parameters and boundary conventions; sampled agreement is diagnostic only. The coordinator reviewed the cap truncation inequality, full-branch vanishing arguments, allocation joins and gauge cancellation. The stage-5 symbolic adapters likewise have a documented mathematical meaning; they are not a formal semantics proof of Python.

The computation trusts the stated Python/FLINT/Arb/C++ arithmetic stack. The interval lower-envelope proof and cited theorems remain explicit in the package. Hash manifests establish input identity, not mathematical correctness. Separate agents performed the component proof audit and kernel-link author replay; the coordinator performed the clean builds and integration checks. No external human review is claimed.

## Follow-up completeness audit

The 2026-11-13 follow-up reviewed the supplied missing-verifier critique against the actual stage drivers, Lean theorem applications, written component arguments, and files eligible for Git inclusion. All 229 rows in the six top-level stage/independent manifests existed, matched their declared hashes and byte counts, and were included in the prospective publication set. No mathematical source/data file examined was ignored, and no publication symlinks were found. README links and the revised ignore behavior passed focused checks.

The missing pair/triangle, census, spherical-certificate and kernel-evaluator objections are addressed by the included files. In the separate Lean formalization, allocation and arbitrary-packing density transfer are proved in Lean. The non-Lean path instead uses the written density-transfer theorem and its exact/interval certificate replay. This was a source and publication-completeness audit, not another expensive sign replay or a new line-by-line audit of every inherited arithmetic engine. The preceding fresh-run evidence remains the computational basis.

## Non-Lean proof path

The preceding paragraphs describe the separate Lean formalization and its historical
replay. The public non-Lean proof path is now intentionally independent: `verify_all.py`
does not import or invoke Lean, and the written periodic-patch argument in `paper.tex`
and `verify/stage5_kernelbox/proofs/conditional_theorem.md` supplies the passage from
finite certificate inequalities to arbitrary-packing density. A clean non-Lean replay
therefore requires only the files in `data/` and `verify/`, together with the pinned
Python/FLINT/Arb/C++ dependencies.

## Solo continuation checkpoint — 2026-11-13

All delegated workers and proof processes were explicitly stopped and reaped before
solo continuation. The remaining seven theorem premises are unchanged. An attempt
to lower the peak memory of the degree-16 surplus transform split the 17 matrix
rows into smaller modules; even a single row still exceeded 4 GB during kernel
reduction, so no row certificate was accepted. The split is retained as an
unaccepted work-in-progress source and must not be counted as a proof. No final
clean build or unconditional theorem claim is made from this checkpoint.

## Solo build optimization checkpoint — 2026-11-14

The isolated verifier now schedules dependency-ready Lean modules in batches
of at most two, including replay shards. It remains dependency-safe, compiles
every staged source (including otherwise unimported sources), and stays within
the documented aggregate-memory limit. The driver and replay-staging
regression tests pass after this change.

A fresh shard-256 run regenerated all six complete replay families and entered
the publication build. A single 256-node state module compiled in isolation
with about 1.3 GiB RSS; the first large check shard also compiled successfully
under the two-worker scheduler. The full run is still compiling Code24 replay
shards. This is a resource-saving build experiment, not a completion receipt.
The unconditional bound remains unverified and the seven concrete certificate
premises remain open as described above.
