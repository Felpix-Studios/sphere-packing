# Isolated Lean build

`verify_lean.py` compiles every Lean module of the publication from source in a
new directory, then audits the axioms of every theorem. It needs no private
checkout and no earlier build products.

The Lean proof is separate from the non-Lean computer-assisted proof in
`../../verify`. This build reads nothing outside the `lean` folder and shares no
code, input or result with those checkers.

From this `lean` folder, after installing the pinned Lean and Mathlib dependencies:

```sh
python3 verify/verify_lean.py --out /tmp/d4-lean-clean --workers 4 --require-unconditional
```

The output directory must not already exist. The driver:

1. Copies every publication Lean module and `Check.lean` into `source/` and
   records their SHA-256 values in `SOURCE_MANIFEST.json`.
2. Sorts the complete tree by imports and compiles every module to a new
   `oleans/` directory. A module under `D4Bound/` that nothing imports is still
   compiled. Existing publication `.olean` files are excluded; installed public
   dependency artifacts may be reused.
3. Compiles the modules listed in `NATIVE_LIBRARIES` to C (`lean -c`), links
   each with the toolchain's `leanc` into `native/`, and loads the libraries
   (`--load-dynlib`) into every later module that imports them. These modules
   hold the executable certificate checkers and import only `Init`; the driver
   rejects a listed module that imports anything else.
4. Fails on a compiler error, on a `sorry` warning, and stops the other running
   compilers when one module fails.
5. Imports every compiled module into one audit file with the body of
   `Check.lean`. Every theorem named `D4Bound.*` may depend only on `propext`,
   `Classical.choice`, `Quot.sound` and the per-use axioms that `native_decide`
   adds. Anything else, including `sorryAx` and a declared axiom, fails.
6. Checks again that the publication sources and the staged copy are unchanged.

`RESULT.json` records the module list, the number of audited theorems, the
number of `native_decide` axioms, the hashes of the emitted C files and
libraries, and the printed axioms of each theorem named in `Check.lean`.
`MODULE_SECONDS.json` has the compile time of each module and `logs/` has one
log per module.

## What `native_decide` adds to the trust base

The large finite checks (the near-code and surplus Bernstein trees, the kernel
box search and the cyclic sign cases) are single `native_decide` evaluations of
checkers whose soundness theorems are kernel-checked. Each use adds one axiom
`NAME._native.native_decide.ax_N` and trusts the Lean compiler. The cyclic sign
checkers also run as precompiled libraries, which adds the C compiler bundled
with the toolchain. The mathematical reductions and every soundness proof use
only the three standard axioms.

## Options

- `--workers N` runs up to N Lean processes at once (default 2). Each peaks near
  3.5 GB. The longest modules are the three surplus trees, more than an hour
  each in the interpreter; they need about 1 to 2.5 GB and run well in parallel.
- `--check-generators` also runs each source generator in `scripts/` with
  `--check`. This compares the Lean data modules with the certificate files of
  the D4 package (`../data`, `../verify`). It is a provenance check: it shows
  both proofs use the same certificate. The Lean proof does not depend on it.
- `--resume` continues an interrupted run in the same `--out`. It reuses the
  oleans already written there and refuses to start if any source differs from
  `SOURCE_MANIFEST.json`. `RESULT.json` then records `resumed: true`.
- `--require-unconditional` is the proof-closure gate. It adds a typed Lean
  application of `d4_density_bound_concrete` to a set of centres and its
  `IsUnitPacking` proof alone, at the claimed density ceiling. It fails while
  the concrete theorem keeps any certificate premise. Without this flag a PASS
  records compilation and the axiom audit only; `RESULT.json` states
  `unconditional_bound_checked` either way.

## Recorded build

`recorded/` holds the files of the clean build of 2026-11-15: `lean.json`
(`RESULT.json`), `axioms.log`, `MODULE_SECONDS.json` and `SOURCE_MANIFEST.json`.

## Tests

```sh
python3 -m unittest discover -s verify -p test_lean_driver.py -v
```

The tests cover import ordering, the frozen-source checks, the scheduler
(failure, `sorry`, resume, library loading order) and the axiom audit. They use
a stand-in compiler and do not certify the publication's proofs.
