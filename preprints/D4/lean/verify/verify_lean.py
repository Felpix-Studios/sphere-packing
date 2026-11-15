#!/usr/bin/env python3
"""Compile every publication module from source, then audit declared axioms.

Run from the lean folder: python3 verify/verify_lean.py --out NEW_DIRECTORY [--workers N]
Mathlib and elan must already be installed; no dependency update is performed.

This build reads nothing outside the lean folder.  It shares no code, input or result
with the non-Lean checkers in D4/verify.  `--check-generators` is a separate, optional
comparison of the Lean data modules with the certificate files of the D4 package.

Finite certificate checks use `native_decide`.  The modules in NATIVE_LIBRARIES hold
the executable checkers; they import only `Init`, so this driver compiles each to C,
links it with the toolchain's `leanc` and loads it (`--load-dynlib`) into every later
module that imports it.  Without that the checks run in the interpreter and take hours.
The bundled C compiler is then part of the trust base, together with the Lean compiler.

Each Lean process peaks near 3.5 GB; choose --workers to fit the machine.
"""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

LEAN = Path(__file__).resolve().parents[1]

# Optional provenance check (--check-generators): each entry is a script in scripts/ and
# its arguments; `--check` is appended.  These read certificate files of the D4 package.
GENERATORS = (
    "gen_scalar.py", "gen_v7.py", "gen_latitude.py", "gen_census.py",
    "gen_census_proofs.py", "gen_spherical_annular.py", "gen_projected_eight.py",
    "gen_spherical_angular.py", "gen_spherical_sign.py", "gen_spherical_sign_pair.py",
    "gen_spherical_sign_rays.py", "gen_spherical_sign_tensor.py",
    "gen_spherical_array_data.py", "gen_spherical_affine.py", "gen_spherical_power.py",
    "gen_spherical_raw.py", "gen_spherical_transform.py", "gen_spherical_concrete.py",
    "gen_moderate_graph.py",
    "gen_census_gram.py", "gen_census_gram_data.py",
    "gen_census_gram_planes.py", "gen_census_gram_checks.py",
    "gen_spherical_surplus_affine.py", "gen_spherical_surplus_bounds.py",
    "gen_spherical_surplus_data.py", "gen_spherical_surplus_energy.py",
    "gen_spherical_surplus_pair.py", "gen_spherical_surplus_physical.py",
    "gen_spherical_surplus_power.py", "gen_spherical_surplus_raw.py",
    "gen_spherical_surplus_sign_bounds.py", "gen_spherical_surplus_sign.py",
    "gen_spherical_surplus_table.py", "gen_spherical_surplus_triangle.py",
    *(f"{name} --index {index}" for name in
      ("gen_spherical_surplus_transform.py", "gen_spherical_surplus_tree.py")
      for index in (0, 1, 2)),
)
# Kernel-replay shards are generated into an isolated build, never published.
REPLAY_FOLDER = Path("D4Bound/ReplayGenerated")
SURPLUS_FOLDER = Path("D4Bound/SurplusReplayGenerated")

# Init-only checker modules that are precompiled and loaded as shared libraries.
NATIVE_LIBRARIES = (
    "D4Bound.CyclicNativeCore", "D4Bound.CyclicNativePoly", "D4Bound.CyclicNativeCorr",
    "D4Bound.CyclicNativeFullGThr", "D4Bound.CyclicNativeAllocLo", "D4Bound.CyclicNativeExtCorr",
)
LIBRARY_SUFFIX = ".dylib" if sys.platform == "darwin" else ".so"

STANDARD_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
NATIVE_AXIOM_MARK = "._native.native_decide.ax_"

# The final closure gate is a typed application, not a name/axiom-list heuristic.
CLOSED_BOUND_CHECK = """example (P : Set D4Bound.E4) (hP : D4Bound.IsUnitPacking P) :
    D4Bound.upperDensity P < ENNReal.ofReal (629521681653 / 1000000000000) :=
  D4Bound.d4_density_bound_concrete P hP
"""


def audit_axioms(text, expected):
    """Return the printed axioms of each expected theorem; reject anything unapproved.

    Approved: the three standard axioms and the per-use axioms of `native_decide`.
    A theorem with no `#print axioms` line in the log is a failure, not a pass.
    """
    found = {name: [] for name in re.findall(r"'([^']+)' does not depend on any axioms", text)}
    for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        found[name] = [item.strip() for item in body.split(",") if item.strip()]
    result = {}
    for name in expected:
        if name not in found:
            raise ValueError(f"no axiom report for {name}")
        bad = [axiom for axiom in found[name]
               if axiom not in STANDARD_AXIOMS and NATIVE_AXIOM_MARK not in axiom]
        if bad:
            raise ValueError(f"{name} depends on unapproved axioms: {bad}")
        result[name] = found[name]
    return result


def publication_sources(lean):
    """Inventory sources without resolving imports into not-yet-generated files."""
    paths = {Path("D4Bound.lean"), Path("Check.lean")}
    paths.update(path.relative_to(lean) for path in (lean / "D4Bound").rglob("*.lean"))
    if any(path.is_relative_to(folder) for path in paths
           for folder in (REPLAY_FOLDER, SURPLUS_FOLDER)):
        raise ValueError("generated replay files belong in the isolated build, not publication sources")
    return sorted(paths)


def module_order(root):
    ordered, visiting, done = [], set(), set()
    def visit(name):
        if name in done:
            return
        if name in visiting:
            raise ValueError(f"cyclic Lean imports at {name}")
        visiting.add(name)
        path = root / (name.replace(".", "/") + ".lean")
        for dependency in re.findall(r"^import\s+(D4Bound(?:\.\w+)*)\s*$", path.read_text(), re.M):
            visit(dependency)
        visiting.remove(name)
        done.add(name)
        ordered.append(name)
    visit("D4Bound")
    # An unfinished or accidentally unimported file must not silently escape the
    # full compilation. Check every source, including independent check modules.
    for path in sorted((root / "D4Bound").rglob("*.lean")):
        visit(".".join(path.relative_to(root).with_suffix("").parts))
    return ordered


def clean_environment(lean, build):
    """Reuse public dependency artifacts, never this project's old oleans."""
    lake = shutil.which("lake")
    if not lake:
        raise ValueError("lake is not on PATH; install elan and the pinned dependencies")
    paths = subprocess.run([lake, "env", "printenv", "LEAN_PATH"], cwd=lean,
                           text=True, capture_output=True, check=True).stdout.strip()
    compiler = subprocess.run([lake, "env", "which", "lean"], cwd=lean,
                              text=True, capture_output=True, check=True).stdout.strip()
    if not Path(compiler).is_file():
        raise ValueError("could not resolve the pinned Lean compiler")
    old_build = (lean / ".lake/build").resolve()
    dependencies = []
    for entry in paths.split(os.pathsep):
        if not entry:
            continue
        path = Path(entry)
        if not path.is_absolute():
            path = lean / path
        path = path.resolve()
        if path.is_relative_to(old_build) or path.is_relative_to(lean.resolve()):
            continue
        if (path / "D4Bound.olean").exists() or (path / "D4Bound").exists():
            raise ValueError(f"dependency path contains cached publication modules: {path}")
        dependencies.append(str(path))
    if not dependencies:
        raise ValueError("no installed Lean/Mathlib dependency paths found")
    env = dict(os.environ, LEAN_NUM_THREADS="1",
               LEAN_PATH=os.pathsep.join([str(build), *dependencies]))
    return compiler, env


def snapshot_sources(lean, destination, order=None):
    """Give this expensive compilation an exact, stable source identity."""
    manifest = {}
    paths = publication_sources(lean) if order is None else [
        *[Path(name.replace(".", "/") + ".lean") for name in order], Path("Check.lean")]
    for relative in paths:
        data = (lean / relative).read_bytes()
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        manifest[str(relative)] = hashlib.sha256(data).hexdigest()
    return manifest


def unchanged_sources(lean, manifest):
    return all((lean / path).is_file() and
               hashlib.sha256((lean / path).read_bytes()).hexdigest() == digest
               for path, digest in manifest.items())


def _imports(source):
    """Return publication-module imports from one staged source file."""
    return re.findall(r"^import\s+(D4Bound(?:\.\w+)*)\s*$", source.read_text(), re.M)


def all_imports(source):
    return re.findall(r"^import\s+(\S+)\s*$", source.read_text(), re.M)


def build_library(compiler, c_file, library):
    """Link one Lean-emitted C file into a shared library that exports its symbols."""
    partial = library.with_name(library.name + ".partial")
    # LEAN_EXPORTING makes lean.h export the module symbols.  Without it the library
    # exports nothing and native_decide silently falls back to the interpreter.
    command = [str(Path(compiler).with_name("leanc")), "-shared", "-O3", "-DNDEBUG",
               "-DLEAN_EXPORTING", "-o", str(partial), str(c_file)]
    if sys.platform == "darwin":
        command.append("-Wl,-undefined,dynamic_lookup")
    subprocess.run(command, check=True, capture_output=True)
    symbols = subprocess.run(["nm", "-g", str(partial)], text=True, capture_output=True,
                             check=True).stdout
    if " T " not in symbols:
        raise ValueError(f"{library.name} exports no text symbols")
    os.replace(partial, library)


def compile_modules(order, source_root, build, compiler, env, out, workers=2,
                    libraries=NATIVE_LIBRARIES):
    """Compile the staged project, at most `workers` modules at a time.

    A module starts only after its in-project imports have produced oleans.  Targets
    that already exist are kept, so an interrupted run can resume on the same frozen
    sources.  Returns (seconds per compiled module, native library records).
    """
    logs, native = out / "logs", out / "native"
    logs.mkdir(exist_ok=True)
    native.mkdir(exist_ok=True)

    def source(name):
        return source_root / (name.replace(".", "/") + ".lean")

    def target(name):
        path = build / (name.replace(".", "/") + ".olean")
        path.parent.mkdir(parents=True, exist_ok=True)
        return path

    def library(name):
        return native / (name + LIBRARY_SUFFIX)

    if set(libraries) - set(order):
        raise ValueError(f"native library modules missing from the sources: {sorted(set(libraries) - set(order))}")
    for name in libraries:
        for dependency in all_imports(source(name)):
            if dependency not in libraries and dependency != "Init" and not dependency.startswith("Init."):
                raise ValueError(f"native library {name} imports {dependency}; only Init is allowed")
    imports = {name: _imports(source(name)) for name in order}
    needs = {}
    for name in order:
        needs[name] = {lib for dep in imports[name] for lib in needs[dep] | ({dep} & set(libraries))}

    def finished(name):
        return target(name).is_file() and (name not in libraries or library(name).is_file())

    children = set()

    def run_one(name):
        start = time.monotonic()
        partial = target(name).with_name(target(name).name + ".partial")
        command = [compiler, "-R", str(source_root), "-o", str(partial)]
        command += [f"--load-dynlib={library(dep)}" for dep in order if dep in needs[name]]
        c_file = native / (name + ".c")
        if name in libraries:
            command += ["-c", str(c_file)]
        log_path = logs / f"{name}.log"
        print("Building", name, flush=True)
        with log_path.open("w") as log:
            child = subprocess.Popen([*command, str(source(name))], cwd=source_root, env=env,
                                     stdout=log, stderr=subprocess.STDOUT)
            children.add(child)
            code = child.wait()
            children.discard(child)
        if code:
            raise ValueError(f"{name} failed with exit {code}; see logs/{name}.log")
        if re.search(r"declaration uses .sorry.", log_path.read_text()):
            raise ValueError(f"sorry warning in {name}")
        if name in libraries:
            build_library(compiler, c_file, library(name))
        os.replace(partial, target(name))
        return round(time.monotonic() - start, 1)

    pending = [name for name in order if not finished(name)]
    built = set(order) - set(pending)
    running, seconds = {}, {}
    with ThreadPoolExecutor(max_workers=workers) as pool:
        try:
            while pending or running:
                for name in [n for n in pending if all(dep in built for dep in imports[n])]:
                    if len(running) >= workers:
                        break
                    pending.remove(name)
                    running[pool.submit(run_one, name)] = name
                if not running:
                    raise ValueError("module dependency cycle or missing import")
                for future in wait(running, return_when=FIRST_COMPLETED)[0]:
                    name = running.pop(future)
                    seconds[name] = future.result()
                    built.add(name)
        except BaseException:
            for child in list(children):
                child.terminate()
            raise
    records = [{"module": name,
                "c_sha256": hashlib.sha256((native / (name + ".c")).read_bytes()).hexdigest(),
                "library_sha256": hashlib.sha256(library(name).read_bytes()).hexdigest()}
               for name in order if name in libraries]
    return seconds, records


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--workers", type=int, default=2,
                    help="concurrent Lean processes, about 3.5 GB each (default: 2)")
    ap.add_argument("--resume", action="store_true",
                    help="continue an interrupted run in --out; the sources must be unchanged")
    ap.add_argument("--check-generators", action="store_true",
                    help="also compare the generated Lean data with the D4 certificate files")
    ap.add_argument("--require-unconditional", action="store_true",
                    help="also require the concrete bound to take only P and IsUnitPacking P")
    args = ap.parse_args()
    if args.workers < 1:
        ap.error("--workers must be positive")
    out = args.out.resolve()
    lean = LEAN
    source_root, manifest_path = out / "source", out / "SOURCE_MANIFEST.json"
    if args.resume and not manifest_path.is_file():
        ap.error("--resume needs an earlier run in --out")
    out.mkdir(parents=True, exist_ok=args.resume)
    result = {"stage": "lean", "status": "FAIL"}
    start = time.monotonic()
    try:
        (out / "generators").mkdir(exist_ok=True)
        for generator in GENERATORS if args.check_generators else ():
            script, *arguments = generator.split()
            with (out / "generators" / f"{generator.replace(' ', '_')}.log").open("w") as log:
                subprocess.run([sys.executable, str(lean / "scripts" / script), *arguments, "--check"],
                               cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)
        result["generated_sources_checked"] = list(GENERATORS) if args.check_generators else []
        if args.resume:
            source_manifest = json.loads(manifest_path.read_text())
        else:
            source_manifest = snapshot_sources(lean, source_root)
            manifest_path.write_text(json.dumps(source_manifest, indent=2) + "\n")

        def frozen():
            return (unchanged_sources(lean, source_manifest)
                    and set(map(str, publication_sources(lean))) == set(source_manifest)
                    and unchanged_sources(source_root, source_manifest)
                    and set(map(str, publication_sources(source_root))) == set(source_manifest))

        if not frozen():
            raise ValueError("publication sources differ from the frozen snapshot")
        order = module_order(source_root)
        build = out / "oleans"
        build.mkdir(exist_ok=args.resume)
        compiler, env = clean_environment(lean, build)
        seconds, libraries = compile_modules(order, source_root, build, compiler, env, out,
                                             args.workers)
        (out / "MODULE_SECONDS.json").write_text(json.dumps(seconds, indent=2) + "\n")
        # Import every compiled source into the audit environment, including
        # declarations that the main theorem does not depend on.
        check_source = (source_root / "Check.lean").read_text()
        full_check = out / "FullCheck.lean"
        full_check.write_text("\n".join(f"import {name}" for name in order) + "\n" +
                              re.sub(r"^import .*\n", "", check_source, flags=re.M) + "\n" +
                              (CLOSED_BOUND_CHECK if args.require_unconditional else ""))
        with (out / "axioms.log").open("w") as log:
            subprocess.run([compiler, "-R", str(out), str(full_check)], cwd=lean, env=env,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        expected = re.findall(r"^#print axioms (\S+)", check_source, re.M)
        if not {"D4Bound.d4_density_bound", "D4Bound.d4_density_bound_concrete"} <= set(expected):
            raise ValueError("Check.lean omits a main theorem")
        audit_text = (out / "axioms.log").read_text()
        counts = re.findall(r"D4_ALL_THEOREMS_AXIOM_AUDIT_PASS (\d+) NATIVE_AXIOMS (\d+)", audit_text)
        if len(counts) != 1 or int(counts[0][0]) == 0:
            raise ValueError("missing complete publication-theorem axiom audit")
        if not frozen() or module_order(source_root) != order:
            raise ValueError("publication sources changed during compilation; rerun on the final sources")
        result.update(modules=order, clean_project_build=not args.resume, resumed=args.resume,
                      all_theorems_audited=int(counts[0][0]), native_axioms=int(counts[0][1]),
                      native_libraries=libraries,
                      source_manifest="SOURCE_MANIFEST.json", sources_unchanged=True,
                      unconditional_bound_checked=args.require_unconditional,
                      scope=("Compilation, axiom audit and concrete density theorem with only packing inputs."
                             if args.require_unconditional else
                             "Compilation and axiom audit. Explicit theorem premises are printed in axioms.log; PASS does not assert their discharge."),
                      axioms=audit_axioms(audit_text, expected),
                      status="PASS")
    except Exception as exc:
        result["error"] = f"{type(exc).__name__}: {exc}"
    result["seconds"] = round(time.monotonic() - start, 2)
    (out / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"], result.get("error", "build and axiom audit"), flush=True)
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
