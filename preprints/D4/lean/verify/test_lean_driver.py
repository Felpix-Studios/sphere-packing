"""Coverage failures in the full Lean build, using temporary source fixtures."""
import tempfile
import unittest
import subprocess
from pathlib import Path
from unittest.mock import patch

from verify_lean import (module_order, snapshot_sources, unchanged_sources, publication_sources,
                         clean_environment, compile_modules, audit_axioms,
                         REPLAY_FOLDER, SURPLUS_FOLDER, LIBRARY_SUFFIX)


class LeanBuildCoverage(unittest.TestCase):
    def test_all_sources_are_checked_in_dependency_order(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "D4Bound").mkdir()
            (root / "D4Bound.lean").write_text("import D4Bound.A\n")
            (root / "D4Bound/A.lean").write_text("import D4Bound.B\n")
            (root / "D4Bound/B.lean").write_text("")
            (root / "D4Bound/Unimported.lean").write_text("import D4Bound.B\n")
            order = module_order(root)
            self.assertEqual(set(order), {"D4Bound", "D4Bound.A", "D4Bound.B", "D4Bound.Unimported"})
            self.assertLess(order.index("D4Bound.B"), order.index("D4Bound.A"))

    def test_cycles_and_missing_sources_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "D4Bound").mkdir()
            (root / "D4Bound.lean").write_text("import D4Bound.A\n")
            with self.assertRaises(FileNotFoundError):
                module_order(root)
            (root / "D4Bound/A.lean").write_text("import D4Bound\n")
            with self.assertRaises(ValueError):
                module_order(root)

    def test_build_snapshot_preserves_input_and_detects_edits(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "project"
            snapshot = Path(directory) / "source"
            root.mkdir()
            (root / "D4Bound.lean").write_text("-- original\n")
            (root / "Check.lean").write_text("import D4Bound\n")
            manifest = snapshot_sources(root, snapshot, ["D4Bound"])
            self.assertTrue(unchanged_sources(root, manifest))
            (root / "D4Bound.lean").write_text("-- edited while compiling\n")
            self.assertFalse(unchanged_sources(root, manifest))
            self.assertEqual((snapshot / "D4Bound.lean").read_text(), "-- original\n")
            (root / "Check.lean").unlink()
            self.assertFalse(unchanged_sources(root, manifest))

    def test_snapshot_precedes_generated_import_resolution(self):
        with tempfile.TemporaryDirectory() as directory:
            root, snapshot = Path(directory) / "project", Path(directory) / "snapshot"
            (root / "D4Bound").mkdir(parents=True)
            (root / "D4Bound.lean").write_text("import D4Bound.ReplayGenerated.Code24.Result\n")
            (root / "Check.lean").write_text("import D4Bound\n")
            snapshot_sources(root, snapshot)
            self.assertEqual((snapshot / "D4Bound.lean").read_text(), (root / "D4Bound.lean").read_text())
            with self.assertRaises(FileNotFoundError):
                module_order(snapshot)

    def test_published_generated_cache_rejected(self):
        for folder in (REPLAY_FOLDER, SURPLUS_FOLDER):
            with self.subTest(folder=folder), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / folder).mkdir(parents=True)
                (root / folder / "Cached.lean").write_text("-- stale\n")
                with self.assertRaisesRegex(ValueError, "isolated build"):
                    publication_sources(root)

    def test_foreign_publication_olean_dependency_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            lean, dependency = root / "lean", root / "foreign"
            lean.mkdir()
            dependency.mkdir()
            (dependency / "D4Bound.olean").write_text("old artifact")
            compiler = root / "lean-bin"
            compiler.touch()
            replies = [subprocess.CompletedProcess([], 0, str(dependency)),
                       subprocess.CompletedProcess([], 0, str(compiler))]
            with patch("verify_lean.shutil.which", return_value="lake"), \
                    patch("verify_lean.subprocess.run", side_effect=replies), \
                    self.assertRaisesRegex(ValueError, "cached publication"):
                clean_environment(lean, root / "build")


FAKE_COMPILER = """#!/bin/sh
echo "ARGS $*"
while [ $# -gt 1 ]; do
  case "$1" in -o) out="$2"; shift;; -c) : > "$2"; shift;; esac
  shift
done
if grep -q FAIL "$1"; then exit 1; fi
if grep -q SORRY "$1"; then echo 'T.lean:1:8: warning: declaration uses `sorry`'; fi
: > "$out"
"""


class Scheduler(unittest.TestCase):
    def project(self, directory, sources):
        root = Path(directory)
        source, build, out = root / "source", root / "oleans", root / "out"
        (source / "D4Bound").mkdir(parents=True)
        build.mkdir()
        out.mkdir()
        for name, text in sources.items():
            (source / (name.replace(".", "/") + ".lean")).write_text(text)
        compiler = root / "lean"
        compiler.write_text(FAKE_COMPILER)
        compiler.chmod(0o755)
        return source, build, out, str(compiler)

    def test_builds_in_dependency_order_and_resumes(self):
        sources = {"D4Bound": "import D4Bound.A\nimport D4Bound.C\n", "D4Bound.A": "import D4Bound.B\n",
                   "D4Bound.B": "", "D4Bound.C": "import Mathlib\n"}
        with tempfile.TemporaryDirectory() as directory:
            source, build, out, compiler = self.project(directory, sources)
            order = module_order(source)
            seconds, libraries = compile_modules(order, source, build, compiler, None, out, 3, ())
            self.assertEqual(set(seconds), set(order))
            self.assertEqual(libraries, [])
            for name in order:
                self.assertTrue((build / (name.replace(".", "/") + ".olean")).is_file())
            self.assertEqual(list(build.rglob("*.partial")), [])
            (build / "D4Bound.olean").unlink()
            seconds, _ = compile_modules(order, source, build, compiler, None, out, 3, ())
            self.assertEqual(set(seconds), {"D4Bound"})

    def test_failure_and_sorry_stop_the_build(self):
        for marker, message in (("FAIL", "failed with exit 1"), ("SORRY", "sorry warning")):
            sources = {"D4Bound": "import D4Bound.A\n", "D4Bound.A": f"-- {marker}\n"}
            with self.subTest(marker=marker), tempfile.TemporaryDirectory() as directory:
                source, build, out, compiler = self.project(directory, sources)
                with self.assertRaisesRegex(ValueError, message):
                    compile_modules(module_order(source), source, build, compiler, None, out, 2, ())
                self.assertEqual(list(build.rglob("*.olean")), [])

    def test_native_libraries_are_built_and_loaded_in_order(self):
        sources = {"D4Bound": "import D4Bound.Use\n", "D4Bound.Core": "import Init\n",
                   "D4Bound.Poly": "import D4Bound.Core\n", "D4Bound.Use": "import D4Bound.Poly\n",
                   "D4Bound.Other": ""}
        libraries = ("D4Bound.Core", "D4Bound.Poly")
        with tempfile.TemporaryDirectory() as directory:
            source, build, out, compiler = self.project(directory, sources)
            with patch("verify_lean.build_library",
                       side_effect=lambda compiler, c_file, library: library.write_text("lib")):
                _, records = compile_modules(module_order(source), source, build, compiler,
                                             None, out, 2, libraries)
            self.assertEqual([row["module"] for row in records], list(libraries))
            core, poly = (str(out / "native" / (name + LIBRARY_SUFFIX)) for name in libraries)
            use = (out / "logs/D4Bound.Use.log").read_text()
            self.assertIn(f"--load-dynlib={core} --load-dynlib={poly}", use)
            self.assertNotIn("--load-dynlib", (out / "logs/D4Bound.Other.log").read_text())
            self.assertIn(" -c ", (out / "logs/D4Bound.Poly.log").read_text())

    def test_bad_native_library_lists_fail(self):
        sources = {"D4Bound": "import D4Bound.Core\n", "D4Bound.Core": "import Mathlib\n"}
        with tempfile.TemporaryDirectory() as directory:
            source, build, out, compiler = self.project(directory, sources)
            order = module_order(source)
            with self.assertRaisesRegex(ValueError, "only Init"):
                compile_modules(order, source, build, compiler, None, out, 2, ("D4Bound.Core",))
            with self.assertRaisesRegex(ValueError, "missing from the sources"):
                compile_modules(order, source, build, compiler, None, out, 2, ("D4Bound.Gone",))


class AxiomAudit(unittest.TestCase):
    LOG = """'D4Bound.a' depends on axioms: [propext, Classical.choice, Quot.sound]
'D4Bound.b' does not depend on any axioms
'D4Bound.c' depends on axioms: [propext,
 Classical.choice,
 D4Bound.V7.fullCheck000._native.native_decide.ax_1_1]
'D4Bound.d' depends on axioms: [propext, sorryAx]
'D4Bound.e' depends on axioms: [D4Bound.my_axiom]
"""

    def test_standard_and_native_axioms_pass(self):
        result = audit_axioms(self.LOG, ["D4Bound.a", "D4Bound.b", "D4Bound.c"])
        self.assertEqual(result["D4Bound.b"], [])
        self.assertEqual(len(result["D4Bound.c"]), 3)

    def test_sorry_declared_axiom_and_missing_report_fail(self):
        for name in ("D4Bound.d", "D4Bound.e", "D4Bound.absent"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                audit_axioms(self.LOG, [name])


if __name__ == "__main__":
    unittest.main()
