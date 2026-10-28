#!/usr/bin/env python3
"""Regression checks for replay portability and certification boundaries.
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().with_name("kernel_replay.sh")
# One source of truth for the library name: the LIB_NAME= line of kernel_replay.sh.
LIB = next(line.split("=", 1)[1].split()[0] for line in SCRIPT.read_text().splitlines()
           if line.startswith("LIB_NAME="))


class ReplayGuards(unittest.TestCase):
    def setUp(self):
        ignored = SCRIPT.parent.parent / ".lake"
        ignored.mkdir(exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix="replay-guards-", dir=ignored)
        self.root = Path(self.temporary.name)
        (self.root / LIB).mkdir()
        (self.root / f"{LIB}.lean").write_text(f"import {LIB}.Basic\n")
        self.source = self.root / LIB / "Basic.lean"
        self.source.write_text("theorem fixture : True := True.intro\n")
        artifacts = self.root / ".lake/build/lib/lean" / LIB
        artifacts.mkdir(parents=True)
        (artifacts.parent / f"{LIB}.olean").write_bytes(b"fixture-root")
        self.artifact = artifacts / "Basic.olean"
        self.artifact.write_bytes(b"fixture-good")
        for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
            (self.root / name).write_text("fixture\n")

    def tearDown(self):
        self.temporary.cleanup()

    def shell(self, commands):
        return subprocess.run(
            ["bash", "-c", 'source "$1"\nPROJECT_DIR="$2"\n' + commands,
             "replay-test", str(SCRIPT), str(self.root)],
            cwd=self.root, text=True, capture_output=True, check=False,
        )

    def snapshot(self):
        result = self.shell("snapshot_inputs")
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout.strip()

    def test_isolated_ignored_work_directories(self):
        result = self.shell('setup_work_dirs\nprintf "%s\\n" "$WORK_DIR" "$SCRATCH_DIR"\n'
                            'setup_work_dirs\nprintf "%s\\n" "$WORK_DIR"')
        self.assertEqual(result.returncode, 0, result.stderr)
        first, scratch, second = map(Path, result.stdout.splitlines())
        self.assertNotEqual(first, second)
        self.assertEqual(first.parent, self.root / ".lake/kernel_replay")
        self.assertEqual(scratch, first / "selftest")

    def test_source_only_change_detected(self):
        before = self.snapshot()
        self.source.write_text("theorem changed : True := True.intro\n")
        self.assertNotEqual(before, self.snapshot())

    def test_same_size_artifact_with_preserved_timestamp_detected(self):
        before = self.snapshot()
        original_stat = self.artifact.stat()
        self.artifact.write_bytes(b"fixture-evil")
        os.utime(self.artifact, ns=(original_stat.st_atime_ns, original_stat.st_mtime_ns))
        self.assertNotEqual(before, self.snapshot())

    def test_new_module_detected(self):
        before = self.snapshot()
        (self.root / LIB / "New.lean").write_text("-- new module\n")
        self.assertNotEqual(before, self.snapshot())

    def test_configuration_change_detected(self):
        before = self.snapshot()
        (self.root / "lake-manifest.json").write_text("changed\n")
        self.assertNotEqual(before, self.snapshot())

    def run_mode(self, mode, override=""):
        # Replace expensive checker operations only. Exercise the actual mode,
        # source/artifact snapshots, freshness checks, and exit classification.
        fixture_checks = '''
setup_work_dirs
TOOLCHAIN_BIN=fixture
check_lake_fresh() { return 0; }
leanchecker_replay() { return 0; }
list_constants() { : > "$1.skipped"; }
export_constants() { return 0; }
analyze_export() { EXPORT_AXIOMS=; EXPORT_RECORDS=1; }
run_export_checkers() { return 0; }
'''
        return self.shell(fixture_checks + override + f"\nmain_full_run {mode}\n")

    def test_uncertified_mode_never_returns_success(self):
        result = self.run_mode(1)
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertIn("UNCERTIFIED", result.stdout)

    def test_unchanged_certified_mode_returns_success(self):
        result = self.run_mode(0)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_edit_during_replay_invalidates_certification(self):
        result = self.run_mode(0, 'run_export_checkers() { echo "-- edit" >> "$PROJECT_DIR/%s/Basic.lean"; }' % LIB)
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertIn("INCONSISTENT", result.stdout)

    def test_failed_lake_freshness_refuses_certification(self):
        result = self.run_mode(0, "check_lake_fresh() { return 3; }")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)

    def test_checker_failure_remains_failure(self):
        result = self.run_mode(0, "run_export_checkers() { ANY_FAIL=1; return 1; }")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)


def main():
    if sys.argv[1:] == ["--test"]:
        sys.argv = [sys.argv[0]]
    unittest.main()


if __name__ == "__main__":
    main()
