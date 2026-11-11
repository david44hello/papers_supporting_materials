#!/usr/bin/env python3
"""Unit tests of kernel_replay.sh (its --test): replay portability and certification boundaries.
Version 0.90 — 2026-11-10. Time limits: a stopped olean replay is a FAIL; a SKIPPED export checker (stopped, or
  declined) ends the run with exit 4; the olean limit stays below 3600 s; lean4lean gets its fuel budgets.
Version 0.80 — 2026-11-10. Part (a) coverage: the stand-in leanchecker names what it replays (--verbose), as the tool.
Version 0.70 — 2026-11-10. Part (a): a parent module that declares constants is one leanchecker run (stand-in tools).
Version 0.60 — 2026-11-10. The split runs (--only-olean, --only-checker N): argument parsing, selection, recorded words.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
Lightweight fixtures; no Lean or checker processes (the expensive steps are replaced by stand-ins).
The fixture library name is read from the LIB_NAME line of kernel_replay.sh.
Usage: test_kernel_replay.py --test
"""
import os
from pathlib import Path
import re
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
        self.temporary = tempfile.TemporaryDirectory(prefix=".replay-test-", dir=SCRIPT.parent)
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

    def run_mode(self, mode, olean_replay, override="", selection="all"):
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
        return self.shell(fixture_checks + override + f"\nmain_full_run {mode} {olean_replay} {selection}\n")

    def test_uncertified_mode_never_returns_success(self):
        result = self.run_mode(1, 1)
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertIn("UNCERTIFIED", result.stdout)

    def test_unchanged_certified_mode_returns_success(self):
        result = self.run_mode(0, 1)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_export_only_skips_the_olean_replay(self):
        result = self.run_mode(0, 0, "leanchecker_replay() { echo REPLAYED; return 0; }")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("NOT RUN(--export-only)", result.stdout)
        self.assertNotIn("REPLAYED", result.stdout)

    def test_edit_during_replay_invalidates_certification(self):
        result = self.run_mode(0, 1, 'run_export_checkers() { echo "-- edit" >> "$PROJECT_DIR/%s/Basic.lean"; }' % LIB)
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertIn("INCONSISTENT", result.stdout)

    def test_failed_lake_freshness_refuses_certification(self):
        result = self.run_mode(0, 1, "check_lake_fresh() { return 3; }")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)

    def test_checker_failure_remains_failure(self):
        result = self.run_mode(0, 1, "run_export_checkers() { ANY_FAIL=1; return 1; }")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)

    # ---- a SELECTED export checker that ends SKIPPED: the real export_checker and exit classification (exit 4);
    # the runner is env (no lock, no gate) and the checker is a stand-in command.
    def test_selected_checker_stopped_at_its_limit_is_skipped_with_exit_4(self):
        result = self.run_mode(0, 0, "RUNNER=/usr/bin/env\nEXPORT_CHECKER_TIME_LIMIT_SECONDS=1\n"
                                     'run_export_checkers() { export_checker nanoda "^accepted" "" "" sleep 5; }',
                               selection="3")
        self.assertEqual(result.returncode, 4, result.stdout + result.stderr)
        self.assertRegex(result.stdout, r"nanoda +SKIPPED\(stopped at the 1 s limit; needs longer\)")

    def test_lean4lean_gets_the_fuel_budgets(self):
        result = self.shell('TOOLCHAIN_BIN=fixture EXPECTED_LEAN4LEAN_COUNT=1\n'
                            'export_checker() { echo "ARGS $*"; }\nrun_one_export_checker 2 fixture.ndjson')
        self.assertIn("fixture/lean4lean --config:whnf=1000000000000", result.stdout, result.stderr)
        self.assertIn("--config:recDepth=1000000000000 --import fixture.ndjson", result.stdout, result.stderr)

    def test_selected_checker_that_declines_the_export_is_skipped_with_exit_4(self):
        declining = "bash -c 'echo \"declined: uses a non-standard axiom [at axiom fixtureAxiom]\"; exit 2'"
        result = self.run_mode(0, 0, "RUNNER=/usr/bin/env\n"
                                     'run_export_checkers() { export_checker "con-leche --verified" "^accepted" "" "" '
                                     + declining + "; }", selection="4")
        self.assertEqual(result.returncode, 4, result.stdout + result.stderr)
        self.assertRegex(result.stdout, r"con-leche --verified +SKIPPED\(checker declines the export, declined: "
                                        r"uses a non-standard axiom, first at: axiom fixtureAxiom\)")

    # ---- split runs: --only-olean (selection "none") and --only-checker N (selection N - 1)
    def test_only_olean_skips_the_export(self):
        result = self.run_mode(0, 1, "export_constants() { echo EXPORTED; return 0; }", selection="none")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("NOT RUN(--only-olean)", result.stdout)
        self.assertNotIn("EXPORTED", result.stdout)

    def test_only_checker_passes_its_selection(self):
        result = self.run_mode(0, 0, 'run_export_checkers() { echo "SELECTION $2"; }', selection="3")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("SELECTION 3", result.stdout)

    def test_only_checker_records_the_rest_as_not_run(self):
        result = self.run_mode(0, 0, "leanchecker_replay() { echo REPLAYED; return 0; }", selection="3")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("REPLAYED", result.stdout)
        self.assertNotIn("NOT RUN(--export-only)", result.stdout)
        # part (a) and the 5 other export checkers; checker 4 (nanoda, index 3) is the one that runs
        self.assertEqual(result.stdout.count("NOT RUN(--only-checker 4)"), 6, result.stdout)
        self.assertFalse([line for line in result.stdout.splitlines()
                          if line.startswith("nanoda ") and "NOT RUN" in line], result.stdout)

    def test_only_checker_export_failure_skips_only_its_checker(self):
        result = self.run_mode(0, 0, "export_constants() { return 1; }", selection="1")
        self.assertEqual(result.stdout.count("SKIPPED(export failed)"), 1, result.stdout)
        self.assertRegex(result.stdout, r"leanchecker-paranoid --from-export +SKIPPED\(export failed\)")
        self.assertEqual(result.stdout.count("NOT RUN(--only-checker 2)"), 6, result.stdout)

    def test_split_runs_check_lake_freshness_on_their_own(self):
        for olean_replay, selection in ((1, "none"), (0, "2")):
            result = self.run_mode(0, olean_replay, "check_lake_fresh() { return 3; }", selection=selection)
            self.assertEqual(result.returncode, 3, f"{selection}: " + result.stdout + result.stderr)

    def test_split_runs_refuse_a_missing_olean(self):
        self.artifact.unlink()
        for olean_replay, selection in ((1, "none"), (0, "2")):
            result = self.run_mode(0, olean_replay, selection=selection)
            self.assertEqual(result.returncode, 3, f"{selection}: " + result.stdout + result.stderr)
            self.assertIn("no olean for", result.stderr)

    def test_split_runs_check_consistency_on_their_own(self):
        edit = 'echo "-- edit" >> "$PROJECT_DIR/%s/Basic.lean"' % LIB
        for olean_replay, selection, override in ((1, "none", "leanchecker_replay() { %s; }" % edit),
                                                  (0, "2", "run_export_checkers() { %s; }" % edit)):
            result = self.run_mode(0, olean_replay, override, selection=selection)
            self.assertEqual(result.returncode, 3, f"{selection}: " + result.stdout + result.stderr)
            self.assertIn("INCONSISTENT", result.stdout)

    def test_split_run_failure_remains_failure(self):
        for olean_replay, selection, override in ((1, "none", "leanchecker_replay() { ANY_FAIL=1; return 1; }"),
                                                  (0, "2", "run_export_checkers() { ANY_FAIL=1; return 1; }")):
            result = self.run_mode(0, olean_replay, override, selection=selection)
            self.assertEqual(result.returncode, 1, f"{selection}: " + result.stdout + result.stderr)

    # ---- part (a), a parent module that declares constants.  The real leanchecker_replay, gated and timed_run run;
    # the runner, lake, lean (only as the constant lister) and leanchecker are stand-ins.  A fixture olean holds
    # the names of the constants its module declares (empty: none).  The stand-in leanchecker, like the tool, replays
    # the argument M and every fixture olean whose module name starts with "M.", prints "replaying <module>" for each
    # with --verbose, and stops with exit 1 at the first module in rejected.txt; it leaves out of its "replaying" lines
    # the modules in unnamed.txt.  It appends its module argument to leanchecker_calls.txt.  A module argument in
    # slow.txt makes it sleep 5 s first (for the time limit).
    STANDIN_LEANCHECKER = r'''#!/usr/bin/env bash
here=$(dirname -- "$0") verbose=0 module='' found=0
oleans="$here/../.lake/build/lib/lean"
for argument in "$@"; do
    case $argument in --verbose|-v) verbose=1 ;; -*) ;; *) module=$argument ;; esac
done
echo "$module" >> "$here/leanchecker_calls.txt"
if grep -qxF -- "$module" "$here/slow.txt"; then sleep 5; fi
while read -r name; do
    [[ $name == "$module" || $name == "$module".* ]] || continue
    found=1
    if (( verbose )) && ! grep -qxF -- "$name" "$here/unnamed.txt"; then echo "replaying $name"; fi
    if grep -qxF -- "$name" "$here/rejected.txt"; then
        echo "leanchecker found a problem in $name" >&2; exit 1
    fi
done < <(cd "$oleans" && find . -name '*.olean' | sed 's|^\./||; s|\.olean$||; s|/|.|g' | LC_ALL=C sort)
(( found )) || { echo "Could not find any oleans for: $module" >&2; exit 1; }
'''
    STANDINS = {
        "runner": '#!/usr/bin/env bash\nexec "$@"\n',
        "lake": '#!/usr/bin/env bash\n'
                '[[ $1 == env ]] || { echo "stand-in lake: unexpected call: $*" >&2; exit 99; }\n'
                'shift\nexec "$@"\n',
        "lean": '#!/usr/bin/env bash\n'
                '[[ $1 == --run && $2 == */ListConstants.lean ]] || { echo "stand-in lean: unexpected call: $*" >&2; exit 99; }\n'
                'shift 2\ncat -- "$@"\n',
        "leanchecker": STANDIN_LEANCHECKER,
    }
    STANDIN_SETUP = '''
setup_work_dirs
STANDINS="$PROJECT_DIR/standins"
RUNNER="$STANDINS/runner"
TOOLCHAIN_BIN="$STANDINS"
HELPER_DIR="$STANDINS"
PATH="$STANDINS:$PATH"
check_lake_fresh() { return 0; }
'''

    def add_module(self, module, constants=""):
        relative = Path(*module.split("."))
        for path, text in ((self.root / relative.with_suffix(".lean"), "-- fixture\n"),
                           (self.root / ".lake/build/lib/lean" / relative.with_suffix(".olean"), constants)):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)

    def standin_fixture(self, modules, rejected=(), unnamed=()):
        """The root (declares nothing), Basic (from setUp) and MODULES {name under the root: its constants}."""
        self.add_module(LIB)
        for module, constants in modules.items():
            self.add_module(f"{LIB}.{module}", constants)
        standins = self.root / "standins"
        standins.mkdir()
        for name, text in self.STANDINS.items():
            (standins / name).write_text(text)
            (standins / name).chmod(0o755)
        (standins / "rejected.txt").write_text("".join(module + "\n" for module in rejected))
        (standins / "unnamed.txt").write_text("".join(module + "\n" for module in unnamed))
        (standins / "slow.txt").write_text("")
        (standins / "leanchecker_calls.txt").write_text("")
        return standins

    def group_fixture(self, group_constants="groupTheorem\n", rejected=(), unnamed=()):
        """The root (declares nothing), Basic, the parent Group with Part1 and Part2 under it, then Later."""
        return self.standin_fixture({"Group": group_constants, "Group.Part1": "partOne\n",
                                     "Group.Part2": "partTwo\n", "Later": "later\n"}, rejected, unnamed)

    def run_olean_replay(self, standins, commands="main_full_run 0 1 none"):
        """The --only-olean run (or COMMANDS); returns the result and the stand-in leanchecker's arguments."""
        result = self.shell(self.STANDIN_SETUP + commands + "\n")
        return result, (standins / "leanchecker_calls.txt").read_text().split()

    def test_parent_with_constants_is_one_leanchecker_run_with_the_modules_under_it(self):
        result, calls = self.run_olean_replay(self.group_fixture())
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        # one run for the group (argument: the parent), none for Part1 and Part2, none for the root
        self.assertEqual(sorted(calls), sorted(f"{LIB}.{module}" for module in ("Basic", "Group", "Later")))
        self.assertIn(f"  {LIB}.Group (+ 2 modules under it, one leanchecker run): accepted", result.stdout)
        # Basic, Group, Group.Part1, Group.Part2, Later; the root declares nothing
        self.assertRegex(result.stdout, r"leanchecker \(olean replay\) +PASS\(5 modules, ")

    def test_rejected_group_run_is_a_failure(self):
        result, calls = self.run_olean_replay(self.group_fixture(rejected=[f"{LIB}.Group"]))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(f"  {LIB}.Group (+ 2 modules under it, one leanchecker run): REJECTED (exit 1)", result.stdout)
        self.assertRegex(result.stdout, r"leanchecker \(olean replay\) +FAIL\(1 of 5 modules: %s\.Group " % LIB)
        self.assertIn(f"leanchecker found a problem in {LIB}.Group", result.stderr)   # the log tail
        self.assertIn(f"{LIB}.Later", calls)

    def test_group_run_stopped_at_the_time_limit_is_a_failure_reported_as_stopped(self):
        standins = self.group_fixture()
        (standins / "slow.txt").write_text(f"{LIB}.Group\n")
        result, calls = self.run_olean_replay(standins, "RUN_TIME_LIMIT_SECONDS=1\nmain_full_run 0 1 none")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(f"  {LIB}.Group (+ 2 modules under it, one leanchecker run): STOPPED at the 1 s limit "
                      "(exit 124; not a rejection)", result.stdout)
        self.assertNotIn("REJECTED", result.stdout)
        self.assertRegex(result.stdout, r"leanchecker \(olean replay\) +FAIL\(1 of 5 modules: %s\.Group .*"
                                        r"stopped at the time limit" % LIB)
        self.assertIn(f"  {LIB}.Later: accepted", result.stdout)

    def test_olean_replay_limit_stays_below_the_long_check_stop(self):
        result = self.shell('echo "$RUN_TIME_LIMIT_SECONDS"')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertLess(int(result.stdout), 3600)

    def test_parent_without_constants_is_still_not_run(self):
        result, calls = self.run_olean_replay(self.group_fixture(group_constants=""))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(f"  {LIB}.Group: parent of other modules and declares no constants; nothing to replay",
                      result.stdout)
        self.assertEqual(sorted(calls),
                         sorted(f"{LIB}.{module}" for module in ("Basic", "Group.Part1", "Group.Part2", "Later")))
        self.assertRegex(result.stdout, r"leanchecker \(olean replay\) +PASS\(4 modules, ")

    def test_modules_after_the_group_are_still_replayed(self):
        result, calls = self.run_olean_replay(self.group_fixture())
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(f"{LIB}.Later", calls)
        self.assertGreater(calls.index(f"{LIB}.Later"), calls.index(f"{LIB}.Group"))
        self.assertIn(f"  {LIB}.Later: accepted", result.stdout)

    def test_module_before_its_parent_is_replayed_twice_and_counted_once(self):
        standins = self.group_fixture()
        result, calls = self.run_olean_replay(standins, 'mapfile -t ALL_MODULES < <(all_modules)\n'
                                              'LOG_DIR="$WORK_DIR/logs"\n'
                                              f'leanchecker_replay part-a {LIB}.Group.Part1 {LIB}.Group {LIB}.Group.Part2\n'
                                              'printf "%s\\n" "${SUMMARY[@]}"')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, [f"{LIB}.Group.Part1", f"{LIB}.Group"])
        self.assertRegex(result.stdout, r"part-a +PASS\(3 modules, ")

    # ---- part (a) coverage: the modules leanchecker names in its exit-0 runs against the modules expected
    def coverage_folder(self, stdout):
        """The folder that the coverage line names (part (a)'s log folder)."""
        match = re.search(r"^  coverage: .*; lists in (.+)$", stdout, re.MULTILINE)
        self.assertIsNotNone(match, "no coverage line in: " + stdout)
        return Path(match.group(1))

    def coverage_lists(self, stdout):
        """The three lists in the folder that the coverage line names, as lists of module names."""
        folder = self.coverage_folder(stdout)
        return {kind: (folder / f"modules_{kind}.txt").read_text().split()
                for kind in ("expected", "confirmed", "no_constants")}

    def test_coverage_of_a_parent_with_constants_is_complete(self):
        result, _ = self.run_olean_replay(self.group_fixture())
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        line = "5 replayed + 1 with no constants = 6 of 6 modules, 0 missing, 0 unknown; lists in "
        self.assertIn("  coverage: " + line, result.stdout)
        self.assertRegex(result.stdout, r"\nleanchecker \(olean replay\) +PASS\(5 modules, .*\n"
                                        r"olean replay coverage +PASS\(" + re.escape(line))
        self.assertNotRegex(result.stdout, r"    (missing|unknown): ")
        modules = [f"{LIB}.{module}" for module in ("Basic", "Group", "Group.Part1", "Group.Part2", "Later")]
        self.assertEqual(self.coverage_lists(result.stdout),
                         {"expected": sorted([LIB, *modules]), "confirmed": sorted(modules), "no_constants": [LIB]})

    def test_module_an_accepting_run_does_not_name_is_missing(self):
        result, _ = self.run_olean_replay(self.group_fixture(unnamed=[f"{LIB}.Group.Part2"]))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        # the exit statuses alone pass; only leanchecker's own list shows the gap
        self.assertIn(f"  {LIB}.Group (+ 2 modules under it, one leanchecker run): accepted", result.stdout)
        self.assertRegex(result.stdout, r"leanchecker \(olean replay\) +PASS\(5 modules, ")
        self.assertRegex(result.stdout, r"olean replay coverage +FAIL\(4 replayed \+ 1 with no constants = 5 of 6 "
                                        r"modules, 1 missing, 0 unknown; lists in ")
        self.assertIn(f"\n    missing: {LIB}.Group.Part2\n", result.stdout)
        self.assertNotIn(f"{LIB}.Group.Part2", self.coverage_lists(result.stdout)["confirmed"])

    def test_module_a_run_names_but_the_build_does_not_make_is_unknown(self):
        standins = self.group_fixture()
        # an olean without a source (a deleted module): leanchecker's run of its parent replays it too
        (self.root / ".lake/build/lib/lean" / LIB / "Group" / "Stale.olean").write_text("stale\n")
        result, _ = self.run_olean_replay(standins)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertRegex(result.stdout, r"leanchecker \(olean replay\) +PASS\(5 modules, ")
        self.assertRegex(result.stdout, r"olean replay coverage +FAIL\(5 replayed \+ 1 with no constants = 6 of 6 "
                                        r"modules, 0 missing, 1 unknown; lists in ")
        self.assertIn(f"\n    unknown: {LIB}.Group.Stale\n", result.stdout)

    def test_root_without_constants_and_no_other_parent_is_unchanged_and_complete(self):
        result, calls = self.run_olean_replay(self.standin_fixture({"Later": "later\n"}))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(f"  {LIB}: parent of other modules and declares no constants; nothing to replay", result.stdout)
        self.assertEqual(sorted(calls), [f"{LIB}.Basic", f"{LIB}.Later"])
        self.assertIn(f"  {LIB}.Later: accepted", result.stdout)
        self.assertRegex(result.stdout, r"leanchecker \(olean replay\) +PASS\(2 modules, ")
        self.assertRegex(result.stdout, r"olean replay coverage +PASS\(2 replayed \+ 1 with no constants = 3 of 3 "
                                        r"modules, 0 missing, 0 unknown; lists in ")

    def test_modules_named_by_a_rejected_run_are_not_confirmed(self):
        result, _ = self.run_olean_replay(self.group_fixture(rejected=[f"{LIB}.Group.Part1"]))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        # the rejected run named Group and Part1 before it stopped; none of its modules counts
        log = self.coverage_folder(result.stdout) / f"{LIB}.Group.log"
        self.assertIn(f"replaying {LIB}.Group\nreplaying {LIB}.Group.Part1\n", log.read_text())
        self.assertRegex(result.stdout, r"olean replay coverage +FAIL\(2 replayed \+ 1 with no constants = 3 of 6 "
                                        r"modules, 3 missing, 0 unknown; lists in ")
        self.assertEqual(self.coverage_lists(result.stdout)["confirmed"], [f"{LIB}.Basic", f"{LIB}.Later"])

    def run_selection(self, selection):
        result = self.shell('write_nanoda_config() { :; }\nrun_one_export_checker() { echo "RAN $1"; }\n'
                            f"run_export_checkers fixture.ndjson {selection}")
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout.split("\n")

    def test_selection_runs_exactly_the_chosen_checkers(self):
        self.assertEqual([line for line in self.run_selection("4") if line], ["RAN 4"])
        self.assertEqual([line for line in self.run_selection("all") if line], [f"RAN {i}" for i in range(6)])

    def dispatch(self, arguments):
        return self.shell('setup_environment() { echo SETUP; }\nmain_full_run() { echo "RUN $*"; }\n'
                          f"main {arguments}")

    def test_split_options_reach_the_full_run(self):
        for arguments, expected in (("--only-olean", "RUN 0 1 none"), ("--only-checker 1", "RUN 0 0 0"),
                                    ("--only-checker 6", "RUN 0 0 5"), ("", "RUN 0 1 all"),
                                    ("--export-only", "RUN 0 0 all"), ("--use-built-oleans", "RUN 1 1 all")):
            result = self.dispatch(arguments)
            self.assertEqual(result.returncode, 0, f"{arguments!r}: " + result.stdout + result.stderr)
            self.assertEqual(result.stdout.split("\n")[:2], ["SETUP", expected], arguments)

    def test_bad_checker_number_is_a_usage_error(self):
        for bad in ("0", "7", "x", "", "12", "-1"):
            result = self.dispatch(f'--only-checker "{bad}"')
            self.assertEqual(result.returncode, 2, f"{bad!r}: " + result.stdout + result.stderr)
            self.assertNotIn("SETUP", result.stdout)

    def test_checker_number_missing_is_a_usage_error(self):
        result = self.dispatch("--only-checker")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertNotIn("SETUP", result.stdout)
        self.assertIn("--only-checker needs N = 1..6", result.stderr)


def main():
    if sys.argv[1:] == ["--test"]:
        sys.argv = [sys.argv[0]]
    unittest.main()


if __name__ == "__main__":
    main()
