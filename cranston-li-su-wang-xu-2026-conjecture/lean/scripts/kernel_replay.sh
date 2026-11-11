#!/usr/bin/env bash
# kernel_replay.sh — re-check every EulerFlow declaration with Lean's kernel and the toolchain's independent checkers.
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
## version 0.90 - 20261110: portable replay for this library; two limits, complete module coverage, explicit gate
##   and lock settings, large lean4lean fuel budgets, and exit 4 when a selected export checker does not finish.
#
# Usage:  scripts/kernel_replay.sh          full run (one thread, nice 19); refuses (exit 3) if Lake reports any EulerFlow
#                                           module out of date, or any olean is missing
#         scripts/kernel_replay.sh --use-built-oleans   check the oleans as built, even if not fresh; exits 3, never 0
#         scripts/kernel_replay.sh --export-only        part (b) only (after a run whose (a) PASSED on the same sources)
#         scripts/kernel_replay.sh --only-olean         part (a) only
#         scripts/kernel_replay.sh --only-checker N     a fresh export + export checker N only, N = 1..6 in
#                                                       EXPORT_CHECKERS order; run (a) and N = 1..6 as 7 separate jobs
#         scripts/kernel_replay.sh --selftest   Lean self-test: known-good inputs must pass, a kernel-invalid olean must fail
#         scripts/kernel_replay.sh --test       unit tests of the run logic with stand-in tools (no Lean)
# Every Lean, lake and checker process runs through scripts/lean_run.sh (the shared compile lock and the priority gate),
# one at a time; waiting for the lock does not count toward a checker's time limit.
# Work files and logs are isolated per invocation under .lake/kernel_replay/ (ignored by Git); override the folder
# with KERNEL_REPLAY_WORK_ROOT.
# Extra prerequisites: Python 3, ripgrep, GNU time, timeout, elan, and all seven checker/export tools named below.
# Exit:   0 no FAIL | 1 some checker FAILed | 2 usage/setup error | 3 oleans missing, stale, or changed during run
#         | 4 a selected export checker did not finish or declined the export (SKIPPED)
#
# (a) leanchecker, olean replay: each EulerFlow.* module's own declarations are replayed by Lean's C++ kernel on top
#     of the imported environment (Mathlib and core are trusted in this mode).  One process per module: a single
#     process re-imports Mathlib for every module and reached 9 GB.  Exception: a parent module that declares
#     constants is replayed in one process together with the modules under it (leanchecker selects by name prefix).
#     Coverage, from leanchecker's own --verbose output: the modules named by its exit-0 runs, plus the parents that
#     declare nothing, must be exactly the modules expected, none missing and none unknown.
# (b) leanexport: every safe EulerFlow constant is exported with its transitive dependencies (core and Mathlib too)
#     into WORK_DIR.  The 6 checkers bundled for `lake check --paranoid` then check that file starting from an
#     empty environment, so they also re-check the Mathlib/core declarations EulerFlow depends on.  `lake check`
#     itself is not used: it builds the project and runs nanoda on 4 threads and con-leche/con-ron on all cores.
#     The axiom policy is audit.py's job; a non-standard axiom (sorryAx of an unproved row included) is reported here
#     in "axioms declared in the export".  con-leche/con-ron DECLINE (exit 2) any export with a non-standard axiom;
#     that is reported as SKIPPED, and the run ends with exit 4.
# Every checker accepts an EMPTY export with exit 0.  So the export is verified to declare every requested name,
# and each checker's own declaration count must equal the count computed from the export.
set -euo pipefail

PROJECT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
RUNNER="$PROJECT_DIR/scripts/lean_run.sh"
WORK_DIR=
SCRATCH_DIR=
RUN_TIME_LIMIT_SECONDS=3300       # each olean replay run and the export: below the priority gate's 3600 s stop for a
                                  # long check, so run part (a) inside ONE long check with the inner gate off
                                  # (LEAN_RUN_GATE=none).  An olean replay stopped at it is a FAIL, reported as stopped
EXPORT_CHECKER_TIME_LIMIT_SECONDS=14400   # each export checker: only to stop a hung tool.  Some checkers need hours on
                                  # kernel computations, so run them in
                                  # a job with no shorter outer limit.  A checker stopped at it is SKIPPED (exit 4)
MEMORY_WARN_KB=8000000            # a peak RSS above this is flagged.  RSS includes the memory-mapped .olean files
                                  # (measured on an earlier project: one module peaked at 9.06 GB RSS = 6.19 GB mapped
                                  # oleans + 2.87 GB anon)
GATE_LINE='^PRIORITY GATE'        # the gate's own stderr lines; not output of the tool
LIB_NAME=EulerFlow                      # the Lean library: lakefile [[lean_lib]] name = root module = source folder
POSITIVE_TEST_MODULE=EulerFlow.Defs.Graph
EXPORT_CHECKERS=("leanchecker --from-export" "leanchecker-paranoid --from-export" "lean4lean --import"
                 "nanoda" "con-leche --verified" "con-ron --verified")
# lean4lean's step budgets (its --config fields); the defaults are too small for the decide +kernel certificates.
LEAN4LEAN_FUEL=(--config:whnf=1000000000000 --config:whnfEager=1000000000000 --config:lazyDelta=1000000000000
                --config:etaExpand=1000000000000 --config:inductiveFuel=1000000000000 --config:recDepth=1000000000000)

SUMMARY=()
ANY_FAIL=0
ANY_SKIPPED=0   # a selected export checker ended SKIPPED (stopped at its limit, or declined): exit 4
RUN_EXIT=0 RUN_SECONDS=0 RUN_RSS_KB=0

die() { echo "ERROR: $*" >&2; exit 2; }

setup_work_dirs() {
    local work_root="${KERNEL_REPLAY_WORK_ROOT:-$PROJECT_DIR/.lake/kernel_replay}"
    mkdir -p "$work_root"
    WORK_DIR=$(mktemp -d "$work_root/run.XXXXXXXX") || die "cannot create isolated replay directory"
    SCRATCH_DIR="$WORK_DIR/selftest"
}

# Runs "$@" through the lock and the gate; the gate's own stderr lines are dropped, the tool's stderr is kept.
gated() {
    local status=0 errors
    errors=$(mktemp "$WORK_DIR/gated.XXXXXX")
    "$RUNNER" "$@" 2> "$errors" || status=$?
    grep -v "$GATE_LINE" "$errors" >&2 || true
    rm -f -- "$errors"
    return "$status"
}

setup_environment() {
    export PATH="$HOME/.elan/bin:$PATH"
    cd "$PROJECT_DIR"   # `lake env` and elan's toolchain choice both need the project directory
    [[ -x $RUNNER ]] || die "missing $RUNNER"
    local lean_binary prefix
    # elan resolves the project's toolchain without starting Lean (lean-toolchain of the project directory).
    lean_binary=$(elan which lean) || die "cannot find the project's Lean toolchain (elan which lean)"
    prefix=$(dirname -- "$(dirname -- "$lean_binary")")
    TOOLCHAIN_BIN="$prefix/bin"
    # Lean tools find core via `lean --print-prefix` unless LEAN_SYSROOT is set; outside the project that is
    # elan's default toolchain (which elan then downloads).  Pin the project's toolchain.
    export LEAN_SYSROOT="$prefix"
    export LEAN_NUM_THREADS=1
    export LEAN_ABORT_ON_PANIC=1   # as `lake check` sets it: a panic aborts instead of continuing with defaults
    local tool
    for tool in lean leanchecker leanchecker-paranoid leanexport lean4lean nanoda_bin con-leche con-ron; do
        [[ -x "$TOOLCHAIN_BIN/$tool" ]] || die "missing toolchain binary $TOOLCHAIN_BIN/$tool"
    done
    command -v python3 > /dev/null || die "python3 is required"
    command -v rg > /dev/null || die "ripgrep is required"
    command -v timeout > /dev/null || die "GNU timeout is required"
    [[ -x /usr/bin/time ]] || die "GNU time (/usr/bin/time) is required"
    setup_work_dirs
    HELPER_DIR="$WORK_DIR/helpers"
    mkdir -p "$HELPER_DIR"
    write_constant_lister "$HELPER_DIR/ListConstants.lean"
    write_export_analyzer "$HELPER_DIR/analyze_export.py"
}

# Prints the name of every constant declared in the given .olean files, as a name literal that leanexport can read
# back.  Unsafe and partial constants (compiler helpers such as `_unsafe_rec`) go to stderr: no safe declaration can
# use them, and nanoda refuses them.  A name that cannot be written as a literal is an error (exit 1).
write_constant_lister() {
    cat > "$1" <<'EOF'
import Lean
open Lean

/-- `name` as a name literal that leanexport's `Syntax.decodeNameLit` reads back as `name`: digits for a numeric
component, `Name.escapePart` («...» when needed) for a string one.  `Name.toString` never escapes a name with macro
scopes (`deriving DecidableEq` makes `T.match_on_same_ctor._@.M._hyg.95`), and leanexport panics on those. -/
def nameLiteral (name : Name) : Except String String := do
  let parts ← name.componentsRev.reverse.mapM fun
    | .str _ part => match Name.escapePart part with
      | some escaped => pure escaped
      | none => throw s!"cannot write {name} as a name literal (a component contains »)"
    | .num _ index => pure (toString index)
    | .anonymous => throw s!"anonymous component in {name}"
  return ".".intercalate parts

unsafe def main (oleanFiles : List String) : IO UInt32 := do
  for file in oleanFiles do
    let (data, region) ← readModuleData file
    for info in data.constants do
      if info.isUnsafe || info.isPartial then
        IO.eprintln s!"skipped unsafe/partial: {info.name}"
      else
        match nameLiteral info.name with
        | .ok literal => IO.println literal
        | .error message => IO.eprintln message; return 1
    region.free
  return 0
EOF
}

# Reads an export and a file of requested names.  Prints key=value lines: declaration-record counts, the axioms
# the export declares, and how many requested names it does not declare (those are written to MISSING_FILE).
write_export_analyzer() {
    cat > "$1" <<'EOF'
import json, sys

DECLARATION_PREFIXES = tuple('{"%s":' % kind for kind in ("axiom", "def", "thm", "opaque", "quot", "inductive"))
export_path, names_path, missing_path = sys.argv[1:4]
names = {0: ""}
declared, axioms = set(), []
counts = {"records": 0, "quot_records": 0, "inductive_records": 0, "inductive_members": 0}
for line in open(export_path, encoding="utf-8"):
    if line.startswith('{"in":'):
        record = json.loads(line)
        part = record["str"] if "str" in record else record["num"]
        component = str(part["str"] if "str" in part else part["i"])
        prefix = names[part["pre"]]
        names[record["in"]] = prefix + "." + component if prefix else component
    elif line.startswith(DECLARATION_PREFIXES):   # a declaration record has exactly one key, its kind
        (kind, body), = json.loads(line).items()
        counts["records"] += 1
        if kind == "inductive":
            members = body["types"] + body["ctors"] + body["recs"]
            counts["inductive_records"] += 1
            counts["inductive_members"] += len(members)
            declared.update(names[member["name"]] for member in members)
        else:
            declared.add(names[body["name"]])
            counts["quot_records"] += kind == "quot"
            if kind == "axiom":
                axioms.append(names[body["name"]])
# Lean prints non-identifier name components as «...»; the export stores them raw.
requested = [line.strip().replace("«", "").replace("»", "") for line in open(names_path, encoding="utf-8")]
requested = [name for name in requested if name]
missing = [name for name in requested if name not in declared]
with open(missing_path, "w", encoding="utf-8") as out:
    out.write("".join(name + "\n" for name in missing))
for key, value in counts.items():
    print(f"{key}={value}")
print(f"requested={len(requested)}")
print(f"missing={len(missing)}")
print("axioms=" + ",".join(axioms))
EOF
}

all_modules() { { echo "$LIB_NAME"; rg --files --hidden --no-ignore "$LIB_NAME" -g '*.lean' | sed 's|\.lean$||; s|/|.|g'; } | sort; }
olean_of() { echo "$PROJECT_DIR/.lake/build/lib/lean/${1//.//}.olean"; }
source_of() { echo "$PROJECT_DIR/${1//.//}.lean"; }

# The oleans must exist.  Whether they describe the current code is check_lake_fresh's job: Lake compares content
# hashes, while file times can mislead (a copy or checkout makes a source look newer without changing it).
# Sets MISSING_MODULES.
check_oleans_fresh() {
    local module
    MISSING_MODULES=()
    for module in "$@"; do
        [[ -f $(olean_of "$module") ]] || MISSING_MODULES+=("$module")
    done
    (( ${#MISSING_MODULES[@]} == 0 )) && return 0
    echo "PRECONDITION: no olean for: ${MISSING_MODULES[*]}" >&2
    return 3
}

# Hash both the current source inventory and artifact contents. This catches source-only edits,
# added/removed modules, and same-size artifact rewrites even when timestamps are preserved.
snapshot_inputs() {
    python3 -I - "$PROJECT_DIR" "$LIB_NAME" <<'PY'
import hashlib, pathlib, sys
root, library = pathlib.Path(sys.argv[1]), sys.argv[2]
sources = sorted([root / (library + ".lean"), *(root / library).rglob("*.lean")])
paths = set(sources)
paths.update(root / name for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"))
for source in sources:
    relative = source.relative_to(root).with_suffix(".olean")
    artifact = root / ".lake/build/lib/lean" / relative
    paths.add(artifact)
    paths.update(artifact.parent.glob(artifact.name + ".*"))
digest = hashlib.sha256()
for path in sorted(paths):
    digest.update(str(path.relative_to(root)).encode() + b"\0")
    if not path.is_file():
        digest.update(b"MISSING\0")
        continue
    with path.open("rb") as stream:
        content = hashlib.sha256()
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            content.update(chunk)
    digest.update(b"FILE\0" + content.digest())
print(digest.hexdigest())
PY
}

# Lake's own freshness test (content hashes): exit 0 iff TARGET and everything it imports are built from the current
# sources (`lake --no-build build` exits 3 when a rebuild would be needed).
check_lake_fresh() {
    local target=$1
    if ! gated lake --no-build build "$target" > "$WORK_DIR/build_freshness.log" 2>&1; then
        echo "PRECONDITION: Lake cannot confirm that $target and its imports are built from the current sources; see $WORK_DIR/build_freshness.log" >&2
        return 3
    fi
}

record() { SUMMARY+=("$(printf '%-36s %s' "$1" "$2")"); }

# timed_run LIMIT OUT ERR COMMAND...: runs COMMAND through the lock and the gate (one thread, nice 19), stopped after
# LIMIT seconds, under GNU time; stdout to OUT, stderr to ERR (may be the same file; the gate's own lines are dropped).
# Sets RUN_EXIT, RUN_SECONDS, RUN_RSS_KB.
timed_run() {
    local limit=$1 out=$2 err=$3; shift 3
    RUN_EXIT=0
    if [[ $out == "$err" ]]; then
        gated /usr/bin/time -o "$err.time" -f '%e %M' \
            timeout "$limit" "$@" > "$out" 2>&1 || RUN_EXIT=$?
    else
        gated /usr/bin/time -o "$err.time" -f '%e %M' \
            timeout "$limit" "$@" > "$out" 2> "$err" || RUN_EXIT=$?
    fi
    read -r RUN_SECONDS RUN_RSS_KB < <(tail -n 1 "$err.time")
    [[ $RUN_SECONDS =~ ^[0-9.]+$ && $RUN_RSS_KB =~ ^[0-9]+$ ]] || { RUN_SECONDS=0; RUN_RSS_KB=0; }
}

resource_note() {
    local note
    note=$(awk -v seconds="$RUN_SECONDS" -v kb="$RUN_RSS_KB" \
        'BEGIN { printf "%.0f s, peak RSS %.1f GB", seconds, kb / 1e6 }')
    (( RUN_RSS_KB > MEMORY_WARN_KB )) && note+=" (ABOVE 8 GB, incl. about 6.2 GB of mapped oleans)"
    echo "$note"
}

show_failure_tail() { echo "---- last lines of $1:" >&2; grep -v '^/\|^backtrace' "$1" | tail -n 12 >&2 || true; }

is_parent_module() {   # true if some other module's name starts with "$1."
    local other
    for other in "${ALL_MODULES[@]}"; do [[ $other == "$1".* ]] && return 0; done
    return 1
}

modules_under() {   # prints each of the modules "${@:2}" whose name starts with "$1."
    local parent=$1 other; shift
    for other in "$@"; do
        if [[ $other == "$parent".* ]]; then echo "$other"; fi
    done
}

replayed_modules_in() {   # the modules that `leanchecker --verbose` names on its "replaying <module>" lines in log $1
    sed -n 's/^replaying \([^ ]\{1,\}\)$/\1/p' "$1"
}

write_sorted() {   # write_sorted FILE ITEM...: the items one per line, sorted, unique (C order, as comm needs)
    local file=$1; shift
    if (( $# > 0 )); then printf '%s\n' "$@"; fi | LC_ALL=C sort -u > "$file" || die "cannot write $file"
}

# Part (a)'s coverage, from leanchecker's own output, over three sorted lists in DIR: modules_expected.txt (the modules
# given to leanchecker_replay), modules_confirmed.txt (named on a "replaying" line of a run that exited 0) and
# modules_no_constants.txt (parents not run because they declare nothing).  MISSING = expected - confirmed -
# no_constants, UNKNOWN = confirmed - expected.  Prints and records one line, then the missing and unknown names;
# returns 1 unless both are empty.
record_replay_coverage() {
    local dir=$1 line name replayed skipped total verdict=PASS
    local expected="$dir/modules_expected.txt" confirmed="$dir/modules_confirmed.txt"
    local no_constants="$dir/modules_no_constants.txt"
    local -a missing unknown
    mapfile -t missing < <(LC_ALL=C comm -23 "$expected" "$confirmed" | LC_ALL=C comm -23 - "$no_constants")
    mapfile -t unknown < <(LC_ALL=C comm -13 "$expected" "$confirmed")
    replayed=$(LC_ALL=C comm -12 "$expected" "$confirmed" | wc -l)
    skipped=$(wc -l < "$no_constants")
    total=$(wc -l < "$expected")
    line="$replayed replayed + $skipped with no constants = $(( replayed + skipped )) of $total modules,"
    line+=" ${#missing[@]} missing, ${#unknown[@]} unknown; lists in $dir"
    (( ${#missing[@]} == 0 && ${#unknown[@]} == 0 )) || verdict=FAIL
    echo "  coverage: $line"
    for name in "${missing[@]}"; do echo "    missing: $name"; done
    for name in "${unknown[@]}"; do echo "    unknown: $name"; done
    record "olean replay coverage" "$verdict($line)"
    [[ $verdict == PASS ]]
}

# (a) Replays the given modules' own declarations, one leanchecker process per module.  leanchecker selects modules
# by NAME PREFIX: `leanchecker M` replays M and every module whose name starts with "M.", each on top of its own
# imports, and fails if any of them fails.  So a parent module that declares constants is replayed together with all
# modules under it in ONE run, and the loop skips those modules when it reaches them.  A parent module that declares
# nothing (the root module) is not run.  A module that came BEFORE its parent in the list would be replayed twice,
# alone and with its parent: correct, only slower (the sorted module list puts every parent first).
# Each run is --verbose: leanchecker prints "replaying <module>" for each module it replays and stops at the first
# failure, so the modules named by a run that exits 0 were all replayed and accepted.  Those modules, checked against
# the modules given (record_replay_coverage), decide part (a) together with the exit statuses.
leanchecker_replay() {
    local label=$1; shift
    local module covered log group_note status=0 failed=() under=() total_seconds=0 peak_kb=0
    local dir="$LOG_DIR/leanchecker" confirmed=() no_constants=()
    local -A replayed=()   # every module some leanchecker run of this call has replayed
    mkdir -p "$dir"
    for module in "$@"; do
        [[ -n ${replayed[$module]:-} ]] && continue   # replayed (and counted) by its parent's run
        under=() group_note=
        if is_parent_module "$module"; then
            if [[ -z $(gated "$TOOLCHAIN_BIN/lean" --run "$HELPER_DIR/ListConstants.lean" "$(olean_of "$module")" 2>&1) ]]; then
                echo "  $module: parent of other modules and declares no constants; nothing to replay"
                no_constants+=("$module"); continue
            fi
            mapfile -t under < <(modules_under "$module" "$@")
            group_note=" (+ ${#under[@]} modules under it, one leanchecker run)"
        fi
        log="$dir/$module.log"
        timed_run "$RUN_TIME_LIMIT_SECONDS" "$log" "$log" lake env "$TOOLCHAIN_BIN/leanchecker" --verbose "$module"
        for covered in "$module" "${under[@]}"; do replayed[$covered]=1; done
        total_seconds=$(awk -v a="$total_seconds" -v b="$RUN_SECONDS" 'BEGIN { print a + b }')
        (( RUN_RSS_KB > peak_kb )) && peak_kb=$RUN_RSS_KB
        if (( RUN_EXIT == 0 )); then
            echo "  $module$group_note: accepted"
            mapfile -t -O "${#confirmed[@]}" confirmed < <(replayed_modules_in "$log")
        elif (( RUN_EXIT == 124 )); then
            echo "  $module$group_note: STOPPED at the ${RUN_TIME_LIMIT_SECONDS} s limit (exit 124; not a rejection)"
            failed+=("$module$group_note stopped at the time limit"); show_failure_tail "$log"
        else echo "  $module$group_note: REJECTED (exit $RUN_EXIT)"; failed+=("$module$group_note"); show_failure_tail "$log"; fi
    done
    RUN_SECONDS=$total_seconds; RUN_RSS_KB=$peak_kb
    if (( ${#failed[@]} == 0 )); then record "$label" "PASS(${#replayed[@]} modules, $(resource_note))"
    else record "$label" "FAIL(${#failed[@]} of ${#replayed[@]} modules: ${failed[*]}; logs in $dir)"; status=1; fi
    write_sorted "$dir/modules_expected.txt" "$@"
    write_sorted "$dir/modules_confirmed.txt" "${confirmed[@]}"
    write_sorted "$dir/modules_no_constants.txt" "${no_constants[@]}"
    record_replay_coverage "$dir" || status=1
    (( status == 0 )) || ANY_FAIL=1
    return "$status"
}

# Writes the safe constants of MODULES to NAMES_FILE and the skipped unsafe/partial ones to NAMES_FILE.skipped.
list_constants() {
    local names_file=$1; shift
    local module
    local -a oleans=()
    for module in "$@"; do oleans+=("$(olean_of "$module")"); done
    if ! gated "$TOOLCHAIN_BIN/lean" --run "$HELPER_DIR/ListConstants.lean" "${oleans[@]}" \
        > "$names_file" 2> "$names_file.skipped"; then
        record "leanexport" "FAIL(listing constants failed: $(grep -v '^skipped' "$names_file.skipped" | head -n 1))"
        ANY_FAIL=1; return 1
    fi
}

# Exports the names in NAMES_FILE, with everything they depend on, from an environment importing MODULES.
export_constants() {
    local export_file=$1 names_file=$2; shift 2
    local log="$export_file.log"
    local -a names
    mapfile -t names < "$names_file"
    (( ${#names[@]} > 0 )) || { record "leanexport" "FAIL(no constants to export)"; ANY_FAIL=1; return 1; }
    timed_run "$RUN_TIME_LIMIT_SECONDS" "$export_file" "$log" lake env "$TOOLCHAIN_BIN/leanexport" "$@" -- "${names[@]}"
    if (( RUN_EXIT != 0 )) || [[ -s $log ]]; then   # leanexport writes nothing to stderr on success
        record "leanexport" "FAIL(exit $RUN_EXIT; $log)"; show_failure_tail "$log"; ANY_FAIL=1; return 1
    fi
}

# Loads the analyzer's key=value lines into EXPORT_* variables; fails unless the export declares every name.
analyze_export() {
    local export_file=$1 names_file=$2 key value
    python3 -I "$HELPER_DIR/analyze_export.py" "$export_file" "$names_file" "$export_file.missing" \
        > "$export_file.analysis" || { record "leanexport" "FAIL(cannot analyze $export_file)"; ANY_FAIL=1; return 1; }
    while IFS='=' read -r key value; do printf -v "EXPORT_${key^^}" '%s' "$value"; done < "$export_file.analysis"
    if (( EXPORT_MISSING != 0 || EXPORT_RECORDS == 0 )); then
        record "leanexport" "FAIL(declares $EXPORT_RECORDS records and lacks $EXPORT_MISSING of $EXPORT_REQUESTED requested names; $export_file.missing)"
        ANY_FAIL=1; return 1
    fi
    # Count conventions (measured on a 51339-record export; con-* per its --help): con-* count one per declaration
    # record (a mutual inductive block is one record); lean4lean likewise but the 4 quotient records as one;
    # nanoda counts each inductive type, constructor and recursor separately.
    EXPECTED_RECORD_COUNT=$EXPORT_RECORDS
    EXPECTED_LEAN4LEAN_COUNT=$(( EXPORT_RECORDS - (EXPORT_QUOT_RECORDS > 0 ? EXPORT_QUOT_RECORDS - 1 : 0) ))
    EXPECTED_NANODA_COUNT=$(( EXPORT_RECORDS - EXPORT_INDUCTIVE_RECORDS + EXPORT_INDUCTIVE_MEMBERS ))
    record "leanexport" "PASS($EXPORT_REQUESTED requested constants + dependencies = $EXPORT_RECORDS declaration records, $(du -h "$export_file" | cut -f1), $(resource_note))"
}

write_nanoda_config() {
    local config=$1 export_file=$2
    python3 -I - "$config" "$export_file" "$EXPORT_AXIOMS" <<'EOF'
import json, sys
config_path, export_path, axioms = sys.argv[1:4]
with open(config_path, "w", encoding="utf-8") as out:
    json.dump({"export_file_path": export_path, "use_stdin": False,
               "permitted_axioms": [name for name in axioms.split(",") if name],
               "unpermitted_axiom_hard_error": True, "num_threads": 1,
               "nat_extension": True, "string_extension": True, "print_success_message": True}, out)
EOF
}

# Runs one export checker.  ACCEPT_REGEX must match its output; if COUNT_REGEX is non-empty, the number it
# captures must equal EXPECTED.  Exit 2 with a "declined" verdict (con-leche/con-ron) is SKIPPED, not FAIL.
# Either SKIPPED (stopped at the limit, or declined) sets ANY_SKIPPED: the run then ends with exit 4.
export_checker() {
    local label=$1 accept_regex=$2 count_regex=$3 expected=$4; shift 4
    local log="$LOG_DIR/export_${label//[^A-Za-z0-9]/_}.log" count reason
    timed_run "$EXPORT_CHECKER_TIME_LIMIT_SECONDS" "$log" "$log" "$@"
    if (( RUN_EXIT == 124 )); then
        record "$label" "SKIPPED(stopped at the ${EXPORT_CHECKER_TIME_LIMIT_SECONDS} s limit; needs longer)"
        ANY_SKIPPED=1; return 2
    fi
    if (( RUN_EXIT == 2 )) && reason=$(grep -Eo '(declined|not implemented yet): [^[(]*' "$log" | head -n 1) \
        && [[ -n $reason ]]; then
        record "$label" "SKIPPED(checker declines the export, ${reason% }, first at: $(grep -Eo '\[at [a-z]+ [^],]*' "$log" | head -n 1 | cut -c5- || true))"
        ANY_SKIPPED=1; return 2
    fi
    if (( RUN_EXIT != 0 )) || ! grep -Eq "$accept_regex" "$log"; then
        record "$label" "FAIL(exit $RUN_EXIT, $(resource_note); $log)"; show_failure_tail "$log"; ANY_FAIL=1; return 1
    fi
    if [[ -z $count_regex ]]; then
        record "$label" "PASS(no count printed; export has $EXPORT_RECORDS records, $(resource_note))"; return 0
    fi
    count=$(grep -Eo "$count_regex" "$log" | grep -Eo '[0-9]+' | tail -n 1 || true)
    if [[ $count != "$expected" ]]; then
        record "$label" "FAIL(reports ${count:-no} declarations, expected $expected; $log)"; ANY_FAIL=1; return 1
    fi
    record "$label" "PASS($count declarations, $(resource_note))"
}

# Export checker number INDEX (0-based, EXPORT_CHECKERS order) on EXPORT_FILE.  Same commands as `lake check
# --paranoid`, but nanoda and con-* pinned to one thread.
run_one_export_checker() {
    local index=$1 export_file=$2
    case $index in
        0) export_checker "${EXPORT_CHECKERS[0]}" "Lean default kernel accepts" "" "" \
               "$TOOLCHAIN_BIN/leanchecker" --from-export "$export_file" ;;
        1) export_checker "${EXPORT_CHECKERS[1]}" "Lean default kernel accepts" "" "" \
               "$TOOLCHAIN_BIN/leanchecker-paranoid" --from-export "$export_file" ;;
        2) export_checker "${EXPORT_CHECKERS[2]}" "^checked [0-9]+ declarations" "^checked [0-9]+ declarations" \
               "$EXPECTED_LEAN4LEAN_COUNT" "$TOOLCHAIN_BIN/lean4lean" "${LEAN4LEAN_FUEL[@]}" --import "$export_file" ;;
        3) export_checker "${EXPORT_CHECKERS[3]}" "no typechecker errors" "^Checked [0-9]+ declarations with no typechecker errors" \
               "$EXPECTED_NANODA_COUNT" "$TOOLCHAIN_BIN/nanoda_bin" "$export_file.nanoda.json" ;;
        4) export_checker "${EXPORT_CHECKERS[4]}" "^con-leche: accepted [0-9]+ declarations" "accepted [0-9]+ declarations" \
               "$EXPECTED_RECORD_COUNT" "$TOOLCHAIN_BIN/con-leche" --jobs=1 "$export_file" ;;
        5) export_checker "${EXPORT_CHECKERS[5]}" "^con-ron: accepted [0-9]+ declarations" "accepted [0-9]+ declarations" \
               "$EXPECTED_RECORD_COUNT" "$TOOLCHAIN_BIN/con-ron" --jobs=1 "$export_file" ;;
        *) die "no export checker number $index" ;;
    esac
}

# The 0-based checker indices that SELECTION names: "all" -> 0..5, a single index -> itself.
selected_checkers() {
    if [[ $1 == all ]]; then seq 0 $(( ${#EXPORT_CHECKERS[@]} - 1 )); else echo "$1"; fi
}

# (b) The export checkers chosen by SELECTION ("all" or one 0-based index) on one export, in EXPORT_CHECKERS
# order.  Returns the number of chosen checkers that did not PASS.
run_export_checkers() {
    local export_file=$1 selection=${2:-all} not_passed=0 index
    write_nanoda_config "$export_file.nanoda.json" "$export_file"
    for index in $(selected_checkers "$selection"); do
        run_one_export_checker "$index" "$export_file" || not_passed=$((not_passed + 1))
    done
    return "$not_passed"
}

# A split run (SELECTION = one 0-based index) records every other export checker as NOT RUN.
record_unselected_checkers() {
    local selection=$1 index
    [[ $selection == all ]] && return 0
    for index in "${!EXPORT_CHECKERS[@]}"; do
        (( index == selection )) || record "${EXPORT_CHECKERS[$index]}" "NOT RUN(--only-checker $(( selection + 1 )))"
    done
}

print_summary() {
    echo
    echo "==== kernel_replay summary $(date '+%Y%m%d__%H:%M') — logs in $LOG_DIR ===="
    printf '%s\n' "${SUMMARY[@]}"
}

# (b) list + export + analyze, then the export checkers chosen by SELECTION ("all" or one 0-based index).
run_export_part() {
    local names_file=$1 export_file=$2 selection=$3 label index chosen="the 6 export checkers"
    [[ $selection == all ]] || chosen="export checker $(( selection + 1 )) only"
    echo "(b) leanexport of every safe $LIB_NAME constant with its dependencies..."
    if list_constants "$names_file" "${ALL_MODULES[@]}" \
        && export_constants "$export_file" "$names_file" "${ALL_MODULES[@]}" \
        && analyze_export "$export_file" "$names_file"; then
        echo "    $EXPORT_RECORDS declaration records; running $chosen..."
        run_export_checkers "$export_file" "$selection" || true
        record "axioms declared in the export" "${EXPORT_AXIOMS//,/, }"
    else
        for index in $(selected_checkers "$selection"); do
            label=${EXPORT_CHECKERS[$index]}; record "$label" "SKIPPED(export failed)"
        done
    fi
    record_unselected_checkers "$selection"
    record "not exported (unsafe/partial)" "$(grep -c '^skipped' "$names_file.skipped" || true) compiler helpers; replayed in (a) only"
}

# USE_BUILT_OLEANS 0/1; OLEAN_REPLAY 0/1 (part (a)); EXPORT_SELECTION "all" | "none" | one 0-based checker index.
main_full_run() {
    local use_built_oleans=$1 not_fresh=$1 olean_replay=$2 export_selection=$3 module
    mapfile -t ALL_MODULES < <(all_modules)
    LOG_DIR="$WORK_DIR/logs_$(date +%Y%m%d_%H%M)"
    mkdir -p "$LOG_DIR"
    echo "Project $PROJECT_DIR: ${#ALL_MODULES[@]} modules; toolchain $TOOLCHAIN_BIN"
    if (( use_built_oleans )); then
        record "certification mode" "UNCERTIFIED(--use-built-oleans requested; this run never exits 0)"
    else
        check_lake_fresh "$LIB_NAME" || exit 3
    fi
    if ! check_oleans_fresh "${ALL_MODULES[@]}"; then
        if (( ! use_built_oleans )); then
            echo "PRECONDITION: build first (e.g. scripts/check.sh), or pass --use-built-oleans. Nothing was checked." >&2
            exit 3
        fi
        not_fresh=1
        record "olean freshness" "NOT FRESH(checking the oleans as built; no olean, NOT checked: ${MISSING_MODULES[*]:-none})"
        mapfile -t ALL_MODULES < <(for module in "${ALL_MODULES[@]}"; do [[ -f $(olean_of "$module") ]] && echo "$module"; done)
    fi
    local before names_file="$WORK_DIR/${LIB_NAME}_constants.txt" export_file="$WORK_DIR/${LIB_NAME}_export.ndjson"
    before=$(snapshot_inputs) || die "cannot snapshot replay inputs"

    if (( olean_replay )); then
        echo "(a) leanchecker olean replay, one process per module:"
        leanchecker_replay "leanchecker (olean replay)" "${ALL_MODULES[@]}" || true
    elif [[ $export_selection == all ]]; then
        record "leanchecker (olean replay)" "NOT RUN(--export-only)"
    else
        record "leanchecker (olean replay)" "NOT RUN(--only-checker $(( export_selection + 1 )))"
    fi
    if [[ $export_selection == none ]]; then
        record "(b) export + export checkers" "NOT RUN(--only-olean)"
    else
        run_export_part "$names_file" "$export_file" "$export_selection"
    fi

    local changed=0
    local after
    after=$(snapshot_inputs) || die "cannot recheck replay inputs"
    [[ $before == "$after" ]] || changed=1
    (( changed )) && record "consistency" "INCONSISTENT(sources, configuration, module inventory, or artifacts changed; rerun after edits and builds stop)"
    print_summary
    (( ANY_FAIL )) && exit 1
    (( changed || not_fresh )) && exit 3
    (( ANY_SKIPPED )) && exit 4
    exit 0
}

# ---------------------------------------------------------------- --selftest (runs Lean) and --test (no Lean)
TEST_FAILURES=0

expect() {   # expect pass|fail DESCRIPTION COMMAND...; shows the summary lines the command produced
    local wanted=$1 description=$2 status=0; shift 2
    SUMMARY=(); ANY_FAIL=0
    "$@" > /dev/null 2>&1 || status=$?
    if [[ $wanted == pass && $status == 0 ]] || [[ $wanted == fail && $status != 0 ]]; then
        echo "ok      $description"
    else
        echo "NOT OK  $description (wanted $wanted, got status $status)"; TEST_FAILURES=$((TEST_FAILURES + 1))
    fi
    (( ${#SUMMARY[@]} == 0 )) || printf '          %s\n' "${SUMMARY[@]}"
}

# KernelReplayBogus: a theorem the elaborator accepts (the kernel check is skipped while adding it) but which is
# ill-typed, since `Nat.zero` is not a proof of `False`.  Every correct kernel must reject it.
write_test_modules() {
    mkdir -p "$SCRATCH_DIR"
    cat > "$SCRATCH_DIR/KernelReplayBogus.lean" <<'EOF'
import Lean
open Lean Elab Command

set_option debug.skipKernelTC true in
run_cmd liftCoreM (addDecl (.thmDecl { name := `kernelReplayBogus, levelParams := [], type := mkConst ``False, value := mkConst ``Nat.zero }))
EOF
    printf 'theorem kernelReplayGood (number : Nat) : number + 0 = number := rfl\n' > "$SCRATCH_DIR/KernelReplayGood.lean"
    # KernelReplayHygienic: `deriving DecidableEq` on a 10-constructor inductive declares macro-scoped constants
    # (`KernelReplayHygienic.match_on_same_ctor._@...._hyg.N`), as deriving DecidableEq can do.
    { printf 'inductive KernelReplayHygienic (size : Nat) where\n'
      printf '  | c%s : Fin size → KernelReplayHygienic size\n' 0 1 2 3 4 5 6 7 8 9
      printf '  deriving DecidableEq\n'; } > "$SCRATCH_DIR/KernelReplayHygienic.lean"
    local module
    for module in KernelReplayBogus KernelReplayGood KernelReplayHygienic; do
        gated "$TOOLCHAIN_BIN/lean" -j1 -R "$SCRATCH_DIR" -o "$SCRATCH_DIR/$module.olean" "$SCRATCH_DIR/$module.lean" \
            || die "the elaborator rejected test module $module"
    done
}

scratch_export() {   # scratch_export MODULE CONSTANT  ->  $SCRATCH_DIR/MODULE.ndjson and MODULE.names
    printf '%s\n' "$2" > "$SCRATCH_DIR/$1.names"
    timed_run "$RUN_TIME_LIMIT_SECONDS" "$SCRATCH_DIR/$1.ndjson" "$LOG_DIR/leanexport_$1.log" \
        env LEAN_PATH="$SCRATCH_DIR" "$TOOLCHAIN_BIN/leanexport" "$1" -- "$2"
    (( RUN_EXIT == 0 )) || die "leanexport failed on test module $1"
}

leanchecker_on_scratch() {
    gated env LEAN_PATH="$SCRATCH_DIR" "$TOOLCHAIN_BIN/leanchecker" "$1" > "$LOG_DIR/leanchecker_$1.log" 2>&1
}

all_export_checkers_accept() { analyze_export "$1" "$2" && run_export_checkers "$1"; }

every_export_checker_rejects() {   # all 6 must report FAIL (a SKIPPED does not count as a rejection)
    analyze_export "$1" "$2" || return 1
    run_export_checkers "$1" || true
    local line rejected=0
    for line in "${SUMMARY[@]}"; do [[ $line == *" FAIL("* ]] && rejected=$((rejected + 1)); done
    (( rejected == ${#EXPORT_CHECKERS[@]} ))
}

lister_names_reach_leanexport() {   # the lister's names for scratch MODULE, incl. a macro-scoped one, all exported
    local names_file="$SCRATCH_DIR/$1.listed" export_file="$SCRATCH_DIR/$1.listed.ndjson"
    gated "$TOOLCHAIN_BIN/lean" --run "$HELPER_DIR/ListConstants.lean" "$SCRATCH_DIR/$1.olean" > "$names_file" || return 1
    grep -q '_hyg' "$names_file" || return 1   # without a macro-scoped name this test would prove nothing
    local -a names
    mapfile -t names < "$names_file"
    gated env LEAN_PATH="$SCRATCH_DIR" "$TOOLCHAIN_BIN/leanexport" "$1" -- "${names[@]}" \
        > "$export_file" 2> "$LOG_DIR/leanexport_$1.listed.log" || return 1
    [[ ! -s $LOG_DIR/leanexport_$1.listed.log ]] && analyze_export "$export_file" "$names_file"
}

project_pipeline_accepts() {   # list + export + analyze + 6 checkers on one known-good project module
    local names_file="$SCRATCH_DIR/project_constants.txt" export_file="$SCRATCH_DIR/project_export.ndjson"
    list_constants "$names_file" "$1" && export_constants "$export_file" "$names_file" "$1" \
        && all_export_checkers_accept "$export_file" "$names_file"
}

main_selftest() {
    LOG_DIR="$SCRATCH_DIR/logs"
    mkdir -p "$LOG_DIR"
    mapfile -t ALL_MODULES < <(all_modules)
    write_test_modules
    scratch_export KernelReplayGood kernelReplayGood
    scratch_export KernelReplayBogus kernelReplayBogus
    head -n 1 "$SCRATCH_DIR/KernelReplayGood.ndjson" > "$SCRATCH_DIR/Empty.ndjson"   # metadata line only

    expect pass "leanchecker accepts a good scratch olean" leanchecker_on_scratch KernelReplayGood
    expect fail "leanchecker rejects an elaborator-accepted, kernel-invalid olean" \
        leanchecker_on_scratch KernelReplayBogus
    expect pass "all 6 export checkers accept the good export" all_export_checkers_accept \
        "$SCRATCH_DIR/KernelReplayGood.ndjson" "$SCRATCH_DIR/KernelReplayGood.names"
    expect pass "each of the 6 export checkers rejects the kernel-invalid export" every_export_checker_rejects \
        "$SCRATCH_DIR/KernelReplayBogus.ndjson" "$SCRATCH_DIR/KernelReplayBogus.names"
    expect fail "an empty export (every checker accepts it) is caught by the completeness check" \
        all_export_checkers_accept "$SCRATCH_DIR/Empty.ndjson" "$SCRATCH_DIR/KernelReplayGood.names"
    expect pass "leanexport reads every name the lister prints, macro-scoped ones included" \
        lister_names_reach_leanexport KernelReplayHygienic

    check_lake_fresh "$POSITIVE_TEST_MODULE" || die "Lake reports $POSITIVE_TEST_MODULE (or an import) out of date"
    check_oleans_fresh "$POSITIVE_TEST_MODULE" || die "the olean of $POSITIVE_TEST_MODULE is missing"
    expect pass "leanchecker replays the project's known-good $POSITIVE_TEST_MODULE" \
        leanchecker_replay "leanchecker (olean replay)" "$POSITIVE_TEST_MODULE"
    expect pass "list + export + 6 checkers accept the project's $POSITIVE_TEST_MODULE" \
        project_pipeline_accepts "$POSITIVE_TEST_MODULE"
    echo
    if (( TEST_FAILURES == 0 )); then echo "kernel_replay --selftest: all 8 tests passed"; return 0; fi
    echo "kernel_replay --selftest: $TEST_FAILURES of 8 tests FAILED"; return 1
}

main() {
    case "${1:-}" in
        "") setup_environment; main_full_run 0 1 all ;;
        --use-built-oleans) setup_environment; main_full_run 1 1 all ;;
        --export-only) setup_environment; main_full_run 0 0 all ;;
        --only-olean) setup_environment; main_full_run 0 1 none ;;
        --only-checker)
            [[ ${2:-} =~ ^[1-6]$ ]] || die "--only-checker needs N = 1..6 (EXPORT_CHECKERS order), got '${2:-}'"
            setup_environment; main_full_run 0 0 $(( $2 - 1 )) ;;
        --selftest) setup_environment; main_selftest ;;
        --test) python3 "$PROJECT_DIR/scripts/test_kernel_replay.py" --test ;;
        -h|--help) sed -n '2,/^set -euo/p' "${BASH_SOURCE[0]}" | sed '$d' ;;
        *) die "unknown argument '$1' (use --test, --selftest, --use-built-oleans, --export-only, --only-olean, --only-checker N, --help, or no argument)" ;;
    esac
}

if [[ ${BASH_SOURCE[0]} == "$0" ]]; then
    main "$@"
fi
