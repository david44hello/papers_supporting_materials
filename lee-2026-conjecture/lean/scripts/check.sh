#!/usr/bin/env bash
# check.sh — final check of LeeDiamLean (source policy and audit): build, source policy, audit, statement-type diff.
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
#
# Usage (no arguments run the full check on the first available CPU):
#   scripts/check.sh --test                    self-test of the source scanner (no Lean).
#   scripts/check.sh --scan                    source policy only (no Lean, no build).
#   scripts/check.sh --stmt-diff <core> <oleans>   statement-type diff, <oleans> = scratch | lake.
#   scripts/check.sh --final <core>            the final check: Mathlib must be built already; `lake build` (one
#                                              thread, nice 19, taskset <core>); source policy; audit (lake oleans);
#                                              statement-type diff (lake oleans). Run ONLY when the leader announces it.
# Exit: 0 PASS | 1 policy/audit/diff failure | 2 usage | other = the failing tool's own code.
set -euo pipefail

project_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
LIB=LeeDiam
BANNED='sorry|admit|sorryAx|native_decide|implemented_by|extern|opaque|ofReduceBool|unsafe|debug[.]skipKernelTC|csimp'

scan_sources() {
    local source_dir=$1 status=0 failed=0
    [[ -d "$source_dir" ]] || { echo "ERROR: missing source directory: $source_dir" >&2; return 2; }
    # Deliberately conservative: forbidden words in comments and strings also fail (reword the comment).
    (cd "$source_dir" && rg --hidden --no-ignore -n -w --glob '*.lean' \
        --glob '!.lake/**' --glob '!.git/**' --glob '!versions/**' --glob '!**/versions/**' "$BANNED" .) || status=$?
    if (( status == 0 )); then
        echo 'ERROR: proof hole or forbidden proof construct in local Lean sources (including Cited).' >&2
        failed=1
    elif (( status != 1 )); then return "$status"; fi
    status=0
    (cd "$source_dir" && rg --hidden --no-ignore -n -w --glob '*.lean' \
        --glob '!.lake/**' --glob '!.git/**' --glob '!versions/**' --glob '!**/versions/**' \
        --glob "!$LIB/Cited/**" 'axiom' .) || status=$?
    if (( status == 0 )); then
        echo "ERROR: axiom outside $LIB/Cited/." >&2
        failed=1
    elif (( status != 1 )); then return "$status"; fi
    return "$failed"
}

run_tests() (
    local fixture
    fixture=$(mktemp -d "$project_dir/scripts/.check-test.XXXXXX")
    trap 'python3 -c "import pathlib, shutil, sys; shutil.rmtree(pathlib.Path(sys.argv[1]))" "$fixture"' EXIT
    mkdir -p "$fixture/$LIB/Cited" "$fixture/$LIB/CitedExtra" "$fixture/.lake/packages/dependency" \
        "$fixture/versions" "$fixture/$LIB/LB/versions"
    printf 'theorem good : True := True.intro\n' > "$fixture/$LIB/Basic.lean"
    printf 'axiom external_result : True\n' > "$fixture/$LIB/Cited/External.lean"
    printf 'theorem dependency_result : True := by sorry\n' > "$fixture/.lake/packages/dependency/Basic.lean"
    printf 'axiom old_assumption : True\ntheorem old_gap : True := by sorry\n' > "$fixture/versions/Old.lean"
    printf 'theorem old_gap : True := by sorry\n' > "$fixture/$LIB/LB/versions/Old.lean"
    scan_sources "$fixture" || { echo 'TEST FAILED: rejected a clean tree.' >&2; return 1; }
    local bad_source
    for bad_source in 'theorem hole : True := by sorry' 'theorem hole : True := by admit' \
        '-- a comment that says sorry' 'axiom invented : True' 'axiom\ninvented : True' 'def hidden := sorryAx' \
        'example : True := by native_decide' '@[implemented_by replacement] def original := 1' \
        '@[extern "foreign"] opaque external : Nat' 'opaque hidden_value : Nat' \
        'theorem by_reduction : True := Lean.ofReduceBool _ _ rfl' 'unsafe def unchecked := 1' \
        'set_option debug.skipKernelTC true' '@[csimp] theorem compiled_replacement : True := True.intro'; do
        printf '%b\n' "$bad_source" > "$fixture/$LIB/Basic.lean"
        if scan_sources "$fixture" >/dev/null 2>&1; then
            echo "TEST FAILED: accepted $bad_source" >&2; return 1
        fi
    done
    printf 'theorem good : True := True.intro\n' > "$fixture/$LIB/Basic.lean"
    printf 'axiom misplaced : True\n' > "$fixture/$LIB/CitedExtra/Bad.lean"
    if scan_sources "$fixture" >/dev/null 2>&1; then
        echo 'TEST FAILED: accepted axiom in CitedExtra.' >&2; return 1
    fi
    printf 'theorem good : True := True.intro\n' > "$fixture/$LIB/CitedExtra/Bad.lean"
    printf 'theorem hole : True := by sorry\n' > "$fixture/$LIB/Cited/External.lean"
    if scan_sources "$fixture" >/dev/null 2>&1; then
        echo 'TEST FAILED: accepted proof hole in Cited.' >&2; return 1
    fi
    echo 'PASS: scanner accepts cited axioms and rejects proof holes, banned words and misplaced axioms.'
)

# AUDIT.md's summary line must say OPEN 0 and VIOLATION 0.
audit_is_clean() {
    local line
    line=$(grep -m1 '^PROVED ' "$project_dir/AUDIT.md") || { echo 'ERROR: AUDIT.md has no summary line.' >&2; return 1; }
    echo "audit: $line"
    [[ "$line" =~ OPEN\ 0\ / ]] && [[ "$line" =~ VIOLATION\ 0\  ]] && return 0
    echo 'ERROR: the audit has OPEN or VIOLATION claims.' >&2
    return 1
}

final_check() {
    local core=$1
    cd "$project_dir"
    export LEAN_NUM_THREADS=1
    # Fail before the real build if Mathlib (shared, the dependency cache) would need compilation.
    nice -n 19 lake --no-build build mathlib/Mathlib
    nice -n 19 taskset -c "$core" lake build
    local scan_status=0 audit_status=0 diff_status=0
    scan_sources . || scan_status=$?
    nice -n 19 python3 scripts/audit.py "$core" --oleans lake || audit_status=$?
    (( audit_status == 0 )) && { audit_is_clean || audit_status=1; }
    nice -n 19 python3 scripts/stmt_diff.py "$core" lake || diff_status=$?
    (( scan_status == 0 && audit_status == 0 && diff_status == 0 )) || return 1
    echo 'PASS: project builds; source policy passes; audit OPEN 0 / VIOLATION 0; every X_proved has the type of X.'
}

main() {
    case "${1:-}" in
        '') [[ $# == 0 ]] || return 2; final_check "$(python3 -c 'import os; print(min(os.sched_getaffinity(0)))')" ;;
        --test) [[ $# == 1 ]] || return 2; run_tests ;;
        --scan) [[ $# == 1 ]] || return 2; scan_sources "$project_dir" && echo 'PASS: source policy.' ;;
        --stmt-diff) [[ $# == 3 ]] || return 2; cd "$project_dir"; python3 scripts/stmt_diff.py "$2" "$3" ;;
        --final) [[ $# == 2 ]] || return 2; final_check "$2" ;;
        *) echo "Usage: $0 [--test | --scan | --stmt-diff <core> <scratch|lake> | --final <core>]" >&2; return 2 ;;
    esac
}

main "$@"
