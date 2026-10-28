#!/usr/bin/env bash
# OssermanLean (project 013) — 2026-10-26 (HibiLiLean's check.sh; adapted for 011 and 013).
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
set -euo pipefail

project_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)

scan_sources() {
    local source_dir=$1 status=0 failed=0
    [[ -d "$source_dir" ]] || { echo "ERROR: missing source directory: $source_dir" >&2; return 2; }
    # Deliberately conservative: forbidden words in comments/strings also fail.
    # Scan hidden/untracked Lean files too; dependencies, Git data, and root backups are excluded.
    (cd "$source_dir" && rg --hidden --no-ignore -n -w --glob '*.lean' \
        --glob '!.lake/**' --glob '!.git/**' --glob '!versions/**' \
        'sorry|admit|sorryAx|native_decide|implemented_by|extern|opaque|ofReduceBool|unsafe|debug[.]skipKernelTC|csimp' .) || status=$?
    if (( status == 0 )); then
        echo 'ERROR: proof hole or forbidden proof construct in local Lean sources (including Cited).' >&2
        failed=1
    elif (( status != 1 )); then return "$status"; fi
    status=0
    (cd "$source_dir" && rg --hidden --no-ignore -n -w --glob '*.lean' \
        --glob '!.lake/**' --glob '!.git/**' --glob '!versions/**' --glob '!Osserman/Cited/**' 'axiom' .) || status=$?
    if (( status == 0 )); then
        echo 'ERROR: axiom outside Osserman/Cited/.' >&2
        failed=1
    elif (( status != 1 )); then return "$status"; fi
    return "$failed"
}

run_tests() (
    local fixture
    fixture=$(mktemp -d "$project_dir/scripts/.check-test.XXXXXX")
    trap 'python3 -c "import pathlib, shutil, sys; shutil.rmtree(pathlib.Path(sys.argv[1]))" "$fixture"' EXIT
    mkdir -p "$fixture/Osserman/Cited" "$fixture/Osserman/CitedExtra" "$fixture/.lake/packages/dependency" "$fixture/versions"
    printf 'theorem good : True := True.intro\n' > "$fixture/Osserman/Basic.lean"
    printf 'axiom external_result : True\n' > "$fixture/Osserman/Cited/External.lean"
    printf 'theorem dependency_result : True := by sorry\n' > "$fixture/.lake/packages/dependency/Basic.lean"
    printf 'axiom old_assumption : True\ntheorem old_gap : True := by sorry\n' > "$fixture/versions/Old.lean"
    scan_sources "$fixture" || return 1
    local bad_source
    for bad_source in 'theorem hole : True := by sorry' 'theorem hole : True := by admit' \
        'axiom invented : True' 'axiom\ninvented : True' 'def hidden := sorryAx' \
        'example : True := by native_decide' '@[implemented_by replacement] def original := 1' \
        '@[extern "foreign"] opaque external : Nat' 'opaque hidden_value : Nat' \
        'theorem by_reduction : True := Lean.ofReduceBool _ _ rfl' 'unsafe def unchecked := 1' \
        'set_option debug.skipKernelTC true' '@[csimp] theorem compiled_replacement : True := True.intro'; do
        printf '%b\n' "$bad_source" > "$fixture/Osserman/Basic.lean"
        if scan_sources "$fixture" >/dev/null 2>&1; then
            echo "TEST FAILED: accepted $bad_source" >&2; return 1
        fi
    done
    printf 'theorem good : True := True.intro\n' > "$fixture/Osserman/Basic.lean"
    printf 'axiom misplaced : True\n' > "$fixture/Osserman/CitedExtra/Bad.lean"
    if scan_sources "$fixture" >/dev/null 2>&1; then
        echo 'TEST FAILED: accepted axiom in CitedExtra.' >&2; return 1
    fi
    printf 'theorem good : True := True.intro\n' > "$fixture/Osserman/CitedExtra/Bad.lean"
    printf 'theorem hole : True := by sorry\n' > "$fixture/Osserman/Cited/External.lean"
    if scan_sources "$fixture" >/dev/null 2>&1; then
        echo 'TEST FAILED: accepted proof hole in Cited.' >&2; return 1
    fi
    echo 'PASS: scanner accepts cited axioms and rejects proof holes and misplaced axioms.'
)

main() {
    case "${1:-}" in
        --test) [[ $# == 1 ]] || return 2; run_tests; return ;;
        '') [[ $# == 0 ]] || return 2 ;;
        *) echo "Usage: $0 [--test]" >&2; return 2 ;;
    esac
    cd "$project_dir"
    export LEAN_NUM_THREADS=1
    # Fail before the real build if Mathlib would need compilation.
    nice -n 19 lake --no-build build mathlib/Mathlib
    nice -n 19 lake build
    local scan_status=0
    scan_sources . || scan_status=$?
    nice -n 19 python3 scripts/audit.py
    # The dependency facts behind AUDIT.md's "Route differences" (a mismatch is a Lean error, so a nonzero exit).
    nice -n 19 lake env lean scripts/route_check.lean
    (( scan_status == 0 )) || return "$scan_status"
    echo 'PASS: project builds; source policy passes; no forbidden assumptions in the paper audit; route facts hold.'
}

main "$@"
