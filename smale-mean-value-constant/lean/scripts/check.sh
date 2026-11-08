#!/usr/bin/env bash
# SmaleLean policy check. Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
set -euo pipefail

project_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)

scan_sources() {
    local source_dir=$1 status=0 failed=0
    [[ -d "$source_dir" ]] || { echo "ERROR: missing source directory: $source_dir" >&2; return 2; }
    # Deliberately conservative: forbidden words in comments/strings also fail.
    # Scan hidden/untracked Lean files too; dependencies, Git data, and root backups are excluded.
    (cd "$source_dir" && rg --hidden --no-ignore -n -w --glob '*.lean' \
        --glob '!.lake/**' --glob '!.git/**' --glob '!versions/**' \
        'sorry|admit|sorryAx|native_decide|implemented_by|extern|unsafe|debug[.]skipKernelTC|csimp' .) || status=$?
    if (( status == 0 )); then
        echo 'ERROR: proof hole or forbidden proof construct in local Lean sources.' >&2
        failed=1
    elif (( status != 1 )); then return "$status"; fi
    status=0
    (cd "$source_dir" && rg --hidden --no-ignore -n -w --glob '*.lean' \
        --glob '!.lake/**' --glob '!.git/**' --glob '!versions/**' 'axiom' .) || status=$?
    if (( status == 0 )); then
        echo 'ERROR: axiom in local Lean sources; the project declares none.' >&2
        failed=1
    elif (( status != 1 )); then return "$status"; fi
    status=0
    # The repository is Apache 2.0. Only Smale/Vendor/ may carry this phrase: its upstream notices are kept word for word.
    (cd "$source_dir" && rg --hidden --no-ignore -n -i --glob '*.lean' --glob '*.md' \
        --glob '!.lake/**' --glob '!.git/**' --glob '!versions/**' --glob '!Smale/Vendor/**' 'all rights reserved' .) || status=$?
    if (( status == 0 )); then
        echo 'ERROR: "All rights reserved" outside Smale/Vendor/.' >&2
        failed=1
    elif (( status != 1 )); then return "$status"; fi
    return "$failed"
}

run_tests() (
    local fixture
    fixture=$(mktemp -d "$project_dir/scripts/.check-test.XXXXXX")
    trap 'python3 -c "import pathlib, shutil, sys; shutil.rmtree(pathlib.Path(sys.argv[1]))" "$fixture"' EXIT
    mkdir -p "$fixture/Smale/Cited" "$fixture/.lake/packages/dependency" "$fixture/versions"
    printf 'theorem good : True := True.intro\n' > "$fixture/Smale/Basic.lean"
    printf 'theorem dependency_result : True := by sorry\n' > "$fixture/.lake/packages/dependency/Basic.lean"
    printf 'axiom old_assumption : True\ntheorem old_gap : True := by sorry\n' > "$fixture/versions/Old.lean"
    scan_sources "$fixture" || return 1
    local bad_source
    for bad_source in 'theorem hole : True := by sorry' 'theorem hole : True := by admit' \
        'axiom invented : True' 'axiom\ninvented : True' 'def hidden := sorryAx' \
        'example : True := by native_decide' '@[implemented_by replacement] def original := 1' \
        '@[extern "foreign"] opaque external : Nat' 'unsafe def unchecked := 1' \
        'set_option debug.skipKernelTC true' '@[csimp] theorem compiled_replacement : True := True.intro'; do
        printf '%b\n' "$bad_source" > "$fixture/Smale/Basic.lean"
        if scan_sources "$fixture" >/dev/null 2>&1; then
            echo "TEST FAILED: accepted $bad_source" >&2; return 1
        fi
    done
    printf 'theorem good : True := True.intro\n' > "$fixture/Smale/Basic.lean"
    printf 'axiom external_result : True\n' > "$fixture/Smale/Cited/External.lean"
    if scan_sources "$fixture" >/dev/null 2>&1; then
        echo 'TEST FAILED: accepted an axiom in a Cited folder.' >&2; return 1
    fi
    printf 'theorem good : True := True.intro\n' > "$fixture/Smale/Cited/External.lean"
    mkdir -p "$fixture/Smale/Vendor"
    printf -- '-- Copyright (c) Someone. All rights reserved.\n' > "$fixture/Smale/Vendor/Notice.lean"
    scan_sources "$fixture" || { echo 'TEST FAILED: rejected an upstream notice in Smale/Vendor.' >&2; return 1; }
    printf -- '-- Copyright (c) Someone. All rights reserved.\n' > "$fixture/Smale/Basic.lean"
    if scan_sources "$fixture" >/dev/null 2>&1; then
        echo 'TEST FAILED: accepted the rights phrase outside Smale/Vendor.' >&2; return 1
    fi
    echo 'PASS: scanner rejects every axiom, proof hole and rights phrase in local sources; dependencies, versions/ and upstream notices in Smale/Vendor are out of scope.'
    # The real script on a small project with Lake stubbed: a failing audit must stop it, with no PASS.
    mkdir -p "$fixture/gate/scripts" "$fixture/gate/bin"
    cp "$project_dir/scripts/check.sh" "$fixture/gate/scripts/check.sh"
    printf '#!/bin/sh\nexit 0\n' > "$fixture/gate/bin/lake"
    chmod +x "$fixture/gate/bin/lake"
    printf 'theorem good : True := True.intro\n' > "$fixture/gate/Good.lean"
    printf 'raise SystemExit("AUDIT FAILED: stub")\n' > "$fixture/gate/scripts/audit.py"
    if PATH="$fixture/gate/bin:$PATH" bash "$fixture/gate/scripts/check.sh" >/dev/null 2>&1; then
        echo 'TEST FAILED: check.sh passed when the audit failed.' >&2; return 1
    fi
    printf 'print("stub")\n' > "$fixture/gate/scripts/audit.py"
    if ! PATH="$fixture/gate/bin:$PATH" bash "$fixture/gate/scripts/check.sh" >/dev/null 2>&1; then
        echo 'TEST FAILED: check.sh failed when the audit passed.' >&2; return 1
    fi
    echo 'PASS: a failing audit stops check.sh, with no PASS line.'
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
    (( scan_status == 0 )) || return "$scan_status"
    echo 'PASS: project builds; source policy passes; no forbidden assumptions in the paper audit.'
}

main "$@"
