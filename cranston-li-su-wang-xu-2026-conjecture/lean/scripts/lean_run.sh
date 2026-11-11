#!/usr/bin/env bash
# lean_run.sh — run ONE Lean/lake command of this project under the shared compile lock and the machine's priority gate.
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
# Version 0.50 (2026-11-10): portable command runner for this library; explicit lock and gate settings, one thread.
#
# Usage:  scripts/lean_run.sh <command> [args...]   e.g.  scripts/lean_run.sh lake build EulerFlow
#         scripts/lean_run.sh --test                 self-test with a stand-in gate (no Lean)
# Runs, from the project root:
#   flock <lock> <gate> --noninteractive -- env LEAN_NUM_THREADS=1 nice -n 19 <command> [args...]
# The lock file and the gate are machine-local: set the environment variables LEAN_RUN_LOCK (a lock file) and
# LEAN_RUN_GATE (an executable gate taking `--noninteractive -- <command>`). Both are required; unset = loud error.
# The value `none` (said explicitly) drops that part: LEAN_RUN_LOCK=none LEAN_RUN_GATE=none runs
#   env LEAN_NUM_THREADS=1 nice -n 19 <command> [args...]
# Exit: the command's exit status (or the gate's / flock's, if they refuse).
set -euo pipefail

project_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)

run_gated() {
    local lock=${LEAN_RUN_LOCK:?lean_run.sh: set LEAN_RUN_LOCK (the compile lock file, or none)} gate=${LEAN_RUN_GATE:?lean_run.sh: set LEAN_RUN_GATE (the priority gate, or none)}
    (( $# > 0 )) || { echo "lean_run.sh: no command given" >&2; return 2; }
    local prefix=()
    if [[ $lock != none ]]; then
        [[ -d $(dirname -- "$lock") ]] || { echo "lean_run.sh: lock directory missing: $(dirname -- "$lock")" >&2; return 2; }
        prefix+=(flock "$lock")
    fi
    if [[ $gate != none ]]; then
        [[ -x $gate ]] || { echo "lean_run.sh: gate not executable: $gate" >&2; return 2; }
        prefix+=("$gate" --noninteractive --)
    fi
    cd "$project_dir"
    ${prefix[@]+"${prefix[@]}"} env LEAN_NUM_THREADS=1 nice -n 19 "$@"
}

run_tests() (
    local fixture
    fixture=$(mktemp -d "$project_dir/scripts/.lean_run-test.XXXXXX")
    trap 'python3 -c "import shutil, sys; shutil.rmtree(sys.argv[1])" "$fixture"' EXIT
    # A stand-in gate: prints its arguments and working directory, then runs the command after `--`.
    printf '%s\n' '#!/usr/bin/env bash' 'printf "GATE %s|" "$@"; printf "CWD %s\n" "$PWD"' \
        'while [[ $1 != -- ]]; do shift; done; shift; exec "$@"' > "$fixture/gate.sh"
    chmod +x "$fixture/gate.sh"
    local output expected
    output=$(cd / && LEAN_RUN_LOCK="$fixture/test.lock" LEAN_RUN_GATE="$fixture/gate.sh" run_gated printf 'ran:%s' "\$LEAN_NUM_THREADS")
    expected="GATE --noninteractive|GATE --|GATE env|GATE LEAN_NUM_THREADS=1|GATE nice|GATE -n|GATE 19|GATE printf|GATE ran:%s|GATE \$LEAN_NUM_THREADS|CWD $project_dir"
    [[ $output == "$expected"* ]] || { echo "TEST FAILED: command line was: $output" >&2; return 1; }
    output=$(LEAN_RUN_LOCK="$fixture/test.lock" LEAN_RUN_GATE="$fixture/gate.sh" run_gated sh -c 'echo "threads=$LEAN_NUM_THREADS"')
    [[ $output == *"threads=1" ]] || { echo "TEST FAILED: LEAN_NUM_THREADS not 1: $output" >&2; return 1; }
    if LEAN_RUN_LOCK="$fixture/missing/test.lock" LEAN_RUN_GATE="$fixture/gate.sh" run_gated true 2>/dev/null; then
        echo 'TEST FAILED: accepted a lock in a missing directory.' >&2; return 1
    fi
    if LEAN_RUN_LOCK="$fixture/test.lock" LEAN_RUN_GATE="$fixture/no-gate.sh" run_gated true 2>/dev/null; then
        echo 'TEST FAILED: accepted a missing gate.' >&2; return 1
    fi
    if LEAN_RUN_LOCK="$fixture/test.lock" LEAN_RUN_GATE="$fixture/gate.sh" run_gated 2>/dev/null; then
        echo 'TEST FAILED: accepted an empty command.' >&2; return 1
    fi
    if LEAN_RUN_LOCK="$fixture/test.lock" LEAN_RUN_GATE="$fixture/gate.sh" run_gated false >/dev/null 2>&1; then
        echo 'TEST FAILED: hid the exit status of a failing command.' >&2; return 1
    fi
    if (unset LEAN_RUN_LOCK; LEAN_RUN_GATE="$fixture/gate.sh" run_gated true) 2>/dev/null; then
        echo 'TEST FAILED: ran without LEAN_RUN_LOCK.' >&2; return 1
    fi
    output=$(cd / && LEAN_RUN_LOCK=none LEAN_RUN_GATE=none run_gated sh -c 'echo "threads=$LEAN_NUM_THREADS cwd=$PWD"')
    [[ $output == "threads=1 cwd=$project_dir" ]] || { echo "TEST FAILED: lock and gate none: $output" >&2; return 1; }
    output=$(LEAN_RUN_LOCK=none LEAN_RUN_GATE="$fixture/gate.sh" run_gated true)
    [[ $output == "GATE --noninteractive|GATE --|GATE env|"* ]] || { echo "TEST FAILED: lock none: $output" >&2; return 1; }
    if LEAN_RUN_LOCK=none LEAN_RUN_GATE=none run_gated false >/dev/null 2>&1; then
        echo 'TEST FAILED: lock and gate none hid the exit status of a failing command.' >&2; return 1
    fi
    if (unset LEAN_RUN_GATE; LEAN_RUN_LOCK=none run_gated true) 2>/dev/null; then
        echo 'TEST FAILED: ran without LEAN_RUN_GATE.' >&2; return 1
    fi
    echo 'PASS: lean_run.sh builds the exact gated command line, runs from the project root, and fails loudly; none drops the lock or the gate.'
)

main() {
    case "${1:-}" in
        --test) [[ $# == 1 ]] || return 2; run_tests ;;
        -h|--help) sed -n '2,/^set -euo/p' "${BASH_SOURCE[0]}" | sed '$d' ;;
        *) run_gated "$@" ;;
    esac
}

main "$@"
