#!/bin/bash
# run_logged.sh - run one command, one thread, and write its output to a log that starts with a header (date, command, Python and
#   library versions, md5 of every program in code/) and ends with the exit code and the end time.
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
# Usage (from the folder root): bash code/run_logged.sh logs/NAME.log COMMAND [ARGS...]
set -uo pipefail
if [ $# -lt 2 ]; then
  echo "usage: bash code/run_logged.sh logs/NAME.log COMMAND [ARGS...]" >&2
  exit 2
fi
log=$1
shift
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
{
  echo "=== START $(date '+%Y-%m-%d %H:%M:%S %Z')"
  echo "=== COMMAND $*"
  echo "=== $(python3 --version 2>&1); $(python3 -c 'import importlib.metadata as md; print(", ".join(f"{pkg} {md.version(pkg)}" for pkg in ("python-flint", "mpmath", "numpy", "scipy")))')"
  echo "=== md5 of the programs:"
  md5sum code/*.py code/*.sh
  "$@"
  rc=$?
  echo "=== END $(date '+%Y-%m-%d %H:%M:%S %Z') exit code $rc"
} > "$log" 2>&1
exit "$rc"
