#!/bin/bash
# axioms.sh — print `#print axioms` for theorems of a compiled scratch module. 20261027.
set -euo pipefail
CORE=$1; MOD=$2; shift 2
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
OL=${OLEAN_DIR:?set OLEAN_DIR to a scratch olean directory}
PROBE=$(mktemp -d)
trap 'python3 -c "import shutil, sys; shutil.rmtree(sys.argv[1])" "$PROBE"' EXIT
{ echo "import $MOD"; for t in "$@"; do echo "#print axioms Cereceda.$t"; done; } > "$PROBE/Probe.lean"
cd "$ROOT"
LP=$(lake env printenv LEAN_PATH)
LEAN_PATH="$OL:$LP" LEAN_NUM_THREADS=1 nice -n 19 taskset -c "$CORE" lean "$PROBE/Probe.lean"
