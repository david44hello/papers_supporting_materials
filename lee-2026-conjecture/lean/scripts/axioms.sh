#!/bin/bash
# axioms.sh — print `#print axioms` for theorems of a compiled scratch module.
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
set -euo pipefail
CORE=$1; MOD=$2; shift 2
ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
OL=${OLEAN_DIR:-$ROOT/.lake/scratch/olean}
mkdir -p "$ROOT/.lake/scratch"
PROBE=$(mktemp -d "$ROOT/.lake/scratch/probe.XXXX")
{ echo "import $MOD"; for t in "$@"; do echo "#print axioms LeeDiam.$t"; done; } > "$PROBE/Probe.lean"
cd "$ROOT"
LP=$(lake env printenv LEAN_PATH)
LEAN_PATH="$OL:$LP" LEAN_NUM_THREADS=1 nice -n 19 taskset -c "$CORE" lean "$PROBE/Probe.lean"
python3 -c 'import shutil, sys; shutil.rmtree(sys.argv[1])' "$PROBE" >/dev/null 2>&1 || true
