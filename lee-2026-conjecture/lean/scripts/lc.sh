#!/bin/bash
# lc.sh — compile one scratch module of LeeDiamLean into a private scratch olean dir (no lake build).
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
set -euo pipefail
CORE=$1; SRC=$2
ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
OL=${OLEAN_DIR:-$ROOT/.lake/scratch/olean}
MOD=${SRC%.lean}
mkdir -p "$OL/$(dirname "$MOD")"
cd "$ROOT"
LP=$(lake env printenv LEAN_PATH)
# Courtesy limit (shared-machine memory): at most 2 of these compiles at once; wait for a free slot.
SLOTDIR="$ROOT/.lake/scratch/lean_slots"; mkdir -p "$SLOTDIR"
while true; do
  for k in 1 2; do exec 9>"$SLOTDIR/slot$k.lock"; if flock -n 9; then break 2; fi; exec 9>&-; done
  sleep 3
done
LEAN_PATH="$OL:$LP" LEAN_NUM_THREADS=1 nice -n 19 taskset -c "$CORE" lean -DautoImplicit=false -DrelaxedAutoImplicit=false --root="$ROOT" -o "$OL/$MOD.olean" "$SRC"
