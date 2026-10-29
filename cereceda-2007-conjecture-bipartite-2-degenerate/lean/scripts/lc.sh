#!/bin/bash
# lc.sh — compile one scratch module of CerecedaLean into a scratch olean dir (no lake build). 20261027.
set -euo pipefail
CORE=$1; SRC=$2
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
OL=${OLEAN_DIR:?set OLEAN_DIR to a scratch olean directory}
MOD=${SRC%.lean}
mkdir -p "$OL/$(dirname "$MOD")"
cd "$ROOT"
LP=$(lake env printenv LEAN_PATH)
LEAN_PATH="$OL:$LP" LEAN_NUM_THREADS=1 nice -n 19 taskset -c "$CORE" lean -DautoImplicit=false -DrelaxedAutoImplicit=false --root="$ROOT" -o "$OL/$MOD.olean" "$SRC"
