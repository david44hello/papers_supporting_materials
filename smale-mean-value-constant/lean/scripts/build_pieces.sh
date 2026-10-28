#!/usr/bin/env bash
# build_pieces.sh — build the 009 master one module per gated run (leaves first); stop at the first failure.
# Usage: scripts/build_pieces.sh <log> <Module> [<Module> ...]     (run from the project root)
set -u
log="$1"; shift
for mod in "$@"; do
  echo "=== $(date +%H:%M:%S) START $mod" >> "$log"
  env LEAN_NUM_THREADS=1 nice -n 19 \
    lake build "$mod" >> "$log" 2>&1
  status=$?
  echo "=== $(date +%H:%M:%S) END $mod exit $status" >> "$log"
  if [ "$status" -ne 0 ]; then echo "STOPPED at $mod (exit $status)" >> "$log"; exit "$status"; fi
done
echo "ALL DONE" >> "$log"
