#!/usr/bin/env bash
# Checks the Lean proof: downloads Mathlib's prebuilt files, builds the proof, checks it, prints the result.
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
set -euo pipefail
cd "$(dirname "$0")"
lake exe cache get
bash scripts/check.sh
