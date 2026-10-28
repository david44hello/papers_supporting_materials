#!/bin/bash
# run_best_constant.sh - the best constant: lambda_{*,N} at p = 3/2 for s = 4 and s = 3.98, N = 3K for K = 400 ... 6400
#   (N = 1200 ... 19200), 26 bisection steps each.
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
# Usage (from the folder root): bash code/run_logged.sh logs/best_constant.log bash code/run_best_constant.sh   (about 25 min)
set -euo pipefail
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
for sval in 4.0 3.98; do
  for kval in 400 800 1600 3200 6400; do
    python3 -B code/best_constant_lp.py --constant 1.5 "$sval" "$kval" 26
  done
done
