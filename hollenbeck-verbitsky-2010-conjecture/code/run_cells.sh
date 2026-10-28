#!/bin/bash
# run_cells.sh - the cell proposition: 140 cells on [4/3, 1.99]; per cell, the largest kappa in {1/2, 13/20, 4/5, 9/10} that proves.
#   Also runs the self-tests of arb_dual.py and certify_arb.py (with their negative controls) first.
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
# Usage (from the folder root): bash code/run_logged.sh logs/cells_arb.log bash code/run_cells.sh   (about 1 hour, one thread)
set -euo pipefail
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
kappas=1/2,13/20,4/5,9/10
python3 -B code/arb_dual.py
python3 -B code/certify_arb.py --test
python3 -B code/certify_arb.py --p-from 4/3 --p-to 19/10 --cells 114 --kappas $kappas --ey 1/5 --et 1/5 --ymax 3 --max-boxes 200000
python3 -B code/certify_arb.py --p-from 19/10 --p-to 99/50 --cells 16 --kappas $kappas --ey 1/5 --et 1/5 --ymax 3 --max-boxes 300000
python3 -B code/certify_arb.py --p-from 99/50 --p-to 199/100 --cells 10 --kappas $kappas --ey 1/5 --et 1/5 --ymax 3 --max-boxes 400000
