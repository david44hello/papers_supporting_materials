#!/bin/bash
# run_false_cells.sh - the false-cell proposition: on the 140 cells of the cell proposition, the largest Delta (a fraction 9/10, 3/4,
#   1/2 or 1/4 of the floating-point width) for which Gamma < e is certified at s = sec^2(pi/2p) - Delta for every p of the cell.
#   Also runs the self-test of badcells_arb.py (with its negative controls) first.
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
# Usage (from the folder root): bash code/run_logged.sh logs/false_cells_arb.log bash code/run_false_cells.sh   (about 35 min)
set -euo pipefail
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
fractions=9/10,3/4,1/2,1/4
python3 -B code/badcells_arb.py --test
python3 -B code/badcells_arb.py --p-from 4/3 --p-to 19/10 --cells 114 --digits 5 --max-pieces 40 --fractions $fractions
python3 -B code/badcells_arb.py --p-from 19/10 --p-to 99/50 --cells 16 --digits 5 --max-pieces 40 --fractions $fractions
python3 -B code/badcells_arb.py --p-from 99/50 --p-to 199/100 --cells 10 --digits 5 --max-pieces 40 --fractions $fractions
