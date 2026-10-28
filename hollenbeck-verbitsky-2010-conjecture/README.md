# The Hollenbeck–Verbitsky (2010) conjecture is false: programs and logs

Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.

Run from this folder. Numbering as in the paper.

| Statement | Kind | Program | Command | Log |
|---|---|---|---|---|
| Prop. 5 (sign of H) | interval (Arb) | `code/saddle_sign_arb.py` | `python3 code/saddle_sign_arb.py --test; python3 code/saddle_sign_arb.py` | `logs/saddle_sign_arb.log` |
| Prop. 5 (sign of H) | interval (mpmath) | `code/saddle_sign_mpmath.py` | `python3 code/saddle_sign_mpmath.py` | `logs/saddle_sign_mpmath.log` |
| Prop. 7; Jaguzović's point (after Cor. 9) | interval (Arb) | `code/point_arb.py` | `python3 code/point_arb.py --test; python3 code/point_arb.py --run` | `logs/point_arb.log` |
| Prop. 7; Prop. 10, s₊ | interval (mpmath) | `code/point_check_mpmath.py` | `python3 code/point_check_mpmath.py --test; python3 code/point_check_mpmath.py --run` | `logs/point_check_mpmath.log` |
| Prop. 8 | interval (Arb), quadrature | `code/counterexample_quadrature_arb.py` | `python3 code/counterexample_quadrature_arb.py --test; for L in 2000 2200 2500 3000; do python3 code/counterexample_quadrature_arb.py --verify 3 2 398 100 1.79 0.0102 0.4865 $L 128; done` | `logs/counterexample_quadrature_arb.log` |
| Prop. 8 | interval (Arb), Beta function | `code/counterexample_beta_arb.py` | `python3 code/counterexample_beta_arb.py --test; python3 code/counterexample_beta_arb.py --necks 2000 2133 2134 2200 2500 3000 --v-cut 120` | `logs/counterexample_beta_arb.log` |
| Prop. 8 (W₁, W₀, threshold) | numerical | `code/counterexample_closed_form.py` | `python3 code/counterexample_closed_form.py` | `logs/counterexample_closed_form.log` |
| Prop. 10, s₊ | interval (Arb) | `code/badcells_arb.py` | `python3 code/badcells_arb.py --test; python3 code/badcells_arb.py --points 7/5 3/2 8/5 17/10 9/5 19/10 --digits 4` | `logs/bracket_upper_arb.log` |
| Prop. 10, s₋ | interval (Arb) | `code/truepoints_arb.py` | `python3 code/truepoints_arb.py 7/5:52986/10000 3/2:39572/10000 8/5:31799/10000 17/10:26921/10000 9/5:23764/10000 19/10:21588/10000 --radius 1/5 --ymax 3 --max-boxes 3000000` | `logs/bracket_lower_arb.log` |
| Prop. 10, s₋ | interval (mpmath) | `code/truepoints_mpmath.py` | `python3 code/truepoints_mpmath.py --test; python3 code/truepoints_mpmath.py --run` | `logs/bracket_lower_mpmath.log` |
| Prop. 11 | interval (Arb) | `code/certify_arb.py` | `bash code/run_cells.sh` | `logs/cells_arb.log` |
| Prop. 13 | interval (Arb) | `code/badcells_arb.py` | `bash code/run_false_cells.sh` | `logs/false_cells_arb.log` |
| Section 7 | numerical (LP) | `code/best_constant_lp.py` | `bash code/run_best_constant.sh` | `logs/best_constant.log` |
| Section 7 | numerical (LP) | `code/best_constant_second.py` | `python3 code/best_constant_second.py --test; python3 code/best_constant_second.py --run` | `logs/best_constant_second.log` |
| Section 7 (checks) | numerical (LP) | `code/best_constant_lp.py` | `python3 code/best_constant_lp.py --test` | `logs/best_constant_controls.log` |

Notes on the logs:

- In `logs/saddle_sign_mpmath.log` the three `FAIL at` lines at the top come from the three negative controls listed at its end.
- `code/truepoints_arb.py` has no test of its own: it runs `certify_cell` of `code/certify_arb.py`, whose `--test` (with its negative controls) is at the top of `logs/cells_arb.log`.
- In `logs/counterexample_quadrature_arb.log` the `--verify` lines print the midpoints of the Arb input balls; each ball contains the exact decimal input, so these enclosures (±2.5·10⁻¹⁰) are wider than those of the `--test` run (±3·10⁻¹⁵).

All logs were made in the same environment: Python 3.12.3, python-flint 0.9.0 (Arb), mpmath 1.4.1, NumPy 2.5.4, SciPy 1.18.1 (`requirements.txt`), with `bash code/run_logged.sh logs/NAME.log COMMAND`, which writes the date, these versions and the md5 of every program at the top of the log.
