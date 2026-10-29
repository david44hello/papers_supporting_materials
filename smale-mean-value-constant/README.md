# Smale's mean value constant exceeds 1.1559 — supporting materials

For the paper "Smale's mean value constant exceeds 1.1559" by Dave Goel.

The paper (version 1.90): https://doi.org/10.5281/zenodo.23731801

An expanded version of the paper, with many other results, is on Zenodo: https://doi.org/10.5281/zenodo.23597020

- pairs/pair_I_K2N18.json: the exact data of the pair (W, B) that proves the paper's main theorem.
- pair_checks/check_pair.py: the program that checks the pair; pair_checks/check_pair.log: the output of its run.
- pair_checks/make_controls.py, pair_checks/controls.log: wrong inputs that the program must reject, and the output.
  pairs/pair_XVII_T6.json is a small pair used only by these controls.
- rebuild_from_printed.py: checks that the numbers printed in the paper (its LaTeX source) give this data.
- lean/: a Lean 4 check of the paper (Lean v4.35.0, Mathlib commit 56a005855ea1). It proves the paper's results from the
  cited results of Jatar and Ng (an unrefereed preprint) and of Dieudonné, except fact (R) of Theorem 5.1, which is checked
  by computer (pair_checks/check_pair.py) and NOT proved in Lean; the main theorems are proved there assuming (R).
  lean/AUDIT.md lists every claim of the paper with its status.

To run (Python 3 with python-flint 0.9.0; about eight minutes on one core), in pair_checks/:

    python3 check_pair.py ../pairs/pair_I_K2N18.json --bound 1.1559837

and, in this folder, with the paper's LaTeX source as the first argument:

    python3 rebuild_from_printed.py <the paper's .tex file> pairs/pair_I_K2N18.json

All lemma, theorem and table numbers in check_pair.py refer to the expanded version: its Lemma 8.6, Lemma 7.11 and (C')
are Lemma 4.3, Lemma 4.2 and (C) of the paper, and its polynomial R and number J are V and Λ. In the output of
check_pair.py --test, the line "CONTROL WRONG" is expected: one test checks that a missing file is reported as an error.

Copyright (C) Dave Goel 2026--now. All rights reserved.
