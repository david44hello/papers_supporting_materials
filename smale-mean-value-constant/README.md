# Smale's mean value constant exceeds 1.1559

The paper: https://doi.org/10.5281/zenodo.23731801

[lean/](lean/) is a Lean 4 proof of the paper's results, except fact (R) of Theorem 5.1: Lean proves the main theorems
assuming (R).

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone https://github.com/david44hello/papers_supporting_materials.git
cd papers_supporting_materials/smale-mean-value-constant/lean
./check.sh
```

Its last lines look like:

```
AUDIT: 83 claims. PROVED: 70, PROVED-ASSUMING-(R): 6, PROVED-FROM-CITED: 7. COMPUTER-CHECKED: 1. Table: .../AUDIT.md
PASS: project builds; source policy passes; no forbidden assumptions in the paper audit.
```

7 claims use results that the paper cites; [AUDIT.md](lean/AUDIT.md) names them, claim by claim.

Fact (R) is checked by computer. To check it, install python-flint 0.9.0, then run, in the same copy (about eight
minutes on one core):

```bash
cd ../pair_checks
python3 check_pair.py ../pairs/pair_I_K2N18.json --bound 1.1559837
```

It ends with (its Lemma 8.6 is Lemma 4.3 of the paper):

```
LEMMA 8.6 for ../pairs/pair_I_K2N18.json with k = 2, n = 18: PASS
```

Copyright (C) Dave Goel 2026--now. All rights reserved.
