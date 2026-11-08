# Smale's mean value constant exceeds 1.1559 — Lean 4 proof

The paper's link is on the [front page of this folder](https://github.com/david44hello/papers_supporting_materials/tree/main/smale-mean-value-constant).

This folder is a Lean 4 proof of the paper's results.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone --branch smale-mean-value-constant-v2.90 --single-branch https://github.com/david44hello/papers_supporting_materials.git
cd papers_supporting_materials/smale-mean-value-constant/lean
./check.sh
```

It takes about 40 minutes on one core, after Mathlib's files are downloaded, and needs about 8 GB of free memory.
Run `./check.sh`, not a bare `lake build`: check.sh builds with one thread.

Its last lines look like:

```
AUDIT: 84 paper claims (+ 6 retired rows). PROVED: 77, PROVED (RETIRED): 6, PROVED-ASSUMING-(R): 7. COMPUTER-CHECKED: 1. Table: .../AUDIT.md
PASS: project builds; source policy passes; no forbidden assumptions in the paper audit.
```

The project declares no axiom; [AUDIT.md](AUDIT.md) says what each claim rests on.

Fact (R) of Theorem 5.1, which Lean proves, is also checked by computer, by the route the paper prints. To run that check,
install python-flint 0.9.0, then run, in the same copy (about eight minutes on one core):

```bash
cd ../pair_checks
python3 check_pair.py ../pairs/pair_I_K2N18.json --bound 1.1559837
```

It ends with (its Lemma 8.6 is Lemma 4.3 of the paper):

```
LEMMA 8.6 for ../pairs/pair_I_K2N18.json with k = 2, n = 18: PASS
```

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. Smale/Vendor/RiemannMap.lean is a modified copy of work by Yury Kudryashov; see the top of that file.
