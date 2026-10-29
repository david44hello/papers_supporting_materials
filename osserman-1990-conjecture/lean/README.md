# The Osserman (1990) conjecture is fully resolved — Lean 4 proof of most of Sections 1–8

The paper: https://doi.org/10.5281/zenodo.23744914

This folder is a Lean 4 proof of most of Sections 1–8 of the paper and six pieces of Sections 9–27. Lean does not
check the paper's main result; [AUDIT_NOTES.md](AUDIT_NOTES.md) says exactly what it checks.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone https://github.com/david44hello/papers_supporting_materials.git
cd papers_supporting_materials/osserman-1990-conjecture/lean
./check.sh
```

Near the end it prints lines like:

```
AUDIT: 370 rows = 351 paper claims (PROVED: 299, PROVED-FROM-CITED: 52); 19 Lean-only rows, not claims of the paper (15 non-vacuity witnesses, 4 helpers: PROVED: 19). Table: .../AUDIT.md
PASS: project builds; source policy passes; no forbidden assumptions in the paper audit; route facts hold.
```

52 claims use results that the paper cites; [AUDIT.md](AUDIT.md) names them, claim by claim.

Copyright (C) Dave Goel 2026--now. All rights reserved.
