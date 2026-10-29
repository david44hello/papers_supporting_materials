# Improving Razmyslov's (1974) bound: the Nagata–Higman index is at most n² − 2 for n ≥ 3

The paper: https://doi.org/10.5281/zenodo.23627984

[lean/](lean/) is a Lean 4 proof of the paper's results. To check it, install Git, Lean
(https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone https://github.com/david44hello/papers_supporting_materials.git
cd papers_supporting_materials/nagata-higman-index/lean
./check.sh
```

Near the end it prints lines like:

```
AUDIT: 147 claims. PROVED: 131, PROVED-FROM-CITED: 16. Table: .../AUDIT.md
PASS: project builds; source policy passes; no forbidden assumptions in the paper audit; route facts hold.
```

16 claims use results that the paper cites; [AUDIT.md](lean/AUDIT.md) names them, claim by claim.

Copyright (C) Dave Goel 2026--now. All rights reserved.
