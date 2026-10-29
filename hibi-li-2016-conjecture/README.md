# The Hibi–Li (2016) conjecture is fully resolved

The paper: https://doi.org/10.5281/zenodo.23704735

[lean/](lean/) is a Lean 4 proof of the paper's results.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone https://github.com/david44hello/papers_supporting_materials.git
cd papers_supporting_materials/hibi-li-2016-conjecture/lean
./check.sh
```

Its last lines look like:

```
AUDIT: 167 claims. PROVED: 142, PROVED-FROM-CITED: 25. Table: .../AUDIT.md
PASS: project builds; source policy passes; no forbidden assumptions in the paper audit.
```

25 claims use results that the paper cites; [AUDIT.md](lean/AUDIT.md) names them, claim by claim.

Copyright (C) Dave Goel 2026--now. All rights reserved.
