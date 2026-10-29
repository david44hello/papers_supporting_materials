# The Cranston–Li–Su–Wang–Xu (2026) conjecture is true — Lean 4 proof

The paper: https://doi.org/10.5281/zenodo.23729901

This folder is a Lean 4 proof of the paper's results.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone https://github.com/david44hello/papers_supporting_materials.git
cd papers_supporting_materials/cranston-li-su-wang-xu-2026-conjecture/lean
./check.sh
```

Its last lines look like:

```
AUDIT: 106 claims. PROVED: 106. Table: .../AUDIT.md
PASS: project builds; source policy passes; no forbidden assumptions in the paper audit.
```

[AUDIT.md](AUDIT.md) lists every claim of the paper, as Lean sees it.

Copyright (C) Dave Goel 2026--now. All rights reserved.
