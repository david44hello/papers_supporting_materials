# The Cranston–Li–Su–Wang–Xu (2026) conjecture is true — Lean 4 proof

The paper's link is on the [front page of this folder](https://github.com/david44hello/papers_supporting_materials/tree/main/cranston-li-su-wang-xu-2026-conjecture).

This folder is a Lean 4 proof of the paper's results.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone --branch cranston-li-su-wang-xu-2026-conjecture-v2.00 --single-branch https://github.com/david44hello/papers_supporting_materials.git
cd papers_supporting_materials/cranston-li-su-wang-xu-2026-conjecture/lean
./check.sh
```

Its last lines look like:

```
AUDIT: 114 claims. PROVED: 114. 114 statements = 81 of the short paper (version 2.00) + 32 of the expanded version only + 1 retired. Table: .../AUDIT.md
PASS: project builds; source policy passes; no forbidden assumptions in the paper audit.
```

The proof takes no result of another paper as given: every statement is proved from Lean's three standard axioms alone.

[AUDIT.md](AUDIT.md) lists every claim of the paper, as Lean sees it.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
