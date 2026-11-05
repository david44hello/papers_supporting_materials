# Diameters of the order and chain polytopes of a connected poset

The paper: https://doi.org/10.5281/zenodo.23968824

[lean/](lean/) is a Lean 4 proof of the results of version 1.50 of the paper (https://doi.org/10.5281/zenodo.23716603), then titled "The Lee (2026) conjecture on the diameters of order and chain polytopes fails in both directions". The numbered results are the same in version 2.10.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone https://github.com/david44hello/papers_supporting_materials.git
cd papers_supporting_materials/lee-2026-conjecture/lean
./check.sh
```

Its last lines look like:

```
stmt_diff: 115 pairs, 0 not allowed
PASS: project builds; source policy passes; audit OPEN 0 / VIOLATION 0; every X_proved has the type of X.
```

31 claims use results that the paper cites; [AUDIT.md](lean/AUDIT.md) names them, claim by claim.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
