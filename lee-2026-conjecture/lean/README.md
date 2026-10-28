# Lee's polytope diameter conjecture — Lean proofs

For version 1.50 of “The Lee (2026) conjecture on the diameters of order and chain polytopes fails in both directions” by Dave Goel.

[AUDIT.md](AUDIT.md) lists 115 claims: 84 proved from Lean's standard foundations and 31 proved using two cited adjacency statements. There are no open claims in the audit. The two statements characterize edges of the order polytope and chain polytope; they are declared in [LeeDiam/Cited/Lee26.lean](LeeDiam/Cited/Lee26.lean).

The order-polytope statement comes from Ikebe–Tamura (1995) and Hibi–Li (2019). The chain-polytope statement comes from Chvátal (1975), using Stanley's (1986) description. These are refereed sources. Lee's 2026 preprint supplies the conjecture and another citation for the adjacency statements; neither Lean assumption rests on that unrefereed preprint. The standard axioms are `propext`, `Classical.choice` and `Quot.sound`.

[AUDIT_NOTES.md](AUDIT_NOTES.md) lists the scope, results of other papers that are not formalized, two open questions, and five proofs where Lean takes another route. The paper's intermediate steps in those five proofs are also checked as separate claims. Expanded-paper results quoted in the short paper are outside this formalization.

Requirements: Lean (installed through elan), Git, Python 3 and ripgrep. From this directory:

```sh
lake exe cache get
lake build
bash scripts/check.sh --final <available-core-number>
git diff --exit-code -- AUDIT.md
```

The toolchain pins Lean v4.35.0; lake-manifest.json pins Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The final check builds with one thread, checks source policy, regenerates the axiom audit, and compares claim/proof types. With no arguments, `scripts/check.sh` runs the same full check on the first available CPU; GitHub uses this form. Optional `scripts/kernel_replay.sh` requires the additional checker binaries listed in its header. Scratch files are local to `.lake/`.

Copyright (C) Dave Goel 2026--now. All rights reserved.
