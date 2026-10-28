# Smale's mean value constant — Lean 4 proofs

For version 1.80 of "Smale's mean value constant exceeds 1.1559" by Dave Goel.

[AUDIT.md](AUDIT.md) lists 83 claims: 70 proved from Lean's standard foundations, 7 proved from cited results, and 6 proved assuming fact (R) of Theorem 5.1. The six are the paper's main results, Theorems 1.1 and 5.1 and Corollary 5.4, each stated twice (once from (R) as the paper states it, once from the exact statement the program checks). Fact (R) is checked by [the accompanying program](../pair_checks/check_pair.py), not proved in Lean.

## Assumptions

The cited results are Jatar and Ng's Propositions 4.2 and 3.1 (arXiv:2610.21472v2, an unrefereed preprint) and Dieudonné's criterion (1931, in the form of Jatar and Ng's Lemma 6.3). They are stated in [Smale/Cited/Basic.lean](Smale/Cited/Basic.lean). The main theorems use Proposition 4.2 and Dieudonné's criterion; they also assume (R): the resultant F(c) of the Dieudonné polynomial P_c of H and its reflection P_c* is a polynomial in c of degree 578 with no zero for c in [-1, 1].

The three standard axioms are `propext`, `Classical.choice` and `Quot.sound`. Each audit row lists its cited assumptions.

## Scope

The audit lists claims from the numbered results, proofs and running text. Its final sections record four differences between the paper's arguments and the Lean proofs, and sentences without a Lean theorem. These include reports of other authors' results, descriptions of the programs, and the numerical observation about where the closest approach occurs. The steps needing a Riemann map are covered by the cited Proposition 3.1; Lean does not construct that map.

Fact (R) remains computer-checked. Facts (D), (C) and (S), and the stated margins in Remark 5.2, are proved in Lean by exact arithmetic. Paper line references are to version 1.80; the data-file header names an earlier version with identical data, as the audit notes explain.

## Build

Install `elan`, Git, Python 3 and ripgrep. From this folder:

```sh
lake exe cache get
lake build
bash scripts/check.sh
git diff --exit-code -- AUDIT.md
```

Lean v4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` are pinned in the toolchain and dependency files. [Smale/Paper/Statements.lean](Smale/Paper/Statements.lean) contains the claims. Optional independent kernel checks are available through `scripts/kernel_replay.sh`, with the checker binaries it names.

Copyright (C) Dave Goel 2026--now. All rights reserved.
