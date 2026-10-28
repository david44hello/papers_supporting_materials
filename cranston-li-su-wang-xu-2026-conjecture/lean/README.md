# The Cranston–Li–Su–Wang–Xu (2026) conjecture is true — the Lean 4 proof

[![Lean build](https://github.com/david44hello/papers_supporting_materials/actions/workflows/lean_build.yml/badge.svg)](https://github.com/david44hello/papers_supporting_materials/actions/workflows/lean_build.yml)

Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.

This folder is a formal proof, checked by the Lean 4 proof assistant, of the results of the paper "The
Cranston–Li–Su–Wang–Xu (2026) conjecture is true" by Dave Goel. Lean checked version 1.51 of the paper. The paper's link
will be added here when it is posted.

## The theorem

Theorem 1.1 of the paper: every even graph (finite; loops and parallel edges allowed, as in the paper) is
A-flow-connected for every finite abelian group A with |A| ≥ 4, and k-flow-connected for every integer k ≥ 4. The
paper also notes that the number 4 cannot be replaced by 3; Lean proves this for the paper's example, the even graph
with two vertices and six parallel edges (`intro_example`). The paper defines these terms in Section 2; the Lean
definitions are in [EulerFlow/Defs/](EulerFlow/Defs/). In Lean:

```lean
theorem thm_1_1_a (G : MGraph V E) (hev : G.IsEven) (A : Type) [AddCommGroup A] [Fintype A]
    (hA : 4 ≤ Fintype.card A) : G.FlowConnected A
theorem thm_1_1_b (G : MGraph V E) (hev : G.IsEven) (k : ℕ) (hk : 4 ≤ k) : G.KFlowConnected k
theorem intro_example :
    (dipole 6).IsEven ∧ ¬ (dipole 6).FlowConnected (ZMod 3) ∧ ¬ (dipole 6).KFlowConnected 3
```

## What is proved

Every result of the paper, numbered or stated in the text, is proved in Lean 4: as one Lean theorem, or, for a few
sentences of the text, by several Lean theorems together (listed in [AUDIT_NOTES.md](AUDIT_NOTES.md), sections F and
G). So are the results of the paper's expanded version that the paper quotes in Section 1 (its Theorems 2.5, 9.1 and
9.2). That makes 93 Lean statements, all in [EulerFlow/Paper/Statements.lean](EulerFlow/Paper/Statements.lean). Every
statement is proved from Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) alone. There is no
other axiom and no unfinished proof (`sorry`) in the project.

## What is not part of the check

The paper also quotes results of other papers as context (its references [1], [2], [4] and [5]). The paper's proofs do
not use them, and they are not part of this check. A few of them are proved here anyway (for example the fact, from
reference [4], that a triangle is A-connected when |A| ≥ 4). Sentences that are not mathematical claims (history,
pointers to other papers, remarks about the text) are listed in [AUDIT_NOTES.md](AUDIT_NOTES.md), section G.

## Where each claim is

[AUDIT.md](AUDIT.md) lists all 93 statements. For each it gives its place in the paper (number and line of the version
1.51 LaTeX source), the paper's claim, and the axioms Lean reports for its proof (`#print axioms`). Each statement's
docstring also begins with its place in the paper (the map is [SHORT_MAP_v1.51.tsv](SHORT_MAP_v1.51.tsv)). Where the
Lean proof takes another route than the text, or where one sentence of the paper is covered by several Lean statements
together, [AUDIT_NOTES.md](AUDIT_NOTES.md) says so (sections A, B, F and G).

## How to check it yourself

Prerequisites: the `elan` Lean toolchain manager, Git, curl, Python 3 and ripgrep (`rg`). From a fresh copy of this
repository:

```bash
git clone https://github.com/david44hello/papers_supporting_materials.git
cd papers_supporting_materials/cranston-li-su-wang-xu-2026-conjecture/lean
lake exe cache get      # downloads prebuilt Mathlib files (it does not compile Mathlib)
lake build
bash scripts/check.sh   # build, scan for forbidden constructs, regenerate AUDIT.md (scripts/audit.py)
git diff --exit-code AUDIT.md   # the regenerated AUDIT.md is identical to the published one
```

GitHub runs these same steps on a fresh machine at every change (the "Lean build" mark at the top; the steps are in
[.github/workflows/lean_build.yml](../../.github/workflows/lean_build.yml) at the top of this repository).

Optional, after a build: `scripts/kernel_replay.sh` re-checks every declaration outside the elaborator: first
`leanchecker` replays each compiled module; then `leanexport` exports the declarations, and the export is checked by
independent checkers: `leanchecker`, its paranoid mode, `lean4lean`, `nanoda`, `con-leche` and `con-ron` (the tools
are listed at the top of the script).

Versions: Lean 4.35.0 (pinned in `lean-toolchain`); Mathlib commit `56a005855ea1` (tag `v4.35.0`; all dependencies
pinned in `lake-manifest.json`).
