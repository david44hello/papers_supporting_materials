# The Cereceda (2007) conjecture holds for bipartite 2-degenerate graphs: the Lean proof

Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.

This folder is the Lean 4 proof of the paper's results (version 3.90). It assumes results of three other works, each quoted from its source in `Cereceda/Cited/`: Theorem 5.22 of Cereceda's PhD thesis (2007), Theorem 1 of Bousquet and Heinrich (2022), and Theorems 8 and 10 of Bonamy, Johnson, Lignos, Patel and Paulusma (2014). Three statements also take a fact about planar graphs as an explicit hypothesis (one of them is Theorem 2 of Bousquet and Heinrich); Lean does not prove these facts. `AUDIT.md` gives each of the 122 claims of the paper with its status in Lean: 111 proved, 8 proved from the cited results, 3 proved given a planar-graph fact, 0 open. `AUDIT_NOTES.md` lists what is not formalized and where the Lean proof takes another route.

Build, from this folder: `lake exe cache get && lake build` (Lean 4 v4.35.0, Mathlib commit 56a005855ea1).
