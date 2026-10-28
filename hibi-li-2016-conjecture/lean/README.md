# The Hibi–Li (2016) conjecture is fully resolved — the Lean 4 proof

[![Lean build](https://github.com/david44hello/papers_supporting_materials/actions/workflows/lean_build.yml/badge.svg)](https://github.com/david44hello/papers_supporting_materials/actions/workflows/lean_build.yml)

Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.

This folder is a formal proof, checked by the Lean 4 proof assistant, of every result of the paper "The Hibi–Li (2016)
conjecture is fully resolved" by Dave Goel. Lean checked version 2.10 of the paper; the posted version 2.20 changes
only the wording of one footnote. The paper: https://doi.org/10.5281/zenodo.23704735
An expanded version of the paper, with many other results, is on Zenodo:
https://doi.org/10.5281/zenodo.23601975

## The theorem, in plain words

Let P be a finite poset with n elements. Its order polytope O(P) and its chain polytope C(P) are two n-dimensional
polytopes. Hibi and Li conjectured in 2016 that (a) for every k, C(P) has at least as many k-dimensional faces as
O(P), and (b) if the two numbers of k-dimensional faces are equal for some k, then O(P) and C(P) are unimodularly
equivalent. Fourier proved (a).

Let X be the five-element poset with two incomparable elements below a third element, which lies below two further
incomparable elements. Hibi and Li showed that O(P) and C(P) are unimodularly equivalent exactly when P does not
contain X. The paper proves: if P contains X, then for every k with 2 ≤ k ≤ n − 1, C(P) has at least the binomial
coefficient C(n−3, k−2) more k-dimensional faces than O(P); and for every n ≥ 5 some n-element poset containing X
attains all these bounds. So (b) holds for every k with 2 ≤ k ≤ n − 1. For edges (k = 1) it fails, for every poset
that contains X: O(P) and C(P) always have equally many edges (Hibi, Li, Sahara and Shikama, 2017), yet they are not
unimodularly equivalent.

In Lean (names ending in `HL` follow Hibi and Li's own published conventions; the full statement is in
[HibiLi/Paper/Statements.lean](HibiLi/Paper/Statements.lean)):

```lean
theorem HibiLi.Paper.conj_1_1_resolved :
    -- (a) for every poset P with n > 1 elements and every 1 ≤ i ≤ n − 1: f_i(O(P)) ≤ f_i(C(P))
    (∀ (P : Type u) [Fintype P] [PartialOrder P], 1 < Fintype.card P → ∀ i, 1 ≤ i → i ≤ Fintype.card P - 1 →
      fNum (orderPolytopeHL P) i ≤ fNum (chainPolytopeHL P) i) ∧
    -- (b) for every 2 ≤ i ≤ n − 1: f_i(O(P)) = f_i(C(P)) implies that O(P) and C(P) are unimodularly equivalent
    (∀ (P : Type u) [Fintype P] [PartialOrder P] [DecidableEq P], 1 < Fintype.card P → ∀ i, 2 ≤ i →
      i ≤ Fintype.card P - 1 → fNum (orderPolytopeHL P) i = fNum (chainPolytopeHL P) i →
      UnimodEquivHL (orderPolytopeHL P) (chainPolytopeHL P)) ∧
    -- (b) fails for i = 1: X has f_1(O(X)) = f_1(C(X)), but O(X) and C(X) are not unimodularly equivalent
    (fNum (orderPolytopeHL XElem) 1 = fNum (chainPolytopeHL XElem) 1 ∧
      ¬ UnimodEquivHL (orderPolytopeHL XElem) (chainPolytopeHL XElem))
```

Theorem 1.2 of the paper, whose part (c) covers every poset that contains X, is `thm_1_2` in the same file.

## What the proof assumes

Mathlib, Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and five results of other
works that the paper cites, stated as axioms in [HibiLi/Cited/](HibiLi/Cited/), each with its source. Lean assumes
them; it does not prove them again. [AUDIT.md](AUDIT.md), which `scripts/check.sh` regenerates from Lean's
`#print axioms`, names in each row the cited results that claim uses.

| Cited result | Source | Refereed? |
|---|---|---|
| `fourier_lemma_4_1`: the switch face-polynomial identity | Fourier, Lemma 4.1, arXiv:2609.23629v1 (2026) | **No: a preprint** |
| `fourier_prop_5_2`: relative transversality | Fourier, Proposition 5.2, arXiv:2609.23629v1 (2026) | **No: a preprint** |
| `hibiLi_thm_2_1`: the unimodular-equivalence criterion | Hibi–Li, Theorem 2.1, Math. Scand. 118 (2016) | Yes |
| `hlss_thm_2_1`: O(P) and C(P) have equally many edges | Hibi–Li–Sahara–Shikama, Theorem 2.1, Discrete Math. 340 (2017) | Yes |
| `ziegler_face_figure`: vertex figures and face figures | Ziegler, Lectures on Polytopes, Chapter 2 (a textbook) | Yes |

The headline theorem above uses the first, second, third and fifth; Theorem 1.2 (c) also uses `hlss_thm_2_1`. Lean
states Ziegler's result in its own words: the wording was not compared with the book. The lemma of Casabella, Joswig
and Kastner that the paper recalls with its proof is not an assumption: Lean proves it.

## Where each claim of the paper is

[HibiLi/Paper/Statements.lean](HibiLi/Paper/Statements.lean) has one Lean theorem per claim, named by the paper's
numbering. [AUDIT.md](AUDIT.md) lists all 167 statements with their place in the paper: 142 PROVED (from Lean's
standard axioms alone) and 25 PROVED-FROM-CITED (from the standard axioms and the cited results named in that row);
none is open. One of the 25, Proposition 3.4, is Fourier's Proposition 5.2 itself, which the paper quotes: Lean states
it as that assumption. One row, `sec5_census_n6` (a count for n = 6), is a claim of an earlier version of the paper that
version 2.10 no longer makes; Lean keeps it. The comment at the top of Statements.lean lists the few sentences
deliberately not formalized: sentences that report other papers' results without using them, pointers to other
documents, bibliographic sentences, an informal summary, and the recalled proof of a cited lemma that Lean proves by
its own route.

## What a referee must read

Lean checks every proof. A referee only needs to check that the statements say what the paper says: the definitions in
[HibiLi/Defs/](HibiLi/Defs/), the cited results in [HibiLi/Cited/](HibiLi/Cited/), and the statements in
[HibiLi/Paper/Statements.lean](HibiLi/Paper/Statements.lean).

Line numbers in Statements.lean and AUDIT.md refer to the LaTeX source of version 2.10 of the paper, unless a row
names another version.

## How to check it yourself

Prerequisites: the `elan` Lean toolchain manager, Git, curl, Python 3 and ripgrep (`rg`). From a fresh copy of this
repository:

```bash
git clone https://github.com/david44hello/papers_supporting_materials.git
cd papers_supporting_materials/hibi-li-2016-conjecture/lean
git checkout hibi-li-2016-conjecture-v2.10   # the version the paper cites
lake exe cache get      # downloads prebuilt Mathlib files (it does not compile Mathlib)
lake build              # the largest file needs about 8 GB of memory
bash scripts/check.sh   # build, scan for proof holes (sorry, admit, native_decide, ...), regenerate AUDIT.md
git diff --exit-code AUDIT.md   # the regenerated AUDIT.md is identical to the published one
```

GitHub runs these same steps on a fresh machine at every change (the "Lean build" mark at the top; the steps are in
[.github/workflows/lean_build.yml](../../.github/workflows/lean_build.yml) at the top of this repository).

Versions: Lean 4.35.0 (pinned in `lean-toolchain`); Mathlib v4.35.0, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`
(all dependencies pinned in `lake-manifest.json`).
