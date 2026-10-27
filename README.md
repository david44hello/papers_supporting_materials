# The Hibi–Li (2016) conjecture is fully resolved — the Lean 4 proof

[![Lean build](https://github.com/david44hello/hibi-li-2016-conjecture-lean/actions/workflows/lean_build.yml/badge.svg)](https://github.com/david44hello/hibi-li-2016-conjecture-lean/actions/workflows/lean_build.yml)

Author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licence: Apache-2.0 (see [LICENSE](LICENSE)), the same as Mathlib.

This repository is a formal proof, checked by the Lean 4 proof assistant, of every result of the 9-page paper
"The Hibi–Li (2016) conjecture is fully resolved" by Dave Goel. The paper's link will be added here when it is posted.
An expanded version of the paper, with many other results, is on Zenodo: https://doi.org/10.5281/zenodo.23601975.

## The theorem, in plain words

Let P be a finite poset with d elements. Its order polytope O(P) and its chain polytope C(P) are two d-dimensional
polytopes. Hibi and Li conjectured in 2016 that (a) for every i, C(P) has at least as many i-dimensional faces as
O(P), and (b) if the two numbers of i-dimensional faces are equal for some i, then O(P) and C(P) are unimodularly
equivalent. Fourier proved (a).

Let X be the five-element poset with two incomparable elements below a third element, which lies below two further
incomparable elements. Hibi and Li showed that O(P) and C(P) are unimodularly equivalent exactly when P does not
contain X. The paper proves: if P contains X, then for every k with 2 ≤ k ≤ d − 1, C(P) has at least the binomial
coefficient C(d−3, k−2) more k-dimensional faces than O(P); and for every d ≥ 5 some d-element poset attains all
these bounds. So (b) holds for every i with 2 ≤ i ≤ d − 1. For edges (i = 1) it fails: the poset X itself has equally many edges in
both polytopes, yet they are not unimodularly equivalent.

In Lean (names ending in `HL` follow Hibi and Li's own published conventions; the full statement is in
[HibiLi/Paper/Statements.lean](HibiLi/Paper/Statements.lean)):

```lean
theorem HibiLi.Paper.conj_1_1_resolved :
    -- (a) for every poset P with d > 1 elements and every 1 ≤ i ≤ d − 1: f_i(O(P)) ≤ f_i(C(P))
    (∀ (P : Type u) [Fintype P] [PartialOrder P], 1 < Fintype.card P → ∀ i, 1 ≤ i → i ≤ Fintype.card P - 1 →
      fNum (orderPolytopeHL P) i ≤ fNum (chainPolytopeHL P) i) ∧
    -- (b) for every 2 ≤ i ≤ d − 1: f_i(O(P)) = f_i(C(P)) implies that O(P) and C(P) are unimodularly equivalent
    (∀ (P : Type u) [Fintype P] [PartialOrder P] [DecidableEq P], 1 < Fintype.card P → ∀ i, 2 ≤ i →
      i ≤ Fintype.card P - 1 → fNum (orderPolytopeHL P) i = fNum (chainPolytopeHL P) i →
      UnimodEquivHL (orderPolytopeHL P) (chainPolytopeHL P)) ∧
    -- (b) fails for i = 1: X has f_1(O(X)) = f_1(C(X)), but O(X) and C(X) are not unimodularly equivalent
    (fNum (orderPolytopeHL XElem) 1 = fNum (chainPolytopeHL XElem) 1 ∧
      ¬ UnimodEquivHL (orderPolytopeHL XElem) (chainPolytopeHL XElem))
```

## What the proof assumes

Mathlib, Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and results that the paper cites
from other papers, stated as axioms in [HibiLi/Cited/](HibiLi/Cited/), each in its source's own words and conventions.
The headline theorem uses exactly these five (row 69 of [AUDIT.md](AUDIT.md), which `scripts/check.sh` regenerates
from Lean's `#print axioms`):

| Cited result | Source | Refereed? |
|---|---|---|
| `fourier_lemma_4_1`: the switch face-polynomial identity | Fourier, Lemma 4.1, arXiv:2609.23629v1 (2026) | **No: a preprint** |
| `fourier_prop_5_2`: relative transversality | Fourier, Proposition 5.2, arXiv:2609.23629v1 (2026) | **No: a preprint** |
| `hibiLi_thm_2_1`: the unimodular-equivalence criterion | Hibi–Li, Theorem 2.1, Math. Scand. 118 (2016) | Yes |
| `ziegler_face_figure`: face figures | Ziegler, Lectures on Polytopes, Chapter 2 | Yes |
| `cjk_dual_connected`: connectivity of subdivision dual graphs | Casabella–Joswig–Kastner, Lemma 2 of the published paper (the Lean file quotes the same statement from arXiv v1, where it is Lemma 3) | Yes |

One more cited result, `hlss_thm_2_1` (Hibi–Li–Sahara–Shikama 2017, Theorem 2.1: O(P) and C(P) always have equally
many edges), is used only for a side remark, not by the headline theorem. Lean assumes these cited results; it does
not prove them again.

## Where each claim of the paper is

[HibiLi/Paper/Statements.lean](HibiLi/Paper/Statements.lean) has one Lean theorem per claim, named by the paper's
numbering: 69 claims, covering every numbered result and the small claims in the text, including the count "for
n = 6, seven of the sixteen posets containing X attain the bound" (`sec5_census_n6`: Lean classifies all 6-element
posets containing X and counts the faces of all 32 polytopes). [AUDIT.md](AUDIT.md) lists every claim with its status:
51 PROVED (from Lean's standard axioms alone), 18 PROVED-FROM-CITED (from the standard axioms and the cited results
named in that row), none open. The comment at the top of Statements.lean
lists the few sentences deliberately not formalized (remarks that only report other papers' results, and informal
proof sketches).

## What a referee must read

Lean checks every proof. A referee only needs to check that the STATEMENTS say what the paper says: the definitions in
[HibiLi/Defs/](HibiLi/Defs/), the cited results in [HibiLi/Cited/](HibiLi/Cited/), and the statements in
[HibiLi/Paper/Statements.lean](HibiLi/Paper/Statements.lean).

The Lean statements were checked against version 0.70 of the paper, and the line numbers in the comments
("lines 736–737") refer to its LaTeX source. Later versions changed wording, not statements; the line numbers will be
realigned to the published version.

## How to check it yourself

Prerequisites: the `elan` Lean toolchain manager, Git, curl, Python 3 and ripgrep (`rg`). From a fresh copy:

```bash
export LEAN_NUM_THREADS=1
lake exe cache get      # downloads prebuilt Mathlib files (it does not compile Mathlib)
lake build              # the largest file needs about 8 GB of memory
bash scripts/check.sh   # build, scan for proof holes (sorry, admit, native_decide, ...), regenerate AUDIT.md
git diff --exit-code AUDIT.md   # the regenerated AUDIT.md is identical to the published one
```

GitHub runs these same steps on a fresh machine at every change (the "Lean build" mark at the top; the steps are in
[.github/workflows/lean_build.yml](.github/workflows/lean_build.yml)).

The n = 6 count, independently in Python (exact arithmetic; needs pycddlib 2.1.8): `python3 scripts/census/census_n6.py 6`.
`scripts/census/gen_fvectors.py` wrote the face-vector data in [HibiLi/Census/](HibiLi/Census/); Lean re-checks every
one of those facts itself, so the Python only proposes.

Optional, after a build: `scripts/kernel_replay.sh --test`, then `scripts/kernel_replay.sh`, re-check every declaration
with Lean's kernel and with independent proof checkers (they need the checker binaries listed at the top of the
script). Checkers that refuse any project with cited assumptions report SKIPPED, by design.

Versions: Lean 4.35.0 (pinned in `lean-toolchain`); Mathlib v4.35.0, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`
(all dependencies pinned in `lake-manifest.json`).

## Acknowledgment

This work was done overwhelmingly by AI models and supervised by the author. The models were Anthropic's Claude and
OpenAI's ChatGPT. The author takes full responsibility for the paper.
