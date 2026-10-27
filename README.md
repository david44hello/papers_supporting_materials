# The Hibi–Li (2016) conjecture is fully resolved — the Lean 4 proof

Author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licence: Apache-2.0 (see [LICENSE](LICENSE)), the same as Mathlib.

This repository is a formal proof, checked by the Lean 4 proof assistant, of every result of the 9-page paper
"The Hibi–Li (2016) conjecture is fully resolved" by Dave Goel (version 1.00; the arXiv link will be added here
when it is posted). An expanded version of the paper, with many other results, is on Zenodo:
https://doi.org/10.5281/zenodo.23601975.

## The theorem, in plain words

Hibi and Li conjectured in 2016 that the order polytope of a finite poset has at most as many faces of each dimension
as its chain polytope, and that equality in one dimension forces the two polytopes to be unimodularly equivalent.
Fourier proved the inequality. The paper proves the rest: if an n-element poset contains the five-element poset X,
then for every k with 2 ≤ k ≤ n − 1 its chain polytope has at least C(n−3, k−2) more k-dimensional faces than its
order polytope, and one poset attains all these bounds for every n ≥ 5. So equality in a dimension k ≥ 2 forces
unimodular equivalence; for edges (k = 1) it does not, as the poset X shows.

In Lean, in Hibi and Li's own published conventions (the full statement is in
[HibiLi/Paper/Statements.lean](HibiLi/Paper/Statements.lean)):

```lean
theorem HibiLi.Paper.conj_1_1_resolved :
    -- (a) f_i(O(P)) ≤ f_i(C(P)) for every finite poset P and every 1 ≤ i ≤ d − 1
    (∀ (P : Type u) [Fintype P] [PartialOrder P], 1 < Fintype.card P → ∀ i, 1 ≤ i → i ≤ Fintype.card P - 1 →
      fNum (orderPolytopeHL P) i ≤ fNum (chainPolytopeHL P) i) ∧
    -- (b) equality in one dimension 2 ≤ i ≤ d − 1 forces unimodular equivalence
    (∀ (P : Type u) [Fintype P] [PartialOrder P] [DecidableEq P], 1 < Fintype.card P → ∀ i, 2 ≤ i →
      i ≤ Fintype.card P - 1 → fNum (orderPolytopeHL P) i = fNum (chainPolytopeHL P) i →
      UnimodEquivHL (orderPolytopeHL P) (chainPolytopeHL P)) ∧
    -- (b) is false for i = 1: the poset X
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
| `cjk_dual_connected`: connectivity of subdivision dual graphs | Casabella–Joswig–Kastner, Lemma 2 (the Lean file quotes arXiv v1, Lemma 3) | Yes |

One more cited result, `hlss_thm_2_1` (Hibi–Li–Sahara–Shikama 2017, Theorem 2.1: the numbers of edges agree), is used
only for a side remark, not by the headline theorem. These cited results are assumptions, not proofs checked here.

## Where each claim of the paper is

[HibiLi/Paper/Statements.lean](HibiLi/Paper/Statements.lean) has one Lean theorem per claim, named by the paper's
numbering: 69 claims, covering every numbered result and the small claims in the text, including the count "for
n = 6, seven of the sixteen posets containing X attain the bound" (`sec5_census_n6`: Lean classifies all 6-element
posets containing X and counts the faces of all 32 polytopes). [AUDIT.md](AUDIT.md) lists every claim with its status:
51 PROVED from the standard axioms alone, 18 PROVED-FROM-CITED, none open. The comment at the top of Statements.lean
lists the few sentences deliberately not formalized (remarks that only report other papers' results, and informal
proof sketches).

## What a referee must read

Lean checks every proof. A referee only needs to check that the STATEMENTS say what the paper says: the definitions in
[HibiLi/Defs/](HibiLi/Defs/), the cited results in [HibiLi/Cited/](HibiLi/Cited/), and the statements in
[HibiLi/Paper/Statements.lean](HibiLi/Paper/Statements.lean).

Line numbers in the comments ("lines 736–737") refer to the LaTeX source of paper version 0.70. Version 1.00 changed
wording only, no statement; the line numbers will be realigned to version 1.00 in a later commit.

## How to check it yourself

Prerequisites: the `elan` Lean toolchain manager, Git, curl, Python 3 and ripgrep (`rg`). From a fresh copy:

```bash
export LEAN_NUM_THREADS=1
lake exe cache get      # prebuilt Mathlib; it does not compile Mathlib
lake build              # the largest file needs about 8 GB of memory
bash scripts/check.sh   # build, scan for proof holes (sorry, admit, native_decide, ...), regenerate AUDIT.md
git diff --exit-code AUDIT.md   # the regenerated AUDIT.md is identical to the published one
```

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
