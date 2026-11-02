# The Hibi–Li (2016) conjecture is fully resolved — notes on the Lean proof

This folder is a formal proof, checked by the Lean 4 proof assistant, of every result of the paper "The Hibi–Li (2016)
conjecture is fully resolved" by Dave Goel. Lean checked version 4.60 of the paper. The paper: https://doi.org/10.5281/zenodo.23704735
An expanded version of the paper, with many other results, is on Zenodo:
https://doi.org/10.5281/zenodo.23601975

The largest file needs about 8 GB of memory.

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

Mathlib, Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and four results of other
works that the paper cites, stated as axioms in [HibiLi/Cited/](HibiLi/Cited/), each with its source. Lean assumes
them; it does not prove them again. [AUDIT.md](AUDIT.md), which `scripts/check.sh` regenerates from Lean's
`#print axioms`, names in each row the cited results that claim uses.

| Cited result | Source | Refereed? |
|---|---|---|
| `fourier_prop_5_2`: relative transversality | Fourier, Proposition 5.2, arXiv:2609.23629v1 (2026) | **No: a preprint** |
| `hibiLi_thm_2_1`: the unimodular-equivalence criterion | Hibi–Li, Theorem 2.1, Math. Scand. 118 (2016) | Yes |
| `hlss_thm_2_1`: O(P) and C(P) have equally many edges | Hibi–Li–Sahara–Shikama, Theorem 2.1, Discrete Math. 340 (2017) | Yes |
| `ziegler_face_figure`: vertex figures and face figures | Ziegler, Lectures on Polytopes, Chapter 2 (a textbook) | Yes |

The headline theorem above uses all four except `hlss_thm_2_1`; Theorem 1.2 (c) also uses `hlss_thm_2_1`. Lean
states Ziegler's result in its own words: the wording was not compared with the book. Two cited results of the paper
are not assumptions, because Lean proves them: the lemma of Casabella, Joswig and Kastner that the paper recalls with
its proof, and Fourier's Lemma 4.1 (the first equality of the paper's Lemma 3.2), which Lean proves along the paper's
informal reading in Section 3 (lines 380–384; [HibiLi/Proofs/Fourier41.lean](HibiLi/Proofs/Fourier41.lean)).
`fourier_lemma_4_1` in HibiLi/Cited/Fourier.lean is therefore a theorem, with its source text kept for the record.

## Where each claim of the paper is

[HibiLi/Paper/Statements.lean](HibiLi/Paper/Statements.lean) has one Lean theorem per claim, named by the paper's
numbering. [AUDIT.md](AUDIT.md) lists all 177 statements with their place in the paper: 158 PROVED (from Lean's
standard axioms alone) and 19 PROVED-FROM-CITED (from the standard axioms and the cited results named in that row);
none is open. One of the 19, Proposition 3.4, is Fourier's Proposition 5.2 itself, which the paper quotes: Lean states
it as that assumption. One row, `sec5_census_n6` (a count for n = 6), is a claim of an earlier version of the paper that
versions 2.10 to 4.60 no longer make; Lean keeps it. The comment at the top of Statements.lean lists the few sentences
deliberately not formalized: sentences that report other papers' results without using them, pointers to other
documents, bibliographic sentences, an informal summary, and the recalled proof of a cited lemma that Lean proves by
its own route.

## Notes on particular sentences

- **Table 1 (lines 148–171).** Its left column restates Theorem 4.1 and Corollary 5.3 (rows `thm_4_1`,
  `thm_4_1_sharp`, `cor_5_3`) and notes that part (b) for 2 ≤ k ≤ n − 1 was "proved independently by Fourier
  [FourierV2, Theorem 8.2]"; its right column gives the best earlier results ([Fourier], [Bha], [FourierGap], [FLM],
  [HL], [Lee], [HLSS]). These citations are background, not claims of this paper, and are not counted. The right
  column's entry "false for k=1" is the row `sec1_partb_false_k1`.
- **Figure 2 (line 146; the file fig_before_after.tex).** The figure shows the equality part of the conjecture before
  and after this paper. Its caption's "for n ≤ 4 no poset contains X" is the row `fig_beforeafter_no_X`. The rest of
  the right panel and of the caption repeats results already in the table above: false for k = 1
  (`sec1_partb_false_k1`), the bounds and one poset attaining them all (`thm_4_1`, `thm_4_1_sharp`, `prop_5_2`; the
  drawn numbers are the binomial coefficients C(n−3, k−2) for n = 5, …, 9), and equality exactly when P does not
  contain X (`cor_5_3`, `thm_1_2`). These are not counted again. The left panel (known for k = 2 [FLM] and k = n − 1
  [HL], open otherwise [Lee]) and the last sentence ([FourierV2, Theorem 8.2]) are background, as in Table 1.
- **Standard facts (lines 209–214).** The paper uses without proof standard facts about polytopes [Ziegler, Chapters
  1–2]. They are not assumptions of the Lean proof: Lean proves each one it uses, except that a polytope of dimension at
  least 1 has a facet, which it derives from the cited face figures (row `sec4_facet_vertex_outside`). The list includes
  "a face of Q contained in a face G of Q is a face of G"; Lean proves it in general (`IsFace.mono` in
  [HibiLi/Polytope/Faces.lean](HibiLi/Polytope/Faces.lean)) and uses it for pyramids (line 252, row
  `sec2_pyramid_face_parts`). The sentence "by a fact listed below, F is the set of their solutions" (line 209) restates
  the standard fact of line 210.
- **The footnote on Hibi and Li's convention (line 217).** Hibi and Li write the order polytope with v_p ≥ v_q for
  p ≤ q. Lean states their cited results in their own conventions (`orderPolytopeHL`, `chainPolytopeHL`,
  `UnimodEquivHL` in [HibiLi/Cited/Others.lean](HibiLi/Cited/Others.lean)) and proves that v ↦ 1 − v maps one order
  polytope onto the other and is unimodular (row `sec2_footnote_HL_convention`), that their chain polytope, defined by
  the maximal chains, equals the paper's (`sec2_HL_chain_convention`), and that the two definitions of unimodular
  equivalence agree (`sec2_HL_unimod_convention`). Theorem 2.2 (`thm_2_2`) is derived from Hibi and Li's Theorem 2.1
  through these rows. For Example 2.1, Lean does not use Hibi and Li's Lemma 1.1: it computes the facets of O(X) and
  C(X) directly (row `ex_2_1_facet_counts`).
- **Dependence on Fourier's preprint (lines 190–192).** The paper says that Theorem 4.1, Corollary 5.3 and Theorem
  1.2(b) "depend on Fourier's preprint only through Lemma 3.2 and Proposition 3.4". In Lean they depend on it even less:
  Lean's `#print axioms` (AUDIT.md) shows that `thm_4_1`, `cor_5_3` and `thm_1_2` use, of Fourier's results, only
  Proposition 5.2 (`fourier_prop_5_2`, the paper's Proposition 3.4). The first equality of Lemma 3.2, which is
  Fourier's Lemma 4.1, is proved in Lean, and the row `lemma_3_2` is PROVED.
- **The informal reading in Section 3 (lines 380–384).** Every sentence is formalized, with no cited result: the
  faces with no segment parallel to the z-axis are the graphs described there (`sec3_informal_before_graph`,
  `sec3_informal_after_graph`), the faces of both kinds and their equal numbers (`sec3_informal_both_kinds`), the count
  of the other faces by F_B + F_R − F_S − F_T (`sec3_nonvertical_coefficient`), the equal numbers of faces with such a
  segment (`sec3_informal_vertical_count`), and the stated equivalence with the first equality of Lemma 3.2
  (`sec3_informal_equivalence`). Together they prove Fourier's Lemma 4.1, which the paper cites; so Lean does not
  assume it. The order of the proof in [HibiLi/Proofs/Fourier41.lean](HibiLi/Proofs/Fourier41.lean) excludes a circle:
  the count of the faces with no such segment (`nonvertical_coefficient_proved`, which is the row
  `sec3_nonvertical_coefficient`) comes first, from the classification rows and with no cited result; the equivalence
  (`informal_equivalence_proved`) is proved from that count; Fourier's Lemma 4.1 (`fourier_lemma_4_1_proved`) comes
  last, from the equivalence and the equal numbers of faces with such a segment. That file imports no file of
  HibiLi/Cited/, and HibiLi/Cited/Fourier.lean imports it.
- **The idea of Fourier's proof (line 395).** The paragraph before Proposition 3.4 sketches Fourier's proof of that
  proposition, which the Lean proof takes as a cited result. The sketch is not formalized, except its first case, which
  is the paper's own reasoning: if L(u) = U(u) at a relative interior point u of a face E of B, then L = U on E, both are
  affine on E, and S|_E and T|_E consist of the nonempty faces of E (row `sec3_transverse_equal_case`).
- **Other papers' results.** The abstract (lines 56–57), the introduction (lines 120–124) and Table 1 report that the
  second version of Fourier's preprint [FourierV2] proves part (b) for 2 ≤ k ≤ n − 1. The paper does not use this
  result, and Lean does not formalize it.

## What a referee must read

Lean checks every proof. A referee only needs to check that the statements say what the paper says: the definitions in
[HibiLi/Defs/](HibiLi/Defs/), the cited results in [HibiLi/Cited/](HibiLi/Cited/), and the statements in
[HibiLi/Paper/Statements.lean](HibiLi/Paper/Statements.lean).

Line numbers in Statements.lean, the files in HibiLi/Cited/ and HibiLi/Defs/, and AUDIT.md refer to the LaTeX source of
version 4.60 of the paper, unless a row names another version. Comments inside the proof files may still name the
lines of the earlier draft for which a proof was written. The figure of the slices of B is Figure 3 in version 4.60
(Figure 2 in earlier versions); Lean names such as `fig2_slices` and `Fig2B.lean` keep the old number.

Versions: Lean 4.35.0 (pinned in `lean-toolchain`); Mathlib v4.35.0, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`
(all dependencies pinned in `lake-manifest.json`).
