# AUDIT NOTES — Lean formalization of paper 004
## version 0.81 - 20261029_0905 — (g) the old README's lines, word for word (the README now says only what to install, run and see).
## version 0.71 - 20261028_1318 — paper v1.50 (no line moved): version mentions only.
## version 0.61 - 20261028_1254 — paper v1.40 (no line moved): version mentions only.
## version 0.51 - 20261028_1229 — paper v1.30 (no line moved): version mentions; + row def_6_1_rank_lt (rv l. 85).
## version 0.41 - 20261028_1204 — paper v1.20 (statements unchanged, no line moved): version mentions only.

Paper: D. Goel, "The Lee (2026) conjecture on the diameters of order and chain polytopes fails in both directions",
short version v1.50 (statements final): `P4_short_v1.50.tex` (main), `sec_chain.tex` (Section 4), `sec_reverse.tex`
(Sections 5-6). "l." = line of the main file unless `ch` (sec_chain) or `rv` (sec_reverse) is named.

Every claim of the paper is one theorem of `LeeDiam/Paper/Statements.lean` (one row per claim, numbered results and
in-text claims). Each row's body is `exact X_proved ...`; the proofs are in the other modules. `AUDIT.md` (written by
`scripts/audit.py`) lists the axioms of every row.

## (a) Cited statements (the only two axioms)

Both are in `LeeDiam/Cited/Lee26.lean`; together they are Theorem 2.1 of the paper (l. 141-144).

| Lean name | Statement | Refereed sources |
|---|---|---|
| `LeeDiam.Cited.adjacency_ideals` | two distinct ideals give an edge of O(P) iff, after possibly interchanging them, I ⊆ J and J \ I is connected | Ikebe-Tamura [IT95]; Hibi-Li [HL19]; restated in [HLSS17, Lemma 1.1(a)] |
| `LeeDiam.Cited.adjacency_antichains` | two distinct antichains give an edge of C(P) iff A △ B is connected | Chvátal [Chv75] for stable-set polytopes, with C(P) = the stable-set polytope of the comparability graph (Stanley [Sta86]); restated in [HLSS17, Lemma 1.1(b)] |

The paper also cites [Lee26, Theorem 4] for Theorem 2.1; [Lee26] is not refereed (see (c)). Both statements are true
and no stronger than the sources. The rows marked PROVED-FROM-CITED in `AUDIT.md` use them; all other rows use only
the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## (b) Not formalized (results of other papers and context sentences; no Lean proof uses them)

| Claim | tex line | Why not a row |
|---|---|---|
| [HLSS17]: O(P) and C(P) have the same number of edges | l. 45, l. 50 | result of another paper, used in no proof |
| [Lee26, Example 5]: small connected posets whose diameters differ by 1 in both directions; the graph of a product of polytopes is the Cartesian product of the graphs | l. 50, l. 67, l. 79 | result of another paper; the additivity of the diameters (l. 50) is proved directly (`sec1_additive`) |
| Lee's computer search (no difference above 1) | l. 50, l. 66, l. 78 | context |
| [Lee26, Corollary 25] as Lee states it | l. 61, l. 80 | its use at l. 61 (2 ≤ diam ≤ w(P)) IS proved: `sec1_between_two_and_width`, `prop_2_3` |
| [ABBLS21, Proposition 16]: diam C(P) ≤ w(P) | l. 160 | result of another paper; the bound itself is proved (`prop_2_3`) |
| Versions 2 and 3 of [Lee26] withdraw the conjecture | l. 59 | bibliographic |
| C(P) is the stable-set polytope of the comparability graph [Sta86] | l. 145 | part of the cited statement `adjacency_antichains` |
| [Sta86]: an ideal is determined by the antichain of its maximal elements (the reason the two polytopes have the same number of vertices) | l. 50 | result of another paper, used in no proof; the equal vertex count itself is proved (`sec1_same_vertices`) through the bijection between up-sets and the antichains of their minimal elements (`HibiLi.upperAntichainEquiv`), applied to the complements of the ideals |
| [Goel26]: diam C(B_k) = ⌊2k/3⌋ + 1; B_7 as a counterexample; the ratio of Question 7.2 is at least 3/2 | l. 116, l. 227 | results of the expanded version, not of this paper |
| Questions 7.1 and 7.2 | l. 221-223, l. 226-227 | open questions, not claims; their formal readings are `question_7_1`, `question_7_2` (`LeeDiam/Defs/Questions.lean`) |

## (c) Unrefereed sources

- [Lee26] J. Lee, arXiv:2610.07413 (preprint, version 1). The Lean files quote the wording of its Theorem 4.
- [Goel26] D. Goel, Zenodo (preprint, the expanded version of this paper).

## (d) The proof-step rule

1. Every numbered result and every in-text claim has a row.
2. Where a Lean proof follows the paper's proof, the row of the result covers the steps of that proof.
3. Where the Lean route differs, every intermediate claim of the paper that the Lean route does not establish has its
   own row, or (when it is a property of a construction that Lean does not build) it is listed below with the
   sentence quoted.
4. Displayed walks and sets that later text reuses are rows of their own (Table 2, the walks V of Lemma 4.9, the
   column walks of Lemma 4.12, ↑y_i, ↓w_i, ↓t_ij).

## (e) Route list: proofs whose Lean route differs from the paper's

| Result | Lean route | Paper steps not established by the Lean route | Rows |
|---|---|---|---|
| Proposition 2.3 (ideals) | exchanges the components of I △ J one at a time in any order | "the components of I △ J are those of I \ J and those of J \ I" (l. 160) | `prop_2_3_components` |
| Lemma 4.5 (comb walks) | counts the components of X ∪ C by their leftmost helper columns | ch l. 66: "a_u is comparable to one or two helpers, and to two iff u = t+1 with t, t+2 ∈ T"; "there are m − 1 glue elements"; "c_t, c_{t+2} lie in the same component iff a_{t+1} ∈ A"; "A ∪ C has m − γ_A components" | `lem_4_5_helpers`, `lem_4_5_glue`, `lem_4_5_same_comp`, `lem_4_5_comp_count` |
| Lemma 4.11 (junction) | takes any walk of Corollary 4.6 and the last state κ that contains a_{i+1}; rows a and c directly, without σ | ch l. 133-135: the paper's comb walk Q with K last in its first phase; "a_{i+1} is present exactly before K, and c_i is absent then" (j ≥ 2 and j = 1) | `lem_4_11_step`, `lem_4_11_step_one` |
| Lemma 4.14 (arithmetic) | `omega` | ch l. 177: the values at k = 2, 3, 4, 5 and g(k) ≥ 3k/4 ≥ (k+3)/2 ≥ ⌈k/2⌉+1 for k ≥ 6 | `lem_4_14_steps` |
| Proposition 6.6 | treats the case Θ ⊆ B directly instead of using σ | rv l. 166: σ maps mixed pairs to mixed pairs, σ(u^±) = σ(u)^±, Iso(σI, σJ) = σ(Iso(I, J)), σJ \ σI = σ(J \ I), σ preserves distances | `prop_6_6_sigma` |
| σ induces graph automorphisms (rv l. 91) | the coordinate permutation x ↦ x ∘ σ is an affine bijection of each polytope onto itself (no cited statement) | none (the claim itself is the row) | `sec6_sigma` |

Note on Lemma 4.11 (ch l. 133-135). The paper takes the comb walk of Lemma 4.5 and orders its first phase
so that the move K comes last; then "a_{i+1} is present exactly before K". The Lean proof takes any walk Q of
Corollary 4.6, lets κ be the last state of Q that contains a_{i+1}, and performs the moves of Q before κ, then the
move κ together with the move of W at which c_i first appears, then the rest of Q. The paper's own step is proved
separately: `lem_4_11_step` (j ≥ 2) builds the paper's Q (the comb walk with K last in its first phase) and proves
"a_{i+1} is present exactly before K" and, in the paper's merged order (`mergeIndexW`, `mergeIndexQ`,
Defs/MergeSchedule.lean), "c_i is absent then"; `lem_4_11_step_one` is the case j = 1. The statement of Lemma 4.11
is proved (`lem_4_11`).

Same route in substance (the paper's steps are established inside Lean helper lemmas; no extra rows):
- Lemma 4.4: proved directly (an element inserted into the states before move μ), not by merging with ({y}, ∅); the
  paper's steps (the sets X_t ∪ {y}, t < μ, are antichains; the comparable element lies in the difference of move μ)
  are established in the helper lemmas `ride_prefix`, `ride_suffix`. Part (ii) is proved directly, not by reversal.
- Uses of Lemma 4.3 in the proofs of Lemmas 4.9, 4.11, 4.12 go through a two-walk merge along a schedule (`merge2`),
  whose hypotheses are exactly the paper's conditions (i) and (ii).
- Section 7, remark after Question 7.1 (l. 223): "if diam O(P) ≤ 1 then any two ideals are nested" and "a chain's
  antichains are ∅ and the singletons" are established inside the Section 1 helpers (contrapositive:
  `S1.two_le_orderDiam`; `S1.chainDiam_chain`).
- Lemma 2.4: the projection argument reorganizes the paper's singleton / non-singleton cases without dropping any
  assertion.
- The vertex descriptions of O(P), C(P) and their finiteness (l. 50, [Sta86]) are proved from the convex-hull
  description of the two polytopes; the paper gives no proof of its own.

All other proofs follow the paper's route.

## (f) Vendored code

`LeeDiam/Vendor/HibiLi` is a copy of the polytope library of a companion formalization (faces, the two polytopes,
0/1 vertices). Changes against the copy: import paths, and lint only (unused section variables omitted, `letI` →
`let`, `simpa` → `simp`); the only change to statements is that unused instance arguments (`[Fintype P]`,
`[PartialOrder P]`) were dropped.

## (g) From the old README

For version 1.50 of “The Lee (2026) conjecture on the diameters of order and chain polytopes fails in both directions” by Dave Goel.

[AUDIT.md](AUDIT.md) lists 115 claims: 84 proved from Lean's standard foundations and 31 proved using two cited adjacency statements. There are no open claims in the audit. The two statements characterize edges of the order polytope and chain polytope; they are declared in [LeeDiam/Cited/Lee26.lean](LeeDiam/Cited/Lee26.lean).

The order-polytope statement comes from Ikebe–Tamura (1995) and Hibi–Li (2019). The chain-polytope statement comes from Chvátal (1975), using Stanley's (1986) description. These are refereed sources. Lee's 2026 preprint supplies the conjecture and another citation for the adjacency statements; neither Lean assumption rests on that unrefereed preprint. The standard axioms are `propext`, `Classical.choice` and `Quot.sound`.

[AUDIT_NOTES.md](AUDIT_NOTES.md) lists the scope, results of other papers that are not formalized, two open questions, and five proofs where Lean takes another route. The paper's intermediate steps in those five proofs are also checked as separate claims. Expanded-paper results quoted in the short paper are outside this formalization.

The toolchain pins Lean v4.35.0; lake-manifest.json pins Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The final check builds with one thread, checks source policy, regenerates the axiom audit, and compares claim/proof types. With no arguments, `scripts/check.sh` runs the same full check on the first available CPU; GitHub uses this form. Optional `scripts/kernel_replay.sh` requires the additional checker binaries listed in its header. Scratch files are local to `.lake/`.
