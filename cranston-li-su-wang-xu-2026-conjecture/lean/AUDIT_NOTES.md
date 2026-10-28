## Notes (hand-written; appended by scripts/audit.py)

In sections A-F, "tex l." means a line of the LaTeX source of the expanded version [3] (v0.30) unless the short
paper is named; section G uses the lines of the short paper's release file p002_short_v1.51.tex.

### A. Route differences (the Lean proof of a claim takes another path than the paper's text)
| # | Claim(s) | Paper's route | Lean's route |
|---|---|---|---|
| A1 | lem_3_2_b | cut the closed walk W at v into one or two directed cycles | L(χ_{Q'}) is a {-1,0,1}-valued flow of G; `circ_decomp` splits it into edge-disjoint directed cycles (same multi-step value t) |
| A2 | lem_3_1 … prop_3_4, lem_9_3 | Section 3 for flows, then "the rule of replacement" for (p,q)-flows (tex l.742-768) | Section 3 proved ONCE for I-flows (any value set I = -I); prop_3_4 is I = A∖{0}, lem_9_3 is I = I(p,q); the in-proof (p,q) facts are the claims lem_9_3_chain/loop/split/const |
| A3 | prop_3_4 (last case) | the flows a𝟙_D are joined "by Lemma 3.3 (a) and (T2)" | the same difference -2a·(reversed arcs), turned into T-steps by `reachable_of_circ` |
| A4 | lem_6_2_a, lem_6_2_b, prop_6_3 | proved directly in Section 6 for ℤ_m | proved as the case q = 1 of lem_9_5 / prop_9_6, whose proofs are the same argument with q in the place of 1 (the paper notes "for q = 1, Theorem 9.1 is Theorem 2.4") |
| A5 | lem_9_5_c | integer representative γ, shows p-3q+1 ≤ γ ≤ p-q-1 | direct check of the four cases a, c ∈ {q, -q}: a + c ∈ {2q, -2q} ⊆ J or a + c = 0 (a balanced pair) |
| A6 | lem_8_5, lem_8_6 | reference directions chosen so that Q passes its edges forward | each edge keeps its direction; χ_Q(e) = ±1; for 8.6 the rounded map is (r_f + χ_Q)/k, forcing the same edges as the paper's E₁ |
| A7 | prop_8_7 | reverse Q for the values -1, -2 | Lemma 8.5/8.6 applied from the other end of the step (the reversal itself is now stated and proved as `sec2_step_value_sign` (i), via `cycleReverse`, but 8.7's proof does not use it) |
| A8 | intro_example (3-flow part) | cites [CLSWX, Theorem 2.1] | direct Lean proof: the integer lifts of the constant ℤ₃-flow 1 are closed under steps of 𝓕(G,3) |
| A9 | CyclicDecomp.small_sum_eq (inside lem_4_3 Case 1) | "two small elements of one colour have a sum with at most one non-zero part …" | compare the two decompositions of a - b coordinate by coordinate (same facts, shorter) |
| A10 | thm_2_5_a | count multi-steps along Prop 3.4's induction (c(G) ≤ M(M+3)/2), then ≤ M steps each | the same count; inside the count a multi-step is used in the equivalent form f' = f + t·h, h a non-zero {-1,0,1}-valued integer flow (equivalence proved both ways: circStep_of_multiStep, circ_decomp) |
| A11 | thm_2_2 | the case \|A\| = 1 (tex l.407) | the same fact proved inside the proof (at most one flow), not by citing sec2_trivial_group |
| A12 | thm_2_3 | "Also G = G⁺/Δ" (tex l.455) | an explicit edge isomorphism EdgeIso (edge bijection + injective vertex map respecting both ends); flows, steps and multi-steps pass along it. G⁺ = expandAt (two ends of v to x₁, two to x₂, as in tex l.452-453); loops deleted first by Lemma 3.1, then induction on Φ |
| A13 | lem_5_1_b | the arcs of the cycles outside Δ form a directed graph H with in = out; its cycles | the same H as an integer flow of G⁺/Δ; its cycles from circ_decomp |
| A14 | rem_2_6 | K₅ contains a triangle | K₅ even and the triangle 0→1→2→0 checked by `decide` (kernel); ℤ₄-flow-connected by thm_2_3 |
| A15 | thm_2_5_b | G* has at most 4(M-μ) edges; triangles undone in reverse order by 5.1(b); loops cost μ more steps at the end (tex l.549-556) | the same count with the invariant 2M + 3Φ (the blow-up adds 3 edges and lowers Φ by 2), so no division; 5.1(b) carried along the edge isomorphism; each loop costs one extra multi-step inside the same budget (B(4M) - B(4(M-1)) ≥ 1). Final bound identical: 16M³+12M²+M |
| A16 | sec7_c_bound, sec7_multistep_bound, sec7_multistep_bound_loopless | the counts in the proof of Theorem 2.5 | the same counts (count_bound, ms_bound, ms_bound_loopless) in the h-form of A10, carried to multiStepGraph by isMultiStep_of_circStep (circ_decomp), walks mapped with the same length |
| A17 | sec2_ref_dir_indep | "the statement does not depend on this choice" (tex l.640-642) | f ↦ (e ↦ -f e on the reversed edges) maps I-flows to I-flows (I = -I) and each step f + tχ_Q to a step with the same t along the flipped cycle; reorienting twice gives G back |
| A18 | rem_9_7_one_cycle | "any two different (p,q)-flows of it differ by a non-zero constant along the cycle" (tex l.860-861) | all edges are on Q, so two flows agree off Q and sec2_agree_outside_cycle gives f' = f + tχ_Q; evenness from heads = permutation of tails |
| A19 | rem_2_6_triangular | (K₅ is triangularly connected: not argued in the paper) | edges ab, cd: a fifth vertex x; triangles [abx, adx] if a = c, else [abx, acx, cdx]; `decide` over Fin 5 |

### B. Route checks done by a dependency walk
For each claim below, the constants its Lean proof uses (directly and transitively, from Lean's environment) were
listed; the claim passes when none of the "must NOT use" names occurs and every control name in "must use" occurs.
| Claim | Must NOT use | Must use (control) | Result (20261027_1024) |
|---|---|---|---|
| sec6_cyclic_flow_connected (tex l.522: "without Lemma 5.1") | lem_5_1_a/b/c, thm_2_3, IsIsolatedTriangle, contract | thm_2_4, prop_6_3 | NOT-USED ×6, USED ×2 — PASS |
| thm_2_2 (tex l.406-413) | Triangle/Thm23 names (7), prop_6_3, thm_2_4, sorryAx | prop_3_4_proved, reduction_preconnected, Sec4.prop_4_4_main, sec4_decomp_exists_proved | PASS |
| thm_2_3 (l.448-457), thm_1_1_a | prop_6_3, thm_2_4, sorryAx | 5.1(a) exists_lift_contract, 5.1(c) flowConnected_contract, thm_2_2_proved, exists_expand, EdgeIso.flowConnected, loop_preconnected (3.1) | PASS |
| thm_2_4 (l.516-520) | Triangle/Thm23 names (7), thm_2_2_proved, sorryAx | prop_3_4, prop_6_3, reduction_preconnected | PASS |
| thm_8_1 (l.686-688), thm_1_1_b | Triangle/Thm23 names (7), sorryAx | thm_2_4, prop_6_3 | PASS |
| thm_9_1 (l.839-841) | Triangle/Thm23 names (7), sorryAx | lem_9_3_of, prop_9_6, reduction_preconnected | PASS |
| sec9_iff (l.728) | Triangle/Thm23 names (7), sorryAx | thm_9_1, thm_9_2 | PASS |
| thm_2_5_a (l.532-547) | Triangle/Thm23 names (7), sorryAx | Sec4.prop_4_4_main, splitLift, splitOff | PASS |
| thm_2_5_b (l.549-556) | prop_6_3, thm_2_4, sorryAx | Count.ms_bound ("the first part"), Count.pull_circStep (5.1b), exists_lift_contract (5.1a), exists_expand, EdgeIso.isIFlow_iff, extLoop | PASS |

The 7 Triangle/Thm23 names: flowConnected_contract, exists_lift_contract, restrict_multiStep, thm_2_3_proved,
exists_expand, expandIso, flowConnected_of_loopless. Walk control: thm_2_3 → thm_2_2_proved USED, thm_2_2 → thm_2_3_proved
NOT-USED.

### C. Sentences of the paper NOT formalized (each needs Dave's sign-off)
| # | tex lines | Sentence | Why not |
|---|---|---|---|
| C1 | 559-564 | Remark 7.1: "The proofs above are constructive …" | a statement about proofs, not a mathematical proposition |
| C2 | 77-79 | "by [CLSWX, Theorem 2.1], a graph that has a nowhere-zero 3-flow and two vertices joined by more than four edge-disjoint paths is neither …" | a cited result used only as context; its consequence for the example graph is PROVED directly (intro_example) |
| C3 | 108-111 | [CLSWX, Observation 4.6] and "a case of [CLSWX, Theorem 5.9(1)]" | cited, context only; the fact used (contracting a triangle) is PROVED (lem_5_1_*), and "a triangle is A-connected for \|A\| ≥ 4" is PROVED (intro_triangle_A_connected) |
| C4 | 200-207 | Remark 2.6 on [CLSWX] Theorem 3.3 and the "only if" half of their Corollary 5.15 (iii) | the content is now STATED and PROVED: rem_2_6_triangular (K₅ is triangularly connected in [CLSWX]'s sense, quoted verbatim, is even, and is ℤ₄-flow-connected, so the "only if" half fails for K₅); only the reading of [CLSWX]'s own sentences is not formalized |
| C5 | 192-198, 586-591, 729-732 | statements of what [CLSWX]/[EHLMNS] proved (Thm 4.2, 4.3, Cor 4.5, Thm 2.9) | history of the problem, not claims of this paper (the one checkable fact, "every even graph admits a circular (2k+1,k)-flow", is sec9_circular, PROVED) |
| C6 | 523 | "We have no count of this kind for all groups at vertices of degree 6 or more." | a statement about the authors' knowledge |
| C7 | 694 | "this case also follows from [CLSWX, Theorem 2.1]" (Remark 8.8, k = 3) | a second, cited route; the claim itself (rem_8_8_k3) is PROVED by the paper's own route |
| C8 | 60-66, 76-77 | what [EHLMNS] asked and [CLSWX] conjectured and proved | history of the problem |
| C9 | 124, 138, 577, 586-587, 709-710 | "an even graph is what [CLSWX] call an Eulerian graph"; "this is the graph 𝓕(G,A) / 𝓕(G,k) / F_mod(G;p,q) of [EHLMNS, CLSWX]" | identifications with the cited papers' definitions; our definitions follow THIS paper's text (Defs/*.lean), which two independent reviews checked against the paper |
| C10 | 857-858 | "for the pairs (2k+1,k) see [CLSWX, Theorem 2.9]" | a pointer to a cited result |

### D. Reference directions
Each Lean graph carries one fixed reference direction per edge (tex l.129). The claims about one named graph
(thm_9_2 and intro_example on `dipole`, rem_2_6 on `K5`, rem_9_7 on `cycleGraph`) are stated for the orientation
written in Defs/Constructions.lean. The claim sec2_ref_dir_indep shows that reversing any set of reference directions
changes none of the connectivity notions (any value set I = -I), so these claims hold for every orientation.

### E. Universes
All statements quantify over graphs whose vertex and edge types live in `Type` (universe 0). The paper's graphs are
finite, and every finite graph is isomorphic to one with vertex set `Fin n` and edge set `Fin m`, which are in
`Type`; graph isomorphism preserves all notions here (Reduction/Iso.lean, EdgeIso). So nothing of the paper is lost.
The claims that quantify over all graphs inside the statement (prop_3_4, lem_9_3, sec9_iff) also range over `Type`. This argument is meta-level: `EdgeIso` relates graphs only inside `Type`.

### F. The short paper's review copy v1.46: new statements and claims covered by composition
Six in-text claims of the short paper had no statement; all six are now PROVED (file Sec2/ShortClaims.lean):
`sec2_step_value_sign` (l.155-157), `sec2_outward_value_ne_zero` (l.171-172), `def_2_1_loop_ends` (l.184),
`sec4_small_dir_indep` (l.324), `sec4_color_unique` (l.323-326), `sec6_not_small_range` (l.445-446).
Claims covered only by putting several Lean statements together:
| Short tex | Claim | Covered by |
|---|---|---|
| l.123-124 (outline) | any two flows with a balanced pair on the same two edges are joined by a chain of steps | `lem_3_2_a` + `lem_3_2_b_joined` + the induction inside `prop_3_4` |
| l.125-126, l.305-306 | for a suitable a, all such constant flows are joined to each other | `lem_3_3_a` + `sec2_multistep_chain` + (T2), inside `prop_3_4` (route A3) |
| l.156-157 | "this gives the same graph" (adjacency of [CLSWX, EHLMNS] = adjacency by a step) | `sec2_agree_outside_cycle`, plus t ≠ 0 because f ≠ f' |
| l.106-108 | the dipole with six parallel edges, with ANY orientation | `intro_example` (one orientation) + `sec2_ref_dir_indep` (section D) |
C9 also covers the short paper's "the same graph" (l.156-157) through `sec2_agree_outside_cycle`.


### G. The SHORT paper, RELEASE v1.51 (p002_short_v1.51.tex, md5 bf0f0a5c) — the paper we post
Line numbers "l." in this section are lines of the release file p002_short_v1.51.tex. Every Lean statement's place in
it is in the column "Short paper v1.51" above and at the start of its docstring (map: SHORT_MAP_v1.51.tsv in this
folder, all 93 rows; 29 statements are long-paper material the short paper does not contain; they stay proved). The
map was moved from v1.48 by a line alignment of the tex files, and every row's quoted text was found at its new line.
Implicit case: `rem_8_8_k3` = Proposition 7.7 with k = 3. [3]'s results quoted at l.110-112 (Theorems 2.5, 9.1, 9.2
there) are `thm_2_5_b`, `thm_9_1`, `thm_9_2`, `sec9_iff` (Lean states more of them).

Sentences of the short paper covered only by putting several proved Lean statements together (sections B and F give
the dependency walks and the long-paper rows):
| Short tex v1.51 | Sentence | Covered by |
|---|---|---|
| l.99-101 | the graph with two vertices and six parallel edges (with ANY orientation) is even and is neither ℤ₃- nor 3-flow-connected | `intro_example` (one orientation) + `sec2_ref_dir_indep` (section D) |
| l.103-104 | "Every even graph in which all degrees are at most 4 is A-flow-connected for every finite abelian group A, of any order (Theorem 2.2)" | `thm_2_2` (no bound on \|A\|) |
| l.117-118 | "any two flows with a balanced pair on the same two edges are joined by a chain of steps" | `lem_3_2_a` + `lem_3_2_b_joined` + the induction inside `prop_3_4` |
| l.118-119 | "For any two edges at a vertex and any a ≠ 0, a balanced pair on these edges occurs in some constant flow with value a" | `lem_3_3_b` (every a ≠ 0; loopless G, as in Lemma 3.2) |
| l.120-121 | "for a suitable a, all constant flows with value a are joined to each other" | `lem_3_3_a` + `sec2_multistep_chain` + (T2), inside `prop_3_4` (route A3) |
| l.121, l.305-306 | "So all flows with a balanced pair are joined to each other" | its own statement `intro_balanced_joined` (hypotheses as the text uses them: 0 ∉ T, T = -T, (T2), G even and loopless, and the induction hypothesis of the proof of Proposition 3.4); its proof is the step `hbal` of `reduction_preconnected`, from the three rows above |
| l.124 | "Statement (LOCAL) is needed only for loopless graphs in which every degree is 0 or at least 4" | `prop_3_4`: its (LOCAL) hypothesis is stated only for such graphs; loops (Lemma 3.1) and vertices of degree 2 (Lemma 3.2) are handled inside its proof |
| l.134 | "Theorem 2.4, which also proves part (a) for cyclic groups" | `sec6_cyclic_flow_connected` (part (a) = `thm_1_1_a` = `thm_2_3` with A = ℤ_m, m ≥ 4) |
| l.154-156 | "this gives the same graph" (adjacency in [1, 2] = adjacency by a step) | `sec2_agree_outside_cycle`, plus t ≠ 0 because f ≠ f' |
| l.389-391 | "Theorem 2.2 follows from Sections 3 and 4. For Theorem 2.3, a vertex of degree at least 6 is replaced by a triangle, and Lemma 5.1 shows that the original graph is then A-flow-connected too." | the walks of section B: `thm_2_2` uses `prop_3_4` and `Sec4.prop_4_4_main`, no triangle names; `thm_2_3` uses `exists_expand`, Lemma 5.1 (a) and (c), `thm_2_2_proved` |
| l.479 | "so these two ends are a balanced pair at v" (end of the proof of Lemma 6.2 (b)) | the conclusion of `lem_6_2_b` (`HasBalancedPairAt … v`) |
| l.508 | Remark 6.4: "Theorem 2.4 proves Theorem 2.3 again for cyclic groups, without Lemma 5.1." | `sec6_cyclic_flow_connected`; the walk of section B shows it uses `thm_2_4` and `prop_6_3`, and NOT Lemma 5.1 or `thm_2_3` |
| l.510 | Remark 6.4: "it requires the value −2a in Lemma 6.2 (b) not to be small. This holds in ℤ_m with m ≥ 4" | `sec6_neg_two_not_small` (used by `prop_6_3`) |
| l.510-512 | Remark 6.4: "but fails, for example, in ℤ₃ × ℤ₃ with S as in Section 4, where −2a = a; there a vertex can have six ends with the same small outward value a and no balanced pair" | `sec6_remark_Z3Z3` (every cyclic decomposition D of ℤ₃ × ℤ₃ and every a ∈ D.S; the graph with two vertices and six parallel edges; Lean: no balanced pair anywhere in the graph) |

The short paper's own sentences that are not mathematical claims (each needs Dave's sign-off; none is a claim we skipped):
| # | short tex v1.51 | Sentence | Why not formalized |
|---|---|---|---|
| G1 | l.94 | table: "open for odd k ≥ 5 in general" | state of knowledge (history) |
| G2 | l.109 | "An expanded version of this paper, with many other results, is posted on Zenodo [3]." | pointer to another paper |
| G3 | l.112 | "None of these results is used here." | a statement about the proofs |
| G4 | l.535 | "We include their short proofs to keep the paper self-contained" | a statement about the text |
| G5 | l.635- | Acknowledgments | not mathematics |
| G6 | l.104-105 | "for A = ℤ₃ this also follows from [1, Theorem 2.1]" | a second, cited route; the claim itself is `thm_2_2` |
| G7 | l.135 | "(Remark 6.4 explains why the counting argument does not work for all groups)" | a pointer |
| G8 | l.508-510 | "The counting argument of Proposition 6.3 does not extend to all groups at vertices of degree 6 or more" | about our proof method; its mathematical content is the ℤ₃ × ℤ₃ row above |
| G9 | l.512-513 | "For this reason, Section 5 first treats graphs with all degrees at most 4 and then reduces larger degrees by triangles." | about the order of the paper |
Of the long-paper C-list: C2, C3, C5, C8, C9 also apply to the short paper (citations, history, identification with
[1], [2]'s definitions); C6 is replaced by G8; C1, C4, C7, C10 are about text the short paper drops.
(Section F uses the line numbers of the review copy v1.46; this section supersedes them for the posted paper.)
