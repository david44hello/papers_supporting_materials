## Notes (hand-written; appended by scripts/audit.py)

In sections A-E, "tex l." means a line of the LaTeX source of the expanded version [3] (v0.30) unless the short
paper is named; sections F and G use the lines of the LaTeX source of the short paper (version 2.00, the final text).

### A. Route differences (the Lean proof of a claim takes another path than the paper's text)
| # | Claim(s) | Paper's route | Lean's route |
|---|---|---|---|
| A1 | lem_3_2_b | cut the closed walk W at v into one or two directed cycles | L(χ_{Q'}) is a {-1,0,1}-valued flow of G; `circ_decomp` splits it into edge-disjoint directed cycles (same multi-step value t) |
| A2 | lem_3_1 … prop_3_4, lem_9_3 | Section 3 for flows, then "the rule of replacement" for (p,q)-flows (tex l.742-768) | Section 3 proved ONCE for I-flows (any value set I = -I); prop_3_4 is I = A∖{0}, lem_9_3 is I = I(p,q); the in-proof (p,q) facts are the claims lem_9_3_chain/loop/split/const |
| A3 | prop_3_4 (last case) | the flows a𝟙_D are joined "by Lemma 3.3 (a) and (T2)" | the same difference -2a·(reversed arcs), turned into T-steps by `reachable_of_circ` |
| A4 | lem_6_2_a, lem_6_2_b, prop_6_3 | proved directly in Section 6 for ℤ_m | proved as the case q = 1 of lem_9_5 / prop_9_6, whose proofs are the same argument with q in the place of 1 (the paper notes "for q = 1, Theorem 9.1 is Theorem 2.4"); the parenthesis in the short paper's proof of Lemma 6.2 (b) (the chain does not start with a step with value 1) is not a step of that Lean proof and has its own statement, `lem_6_2_b_first_step` |
| A5 | lem_9_5_c | integer representative γ, shows p-3q+1 ≤ γ ≤ p-q-1 | direct check of the four cases a, c ∈ {q, -q}: a + c ∈ {2q, -2q} ⊆ J or a + c = 0 (a balanced pair) |
| A6 | lem_8_5, lem_8_6 | reference directions chosen so that Q passes its edges forward | each edge keeps its direction; χ_Q(e) = ±1; for 8.6 the rounded map is (r_f + χ_Q)/k, forcing the same edges as the paper's E₁ |
| A7 | prop_8_7 | reverse Q for the values -1, -2 | Lemma 8.5/8.6 applied from the other end of the step (the reversal itself is now stated and proved as `sec2_step_value_sign` (i), via `cycleReverse`, but 8.7's proof does not use it) |
| A8 | intro_example (3-flow part) | cites [CLSWX, Theorem 2.1] | direct Lean proof: the integer lifts of the constant ℤ₃-flow 1 are closed under steps of 𝓕(G,3) |
| A9 | CyclicDecomp.small_sum_eq (inside lem_4_3 Case 1) | "two small elements of one colour have a sum with at most one non-zero part …"; in the short paper, version 2.00, l.550-553: "If t_3 and t_4 had the same color, both would lie in one cyclic summand of A, and their sum would have at most one non-zero part", then "by the uniqueness of the parts they are the two non-zero parts of a-b" | compare the two decompositions of a - b coordinate by coordinate (same facts, shorter) |
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
| A20 | intro_even_no_bridge | "An even graph has no bridge" (the short paper, version 2.00, l.161; stated without proof) | an Eulerian orientation and the constant integer flow 1 along it; `circ_decomp` splits it into edge-disjoint directed cycles, and the edge lies on one of them; cut at the edge, the rest of that cycle is a path between the two ends of the edge in the graph without the edge |
| A21 | fig_5_degrees | the caption of Figure 5 of the short paper, version 2.00: the picture of the replacement of a vertex by a triangle | stated on the graph WITH the triangle (the frame of Lemma 5.1), so that only definitions of Defs/ are used; the ends are counted edge by edge (`endCount`); that such a graph exists for every vertex of degree at least 6 is a step of the proof of `thm_2_3` (A12) |

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

### C. Sentences of the paper NOT formalized (listed for the author's review)
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

### F. From version 1.59 to version 2.00 of the short paper: what changed in the Lean statements
The 106 statements of the version 1.59 tag keep their Lean types word for word; only their docstrings and line pointers
follow the new text. Version 2.00 adds eight statements, for claims that are new in its captions and its text (files
Sec2/ShortClaims5.lean and Sec2/ShortClaims6.lean; "l." = a line of the version 2.00 source, as in section G):
| Lean name | Place in version 2.00 | Claim |
|---|---|---|
| `fig_1_step` | caption of Figure 1, l.111-114 | a step with value t along a directed cycle adds t on the edges passed in their reference direction, subtracts t on the edges passed against it, keeps the other values, and keeps the flow condition (stated for every directed cycle; the figure draws one with four edges) |
| `intro_even_no_bridge` | l.161 (again l.167-168) | "An even graph has no bridge": every edge lies on a directed cycle, and the two ends of an edge that is not a loop are still joined by a path after the edge is deleted |
| `intro_card_le_two` | l.228-229 | for \|A\| ≤ 2 "a graph then has at most one nowhere-zero A-flow", so every graph is then A-flow-connected |
| `sec2_same_graph` | l.324-325 (again l.750-753) | the adjacency rules of [1] and of [2] "both give the same graph 𝓕(G,A)": each rule holds for two flows exactly when they form a step; stated for every set of allowed values, so also for 𝓕(G,k) |
| `fig_5_degrees` | caption of Figure 5, l.608-610 (again l.655-657) | "The new degrees are 4, 4 and d-2", in the frame of Lemma 5.1: G⁺ with the triangle, d the degree of the vertex x of G⁺/Δ; the hypotheses are the caption's own words (two of the ends go to x₁, two go to x₂) |
| `lem_6_2_b_first_step` | proof of Lemma 6.2 (b), l.698-699 | "The chain does not start with a step with value 1": one of the two edges of Q at v has the value -1 in the direction of Q, and f + χ_Q is 0 on that edge |
| `rem_6_4_small_cycle` | Remark 6.4, l.732-734 | in ℤ₃ × ℤ₃ "a vertex of a cycle of small edges can lie on more than two small edges": 6a = 0, 2a ≠ 0, and the flow with the outward value a on six parallel edges has no balanced pair, six small edges at one vertex, and that vertex on a cycle |
| `intro_const_joined` | outline, l.245-246 | "all constant flows with value a are joined to each other, for every a ≠ 0 when steps of all values are allowed and for a = 1 when only steps with values ±1 and ±2 are allowed" |

The statement `lem_6_2_b_first_step` keeps the two printed hypotheses of Lemma 6.2 (G has no loop; f is a nowhere-zero
flow), although this step does not need them.

One statement is RETIRED: `sec7_three_flows` (version 1.59, Section 7, Definitions: for k = 3 the k-flows are the
nowhere-zero 3-flows of Section 1). Version 2.00 defines the k-flows once, in Section 1 (l.83-84), and no longer prints
that sentence. The statement stays in the file, proved; it is not counted as a claim of the short paper.

Four statements have no sentence in the short paper any more and are now counted with the results of the expanded
version [3]: `thm_2_5_b`, `thm_9_1`, `thm_9_2`, `sec9_iff`. Version 1.59 quoted Theorems 2.5, 9.1 and 9.2 of [3] in its
Section 1; version 2.00 only says what [3] contains (l.302-304). The four stay proved.

Four statements now belong to Remark 5.2 (l.648-649): `intro_triangle_A_connected`, `intro_triangle_A_connected_def`,
`intro_triangle_A_connected_any_dir`, `intro_A_connected_differs`. Version 2.00 says "A-connected in the sense of [6]"
and does not print the definition. The Lean statements keep the definition that version 1.59 printed: a graph H is
A-connected if, for a fixed reference direction of every edge and every map β from V(H) to A with Σ_v β(v) = 0, there
is a map f from E(H) to A ∖ {0} such that at every vertex v the sum of f on the leaving edges minus the sum on the
entering edges is β(v). This is the definition of [1], Section 5.2 (a subgraph H "that admits a β-flow for every
A-boundary β of H (in which case H is called A-connected)", with the same sum), and [1, Theorem 5.9(1)] is the theorem
that Remark 5.2 names.

Counts: 114 statements = 81 of the short paper + 32 of the expanded version only + 1 retired
(version 1.59: 106 = 78 + 28).


### G. The short paper, version 2.00 (the final text)
Line numbers "l." in this section are lines of the LaTeX source of the short paper, version 2.00 (the final text). Every
Lean statement's place in it is in the column "Short paper v2.00" above and at the start of its docstring (map:
SHORT_MAP_v2.00.tsv in this folder, all 114 rows; the 32 rows marked "not in the short paper" are results of the
expanded version [3] that the short paper does not contain, and they stay proved; 1 row is retired, section F). The map
was moved from version 1.59 by a line alignment of the two sources; every row's quoted text was found on its new lines,
and the rows next to changed text were checked by hand. Reference numbers are those of version 2.00: [1] Cranston, Li,
Su, Wang, Xu; [2] Esperet, Hendrey, Lagoutte, Marseloo, Norin, Steiner; [3] the expanded version; [4], [5] two other
papers of the author; [6] Jaeger, Linial, Payan, Tarsi; [7] Tutte.

In-text claims with their own statements, besides the eight of section F (files Sec2/ShortClaims.lean,
Sec2/ShortClaims2.lean, Sec2/ShortClaims3.lean, Sec2/ShortClaims4.lean, IntFlow/ChainLift.lean):
`sec2_step_value_sign` (l.323), `sec2_outward_value_ne_zero` (l.339), `def_2_1_loop_ends` (l.353),
`sec4_small_dir_indep` (l.503-504), `sec4_color_unique` (l.501-505), `sec6_not_small_range` (l.666-667);
`intro_A_connected_differs` (l.649: A-connected is a different notion from A-flow-connected: the graph with two vertices
and one edge is A-flow-connected, as it has no flow, but not A-connected); `sec3_no_edge` (l.471: a graph with no edge
has exactly one flow, for every A); `intro_example_flow_paths` (l.206-208 and the caption of Figure 3, l.220-221: the
six-edge graph has a 3-flow with three values 1 and three values -1, and six edge-disjoint paths join its two
vertices); `intro_even_three_flow` (l.230: an even graph has a 3-flow, namely the value 1 along an Eulerian orientation;
Lean: an Eulerian orientation exists, and for EVERY Eulerian orientation the constant flow 1 is a 3-flow);
`intro_euler_orient_exists` (l.243-244); `intro_degree_two_balanced` (l.281); `intro_triangle_A_connected` (l.648-649:
a triangle is A-connected, |A| ≥ 4, stated with entering minus leaving, the same property for -β),
`intro_triangle_A_connected_def` (the sign of the definition written out in section F, leaving minus entering) and
`intro_triangle_A_connected_any_dir` (the same for any reference directions of the three edges); `sec2_cycle_ends`
(l.337-338: the ends of Q at a vertex v of Q are exactly two); `sec4_small_cycle` (l.492-493); `lem_8_4_fibre`
(Lemma 7.4, l.796-797: a PATH of integer lifts of f; `lem_8_4` is the weaker form, any two lifts are joined, that
Proposition 7.7 uses); `sec7_chain_lift` (l.739-741 and the abstract, l.62-63); `sec2_paths_le_four` (l.231).
Implicit case: `rem_8_8_k3` = Proposition 7.7 with k = 3.

Sentences of the short paper covered by putting proved Lean statements together, or by a definition (section B gives
the dependency walks):
| Short tex v2.00 | Sentence | Covered by |
|---|---|---|
| l.56-57 | abstract: the conjecture for integer flows whose values are between 1 and k-1 in absolute value, "where each change adds a non-zero integer" | the definition of 𝓕(G,k): `kFlowGraph k` (Defs/Graph.lean), steps with a non-zero integer value between `k`-flows; the theorem is `thm_1_1_b` |
| l.57-59 | abstract: "The proof is by induction on the number of edges. If a flow enters a vertex along one edge and leaves it along another edge with the same value, the two edges can be replaced by a single edge; this gives a smaller graph. The main step is to change every flow into a flow with such a pair of edges." | `lem_3_2_a` (the bijection), `lem_3_2_b_joined`, and `prop_3_4` (the induction; only (LOCAL) is left as a hypothesis) |
| l.60-61 | abstract: "For A-flows we do this when all degrees are at most 4; repeatedly replacing a vertex of degree at least 6 by a triangle, following Cranston et al., reduces the general case to this one." | `prop_4_4` and `intro_degree_two_balanced`, which give `thm_2_2`; the route of `thm_2_3` (section B): `lem_5_1_a`, `lem_5_1_b`, `lem_5_1_c` (Lemma 5.1, the triangle) and `thm_2_2`. "following Cranston et al." is credit, not a claim |
| l.62-63 | abstract: "any two nowhere-zero flows with values in the cyclic group ℤ_k, k ≥ 4, are joined by changes that add only 1, -1, 2 or -2, and that such changes lift to integer flows" | first half `thm_2_4` (steps with values in `Tcyc k` = {1, -1, 2, -2}); second half `lem_8_5`, `lem_8_6` (one step) and `sec7_chain_lift` (the whole chain): a walk in 𝓕(G,k) whose j-th `k`-flow is an integer lift of the φ(j)-th flow of the chain, φ monotone from 0 to the end |
| l.196-199 | caption of Figure 2: "For 3 the answer is no"; every yes of the right panel "follows from Theorem 1.1" | `intro_example` (both rows of the figure, the value 3); `thm_1_1_a`, `thm_1_1_b` (every yes of the right panel). What was known before, and the open cells, are history (not counted) |
| l.206-209, l.220-221 | the even graph with two vertices and six parallel edges (with ANY orientation) is neither ℤ₃-flow-connected nor 3-flow-connected | `intro_example` (the orientation of Figure 3: all edges directed from x to y, which is the definition `dipole`) + `sec2_ref_dir_indep` (section D); the hypotheses of [1, Theorem 2.1] for it are `intro_example_flow_paths` |
| l.225-226 | "any two nowhere-zero ℤ_m-flows of an even graph are joined by a chain of steps whose values are in {1,-1,2,-2} (Theorem 2.4)" | `thm_2_4` |
| l.227-228 | "Part (a) rests on Theorem 2.2: every even graph in which all degrees are at most 4 is A-flow-connected for every finite abelian group A." | `thm_2_2` (no bound on \|A\|); the walk of section B: `thm_2_3` (= `thm_1_1_a`) uses `thm_2_2_proved` |
| l.236-239 | "The two edges can then be replaced by a single edge uw (Figure 4), and the flows with this balanced pair correspond to the flows of the smaller graph (Lemma 3.2). By the induction hypothesis the smaller graph is flow-connected, so any two flows with a balanced pair on the same two edges are joined by a chain of steps." | `lem_3_2_a` + `lem_3_2_b_joined` + the induction inside `prop_3_4` |
| l.244-245 | "Any two edges at a vertex of a loopless even graph form a balanced pair in some constant flow with value a" | `lem_3_3_b` (every a ≠ 0; loopless G, as in Lemma 3.2) |
| l.247, l.483 | "So all flows with a balanced pair are joined to each other" | its own statement `intro_balanced_joined` (hypotheses as the text uses them: 0 ∉ T, T = -T, (T2), G even and loopless, and the induction hypothesis of the proof of Proposition 3.4) |
| l.274-276 | caption of Figure 4: a balanced pair at v; "The two edges are replaced by one edge g=uw with the value x; the other edges at v (gray) are unchanged. The flows with this balanced pair correspond to the flows of the smaller graph (Lemma 3.2)." | the definitions `HasBalancedPairAt`, `splitOff`, `splitLift` and `InB` (Defs/); the last sentence is `lem_3_2_a` |
| l.280-281 | "Statement (LOCAL) is needed only for loopless graphs in which every degree is 0 or at least 4: loops can be deleted (Lemma 3.1), and at a vertex of degree 2 the two edges form a balanced pair in every flow, by the flow condition." | `prop_3_4`: its (LOCAL) hypothesis is stated only for such graphs, with at least one edge, as printed at l.465-466; loops (Lemma 3.1) and vertices of degree 2 (`intro_degree_two_balanced`, Lemma 3.2) are handled inside its proof |
| l.282-284 | "Section 4 proves it when every degree is 0 or 4; this gives Theorem 2.2 (all degrees at most 4). In Section 5 a vertex of larger degree is replaced by a triangle, with two of the edges at the vertex going to each of two vertices of the triangle and the others to the third (Figure 5)." | `prop_4_4`, `thm_2_2`; the triangle is `fig_5_degrees` and the route of `thm_2_3` (section A12) |
| l.286-287 | "it holds for \|A\| ≥ 4: if the graph with the triangle is A-flow-connected, then so is the original graph" | `lem_5_1_c` |
| l.291-296 | "the lemmas that turn a step between two nowhere-zero ℤ_k-flows into a step between two k-flows with these residues modulo k (Lemmas 7.5 and 7.6) apply only to steps with values ±1 and ±2. For the cyclic groups ℤ_m with m ≥ 4, Section 6 therefore proves (LOCAL) using only steps with values ±1 and ±2, by a counting argument that needs no bound on the degrees. This gives Theorem 2.4, which also proves part (a) for cyclic groups" | `lem_8_5`, `lem_8_6` (steps with the values 1 and 2) and `prop_8_7` (hypothesis: a {1, -1, 2, -2}-chain); `prop_6_3` (every degree 0 or at least 4, no upper bound); `thm_2_4`; `sec6_cyclic_flow_connected` (part (a) = `thm_1_1_a` = `thm_2_3` with A = ℤ_m, m ≥ 4); the walk of section B: `thm_1_1_b` uses `thm_2_4` |
| l.297-299 | Tutte's lifting theorem [7] in the form of [2, Theorem 2.3]: "every nowhere-zero ℤ_k-flow is the residue modulo k of a k-flow" | `lem_8_3` (the paper's Lemma 7.3, proved in the text and in Lean) |
| l.310 | "a loop is a cycle with one edge, and two parallel edges form a cycle with two edges" | examples with the definition of a cycle (`DirCycle`); the constructions are `loopCycle` (Concrete/Dipole.lean) and `cycleQ` (Concrete/Small.lean) |
| l.325-326, l.751-752 | 𝓕(G,A) and 𝓕(G,k) count "as connected" when they have at most one vertex | the definitions: `FlowConnected` and `KFlowConnected` are `SimpleGraph.Preconnected`, which holds when there is at most one vertex |
| l.333; l.754-755; l.814-816 | one-clause reasons: "as it agrees with f or f′ on every edge"; "because no value of a k-flow is a multiple of k"; "(The statement does not depend on this choice: ...)" | they support the proved rows `sec2_multistep_chain`; `sec8_residues`; and `lem_8_5`, which is proved for every reference direction (section A6) |
| l.449-450 | proof of Lemma 3.3 (a): "because D_1 and D_2 are both Eulerian orientations" | a step inside the proof of `lem_3_3_a` (the reversed arcs carry an integer flow; `circ_decomp` splits it into directed cycles) |
| l.491-493 | Section 4 plan: "First, steps along cycles change a flow into one in which the edges that are not small form a forest (Corollary 4.2); then, as the graph has an edge and every vertex with an edge has degree 4, the small edges contain a cycle, and one more step along that cycle gives a balanced pair (Lemma 4.3)." | `cor_4_2` + `sec4_small_cycle` + `lem_4_3` |
| l.510, l.518; l.671, l.677 | Lemmas 4.1 and 6.1 and the last sentences of their proofs: "So ρ(f′) ≤ ρ(f) − 1" | the conclusions of `lem_4_1` and `lem_6_1` (`ρ(f′) + 1 ≤ ρ(f)`) |
| l.582-584 | "For the proof of Theorem 2.3, a vertex of degree at least 6 is replaced by a triangle (Figure 5); Lemma 5.1 shows that if the new graph is A-flow-connected, then so is the original graph." | the walk of section B: `thm_2_3` uses `exists_expand`, Lemma 5.1 (a) and (c), `thm_2_2_proved`; its induction is on `G.phi` = Σ_v (deg v − 4) in ℕ (truncated at 0), the measure Φ of l.654 (Reduction/Thm23.lean, Reduction/Expand.lean); the second half is `lem_5_1_c` |
| l.630-631 | proof of Lemma 5.1 (a): "(the value z on x_1x_2 is free, and the flow conditions at x_2 and x_1 then fix the other two values)" | a step inside the proof of `lem_5_1_a`, which takes the same three values z, z - β₂, z + β₁ |
| l.700 | "so these two ends are a balanced pair at v" (end of the proof of Lemma 6.2 (b)) | the conclusion of `lem_6_2_b` (`HasBalancedPairAt … v`) |
| l.729 | Remark 6.4: "Theorem 2.4 proves Theorem 2.3 again for cyclic groups, without Lemma 5.1." | `sec6_cyclic_flow_connected`; the walk of section B shows it uses `thm_2_4` and `prop_6_3`, and NOT Lemma 5.1 or `thm_2_3` |
| l.730-731 | Remark 6.4: "the value -2a in Lemma 6.2 (b) is not small. This holds in ℤ_m with m ≥ 4" | `sec6_neg_two_not_small` (used by `prop_6_3`) |
| l.731-734 | Remark 6.4: "but fails, for example, in ℤ₃ × ℤ₃ with S as in Section 4, where -2a = a"; "a vertex of degree 6 can have six ends with the same small outward value a: the flow condition holds, as 6a = 0; there is no balanced pair, as 2a ≠ 0; and all six edges are small" | `sec6_remark_Z3Z3` and `rem_6_4_small_cycle` |
| l.752-753 | 𝓕(G,k) "is the same as the graph 𝓕(G,k) of [1, 2]" | `sec2_same_graph` with A = ℤ and the values `Ik k` (the definition `kFlowGraph`) |
| l.831-833 | proof of Lemma 7.6: "(The term χ_Q is there for the edges of E_1: it forces z(e)=1 below, so that the lift has the value -1 on these edges and the step leads to the value 1, not to k+1.)" | a step inside the proof of `lem_8_6`, which rounds the same map (r_f + χ_Q)/k (section A6) |
| l.855-856 | proof of Proposition 7.7: "(both are integer lifts of f_0)", "(of f_i)", "(of f_s)" | steps inside the proof of `prop_8_7` (`lem_8_4` joins two lifts of one flow) |

The short paper's own sentences that are not mathematical claims (listed for the author's review; none is a claim that
was skipped):
| # | short tex v2.00 | Sentence | Why not formalized |
|---|---|---|---|
| G1 | l.43-45, l.63-64 | the footnote and the abstract's last sentence: "All theorems of this paper are also proved in the Lean 4 proof assistant." | remarks on this folder |
| G2 | l.302 | "An expanded version of this paper, with further results, is posted on Zenodo [3]." | pointer to another paper |
| G3 | l.302-304 | "It bounds the diameter of 𝓕(G,A) by a polynomial in the number of edges when G is even and \|A\| ≥ 4, and it treats graphs with few vertices of odd degree. None of its results is used here." | what another paper contains, and a statement about the proofs (a bound of that kind is proved here: `thm_2_5_b`) |
| G4 | l.288, l.437, l.763 | "we include its short proof"; "We include their short proofs to keep the paper self-contained" | statements about the text |
| G5 | l.866-868 | Acknowledgments | not mathematics |
| G6 | l.228-231 | "For \|A\| ≤ 3 this is not new"; "for A = ℤ₃ it follows from [1, Theorem 2.1], because …" | a second, cited route; the claim itself is `thm_2_2`, the case \|A\| ≤ 2 is `intro_card_le_two`, and the two facts after "because" are `intro_even_three_flow` and `sec2_paths_le_four` |
| G7 | l.297 | "(Remark 6.4 shows where the counting argument fails for other groups)" | a pointer |
| G8 | l.729-730, l.733 | "The counting argument of Proposition 6.3 uses that …"; "the bound of at most n small edges in that argument no longer follows" | about the proof method; its mathematical content is in the two ℤ₃ × ℤ₃ statements above |
| G9 | l.203-205 | [1, Theorem 2.1] stated: for a graph with a 3-flow, ℤ₃-flow-connected ⇔ 3-flow-connected ⇔ all degrees even and no two vertices joined by more than four edge-disjoint paths | a cited result; its use for the six-edge graph is PROVED directly (`intro_example`, `intro_example_flow_paths`) |
| G10 | l.73-74 | "that is, on whether every nowhere-zero flow can be turned into any other one by changes along cycles that keep the flow nowhere-zero" | a restatement of the definition of flow-connected |
| G11 | l.76 | "(for example the cyclic group ℤ_m of the integers modulo m)" | an example of a group; a definition |
| G12 | l.84 | "(they are usually called nowhere-zero k-flows)" | a remark on names |
| G13 | l.118-121, l.131 | what [2] introduced and asked; what [1] call Eulerian; "Theorem 1.1 is [1, Conjecture 4.1]" | history of the problem; identification with another paper's statement |
| G14 | l.139-156 (the table, left column) | "Best result before this paper": the results of [1], [4] and [5] | other papers' results reported as context |
| G15 | l.147, l.155, l.166-172 | the table's two lines on even loopless planar graphs and the paragraph they point to | an account of what earlier papers give for even planar graphs ([2, Section 5 and Corollary 5.8]; [1, Theorems 4.2 and 4.3]); it is not used in this paper; its conclusion is a case of Theorem 1.1, which is proved; Lean does not check the account itself, because Lean's library has no plane graphs and no duals. The paper's own claim in it, "has no bridge", is `intro_even_no_bridge` |
| G16 | l.161-164 | "so the results in the table for graphs without a bridge, from [4] and [5], apply to even graphs. Such results go back to [2, Theorems 6.15 and 6.23] …"; "Neither [4] nor [5] is used here." | other papers' results reported as context, and a statement about the proofs. The first clause, "An even graph has no bridge", is `intro_even_no_bridge` |
| G17 | l.196-199 | caption of Figure 2: "what was known before this paper"; the open cells | state of knowledge (history) |
| G18 | l.209 | "(for ℤ₃, this is also noted in [2, Section 5])" | a pointer |
| G19 | l.226-227 | "for even m, ℤ_m-flow-connectedness, with steps of any value, was known [1, Theorem 4.3]" | history |
| G20 | l.250-254 | what comes from [1]: constant flows along Eulerian orientations, splitting off two edges at a vertex, [1, Lemma 2.3]; "Lemma 3.2 extends this step from Eulerian orientations to all flows with a balanced pair" | credit and context; the flow form of [1, Lemma 2.3] is `lem_3_3_a`, PROVED |
| G21 | l.284-288, l.648 | "This is the reduction of [1, Observation 4.6] …"; "a special case of [1, Theorem 5.9(1)]"; "Lemma 5.1 is the special case of [1, Theorem 5.9(1)] for a triangle" | cited, context only; the fact used (contracting a triangle) is PROVED (`lem_5_1_a`, `lem_5_1_b`, `lem_5_1_c`), and that a triangle is A-connected for \|A\| ≥ 4 is PROVED too (`intro_triangle_A_connected`) |
| G22 | l.290-291 | "Part (b) of Theorem 1.1 does not follow from part (a) by a general principle: whether every ℤ_k-flow-connected graph is k-flow-connected is, for general k, an open problem [2, Problem 2.6]." | state of knowledge |
| G23 | l.383-384 | "Condition (T1) is used for loops in Lemma 3.1, and (T2) is used in Proposition 3.4 to join the constant flows of Lemma 3.3." | about the order of the proofs |
| G24 | l.436-437, l.609-610, l.762-763 | "Part (a) of the next lemma restates [1, Lemma 2.3] …"; "This is the replacement used in the proof of [1, Observation 4.6]."; "Lemma 7.3 is Tutte's lifting theorem in the form of [2, Theorem 2.3], and Lemma 7.4 is contained in the proof of [2, Lemma 5.5]." | credit; the lemmas themselves are PROVED here (`lem_3_3_a`, `lem_8_3`, `lem_8_4`) |
| G25 | l.741-743 | "Throughout this section, a ℤ_k-flow means a nowhere-zero ℤ_k-flow …" | a naming rule |
Of the expanded version's C-list: C2, C3, C5, C8, C9 also apply to the short paper (citations, history, identification
with the definitions of [1] and [2]); C6 is replaced by G8; C1, C4, C7, C10 are about text the short paper does not have.

## From the old README

This folder is a formal proof, checked by the Lean 4 proof assistant, of the results of the paper "The
Cranston–Li–Su–Wang–Xu (2026) conjecture is true" by Dave Goel. Lean checked version 2.00 of the paper. The paper's link
is on the front page of this folder.

## The theorem

Theorem 1.1 of the paper: every even graph (finite; loops and parallel edges allowed, as in the paper) is
A-flow-connected for every finite abelian group A with |A| ≥ 4, and k-flow-connected for every integer k ≥ 4. The
paper also notes that the number 4 cannot be replaced by 3; Lean proves this for the paper's example, the even graph
with two vertices and six parallel edges (`intro_example`). The paper defines these terms in Sections 1 and 2; the Lean
definitions are in [EulerFlow/Defs/](EulerFlow/Defs/). In Lean:

```lean
theorem thm_1_1_a (G : MGraph V E) (hev : G.IsEven) (A : Type) [AddCommGroup A] [Fintype A]
    (hA : 4 ≤ Fintype.card A) : G.FlowConnected A
theorem thm_1_1_b (G : MGraph V E) (hev : G.IsEven) (k : ℕ) (hk : 4 ≤ k) : G.KFlowConnected k
theorem intro_example :
    (dipole 6).IsEven ∧ ¬ (dipole 6).FlowConnected (ZMod 3) ∧ ¬ (dipole 6).KFlowConnected 3
```

## What is proved

Every result of the paper, numbered or stated in the text or in a caption, is proved in Lean 4: as one Lean theorem,
or, for a few sentences of the text, by several Lean theorems together (listed in [AUDIT_NOTES.md](AUDIT_NOTES.md),
section G). That makes 81 Lean statements. The folder also proves 32 results of the paper's expanded version that the
paper does not contain, and it keeps 1 retired statement (section F). All 114 are
in [EulerFlow/Paper/Statements.lean](EulerFlow/Paper/Statements.lean). Every
statement is proved from Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) alone. There is no
other axiom and no unfinished proof (`sorry`) in the project.

## What is not part of the check

The paper also quotes results of other papers as context (its references [1], [2], [4], [5], [6] and [7]). The paper's
proofs do not use them, and they are not part of this check. A few of them are proved here anyway (for example the
fact, from reference [6], that a triangle is A-connected when |A| ≥ 4). In particular, Lean does not check the paper's
account of what earlier papers give for even planar graphs (the table and the paragraph after it): Lean's library has
no plane graphs and no duals; the conclusion of that account is a case of Theorem 1.1, which is proved. Sentences that
are not mathematical claims (history, pointers to other papers, remarks about the text) are listed in
[AUDIT_NOTES.md](AUDIT_NOTES.md), section G.

## Where each claim is

[AUDIT.md](AUDIT.md) lists all 114 statements. For each it gives its place in the paper (number and line of the version
2.00 LaTeX source; the 32 results of the expanded version are marked "not in the short paper", and each docstring gives their place in the expanded version), the paper's claim, and the axioms Lean reports for its proof (`#print axioms`). Each statement's
docstring also begins with its place in the paper (the map is [SHORT_MAP_v2.00.tsv](SHORT_MAP_v2.00.tsv)). Where the
Lean proof takes another route than the text, or where one sentence of the paper is covered by several Lean statements
together, [AUDIT_NOTES.md](AUDIT_NOTES.md) says so (sections A, B and G; section F lists what changed from version 1.59).

Optional, after a build: `scripts/kernel_replay.sh` re-checks every declaration outside the elaborator: first
`leanchecker` replays each compiled module; then `leanexport` exports the declarations, and the export is checked by
independent checkers: `leanchecker`, its paranoid mode, `lean4lean`, `nanoda`, `con-leche` and `con-ron` (the tools
are listed at the top of the script). The script runs every tool through `scripts/lean_run.sh`, which needs two
settings; on a machine with no shared compile lock and no job gate:
`LEAN_RUN_LOCK=none LEAN_RUN_GATE=none scripts/kernel_replay.sh`.

Versions: Lean 4.35.0 (pinned in `lean-toolchain`); Mathlib commit `56a005855ea1` (tag `v4.35.0`; all dependencies
pinned in `lake-manifest.json`).
