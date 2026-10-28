## Notes (hand-written; appended by scripts/audit.py)

In sections A-F, "tex l." means a line of the LaTeX source of the expanded version [3] (v0.30) unless the short
paper is named; section G uses the lines of the LaTeX source of the short paper (version 1.59, the final text).

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

### F. An earlier draft (version 1.46) of the short paper: new statements and claims covered by composition
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


### G. The SHORT paper, version 1.59 — the paper we post
Line numbers "l." in this section are lines of the LaTeX source of the short paper, version 1.59 (the final text). Every
Lean statement's place in it is in the column "Short paper v1.59" above and at the start of its docstring (map:
SHORT_MAP_v1.59.tsv in this folder, all 106 rows; the 23 rows marked "not in the short paper" are long-paper material
the short paper does not contain; they stay proved). The map was moved from version 1.51 by a line alignment of the two
sources; every row's quoted text was found on its new lines, and the rows next to changed text were checked by hand.
In-text claims with their own statements (files Sec2/ShortClaims2.lean, Sec2/ShortClaims3.lean, Sec2/ShortClaims4.lean,
IntFlow/ChainLift.lean): `intro_A_connected_differs` (l.157-158: A-connected is a different notion from A-flow-connected:
the graph with two vertices and one edge is A-flow-connected, as it has no flow, but not A-connected); `sec3_no_edge`
(l.335: a graph with no edge has exactly one flow, for every A);
`intro_example_flow_paths` (l.115-117: the six-edge graph has a nowhere-zero 3-flow with three values 1 and three values
-1, and six edge-disjoint paths join its two vertices); `intro_even_three_flow` (l.121-122: an even graph has a
nowhere-zero 3-flow, namely the value 1 on every edge directed by an Eulerian orientation; Lean: an Eulerian orientation
exists, and for EVERY Eulerian orientation the constant flow 1 is a nowhere-zero 3-flow); `intro_euler_orient_exists`
(l.144-145); `intro_degree_two_balanced` (l.152); `intro_triangle_A_connected` (l.156-157: a triangle is A-connected,
|A| ≥ 4, stated with entering minus leaving, the same property for -β), `intro_triangle_A_connected_def` (l.158-161: the
sign of the definition in the text, leaving minus entering) and `intro_triangle_A_connected_any_dir` (the same for any
reference directions of the three edges); `sec2_cycle_ends` (l.203-204: the ends of Q at a vertex v of Q are exactly
two); `sec4_small_cycle` (l.356-357); `sec7_three_flows` (l.573: for k = 3 the k-flows are the nowhere-zero 3-flows of
Section 1); `lem_8_4_fibre` (Lemma 7.4, l.620-621: a PATH of integer lifts of f; `lem_8_4` is the weaker form, any two
lifts are joined, that Proposition 7.7 uses); `sec7_chain_lift` (l.565-567 and the abstract l.49-51). `sec2_paths_le_four`
(l.122-123).
Implicit case: `rem_8_8_k3` = Proposition 7.7 with k = 3. [3]'s results quoted at l.131-136 (Theorems 2.5, 9.1, 9.2
there) are `thm_2_5_b`, `thm_9_1`, `thm_9_2`, `sec9_iff` (Lean states more of them).

Sentences of the short paper covered by putting proved Lean statements together, or by a definition (sections B and F
give the dependency walks and the long-paper rows):
| Short tex v1.59 | Sentence | Covered by |
|---|---|---|
| l.43-44 | abstract: the conjecture for integer flows with values between 1 and k-1 in absolute value, "where each change adds a non-zero integer" | the definition of 𝓕(G,k): `kFlowGraph k` (Defs/Graph.lean), steps with a non-zero integer value between `k`-flows; the theorem is `thm_1_1_b` |
| l.49-51 | abstract: "a counting argument joins any two nowhere-zero flows with values in ℤ_k, k ≥ 4, by changes that add 1, −1, 2 or −2; every such chain gives a chain of integer flows with values between 1 and k−1 in absolute value, and every integer flow of this chain reduces modulo k to a flow of the given chain" | first half `thm_2_4` (steps with values in `Tcyc k` = {1, −1, 2, −2}); second half `sec7_chain_lift`: a walk in 𝓕(G,k) (its vertices are `k`-flows, its steps have non-zero integer values) whose j-th `k`-flow is an integer lift of the φ(j)-th flow of the chain, φ monotone from 0 to the end |
| l.112-117 | the graph with two vertices and six parallel edges (with ANY orientation) is even and is neither ℤ₃- nor 3-flow-connected | `intro_example` (one orientation) + `sec2_ref_dir_indep` (section D); the hypotheses of [1, Theorem 2.1] for it are `intro_example_flow_paths` |
| l.119-120 | "Every even graph in which all degrees are at most 4 is A-flow-connected for every finite abelian group A, of any order (Theorem 2.2)" | `thm_2_2` (no bound on \|A\|) |
| l.125-126 | "The restriction of the step values to ±1 and ±2 is what the proof of part (b) of Theorem 1.1 needs" | `lem_8_5`, `lem_8_6` (steps with values 1 and 2 only) and `prop_8_7` (hypothesis: a {1, −1, 2, −2}-chain); the walk of section B: `thm_1_1_b` uses `thm_2_4` |
| l.129-132 | the two main questions of [2, Section 1]: Theorem 1.1 answers the first (connectivity); [3, Theorem 2.5] bounds the diameter | `thm_1_1_a`; `thm_2_5_b`: any two flows are joined by a chain of at most 16M³+12M²+M steps, i.e. their distance in 𝓕(G,A) is at most that number |
| l.139-140, l.240-243 | Section 3 reduces the flow-connectedness of all even graphs (of a class closed under deleting a loop and splitting off) to: in every loopless graph of the class with at least one edge, every flow is joined by steps to a flow with a balanced pair | `prop_3_4`: its class hypotheses are closure under deleting a loop (`h_loop`) and under splitting off in loopless graphs (`h_split`); its (LOCAL) hypothesis asks only for loopless graphs with at least one edge in which every degree is 0 or at least 4 (`h_local`), so it implies the version in the text; for the class of ALL even graphs also `sec3_T_nonzero` (T = A ∖ {0} satisfies (T1), (T2)), `sec3_closure` (even graphs are closed under both operations) and `sec2_trivial_group` (\|A\| = 1) |
| l.44-47 | abstract: "The core of the proof is an induction on the number of edges: ... replaced by one edge uw, and the induction hypothesis applies to the smaller graph"; "So the main task is to change every flow into a flow with such a pair" | `lem_3_2_a` (the bijection), `lem_3_2_b_joined`, and `prop_3_4` (the induction; only (LOCAL) is left as a hypothesis) |
| l.48-49 | abstract: "Replacing vertices of degree more than 4 by triangles reduces the problem to graphs with all degrees at most 4" | the route of `thm_2_3` (section B): `lem_5_1_a`, `lem_5_1_b`, `lem_5_1_c` (Lemma 5.1, the triangle) and `thm_2_2` |
| l.178 | "a loop is a cycle with one edge, and two parallel edges form a cycle with two edges" | examples with the definition of a cycle (`DirCycle`); the constructions are `loopCycle` (Concrete/Dipole.lean) and `cycleQ` (Concrete/Small.lean) |
| l.198-199; l.578-579; l.638-639 | one-clause reasons: "as it agrees with f or f′ on every edge"; "because no value of a k-flow is a multiple of k"; "(The statement does not depend on this choice ...)" | they support the proved rows `sec2_multistep_chain`; `sec8_residues`; and `lem_8_5`, which is proved for every reference direction (section A6) |
| l.576-577 | "this graph is the same as the graph 𝓕(G,k) of [CLSWX, EHLMNS]" | the definition `kFlowGraph`; `sec2_agree_outside_cycle` (for every abelian group, so also for ℤ) gives "adjacent iff they differ by a step" |
| l.142-144 | "the flows with this balanced pair correspond to the flows of the smaller graph (Lemma 3.2). ... any two flows with a balanced pair on the same two edges are joined by a chain of steps" | `lem_3_2_a` + `lem_3_2_b_joined` + the induction inside `prop_3_4` |
| l.146-147 | "For any two edges at a vertex of a loopless even graph and any a ≠ 0, the two edges form a balanced pair at that vertex in some constant flow with value a" | `lem_3_3_b` (every a ≠ 0; loopless G, as in Lemma 3.2) |
| l.147-148 | "for a suitable a, all constant flows with value a are joined to each other" | `lem_3_3_a` + `sec2_multistep_chain` + (T2), inside `prop_3_4` (route A3) |
| l.148, l.347 | "So all flows with a balanced pair are joined to each other" | its own statement `intro_balanced_joined` (hypotheses as the text uses them: 0 ∉ T, T = -T, (T2), G even and loopless, and the induction hypothesis of the proof of Proposition 3.4) |
| l.151-152 | "Statement (LOCAL) is needed only for loopless graphs in which every degree is 0 or at least 4: loops can be deleted (Lemma 3.1), and at a vertex of degree 2 the two edges form a balanced pair in every flow, by the flow condition" | `prop_3_4`: its (LOCAL) hypothesis is stated only for such graphs; loops (Lemma 3.1) and vertices of degree 2 (`intro_degree_two_balanced`, Lemma 3.2) are handled inside its proof |
| l.169 | "Theorem 2.4, which also proves part (a) for cyclic groups" | `sec6_cyclic_flow_connected` (part (a) = `thm_1_1_a` = `thm_2_3` with A = ℤ_m, m ≥ 4) |
| l.170-172 | Tutte's lifting theorem in the form of [2, Theorem 2.3]: "every nowhere-zero ℤ_k-flow is the residue modulo k of an integer flow with values between 1 and k-1 in absolute value" | `lem_8_3` (the paper's Lemma 7.3, proved in the text and in Lean) |
| l.190-191 | "this gives the same graph" (adjacency in [1, 2] = adjacency by a step) | `sec2_agree_outside_cycle`, plus t ≠ 0 because f ≠ f' |
| l.354-357 | Section 4 plan: steps make the edges that are not small a forest (Corollary 4.2); as the graph has an edge and every vertex with an edge has degree 4, the small edges contain a cycle; one more step gives a balanced pair (Lemma 4.3) | `cor_4_2` + `sec4_small_cycle` + `lem_4_3` |
| l.372, l.380; l.497, l.503 | Lemmas 4.1 and 6.1 and the last sentences of their proofs: "So ρ(f′) ≤ ρ(f) − 1" | the conclusions of `lem_4_1` and `lem_6_1` (`ρ(f′) + 1 ≤ ρ(f)`) |
| l.435-437 | "Theorem 2.2 follows from Sections 3 and 4. For Theorem 2.3, after the loops are deleted (Lemma 3.1), a vertex of degree at least 6 is replaced by a triangle; Lemma 5.1 ...; induction on Σ_v max(deg v − 4, 0) completes the proof." | the walks of section B: `thm_2_2` uses `prop_3_4` and `Sec4.prop_4_4_main`, no triangle names; `thm_2_3` uses `exists_expand`, Lemma 5.1 (a) and (c), `thm_2_2_proved`; its induction is on `G.phi` = Σ_v (deg v − 4) in ℕ (truncated at 0), the same measure (Reduction/Thm23.lean, Reduction/Expand.lean) |
| l.525 | "so these two ends are a balanced pair at v" (end of the proof of Lemma 6.2 (b)) | the conclusion of `lem_6_2_b` (`HasBalancedPairAt … v`) |
| l.554 | Remark 6.4: "Theorem 2.4 proves Theorem 2.3 again for cyclic groups, without Lemma 5.1." | `sec6_cyclic_flow_connected`; the walk of section B shows it uses `thm_2_4` and `prop_6_3`, and NOT Lemma 5.1 or `thm_2_3` |
| l.556 | Remark 6.4: "it requires the value −2a in Lemma 6.2 (b) not to be small. This holds in ℤ_m with m ≥ 4" | `sec6_neg_two_not_small` (used by `prop_6_3`) |
| l.556-558 | Remark 6.4: "but fails, for example, in ℤ₃ × ℤ₃ with S as in Section 4, where −2a = a; there a vertex of degree 6 can have six ends with the same small outward value a and no balanced pair" | `sec6_remark_Z3Z3` |
| l.565-567 | Section 7 opening: a chain of ℤ_k-flows from Theorem 2.4 becomes a walk in 𝓕(G,k): every ℤ_k-flow of the chain is replaced by a path of k-flows whose residues modulo k form that ℤ_k-flow | its own statement `sec7_chain_lift` (each run of lifts is a path; the order of the chain is kept) |
| l.191-192, l.576 | 𝓕(G,A) and 𝓕(G,k) "count as connected" when they have at most one vertex | the definitions: `FlowConnected` and `KFlowConnected` are `SimpleGraph.Preconnected`, which holds when there is at most one vertex |

The short paper's own sentences that are not mathematical claims (listed for the author's review; none is a claim we
skipped):
| # | short tex v1.59 | Sentence | Why not formalized |
|---|---|---|---|
| G1 | l.107 | table: "open for odd k ≥ 5 in general" | state of knowledge (history) |
| G2 | l.128 | "An expanded version of this paper, with many other results, is posted on Zenodo [3]." | pointer to another paper |
| G3 | l.136 | "None of these results is used here." | a statement about the proofs |
| G4 | l.587 | "We include their short proofs to keep the paper self-contained" | a statement about the text |
| G5 | l.687- | Acknowledgments | not mathematics |
| G6 | l.120-123 | "for A = ℤ₃ this also follows from [1, Theorem 2.1], since …" | a second, cited route; the claim itself is `thm_2_2`, and the two facts after "since" are `intro_even_three_flow` and `sec2_paths_le_four` |
| G7 | l.170 | "(Remark 6.4 explains why the counting argument does not extend to all groups)" | a pointer |
| G8 | l.554-555 | "The counting argument of Proposition 6.3 does not extend to all groups" | about our proof method; its mathematical content is the ℤ₃ × ℤ₃ row above |
| G9 | l.558-559 | "For this reason, the proof of Theorem 2.3 first treats graphs with all degrees at most 4 ... and then reduces larger degrees by triangles." | about the order of the paper |
| G10 | l.112-115 | [1, Theorem 2.1] stated: for a graph with a nowhere-zero 3-flow, ℤ₃-flow-connected ⇔ 3-flow-connected ⇔ all degrees even and no two vertices joined by more than four edge-disjoint paths | a cited result; its use for the six-edge graph is PROVED directly (`intro_example`, `intro_example_flow_paths`) |
| G11 | l.129-131 | the two main questions of combinatorial reconfiguration "as listed in [2, Section 1]" | history (a pointer to [2]); the mathematics is the l.129-132 row above |
| G12 | l.158-161 | the definition of A-connected, following [JLPT] | a definition; the claims that use it are `intro_triangle_A_connected_def` and `intro_triangle_A_connected_any_dir`; that it differs from A-flow-connectedness (l.157-158) is `intro_A_connected_differs` |
| G13 | l.61-62 | "that is, on whether every nowhere-zero flow can be changed into every other one by changes along cycles that keep the flow nowhere-zero" | a restatement of the definition of flow-connected |
| G14 | l.64 | "(for example the cyclic group ℤ_m of the integers modulo m)" | an example of a group; a definition |
Of the long-paper C-list: C2, C3, C5, C8, C9 also apply to the short paper (citations, history, identification with
[1], [2]'s definitions); C6 is replaced by G8; C1, C4, C7, C10 are about text the short paper drops.
(Section F uses the line numbers of an earlier draft, version 1.46; this section supersedes them for the posted paper.)
