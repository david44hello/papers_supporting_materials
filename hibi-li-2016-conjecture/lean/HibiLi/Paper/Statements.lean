/-
HibiLi/Paper/Statements.lean — every mathematical claim of the paper itself (v2.10), one Lean statement each,
named by the paper's own numbering.  This file is the audited surface: a referee compares it with the paper.  Each body links to a proof
elsewhere; scripts/audit.py reports, per claim, exactly which assumptions it rests on.  Statements are FROZEN after
review (DESIGN rule R4).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.PaperDefs
import HibiLi.Cited.Fourier
import HibiLi.Cited.Others
import HibiLi.Polytope.Connectivity
import HibiLi.Proofs.OrderTheory
import HibiLi.Proofs.FacePoly
import HibiLi.Proofs.Summation
import HibiLi.Proofs.SwitchFacts
import HibiLi.Proofs.LU
import HibiLi.Proofs.Prop31
import HibiLi.Polytope.Pyramid
import HibiLi.Example21.Result
import HibiLi.Proofs.Lemma44
import HibiLi.Proofs.LUPiecewise
import HibiLi.Example21.Triangles
import HibiLi.Proofs.Lemma48
import HibiLi.Proofs.Lemma45
import HibiLi.Polytope.CarrierInterior
import HibiLi.Polytope.CarrierSum
import HibiLi.Example21.ZeroOneResult
import HibiLi.Proofs.Lemma36
import HibiLi.Example21.VertexBijection
import HibiLi.Polytope.Dimension
import HibiLi.Polytope.Conventions
import HibiLi.Polytope.Unimodular
import HibiLi.Polytope.Affine
import HibiLi.Polytope.Endpoints
import HibiLi.Polytope.DeltaNonnegative
import HibiLi.Proofs.Lemma46
import HibiLi.Example21.SharpFamily
import HibiLi.Proofs.Lemma42
import HibiLi.Defs.ExtraDefs
import HibiLi.Proofs.SmallClaims
import HibiLi.Proofs.PyramidFacesIff
import HibiLi.Proofs.Chain2Example
import HibiLi.Proofs.Lemma45Full
import HibiLi.Example21.OtherSwitches
import HibiLi.Example21.CenterResult
import HibiLi.Proofs.V060Claims
import HibiLi.Polytope.RelintPartition
import HibiLi.Proofs.R3Small
import HibiLi.Proofs.QEPaper
import HibiLi.Proofs.SPaperDefFull
import HibiLi.Census.Result
import HibiLi.Polytope.AffinityCells
import HibiLi.Proofs.MaxChainFinset
import HibiLi.Proofs.AddV170
import HibiLi.Proofs.AffineFace
import HibiLi.Example21.ProperFacesAffine
import HibiLi.Example21.NamedCells
import HibiLi.Proofs.RoundJClaims
import HibiLi.Proofs.Cov200Claims
import HibiLi.Proofs.Fig2B
import HibiLi.Proofs.Cov1
import HibiLi.Proofs.Informal
import HibiLi.Proofs.VerticalCount
import HibiLi.Proofs.Steps42
import HibiLi.Proofs.Steps46
import HibiLi.Proofs.LinExtRows
import HibiLi.Proofs.StepRows
import HibiLi.Proofs.SubdivRows
import HibiLi.Proofs.PyramidRows
import HibiLi.Proofs.CoverageTail
import HibiLi.Proofs.DeltaPyramid
import HibiLi.Proofs.DeltaOrder
import HibiLi.Proofs.Delta46
import HibiLi.Proofs.DeltaCoefficient

universe u

namespace HibiLi.Paper

open HibiLi Polynomial Finset

/-! ### Paper sentences deliberately NOT formalized (paper v2.10 line numbers)

Every numbered result and every in-text claim of the paper itself has a statement below.  A step inside a proof is
covered by the row of its result when the Lean proof follows the paper's route at that step; where Lean's route
differs, or where the paper states a general fact inside an argument, the step has a row of its own.
Steps covered by the row of their result: lines 387–390 ("`F ∩ F'` is a face of `F` and of `F'`", for cells of `S`
and of `T`) and lines 392–394 ("`(S ∩ T) ∩ (S' ∩ T')` … is a face of `S ∩ T`") are steps of `sec3_subdivisions`;
Lean proves them on the paper's route (`cellsS_inter_faces`, `cellsT_inter_faces`: faces of the common face
`A_ℓ ∩ A_ℓ'`; `cellsR_inter_faces`: a face of `S` meets a face of `T` in a face of `S ∩ T`).
Steps with rows of their own, by result:
* Section 2, pyramids (lines 257–268): `sec2_pyramid_extend`, `sec2_pyramid_cut`, `sec2_pyramid_apex_cut`,
  `sec2_pyramid_face_parts`, `sec2_pyramid_face_cases`.
* Section 3, the cells of `S`, `T`, `R` (lines 367–394): `sec3_affine_in_domain`, `sec3_domain_inter_face`,
  `sec3_R_cell_faces`.
* Lemma 3.5: (i) `lemma_3_5_i_relint`, `lemma_3_5_i_not_both`; (ii) `lemma_3_5_ii_dual_graph`,
  `lemma_3_5_ii_shared_facet`, `lemma_3_5_ii_opposite_sides`, `lemma_3_5_ii_adjacent_common_vertex`,
  `lemma_3_5_ii_vertex_on_edge`; (iii) `lemma_3_5_iii_steps`, `lemma_3_5_top_cells_carrier`.
* Lemma 3.6: `lemma_3_6_cell_branch_L`, `lemma_3_6_cell_branch_U`, `lemma_3_6_nested_L`, `lemma_3_6_nested_U`.
* Lemma 4.2: `lemma_4_2_steps`.  Lemma 4.3: `sec4_upper_cover_below`.  Lemmas 4.4 and 4.5:
  `sec4_no_remaining_below_covers`, `sec4_u0_strict`, `sec4_E_subset_QE`, `lemma_4_5_strict`.  Lemma 4.6:
  `lemma_4_6_point`.  Lemma 4.7: `lemma_4_7_simplex`, `sec4_facet_vertex_outside`, `lemma_4_7_facet_counts`,
  `sec4_facet_families_disjoint`.
* Theorem 4.1 (Section 4.4): `sec4_sum_identity`, `sec4_linext_prefixes`, `sec4_linext_prefix_isLowerSet`,
  `sec4_linext_through_switch`, `sec4_linext_concat`.
* Proposition 5.1: `prop_5_1_X_LU`, `prop_5_1_other_switches`, `prop_5_1_c_switch`, `sec5_affine_face`,
  `prop_5_1_cells_with_carrier_B`, `prop_5_1_by_switches`.  Proposition 5.2: `sec5_bottom_pyramids`,
  `sec5_pyramid_step`.  Corollary 5.3: `cor_5_3_gap_coefficient`.
Not formalized are only sentences that report other papers' results without using them, pointers to other documents,
bibliographic sentences, an informal summary, and the recalled proof of a cited lemma that Lean proves by its own
route:
* Lines 138–156: the right column of the introduction's table (what other papers proved; bibliographic).  Its entry
  "false for k=1 (by [HLSS, Theorem 2.1] and [HL, Theorem 2.1])" (line 148) is formalized: `sec1_partb_false_k1`.
* Lines 98–101 and 106–107: the history of the conjecture (other papers' results): part (a) "earlier for maximal
  ranked posets [AFJ, Corollary 4.2] and for the posets built by disjoint unions and ordinal sums from posets that do
  not contain X [FHL, Theorem 1]"; "Later papers restate part (b) for k ≥ 2 [FLM, Conjecture 1.1], [Lee,
  Conjecture 28]".  (Fourier's part (a), lines 98–99, is formalized: `fourier_thm_1_1`.)
* Lines 32–33 and 187–188: the author note with the link to this Lean proof, and the pointer to the expanded version
  [G] ("None of those results is used here").
* Lines 964–965: "A characterization of the posets that attain the bound of Theorem 4.1 is given in the expanded
  version [G, Theorem 6.1]; it is not used here."
* Lines 159–185 ("Outline of the proof", with the paragraph on the results used without proof; Lean's own assumptions
  are the cited results in the Cited/ files): an informal summary.
* Lines 272–283 (how Fourier passes from `O(P)` to `C(P)`, the notation, what the paper takes from Fourier's preprint and
  what it reproves), 423–425 (the subdivisions,
  polynomials and carriers "are those of [Fourier, Section 4]; so Lemma 3.2 and Proposition 3.4 below apply to them as
  stated") and 458–460 (Fourier's Lemma 4.3 "states only after summing over all carriers; we include the proof"):
  bibliographic sentences about Fourier's preprint, not claims.  (The results they name are rows: `lemma_3_2`,
  `prop_3_4`, `prop_3_1`, `lemma_3_5_i_cover` to `lemma_3_5_iii`, `prop_3_7`.)
* Lines 494–509: the recalled argument for [CJK, Lemma 2] (a segment `[x, y]` through the `e`-cells).  Lean proves the
  lemma itself (`lemma_3_5_ii_dual_graph`) by its own route, documented in the header of
  `HibiLi/Polytope/CJKProof.lean`; the recalled steps are not rows.
The informal reading of lines 435–441 ("not used below") is formalized: `sec3_informal_before`,
`sec3_informal_after`, `sec3_informal_vertical_count` and, for the sentence "Thus `F_B + F_R − F_S − F_T`
compares the numbers of these faces before and after the switch" (lines 439–440), `sec3_nonvertical_coefficient`.
(The n = 6 count of v1.70 lines 737–738, "seven of the sixteen posets containing X attain the bound", is not in v2.10
(nor in v1.80); it stays formalized: `sec5_census_n6`.)

### Cited results that the paper uses without proof

Lean assumes exactly the five results in the Cited/ files: [Fourier, Lemma 4.1, first equality] and
[Fourier, Proposition 5.2] (`Cited/Fourier.lean`), [HL, Theorem 2.1], [HLSS, Theorem 2.1] and Ziegler's face figures
(`Cited/Others.lean`).  The other cited results that the paper uses are proved in Lean wherever Lean uses them, with
no assumption:
* Lines 207–217, the standard facts on polytopes [Ziegler, Chapters 1–2]: Lean proves each fact it uses (for example
  line 211, the relative interiors of the nonempty faces partition a polytope: `sec2_faces_relint_partition`), except
  that a polytope of dimension at least 1 has a facet (line 210), which Lean derives from the cited face figures
  (`sec4_facet_vertex_outside`).
* Lines 227–229, Stanley's vertex description [Stanley, Corollary 1.3 and Theorem 2.2]: `sec2_stanley_vertices`.
* Lines 241–242, [HL, Lemma 1.1] (the facets of `O(P)` and `C(P)`): Lean does not use the general statement; it proves
  the two counts the paper draws from it, `8` and `9` facets for `X`: `ex_2_1_facet_counts`.
* Lines 492–494, [CJK, Lemma 2]: proved, `lemma_3_5_ii_dual_graph` (see above).
-/

/-! ## Section 1 (introduction) and Section 2 (definitions and examples) -/

/-- Lines 64–67 (and line 227): `O(P)` and `C(P)` are `n`-dimensional 0/1 polytopes. -/
theorem sec1_zero_one_polytopes (P : Type*) [Fintype P] [PartialOrder P] :
    (∃ S : Finset (P → ℝ), (∀ v ∈ S, ∀ p, v p = 0 ∨ v p = 1) ∧ orderPolytope P = convexHull ℝ (S : Set (P → ℝ))) ∧
    (∃ S : Finset (P → ℝ), (∀ v ∈ S, ∀ p, v p = 0 ∨ v p = 1) ∧ chainPolytope P = convexHull ℝ (S : Set (P → ℝ))) ∧
    adim (orderPolytope P) = Fintype.card P ∧ adim (chainPolytope P) = Fintype.card P :=
  sec1_zero_one_polytopes_proved P

/-- Lines 67–68: "with equally many vertices" (proved at lines 229–231). -/
theorem sec1_same_vertices (P : Type*) [Fintype P] [PartialOrder P] :
    fNum (orderPolytope P) 0 = fNum (chainPolytope P) 0 :=
  sec1_same_vertices_proved P

open HibiLi Proofs Finset

/-- **P1** (v2.10 l. 229-231): "Sending an upper set to the set of its minimal elements is a bijection from the upper
sets onto the antichains, with inverse `A ↦ {r ∈ P : r ≥ p for some p ∈ A}`, so the two polytopes have equally many
vertices". -/
theorem sec1_upper_antichain_bij (P : Type*) [Fintype P] [PartialOrder P] :
    (∀ S : Set P, IsUpperSet S →
      IsAntichain (· ≤ ·) {p | Minimal (· ∈ S) p} ∧ {r | ∃ p ∈ {p | Minimal (· ∈ S) p}, p ≤ r} = S) ∧
    (∀ A : Set P, IsAntichain (· ≤ ·) A →
      IsUpperSet {r | ∃ p ∈ A, p ≤ r} ∧ {p | Minimal (· ∈ {r | ∃ p ∈ A, p ≤ r}) p} = A) ∧
    fNum (orderPolytope P) 0 = fNum (chainPolytope P) 0 ∧
    (faces (orderPolytope P) 0).Finite ∧ (faces (chainPolytope P) 0).Finite :=
  ⟨(sec1_upper_antichain_bij_proved P).1, (sec1_upper_antichain_bij_proved P).2.1,
    (sec1_upper_antichain_bij_proved P).2.2,
    (orderPolytope_isPolytope P).finite_faces.subset fun _ h => h.1,
    (chainPolytope_isPolytope P).finite_faces.subset fun _ h => h.1⟩

/-- Footnote, lines 231–234: Hibi–Li's order polytope is the image of ours under `v ↦ 1 − v`, a unimodular map. -/
theorem sec2_footnote_HL_convention (P : Type*) [Fintype P] [PartialOrder P] [DecidableEq P] :
    orderPolytopeHL P = (fun v => (fun _ => (1 : ℝ)) - v) '' orderPolytope P ∧
    UnimodEquiv (orderPolytope P) (orderPolytopeHL P) :=
  sec2_footnote_HL_convention_proved P

/-- Hibi–Li's chain polytope (maximal chains only) equals ours (all chains); used to read their theorems. -/
theorem sec2_HL_chain_convention (P : Type*) [Fintype P] [PartialOrder P] :
    chainPolytopeHL P = chainPolytope P :=
  sec2_HL_chain_convention_proved P

/-- Hibi–Li's unimodular equivalence (row vectors) is ours (column vectors), in both directions. -/
theorem sec2_HL_unimod_convention {ι : Type*} [Fintype ι] [DecidableEq ι] (Q Q' : Set (ι → ℝ)) :
    UnimodEquivHL Q Q' ↔ UnimodEquiv Q Q' :=
  sec2_HL_unimod_convention_proved Q Q'

/-- Lines 237–238: "Such an affine bijection maps j-faces onto j-faces, so unimodularly equivalent polytopes have the
same f-vector." -/
theorem sec2_unimod_same_fvector {ι : Type*} [Fintype ι] [DecidableEq ι] (Q Q' : Set (ι → ℝ))
    (h : UnimodEquiv Q Q') (j : ℕ) : fNum Q j = fNum Q' j :=
  h.fNum_eq j

/-- v2.10 l. 234-238 (F12): "Two `n`-dimensional polytopes `Q, Q' ⊆ ℝⁿ` with integer vertices are unimodularly
equivalent (as in [HL]) if `Q' = M(Q) + w` for an integral matrix `M` with `det M = ±1` and an integral vector `w`.
Such an affine bijection maps `j`-faces onto `j`-faces": the map `v ↦ Mv + w` is an affine bijection `f` of `ℝⁿ`, and
for every `j`, `F ↦ f(F)` maps the `j`-faces of `Q` one-to-one onto the `j`-faces of `f(Q) = M(Q) + w`. (It holds for
every set `Q`; the paper needs it for polytopes with integer vertices. The f-vector consequence is
`sec2_unimod_same_fvector`.) -/
theorem sec2_unimod_faces {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (hM : M.det = 1 ∨ M.det = -1) (w : ι → ℤ) :
    ∃ f : (ι → ℝ) ≃ᵃ[ℝ] (ι → ℝ),
      (f : (ι → ℝ) → (ι → ℝ)) = (fun v => (M.map (Int.cast : ℤ → ℝ)).mulVec v + (fun i => (w i : ℝ))) ∧
      ∀ (Q : Set (ι → ℝ)) (j : ℕ), faces (f '' Q) j = (fun F => f '' F) '' faces Q j ∧
        Set.InjOn (fun F => f '' F) (faces Q j) :=
  Proofs.AddV170.unimod_faces_proved M hM w

/-- Lines 103–104: "`O(P)` and `C(P)` always have equally many edges [HLSS, Theorem 2.1]" (cited; read through the
convention theorems above). -/
theorem sec1_edges_agree (P : Type*) [Fintype P] [PartialOrder P] :
    fNum (orderPolytope P) 1 = fNum (chainPolytope P) 1 := by
  classical
  rw [sec2_unimod_same_fvector _ _ (sec2_footnote_HL_convention P).2 1, Cited.hlss_thm_2_1 P,
    sec2_HL_chain_convention P]

/-- Lines 95–97: five distinct elements with `a, b < c < g, h`, `a, b` incomparable and `g, h` incomparable also satisfy
`a, b < g, h`, so they form an induced copy of `X` (an order embedding of `X` onto them). -/
theorem sec1_X_copy_induced {P : Type*} [PartialOrder P] {a b c g h : P} (hX : IsXCopy a b c g h) :
    ∃ f : XElem ↪o P, f XElem.a = a ∧ f XElem.b = b ∧ f XElem.c = c ∧ f XElem.g = g ∧ f XElem.h = h :=
  Proofs.sec1_X_copy_induced_proved hX

/-- v2.10 l. 95-98 (F1): "We say that `P` contains `X` if five elements of `P` satisfy these relations and
incomparabilities, that is, if `P` has an induced subposet isomorphic to `X`; the relations need not be cover
relations": `ContainsX P` (the five elements and
relations) holds iff some order embedding `X ↪o P` exists, iff some subset of `P` with the induced order is
isomorphic to `X`. -/
theorem sec1_containsX_iff (P : Type*) [PartialOrder P] :
    (ContainsX P ↔ Nonempty (XElem ↪o P)) ∧ (ContainsX P ↔ ∃ S : Set P, Nonempty (XElem ≃o S)) :=
  ⟨Proofs.AddV170.containsX_iff_embedding_proved P, Proofs.AddV170.containsX_iff_subposet_proved P⟩

/-- Lines 341–346 (the example after Proposition 3.1; a Section 2 example in v0.70, hence the name): for the
chain `a < b`, both polytopes are triangles with `F_{O(P)} = F_{C(P)} = 3 + 3t + t^2`. -/
theorem sec2_chain2_triangles :
    facePoly (orderPolytope Chain2) = 3 + 3 * X + X ^ 2 ∧
    facePoly (chainPolytope Chain2) = 3 + 3 * X + X ^ 2 :=
  sec2_chain2_triangles_proved

/-- **Example 2.1** (lines 240–250), computed: `f(O(X)) = (8,24,34,24,8,1)` and `f(C(X)) = (8,24,35,26,9,1)` (and no
faces of dimension ≥ 6).  These full f-vectors are no longer in the paper (Example 2.1 listed them up to v1.70); v2.10
states only consequences of them: the facet numbers `8` and `9` (`ex_2_1_facet_counts`) and the differences in each
dimension (`ex_2_1_v180`, `prop_5_1`). -/
theorem ex_2_1 (k : ℕ) :
    fNum (orderPolytope XElem) k = [8, 24, 34, 24, 8, 1].getD k 0 ∧
    fNum (chainPolytope XElem) k = [8, 24, 35, 26, 9, 1].getD k 0 :=
  ex_2_1_proved k

/-- **Example 2.1** in the v2.10 wording (l. 243-249; the name is historical): `O(X)` has `8` facets and `C(X)` has
`9`; "`O(X)` and `C(X)` have equally many faces of dimension `0` and `1`" (Lean adds `f_5`, the polytope itself), "and
`C(X)` has `1`, `2` and `1` more faces of dimension `2`, `3` and `4`, in agreement with the facet numbers `9` and `8`"
(the difference `t^2 + 2t^3 + t^4` of Proposition 5.1). -/
theorem ex_2_1_v180 :
    fNum (orderPolytope XElem) 4 = 8 ∧ fNum (chainPolytope XElem) 4 = 9 ∧
    fNum (orderPolytope XElem) 0 = fNum (chainPolytope XElem) 0 ∧
    fNum (orderPolytope XElem) 1 = fNum (chainPolytope XElem) 1 ∧
    fNum (orderPolytope XElem) 5 = fNum (chainPolytope XElem) 5 ∧
    fNum (chainPolytope XElem) 2 = fNum (orderPolytope XElem) 2 + 1 ∧
    fNum (chainPolytope XElem) 3 = fNum (orderPolytope XElem) 3 + 2 ∧
    fNum (chainPolytope XElem) 4 = fNum (orderPolytope XElem) 4 + 1 := by
  simp only [(ex_2_1 0).1, (ex_2_1 0).2, (ex_2_1 1).1, (ex_2_1 1).2, (ex_2_1 2).1, (ex_2_1 2).2, (ex_2_1 3).1,
    (ex_2_1 3).2, (ex_2_1 4).1, (ex_2_1 4).2, (ex_2_1 5).1, (ex_2_1 5).2]
  decide

/-- **Example 2.1**, the facet counts in the v2.10 wording (l. 241-243): "the facets of `O(P)` correspond to the minimal
elements, the maximal elements and the cover relations of `P`, and those of `C(P)` to the elements and the maximal
chains of `P` [HL, Lemma 1.1]. So `O(X)` has `2+2+4 = 8` facets and `C(X)` has `5+4 = 9`." Lean proves the five
counts for `X` (2 minimal and 2 maximal elements, 4 cover relations, 5 elements, 4 maximal chains) and the two facet
numbers (from `ex_2_1`, computed directly). The general correspondence is Hibi–Li's cited Lemma 1.1; Lean does not use
it, since it computes the facets of `O(X)` and `C(X)` directly. -/
theorem ex_2_1_facet_counts :
    {x : XElem | IsMin x}.ncard = 2 ∧ {x : XElem | IsMax x}.ncard = 2 ∧
    {p : XElem × XElem | p.1 ⋖ p.2}.ncard = 4 ∧ Fintype.card XElem = 5 ∧
    {K : Finset XElem | IsMaxChain (· ≤ ·) (K : Set XElem)}.ncard = 4 ∧
    fNum (orderPolytope XElem) 4 = 2 + 2 + 4 ∧ fNum (chainPolytope XElem) 4 = 5 + 4 := by
  have hmin : {x : XElem | IsMin x} = ↑({XElem.a, XElem.b} : Finset XElem) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, IsMin]
    revert x
    decide
  have hmax : {x : XElem | IsMax x} = ↑({XElem.g, XElem.h} : Finset XElem) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, IsMax]
    revert x
    decide
  have hcov : {p : XElem × XElem | p.1 ⋖ p.2} =
      ↑({(XElem.a, XElem.c), (XElem.b, XElem.c), (XElem.c, XElem.g), (XElem.c, XElem.h)} :
        Finset (XElem × XElem)) := by
    ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, CovBy, lt_iff_le_not_ge, Prod.mk.injEq]
    revert x y
    decide
  have hchains : {K : Finset XElem | IsMaxChain (· ≤ ·) (K : Set XElem)} =
      ↑(Finset.univ.filter fun K : Finset XElem =>
        (∀ x ∈ K, ∀ y ∈ K, x ≤ y ∨ y ≤ x) ∧ ∀ z, (∀ y ∈ K, z ≤ y ∨ y ≤ z) → z ∈ K) := by
    ext K
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Proofs.isMaxChain_finset_iff]
  rw [hmin, hmax, hcov, hchains, Set.ncard_coe_finset, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Set.ncard_coe_finset, (ex_2_1 4).1, (ex_2_1 4).2]
  decide

/-- Lines 104–106: `O(X)` and `C(X)` are not unimodularly equivalent, "as they have 8 and 9 facets, respectively". -/
theorem sec1_X_not_unimod : ¬ UnimodEquiv (orderPolytope XElem) (chainPolytope XElem) := by
  intro h
  have h4 := sec2_unimod_same_fvector _ _ h 4
  rw [(ex_2_1 4).1, (ex_2_1 4).2] at h4
  simp at h4

/-- **Theorem 2.2** (Hibi–Li; lines 252–255), in the paper's conventions: `O(P)` and `C(P)` are unimodularly equivalent
iff `P` does not contain `X`. (Derived from the cited `hibiLi_thm_2_1` and the three convention theorems above.) -/
theorem thm_2_2 (P : Type*) [Fintype P] [PartialOrder P] [DecidableEq P] :
    UnimodEquiv (orderPolytope P) (chainPolytope P) ↔ ¬ ContainsX P := by
  have hfoot := (sec2_footnote_HL_convention P).2
  rw [← Cited.hibiLi_thm_2_1 P, sec2_HL_chain_convention P, sec2_HL_unimod_convention]
  exact ⟨fun h => hfoot.symm.trans h, fun h => hfoot.trans h⟩

section
local instance : DecidableLT XElem := decidableLTOfDecidableLE

/-- v2.10 l. 148 (F9, table; also Theorem 1.2(c), l. 129-131): part (b) of the conjecture is "false for `k=1` (by
[HLSS, Theorem 2.1] and [HL, Theorem 2.1])":
for every finite poset `P` that contains `X`, `O(P)` and `C(P)` have equally many edges ([HLSS],
`sec1_edges_agree`) but are not unimodularly equivalent ([HL, Theorem 2.1], `thm_2_2`); and `X` is such a poset,
with `|X| = 5 > 1`.  The proof uses only these two cited routes, not the face counts of `ex_2_1`. -/
theorem sec1_partb_false_k1 :
    (∀ (P : Type*) [Fintype P] [PartialOrder P] [DecidableEq P], ContainsX P →
      fNum (orderPolytope P) 1 = fNum (chainPolytope P) 1 ∧ ¬ UnimodEquiv (orderPolytope P) (chainPolytope P)) ∧
    1 < Fintype.card XElem ∧ ContainsX XElem := by
  refine ⟨fun P _ _ _ hX => ⟨sec1_edges_agree P, fun h => (thm_2_2 P).1 h hX⟩, by decide, ?_⟩
  refine ⟨.a, .b, .c, .g, .h, ?_⟩
  decide

end

/-- Lines 257–262: the nonempty faces of a pyramid `pyr(Q)` (apex `v` outside `aff(Q)`) are exactly the faces of `Q`,
the apex, and the pyramids over the faces of `Q`. -/
theorem sec2_pyramid_faces {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (v : ι → ℝ)
    (hv : v ∉ affineSpan ℝ Q) (F : Set (ι → ℝ)) :
    IsFace (convexHull ℝ (insert v Q)) F ↔
      IsFace Q F ∨ F = {v} ∨ ∃ G, IsFace Q G ∧ F = convexHull ℝ (insert v G) :=
  Proofs.sec2_pyramid_faces_proved Q hQ v hv F

/-- **P2** (v2.10 l. 259-262): the nonempty faces of a pyramid `conv(Q ∪ {o})` are "the nonempty faces `G` of `Q`, the
apex, and the pyramids `conv(G ∪ {o})` over the nonempty faces `G` of `Q`; as `o ∉ aff(G)`, the pyramid
`conv(G ∪ {o})` has dimension `dim G + 1`, and these faces are pairwise distinct (no `G` contains `o`, and
`conv(G ∪ {o}) ∩ Q = G` as `o ∉ aff(Q)`)". -/
theorem sec2_pyramid_faces_full {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q)
    (o : ι → ℝ) (ho : o ∉ affineSpan ℝ Q) :
    (∀ F, IsFace (convexHull ℝ (insert o Q)) F ↔
      IsFace Q F ∨ F = {o} ∨ ∃ G, IsFace Q G ∧ F = convexHull ℝ (insert o G)) ∧
    (∀ G, IsFace Q G → adim (convexHull ℝ (insert o G)) = adim G + 1) ∧
    (∀ G, IsFace Q G → o ∉ G) ∧
    (∀ G, IsFace Q G → convexHull ℝ (insert o G) ∩ Q = G) ∧
    Set.InjOn (fun G => convexHull ℝ (insert o G)) {G | IsFace Q G} ∧
    (∀ G G', IsFace Q G → IsFace Q G' → convexHull ℝ (insert o G) ≠ G') ∧
    (∀ G, IsFace Q G → G ≠ {o}) ∧
    (∀ G, IsFace Q G → convexHull ℝ (insert o G) ≠ {o}) :=
  sec2_pyramid_faces_full_proved Q hQ o ho

open HibiLi.Proofs.Cov200 in
/-- **Section 2, Faces** (v2.10 l. 203-205): "The set of points of `Q` at which several valid inequalities are all
tight is a face (it is cut out by their sum); we say that they cut it out." Finitely many valid affine inequalities
`l i ≤ c i` (`i ∈ s`); their sum is valid, cuts out the same set, and that set is a face. The paper counts `∅` as a
face (l. 202-203); Lean's `IsFace` is the nonempty case, so the face conclusion carries "if the set is nonempty"
(the empty case is the paper's convention); the first two conclusions need no such hypothesis. -/
theorem sec2_valid_inequalities_face {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (Q : Set E) (s : Finset ι) (l : ι → StrongDual ℝ E) (c : ι → ℝ)
    (hvalid : ∀ i ∈ s, ∀ x ∈ Q, l i x ≤ c i) :
    (∀ x ∈ Q, (∑ i ∈ s, l i) x ≤ ∑ i ∈ s, c i) ∧
      {x ∈ Q | ∀ i ∈ s, l i x = c i} = {x ∈ Q | (∑ i ∈ s, l i) x = ∑ i ∈ s, c i} ∧
      ({x ∈ Q | ∀ i ∈ s, l i x = c i}.Nonempty → IsFace Q {x ∈ Q | ∀ i ∈ s, l i x = c i}) :=
  valid_tight_face_proved Q s l c hvalid

/-- The pyramid rule (line 269; "the pyramid formula of Section 2", line 960): `F_{pyr(Q)}(t) = 1 + (1 + t) F_Q(t)`
for a polytope `Q` and an apex outside its affine hull.  (The name is historical: line 269 has no equation number; the
paper's equation (1) is `E ∩ N₀ = V₄ × (Q_E ∩ V_ζ)` in Lemma 4.5, line 754.) -/
theorem eq_1_pyramid {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (v : ι → ℝ)
    (hv : v ∉ affineSpan ℝ Q) :
    facePoly (convexHull ℝ (insert v Q)) = 1 + (1 + X) * facePoly Q :=
  eq_1_pyramid_proved Q hQ v hv

/-! ### Section 2: coverage rows (review REVIEW_006_cov, 20261028) -/

/-- **Section 2** (v2.10 l. 211), a standard fact the paper uses: every point `u` of a polytope `Q` lies in the
relative interior of exactly one face of `Q`. -/
theorem sec2_faces_relint_partition {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (u : ι → ℝ)
    (hu : u ∈ Q) : ∃! F, IsFace Q F ∧ u ∈ intrinsicInterior ℝ F :=
  Proofs.Cov1.faces_relint_partition Q hQ u hu

/-- **Section 2** (v2.10 l. 227-229): Stanley's vertex description, cited by the paper and proved in Lean: the vertices
of `O(P)` are the indicator vectors of the upper sets of `P`, and those of `C(P)` the indicator vectors of its
antichains. -/
theorem sec2_stanley_vertices (P : Type*) [Fintype P] [PartialOrder P] :
    faces (orderPolytope P) 0 = (fun S : Set P => ({S.indicator 1} : Set (P → ℝ))) '' {S | IsUpperSet S} ∧
    faces (chainPolytope P) 0 =
      (fun A : Set P => ({A.indicator 1} : Set (P → ℝ))) '' {A | IsAntichain (· ≤ ·) A} :=
  ⟨Proofs.Cov1.stanley_order P, Proofs.Cov1.stanley_chain P⟩

/-- v2.10 l. 246-247 (Example 2.1): `t² + 2t³ + t⁴ = t²(1 + t)²`, the bound of Theorem 4.1 for `n = 5 = |X|`. -/
theorem ex_2_1_x_gap : (X ^ 2 + 2 * X ^ 3 + X ^ 4 : ℤ[X]) = gapPoly 5 ∧ Fintype.card XElem = 5 :=
  Proofs.sec5_x_gap

open Classical Filter Topology in
/-- v2.10 l.262-263: "an affine function f on aff(Q) extends to an affine function ... with any prescribed value at o". -/
theorem sec2_pyramid_extend {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ))
    [Nonempty (affineSpan ℝ Q)] (o : ι → ℝ) (ho : o ∉ affineSpan ℝ Q)
    (f : affineSpan ℝ Q →ᵃ[ℝ] ℝ) (c : ℝ) :
    ∃ g : (ι → ℝ) →ᵃ[ℝ] ℝ, (∀ y : affineSpan ℝ Q, g y = f y) ∧ g o = c :=
  Proofs.sec2_pyramid_extend Q o ho f c

open Classical Filter Topology in
/-- v2.10 l.263-265: "the inequality ... cuts out G from pyr(Q) if ... = 1, and conv(G union {o}) if ... = 0". Validity and the tight set are both asserted. -/
theorem sec2_pyramid_cut {ι : Type*} (Q : Set (ι → ℝ)) (V : Finset (ι → ℝ))
    (hQ : Q = convexHull ℝ ↑V) (o : ι → ℝ) (ho : o ∉ affineSpan ℝ Q)
    (G : Set (ι → ℝ)) (g : (ι → ℝ) →ᵃ[ℝ] ℝ) (hg : ∀ x ∈ Q, 0 ≤ g x)
    (hG : {x ∈ Q | g x = 0} = G) (hGface : IsFace Q G) :
    (g o = 1 → (∀ x ∈ convexHull ℝ (insert o Q), 0 ≤ g x) ∧
      {x ∈ convexHull ℝ (insert o Q) | g x = 0} = G) ∧
    (g o = 0 → (∀ x ∈ convexHull ℝ (insert o Q), 0 ≤ g x) ∧
      {x ∈ convexHull ℝ (insert o Q) | g x = 0} = convexHull ℝ (insert o G)) :=
  Proofs.sec2_pyramid_cut_valid Q V hQ o ho G g hg hG hGface

/-- v2.10 l. 262-265 (pyramids), the apex: an affine `g` equal to `1` on `Q` with `g(o) = 0` cuts out `{o}` from
`pyr(Q)`. -/
theorem sec2_pyramid_apex_cut {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (V : Finset (ι → ℝ))
    (hQ : Q = convexHull ℝ ↑V) (o : ι → ℝ) (ho : o ∉ affineSpan ℝ Q) (g : (ι → ℝ) →ᵃ[ℝ] ℝ)
    (hg1 : ∀ x ∈ Q, g x = 1) (hgo : g o = 0) :
    {x ∈ convexHull ℝ (insert o Q) | g x = 0} = {o} :=
  Proofs.sec2_pyramid_apex_cut Q V hQ o ho g hg1 hgo

/-- v2.10 l. 265-267 (pyramids): the vertices of a face `F` of `pyr(Q)` are among `o` and the vertices of `Q`, and
`F ∩ Q`, when nonempty, is a face of `Q`. -/
theorem sec2_pyramid_face_parts {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (V : Finset (ι → ℝ)) (hQ : Q = convexHull ℝ ↑V)
    (o : ι → ℝ) (ho : o ∉ affineSpan ℝ Q) (F : Set (ι → ℝ)) :
    IsFace (convexHull ℝ (insert o Q)) F →
      (∀ v, IsFace F {v} → v = o ∨ IsFace Q {v}) ∧ ((F ∩ Q).Nonempty → IsFace Q (F ∩ Q)) :=
  Proofs.sec2_pyramid_face_parts Q V hQ o ho F

/-! ## Section 3 (cited input: Fourier's chain–order polytopes) -/

open Classical Filter Topology in
/-- v2.10 l.266-268: "G=F intersect Q is a face of pyr(Q) ... whose vertices are the vertices of F other than o. So F=G if o is not in F, F={o} if G is empty, and F=conv(G union {o}) otherwise." -/
theorem sec2_pyramid_face_cases {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ))
    (V : Finset (ι → ℝ)) (hQ : Q = convexHull ℝ ↑V) (o : ι → ℝ)
    (ho : o ∉ affineSpan ℝ Q) (F : Set (ι → ℝ))
    (hF : IsFace (convexHull ℝ (insert o Q)) F) :
    ((F ∩ Q).Nonempty → IsFace (convexHull ℝ (insert o Q)) (F ∩ Q) ∧
      ∀ v, IsFace (F ∩ Q) {v} ↔ IsFace F {v} ∧ v ≠ o) ∧
    (o ∉ F → F = F ∩ Q) ∧ (F ∩ Q = ∅ → F = {o}) ∧
    (o ∈ F → (F ∩ Q).Nonempty → F = convexHull ℝ (insert o (F ∩ Q))) :=
  Proofs.sec2_pyramid_face_cases Q V hQ o ho F hF

/-- Line 299: `O_∅(P) = O(P)` and `O_P(P) = C(P)`. -/
theorem sec3_endpoints (P : Type*) [Fintype P] [PartialOrder P] :
    chainOrderPolytope P ∅ = orderPolytope P ∧ chainOrderPolytope P Set.univ = chainPolytope P :=
  ⟨chainOrderPolytope_empty P, chainOrderPolytope_univ P⟩

/-- The chain–order polytope as displayed in v2.10 (l. 285-298; the name is historical): the order inequalities are
`y_r ≤ y_{r'}` for `r < r'` in `J` (Lean's `chainOrderPolytope` uses `r ≤ r'`; for `r = r'` the inequality is trivial).
The two definitions give the same set. -/
theorem sec3_def_v190 (P : Type*) [Fintype P] [PartialOrder P] (I : Set P) :
    {x : P → ℝ | (∀ p ∈ I, 0 ≤ x p) ∧
       (∀ r ∉ I, 0 ≤ x r ∧ x r ≤ 1) ∧
       (∀ r r', r ∉ I → r' ∉ I → r < r' → x r ≤ x r') ∧
       (∀ r ∉ I, ∀ K : Finset P, (↑K ⊆ I) → IsChainSet P K → (∀ p ∈ K, p < r) → ∑ p ∈ K, x p ≤ x r) ∧
       (∀ K : Finset P, (↑K ⊆ I) → IsChainSet P K → ∑ p ∈ K, x p ≤ 1)} = chainOrderPolytope P I := by
  ext x
  simp only [chainOrderPolytope, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, fun r r' hr hr' hle => ?_, h4, h5⟩
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq]
    · exact h3 r r' hr hr' hlt
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, fun r r' hr hr' hlt => h3 r r' hr hr' hlt.le, h4, h5⟩

/-- Lines 299–303: `O_I(P)` is a polytope of dimension `|P|` (proved there in the paper, and here). -/
theorem sec3_dim (P : Type*) [Fintype P] [PartialOrder P] (I : Set P) (hI : IsLowerSet I) :
    IsPolytope (chainOrderPolytope P I) ∧ adim (chainOrderPolytope P I) = Fintype.card P :=
  sec3_dim_proved P I hI

/-- **W1** (v2.10 l. 301-303): "if `r_1, …, r_m` is a linear extension of `J`, the point with `x_p = 1/(4|P|)` (`p ∈ I`)
and `y_{r_i} = 1/2 + i/(4m)` satisfies every inequality above strictly, as every sum `Σ_{p∈K} x_p` over a chain
`K ⊆ I` is at most `|I|/(4|P|) ≤ 1/4`" (here `e i = r_{i+1}`, and `r_i < r_j` implies `i < j`). -/
theorem sec3_strict_point_v200 (P : Type*) [Fintype P] [PartialOrder P] (I : Set P) [DecidablePred (· ∈ I)] (m : ℕ)
    (e : Fin m ≃ {r : P // r ∉ I}) (hext : ∀ i j : Fin m, (e i : P) < e j → i < j) :
    let pt : P → ℝ := fun p =>
      if hp : p ∈ I then 1 / (4 * Fintype.card P) else 1 / 2 + (((e.symm ⟨p, hp⟩ : ℕ) : ℝ) + 1) / (4 * m)
    (∀ p ∈ I, 0 < pt p) ∧ (∀ r ∉ I, 0 < pt r ∧ pt r < 1) ∧
    (∀ r r', r ∉ I → r' ∉ I → r < r' → pt r < pt r') ∧
    (∀ K : Finset P, (↑K ⊆ I) → IsChainSet P K → ∑ p ∈ K, pt p ≤ 1 / 4) ∧
    (∀ K : Finset P, (↑K ⊆ I) → IsChainSet P K → ∑ p ∈ K, pt p ≤ (I.ncard : ℝ) / (4 * Fintype.card P)) ∧
    (I.ncard : ℝ) / (4 * Fintype.card P) ≤ 1 / 4 ∧
    (∀ r ∉ I, ∀ K : Finset P, (↑K ⊆ I) → IsChainSet P K → (∀ p ∈ K, p < r) → ∑ p ∈ K, pt p < pt r) ∧
    (∀ K : Finset P, (↑K ⊆ I) → IsChainSet P K → ∑ p ∈ K, pt p < 1) :=
  sec3_strict_point_v200_proved P I m e hext

/-- v2.10 l. 299: "Each `O_I(P)` lies in `[0,1]^P`". -/
theorem sec3_in_unit_cube (P : Type*) [Fintype P] [PartialOrder P] (I : Set P) :
    chainOrderPolytope P I ⊆ {x | ∀ p, 0 ≤ x p ∧ x p ≤ 1} := fun _ hx p =>
  chainOrderPolytope_coordinate_bounds P I hx p

/-- Lines 309–310: `B = O_I(P′)` is a polytope of dimension `n − 1`. -/
theorem sec3_B_dim {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    IsPolytope s.B ∧ adim s.B + 1 = Fintype.card P :=
  Proofs.sec3_B_dim_proved s

/-- Lines 306–307: "Let `q` be minimal in `J`, so that `I ∪ {q}` is again an order ideal." -/
theorem sec3_insert_isLowerSet {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    IsLowerSet (insert s.q s.I) :=
  Proofs.insert_isLowerSet s

/-- v2.10 l. 308: for a switch, "`I` is an order ideal of `P'`" (`P' = P \ {q}`). -/
theorem sec3_I_ideal_of_P' {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) : IsLowerSet s.I' :=
  Proofs.I'_isLowerSet s

/-- v2.10 l. 316-317: "Every `r > q` lies in `J \ {q}`, as `J` is an upper set." -/
theorem sec3_gt_q_mem_J {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) {r : P} (hr : s.q < r) :
    r ∉ s.I ∧ r ≠ s.q :=
  ⟨Proofs.not_mem_I_of_gt s hr, hr.ne'⟩

/-- Lines 317–321: `0 ≤ L ≤ U ≤ 1` on `B`, `L` convex, `U` concave. -/
theorem sec3_L_U {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∀ u ∈ s.B, 0 ≤ s.L u ∧ s.L u ≤ s.U u ∧ s.U u ≤ 1) ∧ ConvexOn ℝ Set.univ s.L ∧
    ConcaveOn ℝ Set.univ s.U :=
  ⟨fun _ hu => Proofs.L_U_bounds s hu, Proofs.L_convex s, Proofs.U_concave s⟩

/-- Lines 320–321: `L` and `U` are piecewise affine (a maximum, resp. minimum, of finitely many affine functions). -/
theorem sec3_L_U_piecewise {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∃ (fs : Finset ((s.P' → ℝ) →ᵃ[ℝ] ℝ)) (h : fs.Nonempty), ∀ u, s.L u = fs.sup' h (fun f => f u)) ∧
    (∃ (gs : Finset ((s.P' → ℝ) →ᵃ[ℝ] ℝ)) (h : gs.Nonempty), ∀ u, s.U u = gs.inf' h (fun g => g u)) :=
  Proofs.sec3_L_U_piecewise_proved s

/-- **Proposition 3.1** (lines 323–330; Fourier's Proposition 3.1, which the paper reproves at lines 331–340, as
does Lean): the fibre description of `O_I(P)` and
`O_{I∪{q}}(P)` over `B`, coordinates `(u, z)` with `z` the `q`-coordinate (`z = y_q` on the left, `z = x_q` on the
right; in Lean both are `x q`). -/
theorem prop_3_1 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (x : P → ℝ) :
    (x ∈ chainOrderPolytope P s.I ↔
      (fun p : s.P' => x p.1) ∈ s.B ∧ s.L (fun p => x p.1) ≤ x s.q ∧ x s.q ≤ s.U (fun p => x p.1)) ∧
    (x ∈ chainOrderPolytope P (insert s.q s.I) ↔
      (fun p : s.P' => x p.1) ∈ s.B ∧ 0 ≤ x s.q ∧ x s.q ≤ s.U (fun p => x p.1) - s.L (fun p => x p.1)) :=
  Proofs.prop_3_1_proved s x

/-- Lines 341–346, the worked example: for the chain `a < b` (`Chain2`, `a = 0`, `b = 1`), `I = {a}`, `q = b`:
`B = [0,1]`, `L = x_a`, `U = 1`, and the two fibre polytopes are `O_{{a}}(P)`, which is `O(P)` (lines 341–343: at
the switch of the minimal `p₁ = a`, `L ≡ 0`, so `O_{{p₁}}(P) = O(P)`), and `C(P)`. -/
theorem sec3_chain2_example :
    ∃ s : Switch Chain2, s.I = {0} ∧ s.q = 1 ∧ s.B = {u | ∀ p, 0 ≤ u p ∧ u p ≤ 1} ∧
      (∀ u ∈ s.B, ∀ p, s.L u = u p ∧ s.U u = 1) ∧
      chainOrderPolytope Chain2 s.I = orderPolytope Chain2 ∧
      chainOrderPolytope Chain2 (insert s.q s.I) = chainPolytope Chain2 :=
  Proofs.sec3_chain2_example_proved

/-- **W2** (v2.10 l. 431-433), the chain example `p₁ < p₂` at both switches (of `p₁`: `I = ∅`, `q = p₁`; of `p₂`:
`I = {p₁}`, `q = p₂`): "`L` and `U` are affine, so `S`, `T` and `R` all consist of the faces of `B`, and Lemma 3.2
gives the difference `0`" (the right side `F_B + F_R − F_S − F_T` of Lemma 3.2 is `0`). -/
theorem sec3_chain2_cells_faces :
    ∀ s : Switch Chain2, (s.I = ∅ ∧ s.q = 0) ∨ (s.I = {0} ∧ s.q = 1) →
      AffineOn s.L s.B ∧ AffineOn s.U s.B ∧
      s.cellsS = {C | IsFace s.B C} ∧ s.cellsT = {C | IsFace s.B C} ∧ s.cellsR = {C | IsFace s.B C} ∧
      facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT = 0 ∧
      facePoly (chainOrderPolytope Chain2 (insert s.q s.I)) - facePoly (chainOrderPolytope Chain2 s.I) = 0 :=
  fun s hs => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sec3_chain2_cells_faces_proved s hs
    exact ⟨h1, h2, h3, h4, h5, h6, (Cited.fourier_lemma_4_1 s).trans h6⟩

/-- v2.10 l. 341-343, "At the switch of `p₁` (from `I = ∅` to `I = {p₁}`) we have `L ≡ 0`, so the two polytopes of
Proposition 3.1 coincide: `O_{{p₁}}(P) = O(P)`", in general: if `I` is an order ideal and `q` is a minimal element of
`P`, then `O_{I ∪ {q}}(P) = O_I(P)`. (`q` is incomparable with every
element of `I`, so the only chain of `I ∪ {q}` through `q` is `{q}`, and the inequalities on the coordinate of `q` are
the same before and after.) The example of the paper, the chain `p₁ < p₂` with `I = ∅`, `q = p₁`, is
`sec3_chain2_example`. -/
theorem sec3_minimal_switch (P : Type*) [Fintype P] [PartialOrder P] (I : Set P) (hI : IsLowerSet I) (q : P)
    (hq : IsMin q) : chainOrderPolytope P (insert q I) = chainOrderPolytope P I := by
  by_cases hqI : q ∈ I
  · rw [Set.insert_eq_of_mem hqI]
  have hinc : ∀ p ∈ I, ¬ p < q ∧ ¬ q < p := fun p hp =>
    ⟨fun h => hq.not_lt h, fun h => hqI (hI h.le hp)⟩
  have hnot : ∀ r, r ≠ q → r ∉ I → r ∉ insert q I := fun r hrq hrI h =>
    (Set.mem_insert_iff.1 h).elim hrq hrI
  have hchain_q : ∀ K : Finset P, (↑K ⊆ insert q I) → IsChainSet P K → q ∈ K → K = {q} := by
    intro K hK hc hqK
    ext p
    rw [Finset.mem_singleton]
    constructor
    · intro hpK
      by_contra hpq
      have hpI : p ∈ I := (Set.mem_insert_iff.1 (hK (Finset.mem_coe.2 hpK))).resolve_left hpq
      rcases hc (Finset.mem_coe.2 hpK) (Finset.mem_coe.2 hqK) hpq with h | h
      · exact (hinc p hpI).1 (lt_of_le_of_ne h hpq)
      · exact (hinc p hpI).2 (lt_of_le_of_ne h (Ne.symm hpq))
    · intro hpq
      rw [hpq]
      exact hqK
  have hsub : ∀ K : Finset P, (↑K ⊆ insert q I) → q ∉ K → (↑K ⊆ I) := fun K hK hqK p hp =>
    (Set.mem_insert_iff.1 (hK hp)).resolve_left fun h => hqK (by rw [← h]; exact Finset.mem_coe.1 hp)
  have hsingle : (↑({q} : Finset P) : Set P) ⊆ insert q I := by simp
  have hsingle_chain : IsChainSet P {q} := by simp [IsChainSet]
  ext x
  simp only [chainOrderPolytope, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun p hp => h1 p (Set.mem_insert_of_mem q hp), fun r hr => ?_, fun r r' hr hr' hle => ?_,
      fun r hr K hKI hKc hlt => ?_, fun K hKI hKc => h5 K (hKI.trans (Set.subset_insert q I)) hKc⟩
    · by_cases hrq : r = q
      · rw [hrq]
        have h := h5 {q} hsingle hsingle_chain
        rw [Finset.sum_singleton] at h
        exact ⟨h1 q (Set.mem_insert q I), h⟩
      · exact h2 r (hnot r hrq hr)
    · by_cases hrq : r = q
      · rw [hrq]
        rw [hrq] at hle
        by_cases hr'q : r' = q
        · rw [hr'q]
        · have h := h4 r' (hnot r' hr'q hr') {q} hsingle hsingle_chain
            (fun p hp => by rw [Finset.mem_singleton.1 hp]; exact lt_of_le_of_ne hle (Ne.symm hr'q))
          rwa [Finset.sum_singleton] at h
      · by_cases hr'q : r' = q
        · rw [hr'q] at hle
          exact absurd (le_antisymm hle (hq hle)) hrq
        · exact h3 r r' (hnot r hrq hr) (hnot r' hr'q hr') hle
    · by_cases hrq : r = q
      · rw [hrq]
        rw [hrq] at hlt
        have h0 : ∑ p ∈ K, x p = 0 := Finset.sum_eq_zero fun p hp => absurd (hlt p hp) hq.not_lt
        rw [h0]
        exact h1 q (Set.mem_insert q I)
      · exact h4 r (hnot r hrq hr) K (hKI.trans (Set.subset_insert q I)) hKc hlt
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hout : ∀ r, r ∉ insert q I → r ∉ I := fun r hr h => hr (Set.mem_insert_of_mem q h)
    refine ⟨fun p hp => ?_, fun r hr => h2 r (hout r hr),
      fun r r' hr hr' hle => h3 r r' (hout r hr) (hout r' hr') hle, fun r hr K hKI hKc hlt => ?_,
      fun K hKI hKc => ?_⟩
    · rcases Set.mem_insert_iff.1 hp with hpq | hpI
      · rw [hpq]
        exact (h2 q hqI).1
      · exact h1 p hpI
    · by_cases hqK : q ∈ K
      · rw [hchain_q K hKI hKc hqK, Finset.sum_singleton]
        exact h3 q r hqI (hout r hr) (hlt q hqK).le
      · exact h4 r (hout r hr) K (hsub K hKI hqK) hKc hlt
    · by_cases hqK : q ∈ K
      · rw [hchain_q K hKI hKc hqK, Finset.sum_singleton]
        exact (h2 q hqI).2
      · exact h5 K (hsub K hKI hqK) hKc

/-- v2.10 l. 431-433, the chain example (`P = p₁ < p₂`, `I = {p₁}`, `q = p₂`): "In the example after Proposition 3.1,
`L` and `U` are affine, so `S`, `T` and `R` all consist of the faces of `B`, and Lemma 3.2 gives the difference `0`":
the right side `F_B + F_R − F_S − F_T` of Lemma 3.2 is `0` for this
switch. -/
theorem sec3_chain2_difference_zero :
    ∃ s : Switch Chain2, s.I = {0} ∧ s.q = 1 ∧
      facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT = 0 := by
  obtain ⟨s, hI, hq, -⟩ := sec3_chain2_example
  have hmax : ∀ p : Chain2, ¬ s.q < p := by
    rw [hq]
    decide
  have hT := s.cellsT_eq_faces_of_maximal hmax
  refine ⟨s, hI, hq, ?_⟩
  rw [s.cellsR_eq_S_of_T_faces hT, hT, cellPoly_faces]
  ring

/-- v2.10 l. 341-346 (F7), the example after Proposition 3.1: for the chain `p₁ < p₂` (`Chain2`, `p₁ = 0`, `p₂ = 1`),
`I = {p₁}`, `q = p₂`, and `z = x_{p₂}`: `O_I(P) = {0 ≤ x_{p₁} ≤ z ≤ 1}`, which is `O(P)` ("`O_{{p₁}}(P) = O(P)`", l.
342), and `C(P) = O_{I ∪ {q}}(P) = {x_{p₁} ≥ 0, 0 ≤ z ≤ 1 − x_{p₁}}`, as sets. -/
theorem sec3_chain2_triangles :
    chainOrderPolytope Chain2 {0} = {u | 0 ≤ u 0 ∧ u 0 ≤ u 1 ∧ u 1 ≤ 1} ∧
    chainOrderPolytope Chain2 {0} = orderPolytope Chain2 ∧
    chainOrderPolytope Chain2 (insert 1 {0}) = {u | 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ u 1 ≤ 1 - u 0} ∧
    chainPolytope Chain2 = {u | 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ u 1 ≤ 1 - u 0} := by
  obtain ⟨s, hI, hq, -, -, hO, hC⟩ := sec3_chain2_example
  rw [hI] at hO
  rw [hI, hq] at hC
  refine ⟨hO.trans Proofs.AddV170.chain2_orderPolytope_eq, hO,
    hC.trans Proofs.AddV170.chain2_chainPolytope_eq, Proofs.AddV170.chain2_chainPolytope_eq⟩

open Example21.CenterSwitch Example21.CenterGeometry in
/-- v2.10 l. 361-362 (F2; again at l. 921-922): "for `P = X`, `I = {a, b}` and `q = c`, the maximal cells of `S` are
`B ∩ {x_a ≥ x_b}` and `B ∩ {x_a ≤ x_b}`, and those of `T` are `B ∩ {y_g ≥ y_h}` and `B ∩ {y_g ≤ y_h}`": for the switch
of `c` on `X` (`canonical`: `q = c`, `I = {a, b}`, `g' = g`, `h' = h`; the coordinates of `B` are `x_a, x_b, y_g, y_h`),
the maximal (4-dimensional) cells of `S` are `B ∩ {x_b ≤ x_a}` and `B ∩ {x_a ≤ x_b}`, and those of `T` are
`B ∩ {y_h ≤ y_g}` and `B ∩ {y_g ≤ y_h}`. -/
theorem sec3_X_cuts :
    center.q = XElem.c ∧
    {C | C ∈ center.cellsS ∧ adim C = Fintype.card center.P'} =
      {{u | u ∈ center.B ∧ u canonical.pb ≤ u canonical.pa},
        {u | u ∈ center.B ∧ u canonical.pa ≤ u canonical.pb}} ∧
    {C | C ∈ center.cellsT ∧ adim C = Fintype.card center.P'} =
      {{u | u ∈ center.B ∧ u canonical.ph ≤ u canonical.pg},
        {u | u ∈ center.B ∧ u canonical.pg ≤ u canonical.ph}} :=
  ⟨rfl, Proofs.AddV170.center_S_top, Proofs.AddV170.center_T_top⟩

/-- Lines 349–355 (definition of a subdivision): "the relative interiors (relint) of the cells then partition `Q`"
(proved there, lines 353–355) —
every point of the polytope lies in the relative interior of exactly one cell. -/
theorem sec3_subdivision_relint_partition {ι : Type*} [Fintype ι] (base : Set (ι → ℝ))
    (cells : Finset (Set (ι → ℝ))) (hsub : IsFinitePolytopalSubdivision base cells) (u : ι → ℝ) (hu : u ∈ base) :
    ∃! C, C ∈ cells ∧ u ∈ intrinsicInterior ℝ C :=
  subdivision_relint_partition base cells hsub u hu

/-- Lines 383–385: `S`, `T` and their common refinement `R` are subdivisions of `B` ("All three are subdivisions of
`B`"; proved in the paper at lines 385–394, and here, from the cell description of lines 367–380). -/
theorem sec3_subdivisions {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    ∃ cS cT cR : Finset (Set (s.P' → ℝ)),
      (cS : Set (Set (s.P' → ℝ))) = s.cellsS ∧ (cT : Set (Set (s.P' → ℝ))) = s.cellsT ∧
      (cR : Set (Set (s.P' → ℝ))) = s.cellsR ∧
      IsFinitePolytopalSubdivision s.B cS ∧ IsFinitePolytopalSubdivision s.B cT ∧
      IsFinitePolytopalSubdivision s.B cR :=
  Proofs.sec3_subdivisions_proved s

/-- **P3** (v2.10 l. 356-358 and l. 367-369): "a cell is *maximal* if no other cell contains it" and "The maximal cells of
`S` are the full-dimensional sets among the `A_ℓ = {u ∈ B : L(u) = ℓ(u)}`, for chain sums `ℓ = ℓ_K`" (and the same for
`T`, l. 381 "Similarly for `T`"); equivalently, the maximal cells are the full-dimensional cells. -/
theorem sec3_maximal_cells_full {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (C : Set (s.P' → ℝ)) :
    ((C ∈ s.cellsS ∧ ∀ C' ∈ s.cellsS, C ⊆ C' → C' = C) ↔
      ∃ K ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' ∧ C = s.domL K) ∧
    ((C ∈ s.cellsS ∧ ∀ C' ∈ s.cellsS, C ⊆ C' → C' = C) ↔ C ∈ s.cellsS ∧ adim C = Fintype.card s.P') ∧
    ((C ∈ s.cellsT ∧ ∀ C' ∈ s.cellsT, C ⊆ C' → C' = C) ↔
      ∃ j ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' ∧ C = s.domU j) ∧
    ((C ∈ s.cellsT ∧ ∀ C' ∈ s.cellsT, C ⊆ C' → C' = C) ↔ C ∈ s.cellsT ∧ adim C = Fintype.card s.P') :=
  sec3_maximal_cells_full_proved s C

/-- **P4** (v2.10 l. 370): "`A_ℓ = {u ∈ B : ℓ(u) ≥ ℓ_K(u) for all K}` is a polytope, and `L` equals the affine
function `ℓ` on it" (and the same for `U`, l. 381). -/
theorem sec3_domains_polytope_affine {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∀ K ∈ s.lowBranches,
      s.domL K = {u | u ∈ s.B ∧ ∀ K' ∈ s.lowBranches, s.chainSum K' u ≤ s.chainSum K u} ∧
      IsPolytope (s.domL K) ∧
      ∃ g : (s.P' → ℝ) →ᵃ[ℝ] ℝ, (∀ u, g u = s.chainSum K u) ∧ ∀ u ∈ s.domL K, s.L u = g u) ∧
    (∀ j ∈ s.upBranches,
      s.domU j = {u | u ∈ s.B ∧ ∀ j' ∈ s.upBranches, s.upVal j u ≤ s.upVal j' u} ∧
      IsPolytope (s.domU j) ∧
      ∃ g : (s.P' → ℝ) →ᵃ[ℝ] ℝ, (∀ u, g u = s.upVal j u) ∧ ∀ u ∈ s.domU j, s.U u = g u) :=
  sec3_domains_polytope_affine_proved s

/-- **P5** (v2.10 l. 373-374): "Full-dimensional sets `A_ℓ ⊆ A_ℓ'` have `ℓ = ℓ'`, as `ℓ = L = ℓ'` on the
full-dimensional set `A_ℓ`" (and the same for `U`, l. 381). Only `A_ℓ` needs to be full-dimensional. -/
theorem sec3_full_domains_eq {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∀ K ∈ s.lowBranches, ∀ K' ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' →
      s.domL K ⊆ s.domL K' → s.chainSum K = s.chainSum K' ∧ s.domL K = s.domL K') ∧
    (∀ j ∈ s.upBranches, ∀ j' ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' →
      s.domU j ⊆ s.domU j' → s.upVal j = s.upVal j' ∧ s.domU j = s.domU j') :=
  sec3_full_domains_eq_proved s

/-- **P6** (v2.10 l. 377-380): "The full-dimensional `A_ℓ` cover `B`" (and the same for `U`, l. 381). -/
theorem sec3_full_domains_cover {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∀ u ∈ s.B, ∃ K ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' ∧ u ∈ s.domL K) ∧
    (∀ u ∈ s.B, ∃ j ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' ∧ u ∈ s.domU j) :=
  sec3_full_domains_cover_proved s

/-- Lines 403–408 and 431: every cell of `S`, `T`, `R` has exactly one carrier, and its relative interior lies in
the relative interior of its carrier. -/
theorem sec3_carrier {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (C : Set (s.P' → ℝ))
    (hC : C ∈ s.cellsS ∨ C ∈ s.cellsT ∨ C ∈ s.cellsR) :
    (∃! E, IsCarrier s.B E C) ∧ ∀ E, IsCarrier s.B E C → intrinsicInterior ℝ C ⊆ intrinsicInterior ℝ E :=
  sec3_carrier_proved s C hC

/-- **P7** (v2.10 l. 409-410): "the carrier of `C` is the only face of `B` whose relative interior meets
`relint(C)`", for every cell `C` of `S`, `T` or `R`. -/
theorem sec3_carrier_unique {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (C : Set (s.P' → ℝ))
    (hC : C ∈ s.cellsS ∨ C ∈ s.cellsT ∨ C ∈ s.cellsR) (E : Set (s.P' → ℝ)) (hE : IsCarrier s.B E C) :
    ∀ E', IsFace s.B E' → ((intrinsicInterior ℝ E' ∩ intrinsicInterior ℝ C).Nonempty ↔ E' = E) :=
  sec3_carrier_unique_proved s C hC E hE

open HibiLi.Proofs.Cov200 in
/-- **Section 3, carriers** (v2.10 l. 403-404): "The carrier of a cell is the smallest face of `B` that contains it
(it exists: it is the intersection of all faces of `B` that contain the cell)." For a cell of `S`, `T` or `R`: the
intersection of all faces of `B` containing it is its carrier, and every carrier equals that intersection. -/
theorem sec3_carrier_eq_sInter {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (C : Set (s.P' → ℝ))
    (hC : C ∈ s.cellsS ∨ C ∈ s.cellsT ∨ C ∈ s.cellsR) :
    IsCarrier s.B (⋂₀ {G | IsFace s.B G ∧ C ⊆ G}) C ∧ ∀ K, IsCarrier s.B K C → K = ⋂₀ {G | IsFace s.B G ∧ C ⊆ G} :=
  carrier_sInter_proved s C hC

/-- v2.10 l. 397-403 (F3): "For a face `E` of `B`, the restriction `S|_E` consists of the nonempty sets `S ∩ E` with
`S ∈ S`; each is a face of `S`, as a valid inequality of `B` that cuts out `E` is valid on `S`, so `S|_E` is a
subdivision of `E` into cells of `S` (…). Similarly for `T|_E` and `R|_E`": for each of the three families, every
nonempty `A ∩ E` is a face of `A`, the restriction consists of cells of the family, and it is (the set of) a finite
polytopal subdivision of `E`. -/
theorem sec3_restrict_subdivision {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) {E : Set (s.P' → ℝ)}
    (hE : IsFace s.B E) (K : Set (Set (s.P' → ℝ))) (hK : K = s.cellsS ∨ K = s.cellsT ∨ K = s.cellsR) :
    (∀ A ∈ K, (A ∩ E).Nonempty → IsFace A (A ∩ E)) ∧ s.restrict K E ⊆ K ∧
      ∃ c : Finset (Set (s.P' → ℝ)), (c : Set (Set (s.P' → ℝ))) = s.restrict K E ∧
        IsFinitePolytopalSubdivision E c := by
  obtain ⟨cS, cT, cR, hS, hT, hR, subS, subT, subR⟩ := sec3_subdivisions s
  rcases hK with rfl | rfl | rfl
  · exact Proofs.AddV170.restrict_family s hE _ cS hS subS
  · exact Proofs.AddV170.restrict_family s hE _ cT hT subT
  · exact Proofs.AddV170.restrict_family s hE _ cR hR subR

/-- **Lemma 3.2** (lines 427–430), second equality (the paper's own, line 431; no cited input):
`F_B + F_R − F_S − F_T = Σ_E δ_E` over all nonempty faces `E` of `B`. -/
theorem lemma_3_2_local {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT =
      ∑ᶠ (E : Set (s.P' → ℝ)) (_ : IsFace s.B E), s.delta E :=
  s.sum_delta_eq.symm.trans (finsum_mem_eq_finite_toFinset_sum _ s.B_isPolytope.finite_faces).symm

/-- **Lemma 3.2** (lines 427–430; first equality = Fourier 4.1, cited; second equality = `lemma_3_2_local`): the change
in face polynomials is the sum of the local terms `δ_E` over all nonempty faces `E` of `B`. -/
theorem lemma_3_2 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    {E | IsFace s.B E}.Finite ∧
    facePoly (chainOrderPolytope P (insert s.q s.I)) - facePoly (chainOrderPolytope P s.I) =
      ∑ᶠ (E : Set (s.P' → ℝ)) (_ : IsFace s.B E), s.delta E :=
  ⟨s.B_isPolytope.finite_faces, (Cited.fourier_lemma_4_1 s).trans (lemma_3_2_local s)⟩

/-- **Definition 3.3** (lines 443–448), "the unique cells": for every face `E` of `B` and `u ∈ relint E`, exactly one
cell of `S|_E`, and exactly one cell of `T|_E`, has `u` in its relative interior.  (So `Switch.Transverse`, which
quantifies over all such cells, says exactly what Definition 3.3 says.) -/
theorem def_3_3_unique_cells {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (u : s.P' → ℝ) (hu : u ∈ intrinsicInterior ℝ E) :
    (∃! A, A ∈ s.restrict s.cellsS E ∧ u ∈ intrinsicInterior ℝ A) ∧
      (∃! D, D ∈ s.restrict s.cellsT E ∧ u ∈ intrinsicInterior ℝ D) :=
  Proofs.def_3_3_unique_cells_proved s E hE u hu

/-- Lines 450–451, the clause "Although `L` depends only on the coordinates `x_p` with `p < q` and `U` only on the
coordinates `y_r` with `r > q`, …". -/
theorem sec3_L_U_locality {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (u v : s.P' → ℝ) :
    ((∀ p : s.P', p.1 < s.q → u p = v p) → s.L u = s.L v) ∧
      ((∀ r : s.P', s.q < r.1 → u r = v r) → s.U u = s.U v) :=
  Proofs.sec3_L_U_locality_proved s u v

/-- **Proposition 3.4** (lines 454–456; = Fourier Proposition 5.2, cited as `Cited.fourier_prop_5_2`): `S` and `T` are
transverse relative to the faces of `B`. -/
theorem prop_3_4 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) : s.Transverse :=
  Cited.fourier_prop_5_2 s

/-- **Lemma 3.5(i)** (lines 467–469), first sentence: for `k < e` and a `k`-cell `Y` of `S` or `T` with carrier `E`,
`R(Y)` is nonempty and its members have carrier `E`. -/
theorem lemma_3_5_i_cover {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E)
    (Y : Set (s.P' → ℝ)) (hY : Y ∈ s.cellsS ∨ Y ∈ s.cellsT) (hYE : IsCarrier s.B E Y) (hdim : adim Y < adim E) :
    (s.RR Y).Nonempty ∧ ∀ R ∈ s.RR Y, IsCarrier s.B E R :=
  lemma_3_5_i_cover_proved s hT E hE Y hY hYE hdim

/-- **Lemma 3.5(i)** (lines 469–470), second sentence: these sets are pairwise disjoint, over all such `Y` in `S` and
`T`. -/
theorem lemma_3_5_i_disjoint {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) (Y Y' : Set (s.P' → ℝ))
    (hYY' : (Y ∈ s.cellsS ∧ Y' ∈ s.cellsS ∧ Y ≠ Y') ∨ (Y ∈ s.cellsT ∧ Y' ∈ s.cellsT ∧ Y ≠ Y') ∨
      (Y ∈ s.cellsS ∧ Y' ∈ s.cellsT))
    (hYE : IsCarrier s.B E Y) (hY'E : IsCarrier s.B E Y') (hdim : adim Y = adim Y') (hlt : adim Y < adim E) :
    Disjoint (s.RR Y) (s.RR Y') :=
  lemma_3_5_i_disjoint_proved s hT E hE Y Y' hYY' hYE hY'E hdim hlt

/-- **Lemma 3.5(ii)** (lines 471–474): the bipartite graph `G_E` is connected (the paper's proof, lines 490–526, which
cites [CJK, Lemma 2] for the dual graph and recalls its argument, lines 494–509).  Lean proves [CJK, Lemma 2] itself,
by its own route (`HibiLi/Polytope/CJKProof.lean`; row `lemma_3_5_ii_dual_graph`), with no cited assumption. -/
theorem lemma_3_5_ii {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) : (s.graphG E).Connected :=
  lemma_3_5_ii_proved s hT E hE

open HibiLi.Proofs.Cov200 in
open Filter Topology in
/-- **Lemma 3.5(ii), proof** (v2.10 l. 510-516): "Let `S ∩ T` and `S' ∩ T'` be adjacent `e`-cells of `R|_E`, with
common `(e-1)`-face `D`. The two cells have disjoint interiors and both have `D` as a facet, so they lie on opposite
sides of the hyperplane `aff(D)` of `aff(E)`: each lies on one side, as `D` is a facet of it, and near a point of
`relint(D)` each coincides with the closed half-space bounded by `aff(D)` that contains it". Two cells `A, B ⊆ E`
(polytopes of the dimension of `E`) meet in `D = A ∩ B` (cells of a subdivision meet in a common face), a face of `A`
of dimension `dim E - 1`. Then an affine `h` cuts `aff(D)` out of `aff(E)`, `h ≤ 0` on `A` and `h ≥ 0` on `B`, neither
cell lies in the hyperplane, and near every point of `relint(D)`, within `aff(E)`: `A = {h ≤ 0}` and `B = {h ≥ 0}`.
(Only "`D` is a face of `A`" is assumed; that `D` is a face of `B` is not needed, and disjoint relative interiors
follow from the conclusion.) -/
theorem lemma_3_5_ii_opposite_sides {ι : Type*} [Fintype ι] {E A B : Set (ι → ℝ)}
    (hA : IsPolytope A) (hB : IsPolytope B) (hAE : A ⊆ E) (hBE : B ⊆ E)
    (hAdim : adim A = adim E) (hBdim : adim B = adim E)
    (hfA : IsFace A (A ∩ B)) (hdim : adim (A ∩ B) + 1 = adim E) :
    ∃ h : (ι → ℝ) →ᵃ[ℝ] ℝ, (∀ x ∈ affineSpan ℝ E, h x = 0 ↔ x ∈ affineSpan ℝ (A ∩ B)) ∧
      (∀ x ∈ A, h x ≤ 0) ∧ (∀ x ∈ B, 0 ≤ h x) ∧ (∃ x ∈ A, h x < 0) ∧ (∃ x ∈ B, 0 < h x) ∧
      ∀ x₀ ∈ intrinsicInterior ℝ (A ∩ B), ∀ᶠ y in 𝓝 x₀, y ∈ affineSpan ℝ E →
        ((y ∈ A ↔ h y ≤ 0) ∧ (y ∈ B ↔ 0 ≤ h y)) :=
  opposite_sides_proved hA hB hAE hBE hAdim hBdim hfA hdim

/-- **Lemma 3.5(ii)**, the parenthesis (v2.10 l. 473-474): "each `e`-cell of `R|_E` has this form [`S ∩ T` with `S`, `T`
`e`-cells of `S|_E`, `T|_E`] for exactly one such pair: the `e`-cells of `S|_E` and `T|_E` that contain it". Stated:
every `e`-cell `R` of `R|_E` is `S ∩ T` for such `S`, `T`, and `S` (resp. `T`) is the ONLY `e`-cell of `S|_E` (resp.
`T|_E`) that contains `R`; so any pair `S', T'` with `R = S' ∩ T'` is this pair (it contains `R`). -/
theorem lemma_3_5_ii_pairs {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (R : Set (s.P' → ℝ)) (hR : R ∈ s.topCells s.cellsR E) :
    ∃ S ∈ s.topCells s.cellsS E, ∃ T ∈ s.topCells s.cellsT E, R = S ∩ T ∧
      (∀ S' ∈ s.topCells s.cellsS E, R ⊆ S' → S' = S) ∧ (∀ T' ∈ s.topCells s.cellsT E, R ⊆ T' → T' = T) := by
  obtain ⟨⟨hRne, C, ⟨_, A, hA, D, hD, rfl⟩, rfl⟩, hdim⟩ := hR
  have hle : ∀ {Y Z : Set (s.P' → ℝ)}, Y ⊆ Z → adim Y ≤ adim Z := fun h =>
    Submodule.finrank_mono (vectorSpan_mono ℝ h)
  have hS : A ∩ E ∈ s.topCells s.cellsS E :=
    ⟨⟨hRne.mono fun x hx => ⟨hx.1.1, hx.2⟩, A, hA, rfl⟩,
      le_antisymm (hle Set.inter_subset_right) (hdim.symm.le.trans (hle fun x hx => ⟨hx.1.1, hx.2⟩))⟩
  have hT : D ∩ E ∈ s.topCells s.cellsT E :=
    ⟨⟨hRne.mono fun x hx => ⟨hx.1.2, hx.2⟩, D, hD, rfl⟩,
      le_antisymm (hle Set.inter_subset_right) (hdim.symm.le.trans (hle fun x hx => ⟨hx.1.2, hx.2⟩))⟩
  refine ⟨A ∩ E, hS, D ∩ E, hT, ?_, fun S' hS' hRS' => ?_, fun T' hT' hRT' => ?_⟩
  · ext x
    simp only [Set.mem_inter_iff]
    tauto
  · obtain ⟨x, hx⟩ := hRne
    refine s.topCellsS_eq_of_full_inter hE hS' hS ⟨x, hRS' hx, hx.1.1, hx.2⟩ (le_antisymm ?_ ?_)
    · exact hle (Set.inter_subset_right.trans Set.inter_subset_right)
    · exact hdim.symm.le.trans (hle fun y hy => ⟨hRS' hy, hy.1.1, hy.2⟩)
  · obtain ⟨x, hx⟩ := hRne
    refine s.topCellsT_eq_of_full_inter hE hT' hT ⟨x, hRT' hx, hx.1.2, hx.2⟩ (le_antisymm ?_ ?_)
    · exact hle (Set.inter_subset_right.trans Set.inter_subset_right)
    · exact hdim.symm.le.trans (hle fun y hy => ⟨hRT' hy, hy.1.2, hy.2⟩)

/-- v2.10 l. 509-517 (proof of Lemma 3.5(ii)): two distinct `e`-cells `A`, `B` of a subdivision of an `e`-polytope `E`
that share the facet `D = A ∩ B` (a face of both, of dimension `e − 1`): "Hence `D` lies in no facet of `E` (otherwise
`E` would lie on one side of `aff(D)`), so in no proper face of `E`, and `relint(D) ⊆ relint(E)`". -/
theorem lemma_3_5_ii_shared_facet {ι : Type*} [Fintype ι] {E A B : Set (ι → ℝ)}
    (hE : IsPolytope E) (hA : IsPolytope A) (hB : IsPolytope B) (hAE : A ⊆ E) (hBE : B ⊆ E)
    (hAdim : adim A = adim E) (hBdim : adim B = adim E) (hAB : A ≠ B)
    (hfA : IsFace A (A ∩ B)) (hfB : IsFace B (A ∩ B)) (hdim : adim (A ∩ B) + 1 = adim E) :
    intrinsicInterior ℝ (A ∩ B) ⊆ intrinsicInterior ℝ E :=
  interior_shared_facet hE hA hB hAE hBE hAdim hBdim hAB hfA hfB hdim

/-- **Lemma 3.5(iii)** (line 475; Fourier 4.3, Steps 1–2): `δ_{E,k} ≥ 0` for every face `E` and every `k`. -/
theorem lemma_3_5_iii {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (hT : s.Transverse)
    (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) (k : ℕ) : 0 ≤ s.deltaCoeff E k :=
  lemma_3_5_iii_proved s hT E hE k

/-- v2.10 l. 530-531 (proof of Lemma 3.5(iii)): "an `e`-cell in `E` has carrier `E`", for `S|_E`, `T|_E` and `R|_E`. -/
theorem lemma_3_5_top_cells_carrier {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) :
    (∀ C ∈ s.topCells s.cellsS E, IsCarrier s.B E C) ∧ (∀ C ∈ s.topCells s.cellsT E, IsCarrier s.B E C) ∧
      (∀ C ∈ s.topCells s.cellsR E, IsCarrier s.B E C) := by
  refine ⟨fun C hC => ?_, fun C hC => ?_, fun C hC => ?_⟩
  · rw [s.topCellsS_eq_carried hE] at hC
    exact hC.2.2
  · rw [s.topCellsT_eq_carried hE] at hC
    exact hC.2.2
  · rw [s.topCellsR_eq_carried hE] at hC
    exact hC.2.2

/-- **Lemma 3.6** (lines 536–540), first clause: the `e`-cells of `S|_E` are exactly the maximal convex subsets of `E`
of dimension `e` on which `L` is affine; the same for `T|_E` and `U`.  The second clause, added in v0.60, is
`lemma_3_6_cover`. -/
theorem lemma_3_6 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (A : Set (s.P' → ℝ)) :
    (A ∈ s.topCells s.cellsS E ↔ A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧ AffineOn s.L A ∧
      ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn s.L D → D = A) ∧
    (A ∈ s.topCells s.cellsT E ↔ A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧ AffineOn s.U A ∧
      ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn s.U D → D = A) :=
  Proofs.lemma_3_6_proved s E hE A

/-- **Lemma 3.6**, second clause (new in v0.60; v2.10 lines 539–540): every `e`-dimensional convex subset of `E` on which
`L` is affine lies in an `e`-cell of `S|_E`; the same for `T|_E` and `U`. -/
theorem lemma_3_6_cover {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (D : Set (s.P' → ℝ)) (hDE : D ⊆ E) (hDc : Convex ℝ D) (hDdim : adim D = adim E) :
    (AffineOn s.L D → ∃ C ∈ s.topCells s.cellsS E, D ⊆ C) ∧
      (AffineOn s.U D → ∃ C ∈ s.topCells s.cellsT E, D ⊆ C) :=
  Proofs.lemma_3_6_cover_proved s E hE D hDE hDc hDdim

/-- Lines 357–380: Lean's `cellsS` is built from the full-dimensional branch domains `A_ℓ` (the characterization of
lines 367–380, which the paper proves there).  This bridges back to the paper's DEFINITION of `S` (lines 357–360): its
full-dimensional cells are exactly the maximal full-dimensional convex subsets of `B` on which `L` is affine (and
the same for `T`, `U`). -/
theorem sec3_S_paper_def {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (A : Set (s.P' → ℝ)) :
    (A ∈ s.cellsS ∧ adim A = Fintype.card s.P' ↔ A ⊆ s.B ∧ Convex ℝ A ∧ adim A = Fintype.card s.P' ∧
      AffineOn s.L A ∧ ∀ D, A ⊆ D → D ⊆ s.B → Convex ℝ D → AffineOn s.L D → D = A) ∧
    (A ∈ s.cellsT ∧ adim A = Fintype.card s.P' ↔ A ⊆ s.B ∧ Convex ℝ A ∧ adim A = Fintype.card s.P' ∧
      AffineOn s.U A ∧ ∀ D, A ⊆ D → D ⊆ s.B → Convex ℝ D → AffineOn s.U D → D = A) :=
  Proofs.sec3_S_paper_def_proved s A

/-- Lines 357–360, the paper's DEFINITION of `S` in full: the cells of `S` are exactly the nonempty faces of the maximal
full-dimensional convex subsets of `B` on which `L` is affine (and the same for `T`, `U`). -/
theorem sec3_S_paper_def_full {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    s.cellsS = {C | ∃ A, (A ⊆ s.B ∧ Convex ℝ A ∧ adim A = Fintype.card s.P' ∧ AffineOn s.L A ∧
        ∀ D, A ⊆ D → D ⊆ s.B → Convex ℝ D → AffineOn s.L D → D = A) ∧ IsFace A C} ∧
    s.cellsT = {C | ∃ A, (A ⊆ s.B ∧ Convex ℝ A ∧ adim A = Fintype.card s.P' ∧ AffineOn s.U A ∧
        ∀ D, A ⊆ D → D ⊆ s.B → Convex ℝ D → AffineOn s.U D → D = A) ∧ IsFace A C} :=
  Proofs.sec3_S_paper_def_full_proved s

/-- **Proposition 3.7** (lines 562–564; Fourier 6.1): `F_{O_I(P)} ≤ F_{O_{I∪{q}}(P)}` coefficientwise, derived as the
paper's proof (lines 566–568) does: from Lemma 3.2, Proposition 3.4 and Lemma 3.5(iii). -/
theorem prop_3_7 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (k : ℕ) :
    fNum (chainOrderPolytope P s.I) k ≤ fNum (chainOrderPolytope P (insert s.q s.I)) k := by
  classical
  obtain ⟨hfin, hid⟩ := lemma_3_2 s
  have hsum : facePoly (chainOrderPolytope P (insert s.q s.I)) - facePoly (chainOrderPolytope P s.I) =
      ∑ E ∈ hfin.toFinset, s.delta E := by
    rw [hid]; exact finsum_mem_eq_finite_toFinset_sum _ hfin
  have hcoeff := congrArg (fun p => Polynomial.coeff p k) hsum
  simp only [coeff_sub, Proofs.facePoly_coeff, finsetSum_coeff] at hcoeff
  have hnonneg : 0 ≤ ∑ E ∈ hfin.toFinset, (s.delta E).coeff k := by
    refine Finset.sum_nonneg fun E hE => ?_
    rw [Proofs.delta_coeff]
    split_ifs
    · exact lemma_3_5_iii s (Cited.fourier_prop_5_2 s) E (hfin.mem_toFinset.mp hE) k
    · exact le_refl 0
  omega

/-- **Fourier's Theorem 1.1** (part (a) of the conjecture, paper lines 98–99; Theorem 1.2(a), line 126), DERIVED from
Proposition 3.7 along a linear extension, as in the paper's proof of Theorem 1.2(a) (lines 982–985, "this is Fourier's
argument"; the switches as in lines 879–890): `f_k(O(P)) ≤ f_k(C(P))` for every `k`. -/
theorem fourier_thm_1_1 (P : Type*) [Fintype P] [PartialOrder P] (k : ℕ) :
    fNum (orderPolytope P) k ≤ fNum (chainPolytope P) k := by
  have h := Proofs.mono_of_step (P := P) (fun s k => prop_3_7 s k) ∅ Set.univ isLowerSet_empty isLowerSet_univ
    (Set.empty_subset _) k
  rwa [(sec3_endpoints P).1, (sec3_endpoints P).2] at h

/-! ### Section 3: coverage rows (review REVIEW_006_cov, 20261028) -/

/-- v2.10 l. 332-334: every element comparable to `q` is in `I` and below `q`, or in `J` and above `q`. -/
theorem sec3_q_comparable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    ∀ p : P, (p < s.q ∨ s.q < p) → (p ∈ s.I ∧ p < s.q) ∨ (p ∉ s.I ∧ s.q < p) :=
  Proofs.sec3_q_comparable s

/-- v2.10 l. 336-337: `q` is maximal in `I ∪ {q}`, so a chain of `I ∪ {q}` through `q` is `K ∪ {q}` with `K` a chain
of elements of `I` below `q`. -/
theorem sec3_chains_through_q {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    ∀ K : Finset P, ↑K ⊆ insert s.q s.I → IsChainSet P K → s.q ∈ K → ∀ p ∈ K, p ≠ s.q → p ∈ s.I ∧ p < s.q :=
  Proofs.sec3_chains_through_q s

open Classical Filter Topology in
/-- v2.10 l.336-337: "the element q is maximal in I union {q}, so the chains through q are the sets K union {q} with K as in the definition of L". This row supplies maximality and the converse; sec3_chains_through_q supplies the forward direction. -/
theorem sec3_chains_through_q_converse {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∀ p ∈ insert s.q s.I, ¬ s.q < p) ∧
    ∀ K : Finset P, ↑K ⊆ s.I → IsChainSet P K → (∀ p ∈ K, p < s.q) →
      IsChainSet P (insert s.q K) ∧ ↑(insert s.q K) ⊆ insert s.q s.I :=
  Proofs.sec3_chains_through_q_converse s

/-- v2.10 l. 371-373: a full-dimensional convex `D ⊆ B` on which `L` (and `U`) is affine lies in a full-dimensional
affinity domain `A_ℓ`. -/
theorem sec3_affine_in_domain {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∀ D ⊆ s.B, Convex ℝ D → adim D = Fintype.card s.P' → AffineOn s.L D →
      ∃ K ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' ∧ D ⊆ s.domL K) ∧
    (∀ D ⊆ s.B, Convex ℝ D → adim D = Fintype.card s.P' → AffineOn s.U D →
      ∃ j ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' ∧ D ⊆ s.domU j) :=
  Proofs.sec3_affine_in_domain s

/-- v2.10 l. 386-387: `A_ℓ ∩ A_ℓ' = A_ℓ ∩ {ℓ = ℓ'}` is a face of `A_ℓ` (for `L`, and likewise for `U`). -/
theorem sec3_domain_inter_face {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∀ K ∈ s.lowBranches, ∀ K' ∈ s.lowBranches, (s.domL K ∩ s.domL K').Nonempty →
      s.domL K ∩ s.domL K' = {u ∈ s.domL K | s.chainSum K u = s.chainSum K' u} ∧
        IsFace (s.domL K) (s.domL K ∩ s.domL K')) ∧
    (∀ j ∈ s.upBranches, ∀ j' ∈ s.upBranches, (s.domU j ∩ s.domU j').Nonempty →
      s.domU j ∩ s.domU j' = {u ∈ s.domU j | s.upVal j u = s.upVal j' u} ∧
        IsFace (s.domU j) (s.domU j ∩ s.domU j')) :=
  Proofs.sec3_domain_inter_face s

/-- v2.10 l. 390-392: a face of a cell `S ∩ T` of `R` is `S₀ ∩ T₀`, with `S₀`, `T₀` faces of `S`, `T`. -/
theorem sec3_R_cell_faces {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    ∀ A ∈ s.cellsS, ∀ D ∈ s.cellsT, ∀ F, IsFace (A ∩ D) F → ∃ A₀ D₀, IsFace A A₀ ∧ IsFace D D₀ ∧ F = A₀ ∩ D₀ :=
  Proofs.sec3_R_cell_faces s

/-- **v2.10 l. 435-437** ("An informal reading (not used below)", sentence 1): a face of `O_I(P)` that contains no
segment parallel to the `z`-axis (`z` = the `q`-coordinate) lies in the graph of `L` over a cell of `S`, or in the graph
of `U` over a cell of `T`, or in both (both cell statements); the last case occurs exactly over the set where `L = U`.
  `HasVertical s F` (defined in `HibiLi/Proofs/VerticalCount.lean`): `F` contains a segment parallel to the
`z`-axis, `{x, x + t e_q}` with `t ≠ 0`. -/
theorem sec3_informal_before {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (F : Set (P → ℝ))
    (hF : IsFace (chainOrderPolytope P s.I) F) (hv : ¬ HasVertical s F) :
    ((∃ C ∈ s.cellsS, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.L (fun p => x p.1)}) ∨
     (∃ C ∈ s.cellsT, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.U (fun p => x p.1)})) ∧
    (((∃ C ∈ s.cellsS, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.L (fun p => x p.1)}) ∧
      (∃ C ∈ s.cellsT, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.U (fun p => x p.1)})) ↔
      ∀ x ∈ F, s.L (fun p => x p.1) = s.U (fun p => x p.1)) :=
  Proofs.Informal.informal_before s F hF hv

/-- **v2.10 l. 437-439** (sentence 2): after the switch, a face of `O_{I∪{q}}(P)` that contains no segment parallel to
the `z`-axis lies in the facet `{z = 0}` over a face of `B`, or in the graph of `U − L` over a cell of `R`, or in both;
again the last case (both cell statements) occurs exactly over the set where `L = U`.
  `HasVertical s F` (defined in `HibiLi/Proofs/VerticalCount.lean`): `F` contains a segment parallel to the
`z`-axis, `{x, x + t e_q}` with `t ≠ 0`. -/
theorem sec3_informal_after {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (F : Set (P → ℝ))
    (hF : IsFace (chainOrderPolytope P (insert s.q s.I)) F) (hv : ¬ HasVertical s F) :
    ((∃ G, IsFace s.B G ∧ F ⊆ {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = 0}) ∨
     (∃ C ∈ s.cellsR, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧
        x s.q = s.U (fun p => x p.1) - s.L (fun p => x p.1)})) ∧
    (((∃ G, IsFace s.B G ∧ F ⊆ {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = 0}) ∧
      (∃ C ∈ s.cellsR, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧
        x s.q = s.U (fun p => x p.1) - s.L (fun p => x p.1)})) ↔
      ∀ x ∈ F, s.L (fun p => x p.1) = s.U (fun p => x p.1)) :=
  Proofs.Informal.informal_after s F hF hv

/-- **v2.10 l. 439-441** (sentence 3 of the informal reading): "the first equality of Lemma 3.2 says that the two
polytopes have equally many faces that contain a segment parallel to the `z`-axis": for every `k`, `O_I(P)` and
`O_{I∪{q}}(P)` have equally many `k`-faces that contain such a segment.
  `HasVertical s F` (defined in `HibiLi/Proofs/VerticalCount.lean`): `F` contains a segment parallel to the
`z`-axis, `{x, x + t e_q}` with `t ≠ 0`. -/
theorem sec3_informal_vertical_count {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (k : ℕ) :
    {F | IsFace (chainOrderPolytope P s.I) F ∧ adim F = k ∧ HasVertical s F}.ncard =
      {F | IsFace (chainOrderPolytope P (insert s.q s.I)) F ∧ adim F = k ∧ HasVertical s F}.ncard :=
  Proofs.sec3_informal_vertical_count s k

open Classical Filter Topology in
/-- v2.10 l.439-440: "Thus F_B+F_R-F_S-F_T compares the numbers of these faces before and after the switch". The subtraction is in integers; the cited Fourier identity is the only nonstandard input. -/
theorem sec3_nonvertical_coefficient {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (k : ℕ) :
    ({F | IsFace (chainOrderPolytope P (insert s.q s.I)) F ∧ adim F = k ∧ ¬ HasVertical s F}.ncard : ℤ) -
      ({F | IsFace (chainOrderPolytope P s.I) F ∧ adim F = k ∧ ¬ HasVertical s F}.ncard : ℤ) =
        (facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT).coeff k :=
  Proofs.sec3_nonvertical_coefficient_of s (Cited.fourier_lemma_4_1 s) k

/-- v2.10 l. 450-451: "Although `L` depends only on the coordinates `x_p` with `p < q` and `U` only on the coordinates
`y_r` with `r > q`, these coordinates are coupled by the inequalities of `B`": for `p ∈ I` with `p < q` and `r > q`,
every `u ∈ B` has `u_p ≤ u_r` (the chain inequality `x_p ≤ y_r` of `B`). -/
theorem sec3_coupled_coordinates {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    ∀ p r : s.P', p.1 ∈ s.I → p.1 < s.q → s.q < r.1 → ∀ u ∈ s.B, u p ≤ u r := by
  exact Proofs.sec3_coupled_coordinates s

/-- **Lemma 3.5(i), proof** (v2.10 l. 480-482): a member `R` of `R(Y)` has `relint R ⊆ relint Y`. -/
theorem lemma_3_5_i_relint {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) {Y R : Set (s.P' → ℝ)} :
    (Y ∈ s.cellsS ∨ Y ∈ s.cellsT) → R ∈ s.RR Y → intrinsicInterior ℝ R ⊆ intrinsicInterior ℝ Y :=
  Proofs.lemma_3_5_i_relint s

/-- **Lemma 3.5(i)** (v2.10 l. 487-488): "In particular (take `S = T = Y`), no `k`-cell `Y` with carrier `E` is a cell
of both `S` and `T`" (`k < e = dim E`). -/
theorem lemma_3_5_i_not_both {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (hT : s.Transverse)
    (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) (Y : Set (s.P' → ℝ)) (hYS : Y ∈ s.cellsS) (hYT : Y ∈ s.cellsT)
    (hYE : IsCarrier s.B E Y) (hdim : adim Y < adim E) : False :=
  Proofs.Cov1.not_both s hT E hE Y hYS hYT hYE hdim

/-- **Lemma 3.5(ii), proof** (v2.10 l. 492-494): "The dual graph of the subdivision `R|_E` of `E` ... is connected
[CJK, Lemma 2]" (proved in Lean, `subdivisionDualGraph_connected`); its vertices, the maximal cells, are exactly the
`e`-cells (`e = dim E`). -/
theorem lemma_3_5_ii_dual_graph {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) :
    ∃ c : Finset (Set (s.P' → ℝ)), (c : Set (Set (s.P' → ℝ))) = s.restrict s.cellsR E ∧
      IsFinitePolytopalSubdivision E c ∧ (subdivisionDualGraph c).Connected ∧
      ∀ C ∈ c, (∀ C' ∈ c, C ⊆ C' → C' = C) ↔ adim C = adim E := by
  obtain ⟨-, -, c, hc, hsub⟩ := sec3_restrict_subdivision s hE s.cellsR (Or.inr (Or.inr rfl))
  have hEpoly : IsPolytope E := (sec3_B_dim s).1.face hE
  exact ⟨c, hc, hsub, subdivisionDualGraph_connected E c hEpoly hE.1 hsub,
    Proofs.Cov1.max_iff_full hEpoly hE.1 hsub⟩

/-- **Lemma 3.5(ii), proof** (v2.10 l. 518-523): "Let `S ∩ T` and `S' ∩ T'` be adjacent `e`-cells of `R|_E` ...":
two adjacent `e`-cells of `R|_E` (distinct, meeting in a common face of dimension `e - 1`) are edges of `G_E` with a
common vertex, `S = S'` or `T = T'`. -/
theorem lemma_3_5_ii_adjacent_common_vertex {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) (S S' T T' : Set (s.P' → ℝ))
    (hS : S ∈ s.topCells s.cellsS E) (hS' : S' ∈ s.topCells s.cellsS E)
    (hT₁ : T ∈ s.topCells s.cellsT E) (hT₂ : T' ∈ s.topCells s.cellsT E)
    (hR : S ∩ T ∈ s.topCells s.cellsR E) (hR' : S' ∩ T' ∈ s.topCells s.cellsR E) (hne : S ∩ T ≠ S' ∩ T')
    (hD : IsFace (S ∩ T) (S ∩ T ∩ (S' ∩ T')) ∧ IsFace (S' ∩ T') (S ∩ T ∩ (S' ∩ T')))
    (hdim : adim (S ∩ T ∩ (S' ∩ T')) + 1 = adim E) : S = S' ∨ T = T' :=
  Proofs.Cov1.adjacent_common_vertex s hT hE hS hS' hT₁ hT₂ hR hR' hne hD hdim

/-- **Lemma 3.5(ii), proof** (v2.10 l. 524-525): every vertex of `G_E` lies on an edge: each `e`-cell of `S|_E`
meets some `e`-cell of `T|_E` in an `e`-cell of `R|_E`, and conversely. -/
theorem lemma_3_5_ii_vertex_on_edge {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) :
    (∀ S ∈ s.topCells s.cellsS E, ∃ T ∈ s.topCells s.cellsT E, S ∩ T ∈ s.topCells s.cellsR E) ∧
    (∀ T ∈ s.topCells s.cellsT E, ∃ S ∈ s.topCells s.cellsS E, S ∩ T ∈ s.topCells s.cellsR E) :=
  ⟨fun _ hS => Proofs.Cov1.vertex_on_edge_S s hE hS, fun _ hT => Proofs.Cov1.vertex_on_edge_T s hE hT⟩

/-- **Lemma 3.5(iii), proof** (v2.10 l. 528-531): "For `k > e` there are no cells with carrier `E`. For `k < e`, (i)
gives `ρ_E(k) ≥ σ_E(k) + τ_E(k)`. For `k = e`, the cells with carrier `E` in `S` and `T` are the `e`-cells of `S|_E` and
`T|_E` (an `e`-cell in `E` has carrier `E`), that is, the vertices of `G_E`, and those in `R` are its edges". -/
theorem lemma_3_5_iii_steps {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E)
    (hT : s.Transverse) :
    (∀ k, adim E < k → s.carrierNum s.cellsS E k = 0 ∧
      s.carrierNum s.cellsT E k = 0 ∧ s.carrierNum s.cellsR E k = 0) ∧
    (∀ k, k < adim E → s.carrierNum s.cellsS E k + s.carrierNum s.cellsT E k ≤
      s.carrierNum s.cellsR E k) ∧
    {C | C ∈ s.cellsS ∧ adim C = adim E ∧ IsCarrier s.B E C} = s.topCells s.cellsS E ∧
    {C | C ∈ s.cellsT ∧ adim C = adim E ∧ IsCarrier s.B E C} = s.topCells s.cellsT E ∧
    {C | C ∈ s.cellsR ∧ adim C = adim E ∧ IsCarrier s.B E C} = s.topCells s.cellsR E := by
  exact Proofs.lemma_3_5_iii_steps s E hE hT

/-- **Lemma 3.6, proof** (v2.10 l. 543-548): "An `e`-cell of `S|_E` is a set `S ∩ E` with `S` a face of a maximal cell
`A_ℓ` of `S`. … the two are equal: `S ∩ E = A_ℓ ∩ E = {u ∈ E : L(u) = ℓ(u)}`". -/
theorem lemma_3_6_cell_branch_L {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E)
    (A : Set (s.P' → ℝ)) (hA : A ∈ s.topCells s.cellsS E) :
    ∃ K ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' ∧ A = s.domL K ∩ E ∧
      A = {u ∈ E | s.L u = s.chainSum K u} := by
  exact Proofs.lemma_3_6_cell_branch_L s E hE A hA

/-- **Lemma 3.6, proof** (v2.10 l. 543-548 with l. 559, "For `U`, use the minimum in place of the maximum"): an
`e`-cell of `T|_E` is `A'_j ∩ E = {u ∈ E : U(u) = u_j}` for a full-dimensional affinity domain `A'_j` of `U`. -/
theorem lemma_3_6_cell_branch_U {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E)
    (A : Set (s.P' → ℝ)) (hA : A ∈ s.topCells s.cellsT E) :
    ∃ j ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' ∧ A = s.domU j ∩ E ∧
      A = {u ∈ E | s.U u = s.upVal j u} := by
  exact Proofs.lemma_3_6_cell_branch_U s E hE A hA

/-- **Lemma 3.6, proof** (v2.10 l. 555-557): "Two nested `e`-cells `A_ℓ ∩ E ⊆ A_ℓ' ∩ E` have `ℓ = ℓ'` on `aff(E)`, so
they are equal" (an `e`-cell is nonempty: the hypothesis `nonempty`). -/
theorem lemma_3_6_nested_L {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (K K' : Finset s.P') (E : Set (s.P' → ℝ)) (nonempty : (s.domL K ∩ E).Nonempty)
    (inside : s.domL K ∩ E ⊆ s.domL K' ∩ E) (dimension : adim (s.domL K ∩ E) = adim E) :
    s.domL K ∩ E = s.domL K' ∩ E := by
  exact Proofs.lemma_3_6_nested_L s K K' E nonempty inside dimension

/-- **Lemma 3.6, proof** (v2.10 l. 555-557 with l. 559, "For `U`, use the minimum in place of the maximum"): two
nested nonempty `e`-dimensional sets `A'_j ∩ E ⊆ A'_j' ∩ E` are equal. -/
theorem lemma_3_6_nested_U {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (j j' : Option s.P') (E : Set (s.P' → ℝ)) (nonempty : (s.domU j ∩ E).Nonempty)
    (inside : s.domU j ∩ E ⊆ s.domU j' ∩ E) (dimension : adim (s.domU j ∩ E) = adim E) :
    s.domU j ∩ E = s.domU j' ∩ E := by
  exact Proofs.lemma_3_6_nested_U s j j' E nonempty inside dimension

/-! ## Section 4 (the sharp gap) -/


/-- **Lemma 4.2** (one crossing; lines 580–590): under the crossing hypotheses at some `w`,
`δ_E(t) ≥ t^{e−2}(1+t)^2`.  `CrossingAt` is the v1.00-v1.80 hypothesis ("`H_S`, `H_T` hyperplanes of `aff(E)` through
`w`, and `H_S ≠ H_T`", a clause v2.10 keeps) by `crossingAt_iff_v060`, with `N` "a convex neighborhood of `w` in `E`"
(v1.80); the v2.10 wording of `N`, "some convex set `N ⊆ E`, open in `aff(E)` and containing `w`", is
`lemma_4_2_v190`. -/
theorem lemma_4_2 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (w : s.P' → ℝ) (hw : CrossingAt s E w) (k : ℕ) :
    (X ^ (adim E - 2) * (1 + X) ^ 2 : ℤ[X]).coeff k ≤ (s.delta E).coeff k :=
  Proofs.lemma_4_2_of s (Cited.fourier_prop_5_2 s) (lemma_3_5_i_cover s) (lemma_3_5_i_disjoint s)
    (lemma_3_5_ii s) (lemma_3_5_iii s) (sec3_carrier s) E hE w hw k

/-- Lemma 4.2's hypothesis as worded in v0.60 to v1.80, with `N` a convex neighbourhood of `w` in `E`: `H_S = {φ = φ w}`
and `H_T = {ψ = ψ w}` are hyperplanes of `aff(E)` through `w` (`φ, ψ` nonzero on `dir(E)`), and `H_S ≠ H_T` (this clause
is unchanged in v2.10, lines 585–588; v2.10 words `N` as a convex set open in `aff(E)`, lines 582–583:
`lemma_4_2_v190`).  This is exactly `CrossingAt`, whose last clause is the v0.41 wording "the normals are linearly
independent in the dual of `dir(E)`". -/
theorem crossingAt_iff_v060 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (w : s.P' → ℝ) :
    CrossingAt s E w ↔
      w ∈ intrinsicInterior ℝ E ∧
      ∃ N : Set (s.P' → ℝ), Convex ℝ N ∧ N ⊆ E ∧ N ∈ nhdsWithin w E ∧
      ∃ (S₁ S₂ T₁ T₂ : Set (s.P' → ℝ)) (φ ψ : (s.P' → ℝ) →ₗ[ℝ] ℝ),
        S₁ ∈ s.topCells s.cellsS E ∧ S₂ ∈ s.topCells s.cellsS E ∧
        T₁ ∈ s.topCells s.cellsT E ∧ T₂ ∈ s.topCells s.cellsT E ∧
        (∀ A ∈ s.topCells s.cellsS E, (A ∩ N).Nonempty → A = S₁ ∨ A = S₂) ∧
        (∀ D ∈ s.topCells s.cellsT E, (D ∩ N).Nonempty → D = T₁ ∨ D = T₂) ∧
        S₁ ∩ N = {u ∈ N | φ w ≤ φ u} ∧ S₂ ∩ N = {u ∈ N | φ u ≤ φ w} ∧
        T₁ ∩ N = {u ∈ N | ψ w ≤ ψ u} ∧ T₂ ∩ N = {u ∈ N | ψ u ≤ ψ w} ∧
        φ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧ ψ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧
        {u | u ∈ affineSpan ℝ E ∧ φ u = φ w} ≠ {u | u ∈ affineSpan ℝ E ∧ ψ u = ψ w} :=
  Proofs.crossingAt_iff_v060_proved s E w

/-- Lemma 4.2's hypotheses force `e ≥ 2` (v2.10 line 588: "(this forces `e ≥ 2`)"): the two normals restricted to
`dir(E)` are linearly independent in its dual, so `dim E = dim dir(E) ≥ 2`. -/
theorem lemma_4_2_e_ge_two {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (w : s.P' → ℝ) (hw : CrossingAt s E w) : 2 ≤ adim E := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hli⟩ := hw
  have h := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h
  exact h.trans_eq Subspace.dual_finrank_eq

/-- **Lemma 4.2** with the v2.10 hypothesis (l. 580-590; the name is historical, this wording dates from v1.90): "some
convex set `N ⊆ E`, open in `aff(E)` and containing `w`" (v1.80: "a convex neighborhood `N` of `w` in `E`"); the rest
of the hypothesis is the v1.80 wording, unchanged in v2.10, as in `crossingAt_iff_v060` (the cells meeting `N` are
among `S₁, S₂` and `T₁, T₂`; the half-space description; `H_S`, `H_T` hyperplanes of `aff(E)` through `w`;
`H_S ≠ H_T`), with "(this forces `e ≥ 2`)" (l. 588). Derived from
`lemma_4_2` and `lemma_4_2_e_ge_two`: such an `N` is a neighborhood of `w` within `E`. -/
theorem lemma_4_2_v190 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (w : s.P' → ℝ) (hw : w ∈ intrinsicInterior ℝ E)
    (hN : ∃ N : Set (s.P' → ℝ), Convex ℝ N ∧ N ⊆ E ∧
      (∃ O : Set (s.P' → ℝ), IsOpen O ∧ N = O ∩ (affineSpan ℝ E : Set (s.P' → ℝ))) ∧ w ∈ N ∧
      ∃ (S₁ S₂ T₁ T₂ : Set (s.P' → ℝ)) (φ ψ : (s.P' → ℝ) →ₗ[ℝ] ℝ),
        S₁ ∈ s.topCells s.cellsS E ∧ S₂ ∈ s.topCells s.cellsS E ∧
        T₁ ∈ s.topCells s.cellsT E ∧ T₂ ∈ s.topCells s.cellsT E ∧
        (∀ A ∈ s.topCells s.cellsS E, (A ∩ N).Nonempty → A = S₁ ∨ A = S₂) ∧
        (∀ D ∈ s.topCells s.cellsT E, (D ∩ N).Nonempty → D = T₁ ∨ D = T₂) ∧
        S₁ ∩ N = {u ∈ N | φ w ≤ φ u} ∧ S₂ ∩ N = {u ∈ N | φ u ≤ φ w} ∧
        T₁ ∩ N = {u ∈ N | ψ w ≤ ψ u} ∧ T₂ ∩ N = {u ∈ N | ψ u ≤ ψ w} ∧
        φ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧ ψ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧
        {u | u ∈ affineSpan ℝ E ∧ φ u = φ w} ≠ {u | u ∈ affineSpan ℝ E ∧ ψ u = ψ w}) :
    2 ≤ adim E ∧ ∀ k : ℕ, (X ^ (adim E - 2) * (1 + X) ^ 2 : ℤ[X]).coeff k ≤ (s.delta E).coeff k := by
  obtain ⟨N, hNconv, hNE, ⟨O, hO, hNO⟩, hwN, rest⟩ := hN
  have hwO : w ∈ O := by
    rw [hNO] at hwN
    exact hwN.1
  have hnhds : N ∈ nhdsWithin w E := by
    refine mem_nhdsWithin.2 ⟨O, hO, hwO, fun u hu => ?_⟩
    rw [hNO]
    exact ⟨hu.1, subset_affineSpan ℝ E hu.2⟩
  have hcross := (crossingAt_iff_v060 s E w).2 ⟨hw, N, hNconv, hNE, hnhds, rest⟩
  exact ⟨lemma_4_2_e_ge_two s E w hcross, fun k => lemma_4_2 s E hE w hcross k⟩


/-- Paper lines 679–681: a valid `q` exists — an element `q`, maximal among the elements `m ≥ c` whose strict upper
set is not a chain (as every `r > q` is `≥ c`, maximality says: the strict upper set of every `r > q` is a chain). -/
theorem sec4_q_exists {P : Type*} [Fintype P] [PartialOrder P] {a b c g h : P} (hX : IsXCopy a b c g h) :
    ∃ q, c ≤ q ∧ ¬ IsChain (· ≤ ·) (Set.Ioi q) ∧ ∀ r, q < r → IsChain (· ≤ ·) (Set.Ioi r) :=
  Proofs.q_exists hX.2.2.1 hX.2.2.2.1 hX.2.2.2.2.2.2.1 hX.2.2.2.2.2.2.2

/-- Lines 681–684: "We cannot always take `q = c`: the construction of `E₀` below needs two incomparable upper covers
of `q`, and `c` may have only one, for example when an element `d` with `c < d < g, h` is the only upper cover of
`c`".  In
`a, b < c < d < g, h` (`XdElem`) the elements `a, b, c, g, h` form a copy of `X`, no switch of Section 4 can use
`q = c`, and one does exist (with `q = d`). -/
theorem sec4_q_c_remark :
    IsXCopy XdElem.a XdElem.b XdElem.c XdElem.g XdElem.h ∧ Nonempty (XSwitch XdElem) ∧
      ∀ x : XSwitch XdElem, x.q ≠ XdElem.c :=
  Proofs.sec4_q_c_remark_proved

/-- Lines 681–684, the remark's reason: in `XdElem`, `c`'s strict upper set is not a chain, yet `c` has no two distinct
upper covers (its only cover is `d`), so `E₀` could not be built at `q = c`. -/
theorem sec4_q_c_no_two_covers :
    ¬ IsChain (· ≤ ·) (Set.Ioi XdElem.c) ∧
      ¬ ∃ g' h' : XdElem, XdElem.c ⋖ g' ∧ XdElem.c ⋖ h' ∧ g' ≠ h' :=
  Proofs.sec4_q_c_no_two_covers_proved

/-- v2.10 l. 683-684 ("an element `d` with `c < d < g, h` is the only upper cover of `c`"): in the poset
`a, b < c < d < g, h` (`XdElem`), `d` is the ONLY upper cover of `c` (stronger than
`sec4_q_c_no_two_covers`, which says that `c` has no two distinct upper covers). -/
theorem sec4_d_only_cover_of_c : XdElem.c ⋖ XdElem.d ∧ ∀ y : XdElem, XdElem.c ⋖ y → y = XdElem.d := by
  refine ⟨?_, Proofs.R3Small.Xd_covBy_c⟩
  unfold CovBy
  simp only [lt_iff_le_not_ge]
  decide

/-- **Lemma 4.3** (lines 686–691): `q` has two distinct, incomparable upper covers; `I = P \ ↑q` is an order ideal, `q`
is minimal in `J = ↑q`, and `a, b ∈ I` with `a, b < q`. -/
theorem lemma_4_3 {P : Type*} [Fintype P] [PartialOrder P] {a b c g h q : P} (hX : IsXCopy a b c g h)
    (hcq : c ≤ q) (hq : ¬ IsChain (· ≤ ·) (Set.Ioi q)) (hmax : ∀ r, q < r → IsChain (· ≤ ·) (Set.Ioi r)) :
    (∃ g' h', q ⋖ g' ∧ q ⋖ h' ∧ g' ≠ h' ∧ ¬ g' ≤ h' ∧ ¬ h' ≤ g') ∧
    IsLowerSet (Set.Ici q)ᶜ ∧ (∀ p, p < q → p ∈ (Set.Ici q)ᶜ) ∧
    a ∈ (Set.Ici q)ᶜ ∧ b ∈ (Set.Ici q)ᶜ ∧ a < q ∧ b < q :=
  Proofs.lemma_4_3 hX.1 hX.2.1 hcq hq hmax

/-- **Lemma 4.3** in its final wording (v2.10 lines 687–688: "`q` has at least two upper covers, and any two are
incomparable"): any two distinct upper covers of an element are incomparable (in every poset; with `lemma_4_3`, which
gives two of them). -/
theorem lemma_4_3_covers_incomparable {P : Type*} [PartialOrder P] (q g' h' : P) (hg : q ⋖ g') (hh : q ⋖ h')
    (hne : g' ≠ h') : ¬ g' ≤ h' ∧ ¬ h' ≤ g' :=
  ⟨fun hle => hh.2 hg.1 (lt_of_le_of_ne hle hne), fun hle => hg.2 hh.1 (lt_of_le_of_ne hle hne.symm)⟩

/-- Line 706: "Fix two upper covers `g′` and `h′` of `q`; they need not be `g` and `h`."  Witness `R3Elem`:
`a, b < c < d < g′, h′`, `g′ < g`, with the copy `a, b, c, g, h′` of `X`; a switch of Section 4 exists with `q > c` and
`{g′, h′} ≠ {g, h}`, and every `q` meeting Lemma 4.3's conditions for this copy has this property. -/
theorem sec4_covers_may_differ :
    IsXCopy R3Elem.a R3Elem.b R3Elem.c R3Elem.g R3Elem.hp ∧
    (∃ x : XSwitch R3Elem, x.a = R3Elem.a ∧ x.b = R3Elem.b ∧ x.c = R3Elem.c ∧ x.g = R3Elem.g ∧
      x.h = R3Elem.hp ∧ x.c < x.q ∧ ({x.g', x.h'} : Set R3Elem) ≠ {x.g, x.h}) ∧
    ∀ q : R3Elem, R3Elem.c ≤ q → ¬ IsChain (· ≤ ·) (Set.Ioi q) →
      (∀ r, q < r → IsChain (· ≤ ·) (Set.Ioi r)) →
        R3Elem.c < q ∧ ∀ g' h' : R3Elem, q ⋖ g' → q ⋖ h' → g' ≠ h' →
          ({g', h'} : Set R3Elem) ≠ {R3Elem.g, R3Elem.hp} :=
  Proofs.sec4_covers_may_differ_proved

/-- Line 706 ("they need not be `g` and `h`"), in its bare form: some switch of Section 4 has `q > c` and
`{g′, h′} ≠ {g, h}`. -/
theorem sec4_covers_may_differ_exists :
    ∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (x : XSwitch P),
      x.c < x.q ∧ ({x.g', x.h'} : Set P) ≠ {x.g, x.h} :=
  Proofs.sec4_covers_may_differ_exists_proved


/-- **Lemma 4.4** (lines 717–721): `E₀` is a 4-dimensional face of `B`, cut out (besides `ζ = ζ₀`) by `α, β ≥ 0`,
`max(α, β) ≤ min(γ, η)`, `γ, η ≤ 1`. -/
theorem lemma_4_4 {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)
    (pa pb pg ph : x.toSwitch.P') (hpa : pa.1 = x.a) (hpb : pb.1 = x.b) (hpg : pg.1 = x.g')
    (hph : ph.1 = x.h') :
    IsFace x.toSwitch.B x.E0 ∧ adim x.E0 = 4 ∧
    x.E0 = {u | (∀ p : x.toSwitch.P', p.1 ∈ x.toSwitch.I → p.1 ≠ x.a → p.1 ≠ x.b → u p = 0) ∧
               (∀ r : x.toSwitch.P', r.1 ∉ x.toSwitch.I → r.1 ≠ x.g' → r.1 ≠ x.h' → u r = 1) ∧
               0 ≤ u pa ∧ 0 ≤ u pb ∧ max (u pa) (u pb) ≤ min (u pg) (u ph) ∧ u pg ≤ 1 ∧ u ph ≤ 1} :=
  Proofs.lemma_4_4_proved x pa pb pg ph hpa hpb hpg hph

open Classical in
/-- **P8** (v2.10 l. 723-724), the switch of Section 4.2: "The inequality
`Σ_{p ∈ I∖{a,b}} x_p + Σ_{r ∈ J'∖{g',h'}} (1 − y_r) ≥ 0` is valid on `B` and is tight exactly where `ζ = ζ₀`"
(`J'` = the coordinates of `B` outside `I`). -/
theorem sec4_E0_inequality {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∀ u ∈ x.toSwitch.B,
      0 ≤ (∑ p ∈ univ.filter (fun p : x.toSwitch.P' => p.1 ∈ x.toSwitch.I ∧ p.1 ≠ x.a ∧ p.1 ≠ x.b), u p) +
        ∑ r ∈ univ.filter (fun r : x.toSwitch.P' => r.1 ∉ x.toSwitch.I ∧ r.1 ≠ x.g' ∧ r.1 ≠ x.h'), (1 - u r) ∧
      ((∑ p ∈ univ.filter (fun p : x.toSwitch.P' => p.1 ∈ x.toSwitch.I ∧ p.1 ≠ x.a ∧ p.1 ≠ x.b), u p) +
        ∑ r ∈ univ.filter (fun r : x.toSwitch.P' => r.1 ∉ x.toSwitch.I ∧ r.1 ≠ x.g' ∧ r.1 ≠ x.h'), (1 - u r) = 0 ↔
        x.zeta u = x.zeta x.u0) :=
  sec4_E0_inequality_proved x

/-- **Lemma 4.5** (lines 747–764; local product structure): open `V₄ ∋ (1/4,1/4,3/4,3/4)` and `V_ζ ∋ ζ₀` with
`N₀ = V₄ × V_ζ` such that (a) for every face `E ⊇ E₀` of `B`, membership in `E` within `N₀` depends only on `ζ` (so
`E ∩ N₀ = V₄ × (Q_E ∩ V_ζ)`, with `Q_E` the `ζ`-section; the paper's own `Q_E`, defined in the statement by tight
inequalities, lines 756–758, is in `lemma_4_5_paper`), and (b) on `B ∩ N₀`, `L = max(α + λ_a(ζ), β + λ_b(ζ))` and
`U = min(γ, η)`. -/
theorem lemma_4_5 {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∃ (V4 : Set (Fin 4 → ℝ)) (Vz : Set ({p // p ∉ x.special} → ℝ)), IsOpen V4 ∧ IsOpen Vz ∧
      x.alphaPart x.u0 ∈ V4 ∧ x.zeta x.u0 ∈ Vz ∧
      (∀ E, IsFace x.toSwitch.B E → x.E0 ⊆ E → ∀ u ∈ x.N0 V4 Vz, ∀ v ∈ x.N0 V4 Vz,
        x.zeta u = x.zeta v → (u ∈ E ↔ v ∈ E)) ∧
      (∀ u ∈ x.toSwitch.B, u ∈ x.N0 V4 Vz →
        x.toSwitch.L u = max (u x.pa + x.lamA u) (u x.pb + x.lamB u) ∧ x.toSwitch.U u = min (u x.pg) (u x.ph)) :=
  Proofs.lemma_4_5_proved x

/-- Lines 738–743: all forms of the `a`- and `b`-families vanish at `ζ₀`, so `λ_a(ζ₀) = λ_b(ζ₀) = 0`. -/
theorem sec4_lam_u0 {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    x.lamA x.u0 = 0 ∧ x.lamB x.u0 = 0 :=
  Proofs.sec4_lam_u0_proved x

/-- **Lemma 4.5, full form of (a)** (lines 752–759), with the same `N₀` as (b): for every face `E ⊇ E₀` of `B`,
`ζ₀ ∈ Q_E`, `E ∩ N₀ = V₄ × (Q_E ∩ V_ζ)` and `relint E ∩ N₀ = V₄ × (relint Q_E ∩ V_ζ)`.  Here `Q_E` is the
`ζ`-section of `E` (`XSwitch.QE`).  The paper's own `Q_E` (inequalities tight at `u₀`) is used in `lemma_4_5_paper`
below; the two agree near `ζ₀` (`Proofs.QEPaper.QE_iff_QEpaper`). -/
theorem lemma_4_5_full {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∃ (V4 : Set (Fin 4 → ℝ)) (Vz : Set ({p // p ∉ x.special} → ℝ)), IsOpen V4 ∧ IsOpen Vz ∧
      x.alphaPart x.u0 ∈ V4 ∧ x.zeta x.u0 ∈ Vz ∧
      (∀ E, IsFace x.toSwitch.B E → x.E0 ⊆ E → x.zeta x.u0 ∈ x.QE E ∧ ∀ u ∈ x.N0 V4 Vz,
        (u ∈ E ↔ x.zeta u ∈ x.QE E) ∧
        (u ∈ intrinsicInterior ℝ E ↔ x.zeta u ∈ intrinsicInterior ℝ (x.QE E))) ∧
      (∀ u ∈ x.toSwitch.B, u ∈ x.N0 V4 Vz →
        x.toSwitch.L u = max (u x.pa + x.lamA u) (u x.pb + x.lamB u) ∧ x.toSwitch.U u = min (u x.pg) (u x.ph)) :=
  Proofs.lemma_4_5_full_proved x

/-- **Lemma 4.5(a)** with the paper's OWN `Q_E` (lines 752–759): "`Q_E ∋ ζ₀` is the polyhedron of the points of the
`ζ`-space that satisfy the defining inequalities of `B` that are tight at `u₀` (these involve only `ζ`), those that are
tight on all of `E` being imposed as equations" (`XSwitch.QEpaper`,
Defs/QEPaper.lean); same quantifiers and clauses as `lemma_4_5_full`. -/
theorem lemma_4_5_paper {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∃ (V4 : Set (Fin 4 → ℝ)) (Vz : Set ({p // p ∉ x.special} → ℝ)), IsOpen V4 ∧ IsOpen Vz ∧
      x.alphaPart x.u0 ∈ V4 ∧ x.zeta x.u0 ∈ Vz ∧
      (∀ E, IsFace x.toSwitch.B E → x.E0 ⊆ E → x.zeta x.u0 ∈ x.QEpaper E ∧ ∀ u ∈ x.N0 V4 Vz,
        (u ∈ E ↔ x.zeta u ∈ x.QEpaper E) ∧
        (u ∈ intrinsicInterior ℝ E ↔ x.zeta u ∈ intrinsicInterior ℝ (x.QEpaper E))) ∧
      (∀ u ∈ x.toSwitch.B, u ∈ x.N0 V4 Vz →
        x.toSwitch.L u = max (u x.pa + x.lamA u) (u x.pb + x.lamB u) ∧ x.toSwitch.U u = min (u x.pg) (u x.ph)) :=
  Proofs.lemma_4_5_paper x

open Filter Topology in
/-- **M1** (v2.10 l. 778-782), proof of Lemma 4.5: "Every point of `E` satisfies the inequalities that define `Q_E`, so
`E ⊆ ℝ⁴ × Q_E`; with (product), and as `aff(Q_E ∩ V_ζ) = aff(Q_E)` (`Q_E` is convex and `V_ζ` is a neighborhood of its
point `ζ₀`), this gives `aff(E) = ℝ⁴ × aff(Q_E)`", for every face `E ⊇ E₀` of `B`; the middle equality is stated for
every neighborhood `V` of `ζ₀`. -/
theorem sec4_E_subset_QE {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) (E : Set (x.toSwitch.P' → ℝ))
    (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E) :
    Convex ℝ (x.QEpaper E) ∧ (∀ u ∈ E, x.zeta u ∈ x.QEpaper E) ∧
    (∀ V ∈ 𝓝 (x.zeta x.u0), affineSpan ℝ (x.QEpaper E ∩ V) = affineSpan ℝ (x.QEpaper E)) ∧
    (affineSpan ℝ E : Set (x.toSwitch.P' → ℝ)) = {u | x.zeta u ∈ affineSpan ℝ (x.QEpaper E)} :=
  ⟨Proofs.QEPaper.QEpaper_convex x E, sec4_E_subset_QE_proved x E hE hE0⟩

open HibiLi.Proofs.Cov200 in
/-- **Lemma 4.5(a), proof** (v2.10 l. 766-772): "Every defining inequality of `B` that involves `α, β, γ` or `η` is
strict at `u₀`" (`x_a ≥ 0`, `x_b ≥ 0`, `0 ≤ γ ≤ 1`, `0 ≤ η ≤ 1`, the chain inequalities, and the order inequalities
`y_r ≤ y_{r'}`, `r < r'`, that involve `γ` or `η`). The inequality lists are those of `chainOrderPolytope`; an order
inequality is taken for `r < r'` (for `r = r'` it is `y_r ≤ y_r`). Stronger than the text for chains: every chain
inequality is strict at `u₀`. -/
theorem sec4_u0_strict {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    (∀ p ∈ x.special, 0 < x.u0 p ∧ x.u0 p < 1) ∧
    (∀ r r', r ∉ x.toSwitch.I' → r' ∉ x.toSwitch.I' → r < r' → (r ∈ x.special ∨ r' ∈ x.special) →
      x.u0 r < x.u0 r') ∧
    (∀ r ∉ x.toSwitch.I', ∀ K : Finset x.toSwitch.P', ↑K ⊆ x.toSwitch.I' → IsChainSet x.toSwitch.P' K →
      (∀ p ∈ K, p < r) → ∑ p ∈ K, x.u0 p < x.u0 r) ∧
    (∀ K : Finset x.toSwitch.P', ↑K ⊆ x.toSwitch.I' → IsChainSet x.toSwitch.P' K → ∑ p ∈ K, x.u0 p < 1) :=
  u0_strict_proved x

open Classical in
/-- v2.10 l. 737-742 (F4): "For a chain `K ∋ a` in the definition of `L`, the linear form `Σ_{p∈K∖{a}} x_p`
depends only on `ζ`, as `K∖{a} ⊆ I∖{a,b}` (`b ∉ K`, since `a` and `b` are incomparable); … likewise for the
`b`-family": for `K` a chain of `L` (`lowBranches`), if `a ∈ K`
then `b ∉ K` and the form factors through `ζ` by a linear map; the same with `a, b` exchanged. -/
theorem sec4_family_forms_zeta {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)
    {K : Finset x.toSwitch.P'} (hK : K ∈ x.toSwitch.lowBranches) :
    (x.pa ∈ K → x.pb ∉ K ∧ ∃ F : ({p // p ∉ x.special} → ℝ) →ₗ[ℝ] ℝ,
      ∀ u, x.toSwitch.chainSum (K.erase x.pa) u = F (x.zeta u)) ∧
    (x.pb ∈ K → x.pa ∉ K ∧ ∃ F : ({p // p ∉ x.special} → ℝ) →ₗ[ℝ] ℝ,
      ∀ u, x.toSwitch.chainSum (K.erase x.pb) u = F (x.zeta u)) :=
  ⟨fun ha => ⟨fun hb => Proofs.Lemma46.not_both x hK ha hb,
      Proofs.AddV170.family_form_zeta_proved x hK (Or.inl rfl) ha⟩,
    fun hb => ⟨fun ha => Proofs.Lemma46.not_both x hK ha hb,
      Proofs.AddV170.family_form_zeta_proved x hK (Or.inr rfl) hb⟩⟩

open Classical in
/-- v2.10 l. 783-787 (F5), proof of Lemma 4.5(b): "At `u₀` a chain has sum `1/4` if it contains `a` or `b` (not both),
and sum `0` otherwise, the empty chain included. The terms of `U` other than `γ` and `η` equal `1 > 3/4`. Shrinking `N₀`
(which keeps (a) true) keeps these strict inequalities, so on `B ∩ N₀` only chains containing `a` or `b` attain `L`, and
only `γ` or `η` attains `U`": `lemma_4_5` with, on the same `N₀`, the last sentence (a chain `K` of `L` with
`ℓ_K(u) = L(u)` contains `a` or `b`; a term `j` of `U` with value `U(u)` is `γ` or `η`). -/
theorem lemma_4_5_strict {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∃ (V4 : Set (Fin 4 → ℝ)) (Vz : Set ({p // p ∉ x.special} → ℝ)), IsOpen V4 ∧ IsOpen Vz ∧
      x.alphaPart x.u0 ∈ V4 ∧ x.zeta x.u0 ∈ Vz ∧
      (∀ E, IsFace x.toSwitch.B E → x.E0 ⊆ E → ∀ u ∈ x.N0 V4 Vz, ∀ v ∈ x.N0 V4 Vz,
        x.zeta u = x.zeta v → (u ∈ E ↔ v ∈ E)) ∧
      (∀ u ∈ x.toSwitch.B, u ∈ x.N0 V4 Vz →
        x.toSwitch.L u = max (u x.pa + x.lamA u) (u x.pb + x.lamB u) ∧ x.toSwitch.U u = min (u x.pg) (u x.ph)) ∧
      (∀ u ∈ x.toSwitch.B, u ∈ x.N0 V4 Vz →
        (∀ K ∈ x.toSwitch.lowBranches, x.toSwitch.chainSum K u = x.toSwitch.L u → x.pa ∈ K ∨ x.pb ∈ K) ∧
        (∀ j ∈ x.toSwitch.upBranches, x.toSwitch.upVal j u = x.toSwitch.U u → j = some x.pg ∨ j = some x.ph)) :=
  Proofs.AddV170.lemma_4_5_strict_proved x

/-- **Lemma 4.6** (lines 792–795; with Lemma 4.5 inside its proof): for every face `E ⊇ E₀` of `B`, the hypotheses of
Lemma 4.2 hold at some `w ∈ relint E` (`CrossingAt` contains `w ∈ relint E`). -/
theorem lemma_4_6 {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) (E : Set (x.toSwitch.P' → ℝ))
    (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E) : ∃ w, CrossingAt x.toSwitch E w :=
  Proofs.lemma_4_6_of_3_6 x (fun E hE A => Proofs.lemma_3_6_proved x.toSwitch E hE A) E hE hE0

/-- **Lemma 4.7**, first part of its proof (lines 847–855): an `s`-polytope has at least `C(s+1, κ+1)` faces of
dimension `κ` (`0 ≤ κ ≤ s`).  The paper's cases `κ = −1` (the empty face) and `s ≤ 0` are left out: Lean's `IsFace`
excludes `∅`, and `Q` is nonempty. -/
theorem lemma_4_7_simplex {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (hne : Q.Nonempty)
    (κ : ℕ) (hκ : κ ≤ adim Q) : Nat.choose (adim Q + 1) (κ + 1) ≤ fNum Q κ :=
  Proofs.lemma_4_8_simplex_proved Q hQ hne κ hκ

open HibiLi.Proofs.Cov200 in
/-- **Lemma 4.7, proof** (v2.10 l. 850-851): "an `s`-polytope with `s ≥ 1` has a facet, and, being the convex hull of
its vertices, it has a vertex outside the proper face `D`". A facet is a face of dimension `dim Q - 1`; a vertex is a
`0`-dimensional face `{v}`. -/
theorem sec4_facet_vertex_outside {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (hne : Q.Nonempty)
    (hs : 1 ≤ adim Q) :
    (∃ D, IsFace Q D ∧ adim D + 1 = adim Q) ∧ ∀ D, IsFace Q D → D ≠ Q → ∃ v, IsFace Q {v} ∧ v ∉ D :=
  ⟨exists_facet_proved Q hQ hne (adim Q - 1) (by omega),
    fun D hD hDQ => exists_vertex_not_mem_proved Q hQ hne D hD hDQ⟩

/-- **Lemma 4.7** (lines 841–845): a nonempty `e`-face `E` of an `m`-polytope `B` lies in at least `C(m−e, j)` faces of
dimension `e + j`, for `0 ≤ j ≤ m − e`. -/
theorem lemma_4_7 {ι : Type*} [Fintype ι] (B : Set (ι → ℝ)) (hB : IsPolytope B) (E : Set (ι → ℝ))
    (hE : IsFace B E) (j : ℕ) (hj : j ≤ adim B - adim E) :
    Nat.choose (adim B - adim E) j ≤ {G | IsFace B G ∧ E ⊆ G ∧ adim G = adim E + j}.ncard :=
  Proofs.lemma_4_8_proved B hB E hE j hj

/-- Lines 867–878: for the switch of Section 4.2, the single step from `O_I(P)` to `O_{I∪{q}}(P)` already adds at least
`t^2 (1+t)^{n−3}`. -/
theorem switch_step_gap {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) (k : ℕ) :
    (gapPoly (Fintype.card P)).coeff k ≤
      (fNum (chainOrderPolytope P (insert x.q (Set.Ici x.q)ᶜ)) k : ℤ) - fNum (chainOrderPolytope P (Set.Ici x.q)ᶜ) k := by
  classical
  let s := x.toSwitch
  -- dimensions: B is an (n−1)-polytope (lines 299–303, 309–310), E₀ a 4-face (Lemma 4.4)
  obtain ⟨hBpoly, hBdim⟩ := sec3_dim s.P' s.I' (Proofs.I'_isLowerSet s)
  obtain ⟨hE0face, hE0dim, -⟩ := lemma_4_4 x x.pa x.pb x.pg x.ph
    rfl rfl rfl rfl
  have hB : adim s.B = Fintype.card P - 1 := by rw [Switch.B, hBdim, Proofs.card_P']
  have hn5 : 5 ≤ Fintype.card P := by
    have hle : adim x.E0 ≤ adim s.B :=
      Submodule.finrank_mono (vectorSpan_mono ℝ (fun u hu => hu.1))
    rw [hE0dim, hB] at hle
    omega
  -- Lemma 3.2: the step's change is the sum of the local terms over the (finitely many) faces of B
  obtain ⟨hfin, hid⟩ := lemma_3_2 s
  let F := hfin.toFinset
  have hsum : facePoly (chainOrderPolytope P (insert s.q s.I)) - facePoly (chainOrderPolytope P s.I) =
      ∑ E ∈ F, s.delta E := by
    rw [hid]; exact finsum_mem_eq_finite_toFinset_sum _ hfin
  -- Section 4.4: the counting step (Lemmas 3.5(iii), 4.2, 4.6, 4.7)
  have hgapstep := Proofs.gap_from_local_terms F adim s.delta x.E0 (Fintype.card P - 5)
    (fun E hE k => by
      have hEf : IsFace s.B E := hfin.mem_toFinset.mp hE
      rw [Proofs.delta_coeff]
      split_ifs
      · exact lemma_3_5_iii s (Cited.fourier_prop_5_2 s) E hEf k
      · exact le_refl 0)
    (fun E hE hE0 k => by
      obtain ⟨w, hw⟩ := lemma_4_6 x E (hfin.mem_toFinset.mp hE) hE0
      exact lemma_4_2 s E (hfin.mem_toFinset.mp hE) w hw k)
    (fun j hj => by
      have hcount := lemma_4_7 s.B hBpoly x.E0 hE0face j (by rw [hE0dim, hB]; omega)
      rw [hE0dim, hB, show Fintype.card P - 1 - 4 = Fintype.card P - 5 by omega] at hcount
      have hset : {G | IsFace s.B G ∧ x.E0 ⊆ G ∧ adim G = 4 + j} =
          ↑(F.filter (fun E => x.E0 ⊆ E ∧ adim E = 4 + j)) := by
        ext G
        simp [F, Set.Finite.mem_toFinset]
      rw [hset, Set.ncard_coe_finset] at hcount
      exact hcount) k
  show (gapPoly (Fintype.card P)).coeff k ≤
      (fNum (chainOrderPolytope P (insert s.q s.I)) k : ℤ) - fNum (chainOrderPolytope P s.I) k
  · have hcoeff := congrArg (fun p => Polynomial.coeff p k) hsum
    simp only [coeff_sub, Proofs.facePoly_coeff] at hcoeff
    rw [hcoeff]
    have hg : gapPoly (Fintype.card P) = X ^ 2 * (1 + X) ^ (Fintype.card P - 5 + 2) := by
      unfold gapPoly; congr 2; omega
    rw [hg]
    exact hgapstep

/-- **Theorem 4.1** (lines 572–574), inequality: if `P` contains `X` then `F_C(P) − F_O(P) ≥ t^2 (1+t)^{n−3}`
coefficientwise. -/
theorem thm_4_1 (P : Type*) [Fintype P] [PartialOrder P] (hX : ContainsX P) (k : ℕ) :
    (gapPoly (Fintype.card P)).coeff k ≤ (fNum (chainPolytope P) k : ℤ) - fNum (orderPolytope P) k := by
  classical
  -- Section 4.2: the copy of X, the element q and its covers g', h' (Lemma 4.3), the switch of q
  obtain ⟨a, b, c, g, h, hac, hbc, hcg, hch, hab, hba, hgh, hhg⟩ := hX
  have hXc : IsXCopy a b c g h := ⟨hac, hbc, hcg, hch, hab, hba, hgh, hhg⟩
  obtain ⟨q, hcq, hq, hmax⟩ := sec4_q_exists hXc
  obtain ⟨⟨g', h', hg', hh', hne, hgh', hhg'⟩, -, -, -, -, haq, hbq⟩ := lemma_4_3 hXc hcq hq hmax
  let x : XSwitch P := ⟨a, b, c, g, h, hXc, q, hcq, hq, hmax, g', h', hg', hh', hne, ⟨hgh', hhg'⟩⟩
  let s := x.toSwitch
  have hstep : (gapPoly (Fintype.card P)).coeff k ≤
      (fNum (chainOrderPolytope P (insert s.q s.I)) k : ℤ) - fNum (chainOrderPolytope P s.I) k :=
    switch_step_gap x k
  -- the monotone chain O(P) = O_∅ ≤ O_I and O_{I∪{q}} ≤ O_P = C(P) (Proposition 3.7, lines 879–890)
  have hmono : ∀ I I' : Set P, IsLowerSet I → IsLowerSet I' → I ⊆ I' →
      fNum (chainOrderPolytope P I) k ≤ fNum (chainOrderPolytope P I') k :=
    fun I I' hI hI' hII' => Proofs.mono_of_step (fun s k => prop_3_7 s k) I I' hI hI' hII' k
  have h1 := hmono ∅ s.I isLowerSet_empty s.isLowerSet (Set.empty_subset _)
  have h2 := hmono (insert s.q s.I) Set.univ (Proofs.insert_isLowerSet s) isLowerSet_univ (Set.subset_univ _)
  rw [(sec3_endpoints P).1] at h1
  rw [(sec3_endpoints P).2] at h2
  omega

/-- **P9** (v2.10 l. 867): "As `P` contains `X`, we have `n ≥ 5`" (`n = |P|`). -/
theorem sec5_contains_X_five_le (P : Type*) [Fintype P] [PartialOrder P] (hX : ContainsX P) :
    5 ≤ Fintype.card P :=
  sec5_contains_X_five_le_proved P hX

/-- Theorem 4.1, as stated in the introduction (lines 112–115; also the abstract, lines 47–50, and the table, lines
150–152): for `2 ≤ k ≤ n − 1`, `C(P)` has at least `C(n−3, k−2)` more `k`-faces than `O(P)`. -/
theorem thm_4_1_binom (P : Type*) [Fintype P] [PartialOrder P] (hX : ContainsX P) (k : ℕ) (hk2 : 2 ≤ k)
    (_hkn : k ≤ Fintype.card P - 1) :
    fNum (orderPolytope P) k + Nat.choose (Fintype.card P - 3) (k - 2) ≤ fNum (chainPolytope P) k := by
  have h := thm_4_1 P hX k
  simp only [Proofs.gapPoly_coeff, hk2, ↓reduceIte] at h
  omega


/-! ### Section 4: coverage rows (review REVIEW_006_cov, 20261028) -/

/-- **Lemma 4.2, proof steps** (v2.10 l. 595-629), under the v2.10 hypothesis of Lemma 4.2 for the
given `N, S₁, S₂, T₁, T₂, φ, ψ` (the body of `lemma_4_2_v190`'s hypothesis, unbundled): `S_w = S₁ ∩ S₂` is an
`(e−1)`-cell of `S` with `w` in its relative interior, carrier `E` and affine span `H_S` (l. 595-602), and the same for
`T_w = T₁ ∩ T₂` with `H_T`; `R_w = S_w ∩ T_w` is an `(e−2)`-cell of `R` with `w` in its relative interior, in no `R(Y)`
(l. 604-611; by uniqueness of the cell whose relative interior contains `w`, as in the paper);
`|R(S_w)| ≥ 2`, `|R(T_w)| ≥ 2` (l. 614-620); the four `S_i ∩ T_j` are `e`-cells of `R|_E` (l. 625-629). -/
theorem lemma_4_2_steps {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (w : s.P' → ℝ) (hw : w ∈ intrinsicInterior ℝ E) (N S₁ S₂ T₁ T₂ : Set (s.P' → ℝ))
    (φ ψ : (s.P' → ℝ) →ₗ[ℝ] ℝ)
    (H : Convex ℝ N ∧ N ⊆ E ∧
      (∃ O : Set (s.P' → ℝ), IsOpen O ∧ N = O ∩ (affineSpan ℝ E : Set (s.P' → ℝ))) ∧ w ∈ N ∧
        S₁ ∈ s.topCells s.cellsS E ∧ S₂ ∈ s.topCells s.cellsS E ∧
        T₁ ∈ s.topCells s.cellsT E ∧ T₂ ∈ s.topCells s.cellsT E ∧
        (∀ A ∈ s.topCells s.cellsS E, (A ∩ N).Nonempty → A = S₁ ∨ A = S₂) ∧
        (∀ D ∈ s.topCells s.cellsT E, (D ∩ N).Nonempty → D = T₁ ∨ D = T₂) ∧
        S₁ ∩ N = {u ∈ N | φ w ≤ φ u} ∧ S₂ ∩ N = {u ∈ N | φ u ≤ φ w} ∧
        T₁ ∩ N = {u ∈ N | ψ w ≤ ψ u} ∧ T₂ ∩ N = {u ∈ N | ψ u ≤ ψ w} ∧
        φ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧ ψ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧
        {u | u ∈ affineSpan ℝ E ∧ φ u = φ w} ≠ {u | u ∈ affineSpan ℝ E ∧ ψ u = ψ w}) :
    S₁ ∩ S₂ ∈ s.cellsS ∧ adim (S₁ ∩ S₂) + 1 = adim E ∧ w ∈ intrinsicInterior ℝ (S₁ ∩ S₂) ∧
      IsCarrier s.B E (S₁ ∩ S₂) ∧
      (affineSpan ℝ (S₁ ∩ S₂) : Set _) = {u | u ∈ affineSpan ℝ E ∧ φ u = φ w} ∧
    T₁ ∩ T₂ ∈ s.cellsT ∧ adim (T₁ ∩ T₂) + 1 = adim E ∧ w ∈ intrinsicInterior ℝ (T₁ ∩ T₂) ∧
      IsCarrier s.B E (T₁ ∩ T₂) ∧
      (affineSpan ℝ (T₁ ∩ T₂) : Set _) = {u | u ∈ affineSpan ℝ E ∧ ψ u = ψ w} ∧
    (S₁ ∩ S₂) ∩ (T₁ ∩ T₂) ∈ s.cellsR ∧ adim ((S₁ ∩ S₂) ∩ (T₁ ∩ T₂)) + 2 = adim E ∧
      w ∈ intrinsicInterior ℝ ((S₁ ∩ S₂) ∩ (T₁ ∩ T₂)) ∧
      (∀ Y, (Y ∈ s.cellsS ∨ Y ∈ s.cellsT) → IsCarrier s.B E Y → adim Y + 2 = adim E →
        (S₁ ∩ S₂) ∩ (T₁ ∩ T₂) ∉ s.RR Y) ∧
    2 ≤ (s.RR (S₁ ∩ S₂)).ncard ∧ 2 ≤ (s.RR (T₁ ∩ T₂)).ncard ∧
    S₁ ∩ T₁ ∈ s.topCells s.cellsR E ∧ S₁ ∩ T₂ ∈ s.topCells s.cellsR E ∧
    S₂ ∩ T₁ ∈ s.topCells s.cellsR E ∧ S₂ ∩ T₂ ∈ s.topCells s.cellsR E :=
  Proofs.lemma_4_2_steps_proved s E hE w hw N S₁ S₂ T₁ T₂ φ ψ H

/-- **Lemma 4.3, proof** (v2.10 l. 693-695): "As `P` is finite, every `r > q` satisfies `r ≥ s` for an upper cover
`s` of `q` (a minimal element of `{s' : q < s' ≤ r}`)". -/
theorem sec4_upper_cover_below {P : Type*} [Fintype P] [PartialOrder P] (q r : P) (h : q < r) :
    ∃ s', q ⋖ s' ∧ s' ≤ r := by
  exact Proofs.sec4_upper_cover_below q r h

/-- Section 4.2 (v2.10 l. 708-710): "The coordinates of `B` are `x_p` for `p ∈ I` and `y_r` for `r ∈ J' = J ∖ {q}`;
every `r ∈ J'` satisfies `r > q`". -/
theorem sec4_remaining_above_q {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∀ r : x.toSwitch.P', r.1 ∉ x.toSwitch.I → x.q < r.1 := by
  exact Proofs.sec4_remaining_above_q x

/-- **Lemma 4.4 and Lemma 4.5, proofs** (v2.10 l. 729-730: "unless `r' ∈ {g', h'}`, which is impossible, as
`q < r < r'` and `g', h'` cover `q`"; l. 770-771: "no `r ∈ J'` satisfies `r < g'` (`q < r`, and `g'` covers `q`)"):
no `r ∈ J'` lies below `g'` or `h'`. -/
theorem sec4_no_remaining_below_covers {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∀ r : P, r ∉ x.toSwitch.I → r ≠ x.q → ¬ r < x.g' ∧ ¬ r < x.h' := by
  exact Proofs.sec4_no_remaining_below_covers x

/-- **Lemma 4.6** (v2.10 l. 792-795) with the v2.10 wording of the hypothesis of Lemma 4.2 (l. 580-590): for every face
`E ⊇ E₀` of `B` there are `w ∈ relint E` and "some convex set `N ⊆ E`, open in `aff(E)` and containing `w`", with the
cells meeting `N` among `S₁, S₂` and `T₁, T₂`, the half-space description, and `H_S`, `H_T` hyperplanes of `aff(E)`
through `w` with `H_S ≠ H_T` — exactly the hypothesis `hN` of `lemma_4_2_v190`. -/
theorem lemma_4_6_v190 {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) (E : Set (x.toSwitch.P' → ℝ))
    (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E) :
    ∃ w ∈ intrinsicInterior ℝ E, ∃ N : Set (x.toSwitch.P' → ℝ), Convex ℝ N ∧ N ⊆ E ∧
      (∃ O : Set (x.toSwitch.P' → ℝ), IsOpen O ∧ N = O ∩ (affineSpan ℝ E : Set (x.toSwitch.P' → ℝ))) ∧ w ∈ N ∧
      ∃ (S₁ S₂ T₁ T₂ : Set (x.toSwitch.P' → ℝ)) (φ ψ : (x.toSwitch.P' → ℝ) →ₗ[ℝ] ℝ),
        S₁ ∈ x.toSwitch.topCells x.toSwitch.cellsS E ∧ S₂ ∈ x.toSwitch.topCells x.toSwitch.cellsS E ∧
        T₁ ∈ x.toSwitch.topCells x.toSwitch.cellsT E ∧ T₂ ∈ x.toSwitch.topCells x.toSwitch.cellsT E ∧
        (∀ A ∈ x.toSwitch.topCells x.toSwitch.cellsS E, (A ∩ N).Nonempty → A = S₁ ∨ A = S₂) ∧
        (∀ D ∈ x.toSwitch.topCells x.toSwitch.cellsT E, (D ∩ N).Nonempty → D = T₁ ∨ D = T₂) ∧
        S₁ ∩ N = {u ∈ N | φ w ≤ φ u} ∧ S₂ ∩ N = {u ∈ N | φ u ≤ φ w} ∧
        T₁ ∩ N = {u ∈ N | ψ w ≤ ψ u} ∧ T₂ ∩ N = {u ∈ N | ψ u ≤ ψ w} ∧
        φ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧ ψ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧
        {u | u ∈ affineSpan ℝ E ∧ φ u = φ w} ≠ {u | u ∈ affineSpan ℝ E ∧ ψ u = ψ w} :=
  Proofs.Cov1.lemma_4_6_v190_proved x E hE hE0

open Classical Filter Topology in
/-- v2.10 l.803-809,815-817,834-835: "for such maximal forms mu_a, mu_b of the two families, lambda_a=mu_a and lambda_b=mu_b ... near zeta"; "the two terms of the maximum ... are equal, and so are the two terms of the minimum"; "E contains a segment through w in the alpha-direction, so phi_1 is not identically phi_2 on aff(E)". The gamma segment and the linear-form clause are retained. -/
theorem lemma_4_6_point {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)
    (E : Set (x.toSwitch.P' → ℝ)) (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E) :
    ∃ w ∈ intrinsicInterior ℝ E,
      w x.pa + x.lamA w = w x.pb + x.lamB w ∧ w x.pg = w x.ph ∧
      (∃ ε > 0, ∀ t : ℝ, |t| < ε → w + t • Pi.single x.pa 1 ∈ E ∧ w + t • Pi.single x.pg 1 ∈ E) ∧
      (∃ μa μb : ({p // p ∉ x.special} → ℝ) →ₗ[ℝ] ℝ,
        ∀ᶠ u in 𝓝[E] w, x.lamA u = μa (x.zeta u) ∧ x.lamB u = μb (x.zeta u)) ∧
      ∃ Ka ∈ x.toSwitch.lowBranches, x.pa ∈ Ka ∧
        ∃ Kb ∈ x.toSwitch.lowBranches, x.pb ∈ Kb ∧
          (∀ᶠ u in 𝓝[E] w, x.lamA u = x.toSwitch.chainSum (Ka.erase x.pa) u ∧
            x.lamB u = x.toSwitch.chainSum (Kb.erase x.pb) u) ∧
          (∃ u ∈ affineSpan ℝ E,
            u x.pa + x.toSwitch.chainSum (Ka.erase x.pa) u ≠
              u x.pb + x.toSwitch.chainSum (Kb.erase x.pb) u) :=
  Proofs.lemma_4_6_point_full x E hE hE0

open Classical Filter Topology in
/-- **Lemma 4.7, proof** (v2.10 l. 852-855): "at least `C(s, κ+1)` of the `κ`-faces lie in `D` (the faces of `D`, an
`(s−1)`-polytope); the vertex figure of `v` is an `(s−1)`-polytope whose `(κ−1)`-faces correspond to the `κ`-faces
that contain `v` [Ziegler, Proposition 2.4], so at least `C(s, κ)` of the `κ`-faces contain `v`" (`D` a facet,
`v` a vertex, `s = dim Q`; for `κ = 0` the face `{v}` itself counts). -/
theorem lemma_4_7_facet_counts {ι : Type*} [Fintype ι] (Q D : Set (ι → ℝ))
    (hQ : IsPolytope Q) (hD : IsFace Q D) (facet : adim D + 1 = adim Q)
    (v : ι → ℝ) (hv : IsFace Q {v}) (κ : ℕ) :
    Nat.choose (adim Q) (κ + 1) ≤ {F | IsFace Q F ∧ adim F = κ ∧ F ⊆ D}.ncard ∧
    Nat.choose (adim Q) κ ≤ {F | IsFace Q F ∧ adim F = κ ∧ v ∈ F}.ncard :=
  Proofs.lemma_4_7_facet_counts_all Q D hQ hD facet v hv κ

/-- **Lemma 4.7, proof** (v2.10 l. 855): "no face lies in `D` and contains `v`" (`v ∉ D`). -/
theorem sec4_facet_families_disjoint {ι : Type*} [Fintype ι] (Q D : Set (ι → ℝ))
    (v : ι → ℝ) (outside : v ∉ D) (κ : ℕ) :
    Disjoint {F | IsFace Q F ∧ adim F = κ ∧ F ⊆ D} {F | IsFace Q F ∧ adim F = κ ∧ v ∈ F} := by
  exact Proofs.sec4_facet_families_disjoint Q D v outside κ

/-- **Section 4.4** (v2.10 l. 876-877), the displayed identity
`∑_{e=4}^{n-1} C(n-5, e-4) t^{e-2}(1+t)² = t²(1+t)^{n-3}` (as polynomials in `t = X`). -/
theorem sec4_sum_identity (n : ℕ) (hn : 5 ≤ n) :
    ∑ e ∈ Finset.Icc 4 (n - 1), (Nat.choose (n - 5) (e - 4) : ℤ[X]) * (X ^ (e - 2) * (1 + X) ^ 2) =
      X ^ 2 * (1 + X) ^ (n - 3) :=
  Proofs.Cov1.sum_identity n hn

/-- v2.10 l. 879-883 and 982-985: for a linear extension `p₁, …, p_n` of `P` (`e i = p_{i+1}`), each prefix
`I_j = {p₁, …, p_j}` is an order ideal and `p_{j+1}` is minimal in `P ∖ I_j`. -/
theorem sec4_linext_prefixes (P : Type*) [Fintype P] [PartialOrder P] (e : Fin (Fintype.card P) ≃ P)
    (he : ∀ i j, e i < e j → i < j) (j : ℕ) (hj : j < Fintype.card P) :
    IsLowerSet {p | (e.symm p : ℕ) < j} ∧ e ⟨j, hj⟩ ∉ {p | (e.symm p : ℕ) < j} ∧
      ∀ p, p < e ⟨j, hj⟩ → (e.symm p : ℕ) < j :=
  Proofs.sec4_linext_prefixes P e he j hj

open Classical Filter Topology in
/-- v2.10 l.882: "Each I_j={p_1,...,p_j} (0 <= j <= n, I_0 empty) is an order ideal". The conclusion holds for every natural j, including j=n and n=0. -/
theorem sec4_linext_prefix_isLowerSet {P : Type*} [Fintype P] [PartialOrder P]
    (e : Fin (Fintype.card P) ≃ P) (he : ∀ i j, e i < e j → i < j) (j : ℕ) :
    IsLowerSet {p | (e.symm p : ℕ) < j} :=
  Proofs.sec4_linext_prefix_isLowerSet e he j

/-- v2.10 l. 879-883 (Section 4.4): a linear extension of `I`, then `q`, then a linear extension of `J'` is a linear
extension of `P`: some linear extension has `I_{j₀} = I` and `p_{j₀+1} = q`. -/
theorem sec4_linext_through_switch {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∃ (e : Fin (Fintype.card P) ≃ P) (j₀ : ℕ) (hj₀ : j₀ < Fintype.card P), (∀ i j, e i < e j → i < j) ∧
      {p | (e.symm p : ℕ) < j₀} = x.toSwitch.I ∧ e ⟨j₀, hj₀⟩ = x.q :=
  Proofs.sec4_linext_through_switch x

/-! ## Section 5 (sharpness and the equality part) -/

open Classical Filter Topology in
/-- v2.10 l.879-881: "Now concatenate a linear extension of I, then q, then a linear extension of J'; as I is an order ideal and q=min J, this is a linear extension ... of P." -/
theorem sec4_linext_concat {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (e : Fin (Fintype.card P) ≃ P)
    (hI : ∀ i, e i ∈ s.I ↔ (i : ℕ) < s.I.ncard)
    (hq : (e.symm s.q : ℕ) = s.I.ncard)
    (heI : ∀ i j, e i ∈ s.I → e j ∈ s.I → e i < e j → i < j)
    (heJ : ∀ i j, e i ∉ s.I → e j ∉ s.I → e i ≠ s.q → e j ≠ s.q → e i < e j → i < j) :
    ∀ i j, e i < e j → i < j :=
  Proofs.sec4_linext_concat s e hI hq heI heJ

/-- **Proposition 5.1** (lines 894–896): `F_C(X) − F_O(X) = t^2 + 2t^3 + t^4`. -/
theorem prop_5_1 :
    facePoly (chainPolytope XElem) - facePoly (orderPolytope XElem) = X ^ 2 + 2 * X ^ 3 + X ^ 4 := by
  ext k
  rw [coeff_sub, Proofs.facePoly_coeff, Proofs.facePoly_coeff, (ex_2_1 k).1, (ex_2_1 k).2]
  rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [coeff_X_pow]

/-- Proof of Proposition 5.1 "by hand" (lines 898–903), the switches other than `c` along `a, b, c, g, h`: at a
switch of `a` or `b`, `L ≡ 0` on `B`; at a switch of `g` or `h`, `U ≡ 1` on `B`; and every switch of an element
other than `c` leaves the face polynomial unchanged. -/
theorem prop_5_1_other_switches (s : Switch XElem) :
    ((s.q = XElem.a ∨ s.q = XElem.b) → ∀ u ∈ s.B, s.L u = 0) ∧
    ((s.q = XElem.g ∨ s.q = XElem.h) → ∀ u ∈ s.B, s.U u = 1) ∧
    (s.q ≠ XElem.c → facePoly (chainOrderPolytope XElem (insert s.q s.I)) = facePoly (chainOrderPolytope XElem s.I)) :=
  prop_5_1_other_switches_of s (Cited.fourier_lemma_4_1 s)

/-- **P10** (v2.10 l. 341-342 and l. 899-903): "At the switch of `p₁` (from `I = ∅` to `I = {p₁}`) we have `L ≡ 0`, so
the two polytopes of Proposition [fibres] coincide: `O_{p₁}(P) = O(P)`, with `x_{p₁} = v_{p₁}`"; and "no element of `I`
lies below the switched element, so `L ≡ 0` is affine on `B`. Hence `S` consists of the faces of `B`, so `F_S = F_B`;
and `R = T`, as each cell `F ∩ T` (`F` a face of `B`, `T ∈ T`) is a face of `T`. So the change is
`F_B + F_T − F_B − F_T = 0`; likewise at `g` and `h`, where `U ≡ 1`", stated for every switch (the change is the right
side `F_B + F_R − F_S − F_T` of Lemma 3.2). -/
theorem sec5_minimal_switch_faces {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    ((∀ p ∈ s.I, ¬ p < s.q) →
      (∀ u, s.L u = 0) ∧ AffineOn s.L s.B ∧ s.cellsS = {C | IsFace s.B C} ∧ cellPoly s.cellsS = facePoly s.B ∧
      s.cellsR = s.cellsT ∧ facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT = 0 ∧
      facePoly (chainOrderPolytope P (insert s.q s.I)) - facePoly (chainOrderPolytope P s.I) = 0) ∧
    ((∀ p : P, ¬ s.q < p) →
      (∀ u, s.U u = 1) ∧ AffineOn s.U s.B ∧ s.cellsT = {C | IsFace s.B C} ∧ cellPoly s.cellsT = facePoly s.B ∧
      s.cellsR = s.cellsS ∧ facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT = 0 ∧
      facePoly (chainOrderPolytope P (insert s.q s.I)) - facePoly (chainOrderPolytope P s.I) = 0) ∧
    (∀ s' : Switch Chain2, s'.I = ∅ → s'.q = 0 →
      (∀ u, s'.L u = 0) ∧ chainOrderPolytope Chain2 (insert s'.q s'.I) = orderPolytope Chain2) :=
  by
    obtain ⟨ha, hb, hc⟩ := sec5_minimal_switch_faces_proved s
    refine ⟨fun h => ?_, fun h => ?_, hc⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ha h
      exact ⟨h1, h2, h3, h4, h5, h6, (Cited.fourier_lemma_4_1 s).trans h6⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb h
      exact ⟨h1, h2, h3, h4, h5, h6, (Cited.fourier_lemma_4_1 s).trans h6⟩

/-- Proof of Proposition 5.1 "by hand" (lines 905–937) and Figure 2 (lines 657–671): the switch of `c` in `X` exists;
for it `E₀ = B`, only the carrier `B` contributes, `S` and `T` each have two 4-cells and one 3-cell with carrier `B`,
`R` has four 4-cells, four 3-cells and one 2-cell with carrier `B`, and `δ_B = t^2 + 2t^3 + t^4`. -/
theorem prop_5_1_c_switch :
    Nonempty (XSwitch XElem) ∧ ∀ x : XSwitch XElem, x.q = XElem.c ∧ x.E0 = x.toSwitch.B ∧
      (∀ E, IsFace x.toSwitch.B E → E ≠ x.toSwitch.B → x.toSwitch.delta E = 0) ∧
      (∀ k, x.toSwitch.carrierNum x.toSwitch.cellsS x.toSwitch.B k = if k = 4 then 2 else if k = 3 then 1 else 0) ∧
      (∀ k, x.toSwitch.carrierNum x.toSwitch.cellsT x.toSwitch.B k = if k = 4 then 2 else if k = 3 then 1 else 0) ∧
      (∀ k, x.toSwitch.carrierNum x.toSwitch.cellsR x.toSwitch.B k =
        if k = 4 then 4 else if k = 3 then 4 else if k = 2 then 1 else 0) ∧
      x.toSwitch.delta x.toSwitch.B = X ^ 2 + 2 * X ^ 3 + X ^ 4 :=
  prop_5_1_c_switch_proved

open Example21 in
/-- **P11** (v2.10 l. 921-925), the switch of `c` in `X`: "here `L = max(0, α, β)`, and `A_0 = B ∩ {α = β = 0}` is not
full-dimensional; likewise `U = min(γ, η, 1)`, and `A_1 = B ∩ {γ = η = 1}`" (`A_0` is the domain of the empty chain,
`A_1` the domain of the constant branch `1`; neither is full-dimensional). -/
theorem sec5_center_A0_A1 :
    let s := CenterResult.center
    let α : (s.P' → ℝ) → ℝ := fun u => u CenterSwitch.canonical.pa
    let β : (s.P' → ℝ) → ℝ := fun u => u CenterSwitch.canonical.pb
    let γ : (s.P' → ℝ) → ℝ := fun u => u CenterSwitch.canonical.pg
    let η : (s.P' → ℝ) → ℝ := fun u => u CenterSwitch.canonical.ph
    (∀ u, s.L u = max 0 (max (α u) (β u))) ∧
    s.domL ∅ = {u | u ∈ s.B ∧ α u = 0 ∧ β u = 0} ∧ adim (s.domL ∅) ≠ Fintype.card s.P' ∧
    (∀ u, s.U u = min (min (γ u) (η u)) 1) ∧
    s.domU none = {u | u ∈ s.B ∧ γ u = 1 ∧ η u = 1} ∧ adim (s.domU none) ≠ Fintype.card s.P' := by
  intro s α β γ η
  exact sec5_center_A0_A1_proved

open HibiLi.Proofs.Cov200 in
/-- **Section 5** (v2.10 l. 932): "A cell `S ∩ T` of `R` has carrier `B` only if `S` and `T` do." Stated for every
switch, every cell `S` of `S` and `T` of `T`. -/
theorem sec5_RT_carrier {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) {S T : Set (s.P' → ℝ)}
    (hS : S ∈ s.cellsS) (hT : T ∈ s.cellsT) (h : IsCarrier s.B s.B (S ∩ T)) :
    IsCarrier s.B s.B S ∧ IsCarrier s.B s.B T :=
  RT_carrier_proved s hS hT h

open HibiLi.Proofs.Cov200 in
open HibiLi.Example21 HibiLi.Example21.CenterGeometry in
/-- **Figure 2** (v2.10 l. 665-667): "The function `L` is affine on no neighborhood of a point with `ξ = 0` (these points
lie in the `3`-cell `B ∩ {α = β}` of `S`, blue), and `U` is affine on no neighborhood of a point with `ω = 0`". In the
figure's slice `Π = {α + β = 1/2, γ + η = 3/2}` of `B` (the switch of `c` in `X`): for every point `v` of `B ∩ Π` with
`ξ = α - β = 0` and every `ε > 0`, `L` is not affine on `B ∩ Π ∩ ball(v, ε)`; likewise `U` at `ω = γ - η = 0`. (Not
affine on these slice neighbourhoods implies not affine on any neighbourhood of `v` in `B`.) -/
theorem fig2_L_not_affine_near :
    (∀ v : Coord → ℝ, v ∈ center.B → v CenterSwitch.canonical.pa + v CenterSwitch.canonical.pb = 1 / 2 →
      v CenterSwitch.canonical.pg + v CenterSwitch.canonical.ph = 3 / 2 →
      v CenterSwitch.canonical.pa = v CenterSwitch.canonical.pb → ∀ ε > 0,
      ¬ AffineOn center.L {u | u ∈ center.B ∧ u CenterSwitch.canonical.pa + u CenterSwitch.canonical.pb = 1 / 2 ∧
        u CenterSwitch.canonical.pg + u CenterSwitch.canonical.ph = 3 / 2 ∧ dist u v < ε}) ∧
    (∀ v : Coord → ℝ, v ∈ center.B → v CenterSwitch.canonical.pa + v CenterSwitch.canonical.pb = 1 / 2 →
      v CenterSwitch.canonical.pg + v CenterSwitch.canonical.ph = 3 / 2 →
      v CenterSwitch.canonical.pg = v CenterSwitch.canonical.ph → ∀ ε > 0,
      ¬ AffineOn center.U {u | u ∈ center.B ∧ u CenterSwitch.canonical.pa + u CenterSwitch.canonical.pb = 1 / 2 ∧
        u CenterSwitch.canonical.pg + u CenterSwitch.canonical.ph = 3 / 2 ∧ dist u v < ε}) :=
  ⟨fun v hv ha hg hξ _ hε => L_not_affine_near_proved v hv ha hg hξ hε,
    fun v hv ha hg hω _ hε => U_not_affine_near_proved v hv ha hg hω hε⟩

open HibiLi.Proofs.Fig2B in
open HibiLi.Example21 HibiLi.Example21.CenterGeometry in
/-- **Figure 2** (v2.10 l. 665-667), strict reading: "The function `L` is affine on no neighborhood of a point with
`ξ = 0` ..., and `U` is affine on no neighborhood of a point with `ω = 0`". For EVERY point `v` of `B` (the switch of `c`
in `X`, coordinates `α, β, γ, η`, l. 659-661) with `ξ = α - β = 0` and every `ε > 0`, `L` is not affine on the
neighbourhood `B ∩ ball(v, ε)` of `v` in `B`; likewise `U` at every point of `B` with `ω = γ - η = 0`. (The row
`fig2_L_not_affine_near` is the same claim for neighbourhoods inside the figure's slice plane.) -/
theorem fig2_not_affine_near_B :
    (∀ v ∈ center.B, v CenterSwitch.canonical.pa = v CenterSwitch.canonical.pb → ∀ ε > 0,
      ¬ AffineOn center.L {u | u ∈ center.B ∧ dist u v < ε}) ∧
    (∀ v ∈ center.B, v CenterSwitch.canonical.pg = v CenterSwitch.canonical.ph → ∀ ε > 0,
      ¬ AffineOn center.U {u | u ∈ center.B ∧ dist u v < ε}) :=
  ⟨fun v hv hξ _ hε => L_not_affine_near_B_proved v hv hξ hε,
    fun v hv hω _ hε => U_not_affine_near_B_proved v hv hω hε⟩

/-- **Proposition 5.1**, proof, v2.10 l. 913-921, for every switch and every face `E` of `B`: if `L` is affine on `E`,
then `E` is a cell of `S` (l. 916), `S|_E` consists of the (nonempty) faces of `E`, `E` is the only cell of `S` with
carrier `E`, `R|_E = T|_E`, and `δ_{E,k} = 0` for all `k`; the same with `U`, `T` and `S` exchanged. -/
theorem sec5_affine_face {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) :
    (AffineOn s.L E → E ∈ s.cellsS ∧
      s.restrict s.cellsS E = {C | IsFace E C} ∧
      (∀ C ∈ s.cellsS, IsCarrier s.B E C → C = E) ∧
      s.restrict s.cellsR E = s.restrict s.cellsT E ∧
      ∀ k, s.deltaCoeff E k = 0) ∧
    (AffineOn s.U E → E ∈ s.cellsT ∧
      s.restrict s.cellsT E = {C | IsFace E C} ∧
      (∀ C ∈ s.cellsT, IsCarrier s.B E C → C = E) ∧
      s.restrict s.cellsR E = s.restrict s.cellsS E ∧
      ∀ k, s.deltaCoeff E k = 0) := by
  refine ⟨fun hL => ?_, fun hU => ?_⟩
  · have hES := B3.mem_cellsS_of_affineOn s hE hL
    exact ⟨hES, B3.restrict_cellsS_eq_faces s hES, fun C hC hcar => B3.carrier_eq_of_cellsS s hE hES hC hcar,
      B3.restrict_cellsR_eq_T s hE hES, fun k => B3.deltaCoeff_eq_zero_of_S s hE hES k⟩
  · have hET := B3.mem_cellsT_of_affineOn s hE hU
    exact ⟨hET, B3.restrict_cellsT_eq_faces s hET, fun C hC hcar => B3.carrier_eq_of_cellsT s hE hET hC hcar,
      B3.restrict_cellsR_eq_S s hE hET, fun k => B3.deltaCoeff_eq_zero_of_T s hE hET k⟩

open Example21 in
/-- Proposition 5.1, switch of `c` in `X` (paper v2.10 l. 908-914): every proper face of `B` lies in one of the
eight hyperplanes `α = 0, β = 0, γ = 1, η = 1, α = γ, α = η, β = γ, β = η`; on the first four `L` or `U` is affine; on the
other four `L` and `U` are both affine (for example, on `α = γ`, `L = α` and `U = γ`; Lean also states `L = U` there);
so on every proper face `E` of `B`, `L` or `U` is affine. -/
theorem prop_5_1_proper_faces_affine :
    let s := CenterResult.center
    let α : (s.P' → ℝ) → ℝ := fun u => u CenterSwitch.canonical.pa
    let β : (s.P' → ℝ) → ℝ := fun u => u CenterSwitch.canonical.pb
    let γ : (s.P' → ℝ) → ℝ := fun u => u CenterSwitch.canonical.pg
    let η : (s.P' → ℝ) → ℝ := fun u => u CenterSwitch.canonical.ph
    (∀ E, IsFace s.B E → E ≠ s.B →
      E ⊆ {u | α u = 0} ∨ E ⊆ {u | β u = 0} ∨ E ⊆ {u | γ u = 1} ∨ E ⊆ {u | η u = 1} ∨
      E ⊆ {u | α u = γ u} ∨ E ⊆ {u | α u = η u} ∨ E ⊆ {u | β u = γ u} ∨ E ⊆ {u | β u = η u}) ∧
    AffineOn s.L {u | u ∈ s.B ∧ α u = 0} ∧ AffineOn s.L {u | u ∈ s.B ∧ β u = 0} ∧
    AffineOn s.U {u | u ∈ s.B ∧ γ u = 1} ∧ AffineOn s.U {u | u ∈ s.B ∧ η u = 1} ∧
    (∀ u ∈ s.B, (α u = γ u ∨ α u = η u ∨ β u = γ u ∨ β u = η u) → s.L u = s.U u) ∧
    (AffineOn s.L {u | u ∈ s.B ∧ α u = γ u} ∧ AffineOn s.U {u | u ∈ s.B ∧ α u = γ u}) ∧
    (AffineOn s.L {u | u ∈ s.B ∧ α u = η u} ∧ AffineOn s.U {u | u ∈ s.B ∧ α u = η u}) ∧
    (AffineOn s.L {u | u ∈ s.B ∧ β u = γ u} ∧ AffineOn s.U {u | u ∈ s.B ∧ β u = γ u}) ∧
    (AffineOn s.L {u | u ∈ s.B ∧ β u = η u} ∧ AffineOn s.U {u | u ∈ s.B ∧ β u = η u}) ∧
    (∀ E, IsFace s.B E → E ≠ s.B → AffineOn s.L E ∨ AffineOn s.U E) := by
  intro s α β γ η
  exact ⟨fun _ hE hne => B2.proper_face_hyperplane hE hne, B2.L_alpha, B2.L_beta, B2.U_gamma, B2.U_eta,
    fun _ hu h => B2.L_eq_U hu h, B2.LU_alpha_gamma, B2.LU_alpha_eta, B2.LU_beta_gamma, B2.LU_beta_eta,
    fun _ hE hne => B2.proper_face_affine hE hne⟩

open Example21 Example21.CenterRegions Example21.NamedCells Example21.CenterGeometry in
/-- **Proposition 5.1**, proof, switch of `c` in `X`, v2.10 l. 925-929: "The cells with carrier `B` are: in `S`, two
`4`-cells and the `3`-cell `B ∩ {α = β}`; in `T`, two `4`-cells and the `3`-cell `B ∩ {γ = η}`; in `R`, four `4`-cells,
four `3`-cells and the `2`-cell `B ∩ {α = β, γ = η}`". Stated in the coordinates `(α, β, γ, η) = (x_a, x_b, y_g, y_h)`
(`canonicalEquiv`, an affine bijection, which keeps dimensions: last conjunct), with every cell named. -/
theorem prop_5_1_cells_with_carrier_B :
    (fun C => canonicalEquiv '' C) '' {C | C ∈ center.cellsS ∧ IsCarrier center.B center.B C} =
      {body (some false) none, body (some true) none, wallS} ∧
    (fun C => canonicalEquiv '' C) '' {C | C ∈ center.cellsT ∧ IsCarrier center.B center.B C} =
      {body none (some false), body none (some true), wallT} ∧
    (fun C => canonicalEquiv '' C) '' {C | C ∈ center.cellsR ∧ IsCarrier center.B center.B C} =
      Set.range (fun p : Bool × Bool => quad p.1 p.2) ∪ Set.range half ∪ {corner} ∧
    adim wallS = 3 ∧ adim wallT = 3 ∧ (∀ l u, adim (quad l u) = 4) ∧ (∀ i, adim (half i) = 3) ∧
      adim corner = 2 ∧ (∀ C : Set (Coord → ℝ), adim (canonicalEquiv '' C) = adim C) :=
  NamedCells.center_cells_with_carrier_B

open Example21 Example21.CenterRegions Example21.NamedCells Example21.CenterGeometry in
/-- **Figure 2** caption, v2.10 l. 660-670: the slice of `B` by the plane `{α + β = 1/2, γ + η = 3/2}` through
`u₀ = (1/4, 1/4, 3/4, 3/4)`, in the coordinates `ξ = α − β`, `ω = γ − η`, is the square `|ξ|, |ω| ≤ 1/2`; "the point
`u₀`, the four half-axes and the four quadrants are the slices of the `2`-, `3`- and `4`-dimensional cells of `R` with
carrier `B`" (the cells named in `prop_5_1_cells_with_carrier_B`).  `base` is the image of `B` in the `Fin 4`
coordinates (first conjunct), so these are slices of `B`. -/
theorem fig2_slices :
    canonicalEquiv '' center.B = base ∧ u0 ∈ slicePlane ∧ sliceCoords u0 = (0, 0) ∧
    sliceCoords '' (base ∩ slicePlane) = {x | |x.1| ≤ 1/2 ∧ |x.2| ≤ 1/2} ∧
    (∀ l u : Bool, sliceCoords '' (quad l u ∩ slicePlane) =
      {x | |x.1| ≤ 1/2 ∧ |x.2| ≤ 1/2 ∧ (if l then 0 ≤ x.1 else x.1 ≤ 0) ∧ (if u then 0 ≤ x.2 else x.2 ≤ 0)}) ∧
    (∀ u : Bool, sliceCoords '' (halfS u ∩ slicePlane) =
      {x | x.1 = 0 ∧ |x.2| ≤ 1/2 ∧ (if u then 0 ≤ x.2 else x.2 ≤ 0)}) ∧
    (∀ l : Bool, sliceCoords '' (halfT l ∩ slicePlane) =
      {x | x.2 = 0 ∧ |x.1| ≤ 1/2 ∧ (if l then 0 ≤ x.1 else x.1 ≤ 0)}) ∧
    sliceCoords '' (corner ∩ slicePlane) = {(0, 0)} :=
  ⟨CenterGeometry.image_B, NamedCells.fig2_slices⟩

open Example21 Example21.CenterRegions Example21.NamedCells Example21.CenterGeometry in
/-- **Figure 2** caption, v2.10 l. 665-666, for bands: `L = max(α, β)` is not affine on any band `|α − β| ≤ t`
(`0 < t ≤ 1/2`) of the slice (the caption's stronger "affine on no neighborhood of a point with `ξ = 0`" is the row
`fig2_not_affine_near_B`). -/
theorem fig2_L_not_affine_band (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    ¬ AffineOn center.L {u | u ∈ center.B ∧ u CenterSwitch.canonical.pa + u CenterSwitch.canonical.pb = 1 / 2 ∧
      u CenterSwitch.canonical.pg + u CenterSwitch.canonical.ph = 3 / 2 ∧
      |u CenterSwitch.canonical.pa - u CenterSwitch.canonical.pb| ≤ t} :=
  NamedCells.center_L_not_affine_across t ht ht'

open Example21 Example21.CenterRegions Example21.NamedCells Example21.CenterGeometry in
/-- **Figure 2** caption, v2.10 l. 666-667, for bands: `U = min(γ, η)` is not affine on any band `|γ − η| ≤ t` of
the slice (the caption's stronger "affine on no neighborhood of a point with `ω = 0`" is the row
`fig2_not_affine_near_B`). -/
theorem fig2_U_not_affine_band (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    ¬ AffineOn center.U {u | u ∈ center.B ∧ u CenterSwitch.canonical.pa + u CenterSwitch.canonical.pb = 1 / 2 ∧
      u CenterSwitch.canonical.pg + u CenterSwitch.canonical.ph = 3 / 2 ∧
      |u CenterSwitch.canonical.pg - u CenterSwitch.canonical.ph| ≤ t} :=
  NamedCells.center_U_not_affine_across t ht ht'

/-- Figure 2 caption (lines 657–661) and proof of Proposition 5.1 (lines 905–907): for `P = X` (the switch of `c`,
`I = {a, b}`, `J′ = {g, h}`), `L = max(α, β)` and `U = min(γ, η)` on all of `B`. -/
theorem prop_5_1_X_LU : ∀ x : XSwitch XElem,
    x.q = XElem.c ∧ x.toSwitch.I = {XElem.a, XElem.b} ∧ x.toSwitch.Iᶜ \ {x.q} = {XElem.g, XElem.h} ∧
      ({x.a, x.b} : Set XElem) = {XElem.a, XElem.b} ∧ ({x.g', x.h'} : Set XElem) = {XElem.g, XElem.h} ∧
      ∀ u ∈ x.toSwitch.B, x.toSwitch.L u = max (u x.pa) (u x.pb) ∧ x.toSwitch.U u = min (u x.pg) (u x.ph) :=
  Proofs.prop_5_1_X_LU_proved

section
local instance : DecidableLT XElem := decidableLTOfDecidableLE

open Polynomial in
/-- v2.10 l. 245-246 and 897-938 (F6): "Proposition 5.1 shows that `F_C(X) − F_O(X) = t^2+2t^3+t^4`", by the proof of
Proposition 5.1 itself. Switch along `a, b, c, g, h` (`O(X) = O_∅(X)`, `C(X) = O_X(X)`); by Lemma 3.2 each switch
changes `F` by the sum of its local terms. The switches of `a`, `b`, `g`, `h` change nothing
(`prop_5_1_other_switches`); for the switch of `c` (`I = {a, b}`) every local term other than `δ_B` is `0` and
`δ_B = t² + 2t³ + t⁴` (`prop_5_1_c_switch`); "adding the five changes gives the claim":
`F_C(X) − F_O(X) = t² + 2t³ + t⁴`. Same statement as `prop_5_1`, by the paper's route: it does not use the
computed face numbers of Example 2.1 (`ex_2_1`), and it uses Fourier's Lemma 4.1 (cited, inside `lemma_3_2`). -/
theorem prop_5_1_by_switches :
    facePoly (chainPolytope XElem) - facePoly (orderPolytope XElem) = X ^ 2 + 2 * X ^ 3 + X ^ 4 := by
  classical
  -- the switch of `c`: its change is `δ_B`
  obtain ⟨⟨x⟩, hc⟩ := prop_5_1_c_switch
  obtain ⟨-, -, hzero, -, -, -, hdelta⟩ := hc x
  obtain ⟨hq, hI, -⟩ := prop_5_1_X_LU x
  have hq' : x.toSwitch.q = XElem.c := hq
  have hBface : IsFace x.toSwitch.B x.toSwitch.B := IsFace.refl (Proofs.B_nonempty x.toSwitch)
  have hother : ∀ E, E ≠ x.toSwitch.B → (∑ᶠ (_ : IsFace x.toSwitch.B E), x.toSwitch.delta E) = 0 := by
    intro E hE
    by_cases hface : IsFace x.toSwitch.B E
    · simp only [finsum_eq_if, hface, ↓reduceIte]
      exact hzero E hface hE
    · simp only [finsum_eq_if, hface, ↓reduceIte]
  have hsum : ∑ᶠ (E : Set (x.toSwitch.P' → ℝ)) (_ : IsFace x.toSwitch.B E), x.toSwitch.delta E =
      x.toSwitch.delta x.toSwitch.B := by
    rw [finsum_eq_single _ x.toSwitch.B hother, finsum_eq_if]
    simp only [hBface, ↓reduceIte]
  have h3 := (lemma_3_2 x.toSwitch).2
  rw [hsum, hdelta, hq', hI] at h3
  -- the switches of `a`, `b`, `g`, `h` change nothing
  have h1 : facePoly (chainOrderPolytope XElem (insert XElem.a ∅)) = facePoly (chainOrderPolytope XElem ∅) :=
    (prop_5_1_other_switches Proofs.AddV170.switchXa).2.2 (by decide)
  have h2 : facePoly (chainOrderPolytope XElem (insert XElem.b {XElem.a})) =
      facePoly (chainOrderPolytope XElem {XElem.a}) :=
    (prop_5_1_other_switches Proofs.AddV170.switchXb).2.2 (by decide)
  have h4 : facePoly (chainOrderPolytope XElem (insert XElem.g {XElem.c, XElem.a, XElem.b})) =
      facePoly (chainOrderPolytope XElem {XElem.c, XElem.a, XElem.b}) :=
    (prop_5_1_other_switches Proofs.AddV170.switchXg).2.2 (by decide)
  have h5 : facePoly (chainOrderPolytope XElem (insert XElem.h {XElem.g, XElem.c, XElem.a, XElem.b})) =
      facePoly (chainOrderPolytope XElem {XElem.g, XElem.c, XElem.a, XElem.b}) :=
    (prop_5_1_other_switches Proofs.AddV170.switchXh).2.2 (by decide)
  -- the ideals along `a, b, c, g, h`
  have e1 : (insert XElem.a ∅ : Set XElem) = {XElem.a} := Set.ext (by decide)
  have e2 : (insert XElem.b {XElem.a} : Set XElem) = {XElem.a, XElem.b} := Set.ext (by decide)
  have e5 : (insert XElem.h {XElem.g, XElem.c, XElem.a, XElem.b} : Set XElem) = Set.univ :=
    Set.eq_univ_of_forall (by decide)
  rw [e1] at h1
  rw [e2] at h2
  rw [← chainOrderPolytope_univ, ← chainOrderPolytope_empty, ← e5]
  linear_combination h5 + h4 + h3 + h2 + h1

end

/-- **Proposition 5.2** (lines 941–946): `P_n` (here `sharpFamily (n−5)`) has `n` elements, contains `X`, and
`F_C(P_n) − F_O(P_n) = t^2 (1+t)^{n−3}`. -/
theorem prop_5_2 (m : ℕ) :
    Fintype.card (sharpFamily m) = m + 5 ∧ ContainsX (sharpFamily m) ∧
    facePoly (chainPolytope (sharpFamily m)) - facePoly (orderPolytope (sharpFamily m)) = gapPoly (m + 5) :=
  prop_5_2_proved m

/-- v2.10 l. 948-959 (F11), proof of Proposition 5.2, with `0̂` the new minimum (l. 942): "the points of `O(P_{m+1})`
with `v_0̂ = θ` are … the points `(θ, θ1 + (1−θ)v')` with `v' ∈ O(P_m)` …, the polytope `O(P_{m+1})` is the pyramid over
`{0} × O(P_m)` with apex `1'`. Every maximal chain of `P_{m+1}` contains `0̂`, … so the section of `C(P_{m+1})` at
`x_0̂ = θ` is `{θ} × (1−θ)C(P_m)`, and, … the polytope `C(P_{m+1})` is the pyramid over `{0} × C(P_m)` with apex the
unit vector `e_0̂`." Here `P_{m+1} = WithBot P_m` (`0̂ = ⊥`; this is how
`sharpFamily (m+1)` is built from `sharpFamily m`), and `O(P_m)`, `C(P_m)` sit in the hyperplane `v_0̂ = 0` by
`bottomLift`. For `0 ≤ θ ≤ 1`: the section of `O` at `v_0̂ = θ` is the set of `θ1 + (1−θ)·lift(w)`, `w ∈ O(P_m)`
(its `0̂` coordinate is `θ`, the others are `θ1 + (1−θ)w`); `O(P_{m+1})` is the convex hull of the apex `1` and the
lifted `O(P_m)`, with the apex off the base's affine hull (a pyramid, as in `sec2_pyramid_faces` and `eq_1_pyramid`);
every maximal chain of `P_{m+1}` contains `0̂`; the section of `C` at `x_0̂ = θ` is the set of `θe_0̂ + (1−θ)·lift(w)`,
`w ∈ C(P_m)` (`0̂` coordinate `θ`, the others `(1−θ)w`); and `C(P_{m+1})` is the pyramid over the lifted `C(P_m)` with
apex `e_0̂` (`1` at `0̂`, `0` elsewhere). Stated for every finite poset `P`, so for every `P_m`. -/
theorem sec5_bottom_pyramids (P : Type*) [Fintype P] [PartialOrder P] :
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      {v | v ∈ orderPolytope (WithBot P) ∧ v ⊥ = θ} =
        (fun w : P → ℝ => θ • orderBottomApex + (1 - θ) • bottomLift w) '' orderPolytope P) ∧
    orderPolytope (WithBot P) = convexHull ℝ (insert orderBottomApex (bottomLift '' orderPolytope P)) ∧
    orderBottomApex ∉ affineSpan ℝ (bottomLift '' orderPolytope P) ∧
    (∀ pp : WithBot P, orderBottomApex (P := P) pp = 1) ∧
    (∀ K : Set (WithBot P), IsMaxChain (· ≤ ·) K → ⊥ ∈ K) ∧
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      {x | x ∈ chainPolytope (WithBot P) ∧ x ⊥ = θ} =
        (fun w : P → ℝ => θ • chainBottomApex + (1 - θ) • bottomLift w) '' chainPolytope P) ∧
    chainPolytope (WithBot P) = convexHull ℝ (insert chainBottomApex (bottomLift '' chainPolytope P)) ∧
    chainBottomApex ∉ affineSpan ℝ (bottomLift '' chainPolytope P) ∧
    chainBottomApex (P := P) ⊥ = 1 ∧ (∀ pp : P, chainBottomApex (P := P) pp = 0) :=
  Proofs.AddV170.bottom_pyramids_proved P

/-- **Theorem 4.1**, attainment (lines 574–576): for every `n ≥ 5`, equality holds for some `n`-element poset `P`
containing `X` (Proposition 5.2). -/
theorem thm_4_1_sharp (n : ℕ) (hn : 5 ≤ n) :
    ∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P), Fintype.card P = n ∧ ContainsX P ∧
      ∀ k, (fNum (chainPolytope P) k : ℤ) - fNum (orderPolytope P) k = (gapPoly n).coeff k := by
  obtain ⟨hcard, hX, hpoly⟩ := prop_5_2 (n - 5)
  have hn : n - 5 + 5 = n := by omega
  rw [hn] at hcard hpoly
  refine ⟨sharpFamily (n - 5), inferInstance, inferInstance, hcard, hX, fun k => ?_⟩
  have := congrArg (fun p => Polynomial.coeff p k) hpoly
  simpa only [coeff_sub, Proofs.facePoly_coeff] using this

/-- v1.70 lines 737–738 (not in v1.80 or v2.10): "For `n = 6`, seven of the sixteen posets containing `X` attain the
bound, `P_6` among them".  The sixteen posets `censusPoset i` (Defs/Census.lean) are a complete, irredundant list of the
6-element posets containing `X` up to isomorphism; exactly seven of them have `F_C − F_O = t²(1+t)³`; one of them is
`P_6 = sharpFamily 1`. -/
theorem sec5_census_n6 :
    (∀ i, Fintype.card (censusPoset i) = 6) ∧
    (∀ i, ContainsX (censusPoset i)) ∧
    (∀ i j, Nonempty (censusPoset i ≃o censusPoset j) → i = j) ∧
    (∀ (P : Type*) [Fintype P] [PartialOrder P], Fintype.card P = 6 → ContainsX P →
        ∃ i, Nonempty (P ≃o censusPoset i)) ∧
    (∃ S : Finset (Fin 16), S.card = 7 ∧ ∀ i, i ∈ S ↔
        facePoly (chainPolytope (censusPoset i)) - facePoly (orderPolytope (censusPoset i)) = gapPoly 6) ∧
    (∃ i, Nonempty (censusPoset i ≃o sharpFamily 1) ∧
        facePoly (chainPolytope (censusPoset i)) - facePoly (orderPolytope (censusPoset i)) = gapPoly 6) :=
  Census.sec5_census_n6_proved

/-- **Corollary 5.3** (lines 967–972): for `2 ≤ k ≤ n − 1`, `f_k(O(P)) = f_k(C(P))` iff `P` does not contain `X`, iff
`O(P)` and `C(P)` are unimodularly equivalent. -/
theorem cor_5_3 (P : Type*) [Fintype P] [PartialOrder P] [DecidableEq P] (k : ℕ) (hk2 : 2 ≤ k)
    (hkn : k ≤ Fintype.card P - 1) :
    (fNum (orderPolytope P) k = fNum (chainPolytope P) k ↔ ¬ ContainsX P) ∧
    (¬ ContainsX P ↔ UnimodEquiv (orderPolytope P) (chainPolytope P)) := by
  refine ⟨⟨fun heq hX => ?_, fun hnX => sec2_unimod_same_fvector _ _ ((thm_2_2 P).mpr hnX) k⟩,
    (thm_2_2 P).symm⟩
  have hgap := thm_4_1_binom P hX k hk2 hkn
  have hpos : 0 < Nat.choose (Fintype.card P - 3) (k - 2) := Nat.choose_pos (by omega)
  omega

/-- **Theorem 1.2** (thm:resolution), v2.10 l. 123-133: for a finite poset `P` with `n ≥ 2` elements,
(a) (Fourier, Theorem 1.1) `f_k(O(P)) ≤ f_k(C(P))` for every `k` (`fourier_thm_1_1`, proved from Proposition 3.7);
(b) for `2 ≤ k ≤ n − 1`, `f_k(O(P)) = f_k(C(P))` iff `O(P)` and `C(P)` are unimodularly equivalent (Corollary 5.3);
(c) `f_1(O(P)) = f_1(C(P))` [HLSS], while `O(P)` and `C(P)` are not unimodularly equivalent if `P` contains `X`
("Theorem 2.2; for `P = X`, see also Example 2.1"), so "part (b) of Conjecture 1.1 fails for `k = 1`, for every poset
that contains `X`": the fourth conjunct is `P = X` (equal edge counts, not equivalent, via the facet numbers), and the
last conjunct is every poset `Q` that contains `X` (by `thm_2_2`). The hypothesis `n ≥ 2` is kept as in the paper; it
is not needed. -/
theorem thm_1_2 (P : Type*) [Fintype P] [PartialOrder P] [DecidableEq P] (_hn : 2 ≤ Fintype.card P) :
    (∀ k, fNum (orderPolytope P) k ≤ fNum (chainPolytope P) k) ∧
    (∀ k, 2 ≤ k → k ≤ Fintype.card P - 1 →
      (fNum (orderPolytope P) k = fNum (chainPolytope P) k ↔ UnimodEquiv (orderPolytope P) (chainPolytope P))) ∧
    fNum (orderPolytope P) 1 = fNum (chainPolytope P) 1 ∧
    (fNum (orderPolytope XElem) 1 = fNum (chainPolytope XElem) 1 ∧
      ¬ UnimodEquiv (orderPolytope XElem) (chainPolytope XElem)) ∧
    (∀ (Q : Type*) [Fintype Q] [PartialOrder Q] [DecidableEq Q], ContainsX Q →
      fNum (orderPolytope Q) 1 = fNum (chainPolytope Q) 1 ∧ ¬ UnimodEquiv (orderPolytope Q) (chainPolytope Q)) :=
  ⟨fourier_thm_1_1 P, fun k hk2 hkn => (cor_5_3 P k hk2 hkn).1.trans (cor_5_3 P k hk2 hkn).2,
    sec1_edges_agree P, ⟨sec1_edges_agree XElem, sec1_X_not_unimod⟩,
    fun Q _ _ _ hX => ⟨sec1_edges_agree Q, fun h => (thm_2_2 Q).1 h hX⟩⟩

/-- Conjecture 1.1 resolved, in the PAPER's conventions (lines 120–121: "With part (a) and the case `k=1`, this resolves
Conjecture 1.1"; abstract line 57: "With Fourier's inequality, these results settle the conjecture"): part (a) for every
`1 ≤ i ≤ d − 1`; part (b) for every `2 ≤ i ≤ d − 1`; and part (b) fails for `i = 1` (the poset `X`). -/
theorem conj_1_1_resolved_paper :
    (∀ (P : Type u) [Fintype P] [PartialOrder P], 1 < Fintype.card P → ∀ i, 1 ≤ i → i ≤ Fintype.card P - 1 →
      fNum (orderPolytope P) i ≤ fNum (chainPolytope P) i) ∧
    (∀ (P : Type u) [Fintype P] [PartialOrder P] [DecidableEq P], 1 < Fintype.card P → ∀ i, 2 ≤ i →
      i ≤ Fintype.card P - 1 → fNum (orderPolytope P) i = fNum (chainPolytope P) i →
      UnimodEquiv (orderPolytope P) (chainPolytope P)) ∧
    (fNum (orderPolytope XElem) 1 = fNum (chainPolytope XElem) 1 ∧
      ¬ UnimodEquiv (orderPolytope XElem) (chainPolytope XElem)) := by
  refine ⟨fun P _ _ _ i _ _ => fourier_thm_1_1 P i, fun P _ _ _ _ i hi2 hin heq => ?_, ?_, sec1_X_not_unimod⟩
  · exact (thm_2_2 P).mpr ((cor_5_3 P i hi2 hin).1.mp heq)
  · rw [(ex_2_1 1).1, (ex_2_1 1).2]; rfl

/-- **Conjecture 1.1 (lines 71–81; Hibi–Li 2016, Conjecture 2.4) is resolved — the HEADLINE, stated in Hibi–Li's own
published conventions** (their `O(P)` with `a_i ≥ a_j`, `C(P)` by maximal chains, unimodular equivalence by row
vectors): (a) `f_i ≤ f'_i` for all `1 ≤ i ≤ d − 1`; (b) if `f_i = f'_i` for some `2 ≤ i ≤ d − 1` then `O(P)` and `C(P)`
are unimodularly equivalent; and (b) is false for `i = 1`, witnessed by `X`. -/
theorem conj_1_1_resolved :
    (∀ (P : Type u) [Fintype P] [PartialOrder P], 1 < Fintype.card P → ∀ i, 1 ≤ i → i ≤ Fintype.card P - 1 →
      fNum (orderPolytopeHL P) i ≤ fNum (chainPolytopeHL P) i) ∧
    (∀ (P : Type u) [Fintype P] [PartialOrder P] [DecidableEq P], 1 < Fintype.card P → ∀ i, 2 ≤ i →
      i ≤ Fintype.card P - 1 → fNum (orderPolytopeHL P) i = fNum (chainPolytopeHL P) i →
      UnimodEquivHL (orderPolytopeHL P) (chainPolytopeHL P)) ∧
    (fNum (orderPolytopeHL XElem) 1 = fNum (chainPolytopeHL XElem) 1 ∧
      ¬ UnimodEquivHL (orderPolytopeHL XElem) (chainPolytopeHL XElem)) := by
  classical
  have hO : ∀ (P : Type u) [Fintype P] [PartialOrder P] (i : ℕ),
      fNum (orderPolytopeHL P) i = fNum (orderPolytope P) i := fun P _ _ i => by
    classical
    exact (sec2_unimod_same_fvector _ _ (sec2_footnote_HL_convention P).2 i).symm
  have hU : ∀ (P : Type u) [Fintype P] [PartialOrder P] [DecidableEq P],
      UnimodEquivHL (orderPolytopeHL P) (chainPolytopeHL P) ↔ UnimodEquiv (orderPolytope P) (chainPolytope P) :=
    fun P _ _ _ => by rw [Cited.hibiLi_thm_2_1 P, thm_2_2 P]
  obtain ⟨ha, hb, hc⟩ := conj_1_1_resolved_paper.{u}
  refine ⟨fun P _ _ hd i h1 hi => ?_, fun P _ _ _ hd i h2 hi heq => ?_, ?_, ?_⟩
  · rw [hO P i, sec2_HL_chain_convention P]; exact ha P hd i h1 hi
  · rw [hO P i, sec2_HL_chain_convention P] at heq
    exact (hU P).mpr (hb P hd i h2 hi heq)
  · rw [(sec2_unimod_same_fvector _ _ (sec2_footnote_HL_convention XElem).2 1).symm,
      sec2_HL_chain_convention XElem]
    exact hc.1
  · rw [Cited.hibiLi_thm_2_1 XElem, ← thm_2_2 XElem]; exact hc.2

/-! ### Section 5: coverage rows (review REVIEW_006_cov, 20261028) -/

/-- v2.10 l. 176-177 and 960-961: each pyramid step multiplies `F_C − F_O` by `1 + t`. -/
theorem sec5_pyramid_step : ∀ m, facePoly (chainPolytope (sharpFamily (m + 1))) -
    facePoly (orderPolytope (sharpFamily (m + 1))) =
      (1 + X) * (facePoly (chainPolytope (sharpFamily m)) - facePoly (orderPolytope (sharpFamily m))) :=
  Proofs.sec5_pyramid_step

/-- **Corollary 5.3, proof** (v2.10 l. 976-977): "the coefficient of `t^k` in `t²(1+t)^{n−3}` is `C(n−3, k−2) ≥ 1`"
(for `2 ≤ k ≤ n − 1`). -/
theorem cor_5_3_gap_coefficient (n k : ℕ) (hn : 5 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n - 1) :
    (gapPoly n).coeff k = (Nat.choose (n - 3) (k - 2) : ℤ) ∧ 1 ≤ Nat.choose (n - 3) (k - 2) := by
  exact Proofs.cor_5_3_gap_coefficient n k hn hk hkn

end HibiLi.Paper
