/-
HibiLi/Paper/Statements.lean — every mathematical claim of the 9-page paper itself (v0.70), one Lean statement each,
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

universe u

namespace HibiLi.Paper

open HibiLi Polynomial Finset

/-! ### Paper sentences deliberately NOT formalized (paper v0.70 line numbers)

Every mathematical claim of the paper itself has a statement below.  Not formalized are only sentences that report
other papers' results without using them, and informal summaries of proofs that are formalized below:
* Lines 89–90: "and even the same Ehrhart polynomial [Stanley]".  A remark cited to Stanley (1986) and used in no
  proof; Mathlib has no Ehrhart polynomials.
* Lines 72–81: the right column of the introduction's table (what other papers proved; bibliographic).
* Lines 120–125: the history of the conjecture (other papers' results).
* Lines 170–171: the pointer to the long version [G].
* Line 201: the facet remark cited to [HL, Lemma 1.1]; used in no proof.
* Lines 737–738: "all attaining posets are characterized in [G, Theorem 6.1]" (a pointer to the long version).
* Lines 150–168 ("The idea of the proof") and 308–312: informal sketches of proofs formalized below.
(The n = 6 count at lines 736–737, "seven of the sixteen posets containing X attain the bound", IS formalized:
`sec5_census_n6`.)
-/

/-! ## Section 1 (introduction) and Section 2 (definitions and examples) -/

/-- Lines 86–89 (and line 180): `O(P)` and `C(P)` are `n`-dimensional 0/1 polytopes. -/
theorem sec1_zero_one_polytopes (P : Type*) [Fintype P] [PartialOrder P] :
    (∃ S : Finset (P → ℝ), (∀ v ∈ S, ∀ p, v p = 0 ∨ v p = 1) ∧ orderPolytope P = convexHull ℝ (S : Set (P → ℝ))) ∧
    (∃ S : Finset (P → ℝ), (∀ v ∈ S, ∀ p, v p = 0 ∨ v p = 1) ∧ chainPolytope P = convexHull ℝ (S : Set (P → ℝ))) ∧
    adim (orderPolytope P) = Fintype.card P ∧ adim (chainPolytope P) = Fintype.card P :=
  sec1_zero_one_polytopes_proved P

/-- Line 89: "with the same number of vertices". -/
theorem sec1_same_vertices (P : Type*) [Fintype P] [PartialOrder P] :
    fNum (orderPolytope P) 0 = fNum (chainPolytope P) 0 :=
  sec1_same_vertices_proved P

/-- Footnote, lines 180–182: Hibi–Li's order polytope is the image of ours under `v ↦ 1 − v`, a unimodular map. -/
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

/-- Lines 186–188: "Such an affine bijection maps j-faces onto j-faces, so unimodularly equivalent polytopes have the
same f-vector." -/
theorem sec2_unimod_same_fvector {ι : Type*} [Fintype ι] [DecidableEq ι] (Q Q' : Set (ι → ℝ))
    (h : UnimodEquiv Q Q') (j : ℕ) : fNum Q j = fNum Q' j :=
  h.fNum_eq j

/-- Lines 125–127: "the two polytopes always have the same number of edges [HLSS]" (cited; read through the
convention theorems above). -/
theorem sec1_edges_agree (P : Type*) [Fintype P] [PartialOrder P] :
    fNum (orderPolytope P) 1 = fNum (chainPolytope P) 1 := by
  classical
  rw [sec2_unimod_same_fvector _ _ (sec2_footnote_HL_convention P).2 1, Cited.hlss_thm_2_1 P,
    sec2_HL_chain_convention P]

/-- Lines 91–94: five distinct elements with `a, b < c < g, h`, `a, b` incomparable and `g, h` incomparable also satisfy
`a, b < g, h`, so they form an induced copy of `X` (an order embedding of `X` onto them). -/
theorem sec1_X_copy_induced {P : Type*} [PartialOrder P] {a b c g h : P} (hX : IsXCopy a b c g h) :
    ∃ f : XElem ↪o P, f XElem.a = a ∧ f XElem.b = b ∧ f XElem.c = c ∧ f XElem.g = g ∧ f XElem.h = h :=
  Proofs.sec1_X_copy_induced_proved hX

/-- Lines 190–192: for the chain `a < b`, both polytopes are triangles with `F_{O(P)} = F_{C(P)} = 3 + 3t + t^2`. -/
theorem sec2_chain2_triangles :
    facePoly (orderPolytope Chain2) = 3 + 3 * X + X ^ 2 ∧
    facePoly (chainPolytope Chain2) = 3 + 3 * X + X ^ 2 :=
  sec2_chain2_triangles_proved

/-- **Example 2.1** (lines 194–205): `f(O(X)) = (8,24,34,24,8,1)` and `f(C(X)) = (8,24,35,26,9,1)` (and no faces of
dimension ≥ 6). -/
theorem ex_2_1 (k : ℕ) :
    fNum (orderPolytope XElem) k = [8, 24, 34, 24, 8, 1].getD k 0 ∧
    fNum (chainPolytope XElem) k = [8, 24, 35, 26, 9, 1].getD k 0 :=
  ex_2_1_proved k

/-- Lines 127–129: `O(X)` and `C(X)` are not unimodularly equivalent ("both have 24 edges, but 8 and 9 facets"). -/
theorem sec1_X_not_unimod : ¬ UnimodEquiv (orderPolytope XElem) (chainPolytope XElem) := by
  intro h
  have h4 := sec2_unimod_same_fvector _ _ h 4
  rw [(ex_2_1 4).1, (ex_2_1 4).2] at h4
  simp at h4

/-- **Theorem 2.2** (Hibi–Li; lines 207–210), in the paper's conventions: `O(P)` and `C(P)` are unimodularly equivalent
iff `P` does not contain `X`. (Derived from the cited `hibiLi_thm_2_1` and the three convention theorems above.) -/
theorem thm_2_2 (P : Type*) [Fintype P] [PartialOrder P] [DecidableEq P] :
    UnimodEquiv (orderPolytope P) (chainPolytope P) ↔ ¬ ContainsX P := by
  have hfoot := (sec2_footnote_HL_convention P).2
  rw [← Cited.hibiLi_thm_2_1 P, sec2_HL_chain_convention P, sec2_HL_unimod_convention]
  exact ⟨fun h => hfoot.symm.trans h, fun h => hfoot.trans h⟩

/-- Lines 212–214: the nonempty faces of a pyramid `pyr(Q)` (apex `v` outside `aff(Q)`) are exactly the faces of `Q`,
the apex, and the pyramids over the faces of `Q`. -/
theorem sec2_pyramid_faces {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (v : ι → ℝ)
    (hv : v ∉ affineSpan ℝ Q) (F : Set (ι → ℝ)) :
    IsFace (convexHull ℝ (insert v Q)) F ↔
      IsFace Q F ∨ F = {v} ∨ ∃ G, IsFace Q G ∧ F = convexHull ℝ (insert v G) :=
  Proofs.sec2_pyramid_faces_proved Q hQ v hv F

/-- **Equation (1)** (line 215), the pyramid rule: `F_{pyr(Q)}(t) = 1 + (1 + t) F_Q(t)` for a polytope `Q` and an apex
outside its affine hull. -/
theorem eq_1_pyramid {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (v : ι → ℝ)
    (hv : v ∉ affineSpan ℝ Q) :
    facePoly (convexHull ℝ (insert v Q)) = 1 + (1 + X) * facePoly Q :=
  eq_1_pyramid_proved Q hQ v hv

/-! ## Section 3 (cited input: Fourier's chain–order polytopes) -/

/-- Line 241: `O_∅(P) = O(P)` and `O_P(P) = C(P)`. -/
theorem sec3_endpoints (P : Type*) [Fintype P] [PartialOrder P] :
    chainOrderPolytope P ∅ = orderPolytope P ∧ chainOrderPolytope P Set.univ = chainPolytope P :=
  ⟨chainOrderPolytope_empty P, chainOrderPolytope_univ P⟩

/-- Lines 241–242: `O_I(P)` is a polytope of dimension `|P|` (Fourier §2; we prove it). -/
theorem sec3_dim (P : Type*) [Fintype P] [PartialOrder P] (I : Set P) (hI : IsLowerSet I) :
    IsPolytope (chainOrderPolytope P I) ∧ adim (chainOrderPolytope P I) = Fintype.card P :=
  sec3_dim_proved P I hI

/-- Lines 248–249: `B = O_I(P′)` is a polytope of dimension `n − 1`. -/
theorem sec3_B_dim {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    IsPolytope s.B ∧ adim s.B + 1 = Fintype.card P :=
  Proofs.sec3_B_dim_proved s

/-- Lines 245–246: "Let `q` be minimal in `J`, so that `I ∪ {q}` is again an order ideal." -/
theorem sec3_insert_isLowerSet {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    IsLowerSet (insert s.q s.I) :=
  Proofs.insert_isLowerSet s

/-- Lines 255–257: `0 ≤ L ≤ U ≤ 1` on `B`, `L` convex, `U` concave. -/
theorem sec3_L_U {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∀ u ∈ s.B, 0 ≤ s.L u ∧ s.L u ≤ s.U u ∧ s.U u ≤ 1) ∧ ConvexOn ℝ Set.univ s.L ∧
    ConcaveOn ℝ Set.univ s.U :=
  ⟨fun _ hu => Proofs.L_U_bounds s hu, Proofs.L_convex s, Proofs.U_concave s⟩

/-- Lines 256–257: `L` and `U` are piecewise affine (a maximum, resp. minimum, of finitely many affine functions). -/
theorem sec3_L_U_piecewise {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∃ (fs : Finset ((s.P' → ℝ) →ᵃ[ℝ] ℝ)) (h : fs.Nonempty), ∀ u, s.L u = fs.sup' h (fun f => f u)) ∧
    (∃ (gs : Finset ((s.P' → ℝ) →ᵃ[ℝ] ℝ)) (h : gs.Nonempty), ∀ u, s.U u = gs.inf' h (fun g => g u)) :=
  Proofs.sec3_L_U_piecewise_proved s

/-- **Proposition 3.1** (lines 259–266; Fourier 3.1, cited; proved here anyway): the fibre description of `O_I(P)` and
`O_{I∪{q}}(P)` over `B`, coordinates `(u, z)` with `z` the `q`-coordinate (`z = y_q` on the left, `z = x_q` on the
right; in Lean both are `x q`). -/
theorem prop_3_1 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (x : P → ℝ) :
    (x ∈ chainOrderPolytope P s.I ↔
      (fun p : s.P' => x p.1) ∈ s.B ∧ s.L (fun p => x p.1) ≤ x s.q ∧ x s.q ≤ s.U (fun p => x p.1)) ∧
    (x ∈ chainOrderPolytope P (insert s.q s.I) ↔
      (fun p : s.P' => x p.1) ∈ s.B ∧ 0 ≤ x s.q ∧ x s.q ≤ s.U (fun p => x p.1) - s.L (fun p => x p.1)) :=
  Proofs.prop_3_1_proved s x

/-- Lines 267–270, the worked example: for the chain `a < b` (`Chain2`, `a = 0`, `b = 1`), `I = {a}`, `q = b`:
`B = [0,1]`, `L = x_a`, `U = 1`, and the two fibre polytopes are `O_{{a}}(P)`, which is `O(P)` ("as `a` is
minimal"), and `C(P)`. -/
theorem sec3_chain2_example :
    ∃ s : Switch Chain2, s.I = {0} ∧ s.q = 1 ∧ s.B = {u | ∀ p, 0 ≤ u p ∧ u p ≤ 1} ∧
      (∀ u ∈ s.B, ∀ p, s.L u = u p ∧ s.U u = 1) ∧
      chainOrderPolytope Chain2 s.I = orderPolytope Chain2 ∧
      chainOrderPolytope Chain2 (insert s.q s.I) = chainPolytope Chain2 :=
  Proofs.sec3_chain2_example_proved

/-- Lines 273–276 (definition of a subdivision): "the relative interiors of the cells then partition the polytope" —
every point of the polytope lies in the relative interior of exactly one cell. -/
theorem sec3_subdivision_relint_partition {ι : Type*} [Fintype ι] (base : Set (ι → ℝ))
    (cells : Finset (Set (ι → ℝ))) (hsub : IsFinitePolytopalSubdivision base cells) (u : ι → ℝ) (hu : u ∈ base) :
    ∃! C, C ∈ cells ∧ u ∈ intrinsicInterior ℝ C :=
  subdivision_relint_partition base cells hsub u hu

/-- Lines 283–286: `S`, `T` and their common refinement `R` are subdivisions of `B` [Fourier, Section 4]
(proved here, from the cell description of lines 281–283). -/
theorem sec3_subdivisions {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    ∃ cS cT cR : Finset (Set (s.P' → ℝ)),
      (cS : Set (Set (s.P' → ℝ))) = s.cellsS ∧ (cT : Set (Set (s.P' → ℝ))) = s.cellsT ∧
      (cR : Set (Set (s.P' → ℝ))) = s.cellsR ∧
      IsFinitePolytopalSubdivision s.B cS ∧ IsFinitePolytopalSubdivision s.B cT ∧
      IsFinitePolytopalSubdivision s.B cR :=
  Proofs.sec3_subdivisions_proved s

/-- Lines 288–290 and 313–314: every cell of `S`, `T`, `R` has exactly one carrier, and its relative interior lies in
the relative interior of its carrier. -/
theorem sec3_carrier {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (C : Set (s.P' → ℝ))
    (hC : C ∈ s.cellsS ∨ C ∈ s.cellsT ∨ C ∈ s.cellsR) :
    (∃! E, IsCarrier s.B E C) ∧ ∀ E, IsCarrier s.B E C → intrinsicInterior ℝ C ⊆ intrinsicInterior ℝ E :=
  sec3_carrier_proved s C hC

/-- **Lemma 3.2** (lines 304–307), second equality (the paper's own, lines 313–314; no cited input):
`F_B + F_R − F_S − F_T = Σ_E δ_E` over all nonempty faces `E` of `B`. -/
theorem lemma_3_2_local {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT =
      ∑ᶠ (E : Set (s.P' → ℝ)) (_ : IsFace s.B E), s.delta E :=
  s.sum_delta_eq.symm.trans (finsum_mem_eq_finite_toFinset_sum _ s.B_isPolytope.finite_faces).symm

/-- **Lemma 3.2** (lines 304–307; first equality = Fourier 4.1, cited; second equality = `lemma_3_2_local`): the change
in face polynomials is the sum of the local terms `δ_E` over all nonempty faces `E` of `B`. -/
theorem lemma_3_2 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    {E | IsFace s.B E}.Finite ∧
    facePoly (chainOrderPolytope P (insert s.q s.I)) - facePoly (chainOrderPolytope P s.I) =
      ∑ᶠ (E : Set (s.P' → ℝ)) (_ : IsFace s.B E), s.delta E :=
  ⟨s.B_isPolytope.finite_faces, (Cited.fourier_lemma_4_1 s).trans (lemma_3_2_local s)⟩

/-- **Definition 3.3** (lines 316–321), "the unique cells": for every face `E` of `B` and `u ∈ relint E`, exactly one
cell of `S|_E`, and exactly one cell of `T|_E`, has `u` in its relative interior.  (So `Switch.Transverse`, which
quantifies over all such cells, says exactly what Definition 3.3 says.) -/
theorem def_3_3_unique_cells {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (u : s.P' → ℝ) (hu : u ∈ intrinsicInterior ℝ E) :
    (∃! A, A ∈ s.restrict s.cellsS E ∧ u ∈ intrinsicInterior ℝ A) ∧
      (∃! D, D ∈ s.restrict s.cellsT E ∧ u ∈ intrinsicInterior ℝ D) :=
  Proofs.def_3_3_unique_cells_proved s E hE u hu

/-- Lines 323–324: "`L` depends only on the coordinates `x_p` with `p < q`, and `U` only on the `y_r` with
`r > q`." -/
theorem sec3_L_U_locality {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (u v : s.P' → ℝ) :
    ((∀ p : s.P', p.1 < s.q → u p = v p) → s.L u = s.L v) ∧
      ((∀ r : s.P', s.q < r.1 → u r = v r) → s.U u = s.U v) :=
  Proofs.sec3_L_U_locality_proved s u v

/-- **Proposition 3.4** (lines 327–329; = Fourier Proposition 5.2, cited as `Cited.fourier_prop_5_2`): `S` and `T` are
transverse relative to the faces of `B`. -/
theorem prop_3_4 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) : s.Transverse :=
  Cited.fourier_prop_5_2 s

/-- **Lemma 3.5(i)** (lines 340–342), first sentence: for `k < e` and a `k`-cell `Y` of `S` or `T` with carrier `E`,
`R(Y)` is nonempty and its members have carrier `E`. -/
theorem lemma_3_5_i_cover {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E)
    (Y : Set (s.P' → ℝ)) (hY : Y ∈ s.cellsS ∨ Y ∈ s.cellsT) (hYE : IsCarrier s.B E Y) (hdim : adim Y < adim E) :
    (s.RR Y).Nonempty ∧ ∀ R ∈ s.RR Y, IsCarrier s.B E R :=
  lemma_3_5_i_cover_proved s hT E hE Y hY hYE hdim

/-- **Lemma 3.5(i)** (lines 342–343), second sentence: these sets are pairwise disjoint, over all such `Y` in `S` and
`T`. -/
theorem lemma_3_5_i_disjoint {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) (Y Y' : Set (s.P' → ℝ))
    (hYY' : (Y ∈ s.cellsS ∧ Y' ∈ s.cellsS ∧ Y ≠ Y') ∨ (Y ∈ s.cellsT ∧ Y' ∈ s.cellsT ∧ Y ≠ Y') ∨
      (Y ∈ s.cellsS ∧ Y' ∈ s.cellsT))
    (hYE : IsCarrier s.B E Y) (hY'E : IsCarrier s.B E Y') (hdim : adim Y = adim Y') (hlt : adim Y < adim E) :
    Disjoint (s.RR Y) (s.RR Y') :=
  lemma_3_5_i_disjoint_proved s hT E hE Y Y' hYY' hYE hY'E hdim hlt

/-- **Lemma 3.5(ii)** (lines 344–346): the bipartite graph `G_E` is connected (the paper's proof, lines 360–373, from
CJK Lemma 2). -/
theorem lemma_3_5_ii {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) : (s.graphG E).Connected :=
  lemma_3_5_ii_proved s hT E hE

/-- **Lemma 3.5(iii)** (line 347; Fourier 4.3, Steps 1–2): `δ_{E,k} ≥ 0` for every face `E` and every `k`. -/
theorem lemma_3_5_iii {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (hT : s.Transverse)
    (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) (k : ℕ) : 0 ≤ s.deltaCoeff E k :=
  lemma_3_5_iii_proved s hT E hE k

/-- **Lemma 3.6** (lines 381–385), first clause: the `e`-cells of `S|_E` are exactly the maximal convex subsets of `E`
of dimension `e` on which `L` is affine; the same for `T|_E` and `U`.  The second clause, added in v0.60, is
`lemma_3_6_cover`. -/
theorem lemma_3_6 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (A : Set (s.P' → ℝ)) :
    (A ∈ s.topCells s.cellsS E ↔ A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧ AffineOn s.L A ∧
      ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn s.L D → D = A) ∧
    (A ∈ s.topCells s.cellsT E ↔ A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧ AffineOn s.U A ∧
      ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn s.U D → D = A) :=
  Proofs.lemma_3_6_proved s E hE A

/-- **Lemma 3.6**, second clause (new in v0.60, lines 384–385): every `e`-dimensional convex subset of `E` on which
`L` is affine lies in an `e`-cell of `S|_E`; the same for `T|_E` and `U`. -/
theorem lemma_3_6_cover {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (D : Set (s.P' → ℝ)) (hDE : D ⊆ E) (hDc : Convex ℝ D) (hDdim : adim D = adim E) :
    (AffineOn s.L D → ∃ C ∈ s.topCells s.cellsS E, D ⊆ C) ∧
      (AffineOn s.U D → ∃ C ∈ s.topCells s.cellsT E, D ⊆ C) :=
  Proofs.lemma_3_6_cover_proved s E hE D hDE hDc hDdim

/-- Lines 276–283: Lean's `cellsS` is built from the full-dimensional branch domains `A_ℓ` (the cited
characterization, lines 281–283).  This bridges back to the paper's DEFINITION of `S` (lines 276–279): its
full-dimensional cells are exactly the maximal full-dimensional convex subsets of `B` on which `L` is affine (and
the same for `T`, `U`). -/
theorem sec3_S_paper_def {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (A : Set (s.P' → ℝ)) :
    (A ∈ s.cellsS ∧ adim A = Fintype.card s.P' ↔ A ⊆ s.B ∧ Convex ℝ A ∧ adim A = Fintype.card s.P' ∧
      AffineOn s.L A ∧ ∀ D, A ⊆ D → D ⊆ s.B → Convex ℝ D → AffineOn s.L D → D = A) ∧
    (A ∈ s.cellsT ∧ adim A = Fintype.card s.P' ↔ A ⊆ s.B ∧ Convex ℝ A ∧ adim A = Fintype.card s.P' ∧
      AffineOn s.U A ∧ ∀ D, A ⊆ D → D ⊆ s.B → Convex ℝ D → AffineOn s.U D → D = A) :=
  Proofs.sec3_S_paper_def_proved s A

/-- Lines 276–279, the paper's DEFINITION of `S` in full: the cells of `S` are exactly the nonempty faces of the maximal
full-dimensional convex subsets of `B` on which `L` is affine (and the same for `T`, `U`). -/
theorem sec3_S_paper_def_full {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    s.cellsS = {C | ∃ A, (A ⊆ s.B ∧ Convex ℝ A ∧ adim A = Fintype.card s.P' ∧ AffineOn s.L A ∧
        ∀ D, A ⊆ D → D ⊆ s.B → Convex ℝ D → AffineOn s.L D → D = A) ∧ IsFace A C} ∧
    s.cellsT = {C | ∃ A, (A ⊆ s.B ∧ Convex ℝ A ∧ adim A = Fintype.card s.P' ∧ AffineOn s.U A ∧
        ∀ D, A ⊆ D → D ⊆ s.B → Convex ℝ D → AffineOn s.U D → D = A) ∧ IsFace A C} :=
  Proofs.sec3_S_paper_def_full_proved s

/-- **Proposition 3.7** (lines 401–405; Fourier 6.1): `F_{O_I(P)} ≤ F_{O_{I∪{q}}(P)}` coefficientwise, derived as the
paper's remark (lines 404–405) says: from Lemma 3.2, Proposition 3.4 and Lemma 3.5(iii). -/
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

/-- **Fourier's Theorem 1.1** (part (a) of the conjecture, paper lines 123–124), DERIVED from Proposition 3.7 along a
linear extension (as in lines 680–689; Fourier §6): `f_k(O(P)) ≤ f_k(C(P))` for every `k`. -/
theorem fourier_thm_1_1 (P : Type*) [Fintype P] [PartialOrder P] (k : ℕ) :
    fNum (orderPolytope P) k ≤ fNum (chainPolytope P) k := by
  have h := Proofs.mono_of_step (P := P) (fun s k => prop_3_7 s k) ∅ Set.univ isLowerSet_empty isLowerSet_univ
    (Set.empty_subset _) k
  rwa [(sec3_endpoints P).1, (sec3_endpoints P).2] at h

/-! ## Section 4 (the sharp gap) -/


/-- **Lemma 4.2** (one crossing; lines 419–432): under the crossing hypotheses at some `w`,
`δ_E(t) ≥ t^{e−2}(1+t)^2`.  `CrossingAt` is the v0.70 hypothesis ("`H_S`, `H_T` hyperplanes of `aff(E)` through
`w`, and `H_S ≠ H_T`") by `crossingAt_iff_v060`. -/
theorem lemma_4_2 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (w : s.P' → ℝ) (hw : CrossingAt s E w) (k : ℕ) :
    (X ^ (adim E - 2) * (1 + X) ^ 2 : ℤ[X]).coeff k ≤ (s.delta E).coeff k :=
  Proofs.lemma_4_2_of s (Cited.fourier_prop_5_2 s) (lemma_3_5_i_cover s) (lemma_3_5_i_disjoint s)
    (lemma_3_5_ii s) (lemma_3_5_iii s) (sec3_carrier s) E hE w hw k

/-- Lemma 4.2's hypothesis as worded in v0.60 and v0.70 (lines 421–429): `H_S = {φ = φ w}` and `H_T = {ψ = ψ w}` are
hyperplanes of `aff(E)` through `w` (`φ, ψ` nonzero on `dir(E)`), and `H_S ≠ H_T`.  This is exactly `CrossingAt`,
whose last clause is the v0.41 wording "the normals are linearly independent in the dual of `dir(E)`". -/
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


/-- Paper lines 474–476: a valid `q` exists — an element `q`, maximal among the elements `m ≥ c` whose strict upper
set is not a chain (as every `r > q` is `≥ c`, maximality says: the strict upper set of every `r > q` is a chain). -/
theorem sec4_q_exists {P : Type*} [Fintype P] [PartialOrder P] {a b c g h : P} (hX : IsXCopy a b c g h) :
    ∃ q, c ≤ q ∧ ¬ IsChain (· ≤ ·) (Set.Ioi q) ∧ ∀ r, q < r → IsChain (· ≤ ·) (Set.Ioi r) :=
  Proofs.q_exists hX.2.2.1 hX.2.2.2.1 hX.2.2.2.2.2.2.1 hX.2.2.2.2.2.2.2

/-- Lines 476–477: "`q = c` would not do in general: `E₀` below needs two incomparable upper covers of `q`".  In
`a, b < c < d < g, h` (`XdElem`) the elements `a, b, c, g, h` form a copy of `X`, no switch of Section 4 can use
`q = c`, and one does exist (with `q = d`). -/
theorem sec4_q_c_remark :
    IsXCopy XdElem.a XdElem.b XdElem.c XdElem.g XdElem.h ∧ Nonempty (XSwitch XdElem) ∧
      ∀ x : XSwitch XdElem, x.q ≠ XdElem.c :=
  Proofs.sec4_q_c_remark_proved

/-- Lines 476–477, the remark's reason: in `XdElem`, `c`'s strict upper set is not a chain, yet `c` has no two distinct
upper covers (its only cover is `d`), so `E₀` could not be built at `q = c`. -/
theorem sec4_q_c_no_two_covers :
    ¬ IsChain (· ≤ ·) (Set.Ioi XdElem.c) ∧
      ¬ ∃ g' h' : XdElem, XdElem.c ⋖ g' ∧ XdElem.c ⋖ h' ∧ g' ≠ h' :=
  Proofs.sec4_q_c_no_two_covers_proved

/-- **Lemma 4.3** (lines 479–483): `q` has two distinct, incomparable upper covers; `I = P \ ↑q` is an order ideal, `q`
is minimal in `J = ↑q`, and `a, b ∈ I` with `a, b < q`. -/
theorem lemma_4_3 {P : Type*} [Fintype P] [PartialOrder P] {a b c g h q : P} (hX : IsXCopy a b c g h)
    (hcq : c ≤ q) (hq : ¬ IsChain (· ≤ ·) (Set.Ioi q)) (hmax : ∀ r, q < r → IsChain (· ≤ ·) (Set.Ioi r)) :
    (∃ g' h', q ⋖ g' ∧ q ⋖ h' ∧ g' ≠ h' ∧ ¬ g' ≤ h' ∧ ¬ h' ≤ g') ∧
    IsLowerSet (Set.Ici q)ᶜ ∧ (∀ p, p < q → p ∈ (Set.Ici q)ᶜ) ∧
    a ∈ (Set.Ici q)ᶜ ∧ b ∈ (Set.Ici q)ᶜ ∧ a < q ∧ b < q :=
  Proofs.lemma_4_3 hX.1 hX.2.1 hcq hq hmax

/-- Line 494: "(If `q > c`, `g′, h′` may differ from `g, h`.)"  Witness `R3Elem`: `a, b < c < d < g′, h′`, `g′ < g`, with
the copy `a, b, c, g, h′` of `X`; a switch of Section 4 exists with `q > c` and `{g′, h′} ≠ {g, h}`, and every `q`
meeting Lemma 4.3's conditions for this copy has this property. -/
theorem sec4_covers_may_differ :
    IsXCopy R3Elem.a R3Elem.b R3Elem.c R3Elem.g R3Elem.hp ∧
    (∃ x : XSwitch R3Elem, x.a = R3Elem.a ∧ x.b = R3Elem.b ∧ x.c = R3Elem.c ∧ x.g = R3Elem.g ∧
      x.h = R3Elem.hp ∧ x.c < x.q ∧ ({x.g', x.h'} : Set R3Elem) ≠ {x.g, x.h}) ∧
    ∀ q : R3Elem, R3Elem.c ≤ q → ¬ IsChain (· ≤ ·) (Set.Ioi q) →
      (∀ r, q < r → IsChain (· ≤ ·) (Set.Ioi r)) →
        R3Elem.c < q ∧ ∀ g' h' : R3Elem, q ⋖ g' → q ⋖ h' → g' ≠ h' →
          ({g', h'} : Set R3Elem) ≠ {R3Elem.g, R3Elem.hp} :=
  Proofs.sec4_covers_may_differ_proved

/-- Line 494, in its bare form: some switch of Section 4 has `q > c` and `{g′, h′} ≠ {g, h}`. -/
theorem sec4_covers_may_differ_exists :
    ∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (x : XSwitch P),
      x.c < x.q ∧ ({x.g', x.h'} : Set P) ≠ {x.g, x.h} :=
  Proofs.sec4_covers_may_differ_exists_proved


/-- **Lemma 4.4** (lines 506–513): `E₀` is a 4-dimensional face of `B`, cut out (besides `ζ = ζ₀`) by `α, β ≥ 0`,
`max(α, β) ≤ min(γ, η)`, `γ, η ≤ 1`. -/
theorem lemma_4_4 {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)
    (pa pb pg ph : x.toSwitch.P') (hpa : pa.1 = x.a) (hpb : pb.1 = x.b) (hpg : pg.1 = x.g')
    (hph : ph.1 = x.h') :
    IsFace x.toSwitch.B x.E0 ∧ adim x.E0 = 4 ∧
    x.E0 = {u | (∀ p : x.toSwitch.P', p.1 ∈ x.toSwitch.I → p.1 ≠ x.a → p.1 ≠ x.b → u p = 0) ∧
               (∀ r : x.toSwitch.P', r.1 ∉ x.toSwitch.I → r.1 ≠ x.g' → r.1 ≠ x.h' → u r = 1) ∧
               0 ≤ u pa ∧ 0 ≤ u pb ∧ max (u pa) (u pb) ≤ min (u pg) (u ph) ∧ u pg ≤ 1 ∧ u ph ≤ 1} :=
  Proofs.lemma_4_4_proved x pa pb pg ph hpa hpb hpg hph

/-- **Lemma 4.5** (lines 534–551; local product structure): open `V₄ ∋ (1/4,1/4,3/4,3/4)` and `V_ζ ∋ ζ₀` with
`N₀ = V₄ × V_ζ` such that (a) for every face `E ⊇ E₀` of `B`, membership in `E` within `N₀` depends only on `ζ` (so
`E ∩ N₀ = V₄ × (Q_E ∩ V_ζ)`, with `Q_E` the `ζ`-section; the paper's description of `Q_E` by tight inequalities is used
only inside the proof), and (b) on `B ∩ N₀`, `L = max(α + λ_a(ζ), β + λ_b(ζ))` and `U = min(γ, η)`. -/
theorem lemma_4_5 {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∃ (V4 : Set (Fin 4 → ℝ)) (Vz : Set ({p // p ∉ x.special} → ℝ)), IsOpen V4 ∧ IsOpen Vz ∧
      x.alphaPart x.u0 ∈ V4 ∧ x.zeta x.u0 ∈ Vz ∧
      (∀ E, IsFace x.toSwitch.B E → x.E0 ⊆ E → ∀ u ∈ x.N0 V4 Vz, ∀ v ∈ x.N0 V4 Vz,
        x.zeta u = x.zeta v → (u ∈ E ↔ v ∈ E)) ∧
      (∀ u ∈ x.toSwitch.B, u ∈ x.N0 V4 Vz →
        x.toSwitch.L u = max (u x.pa + x.lamA u) (u x.pb + x.lamB u) ∧ x.toSwitch.U u = min (u x.pg) (u x.ph)) :=
  Proofs.lemma_4_5_proved x

/-- Lines 528–532: all forms of the `a`- and `b`-families vanish at `ζ₀`, so `λ_a(ζ₀) = λ_b(ζ₀) = 0`. -/
theorem sec4_lam_u0 {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    x.lamA x.u0 = 0 ∧ x.lamB x.u0 = 0 :=
  Proofs.sec4_lam_u0_proved x

/-- **Lemma 4.5, full form of (a)** (lines 539–546), with the same `N₀` as (b): for every face `E ⊇ E₀` of `B`,
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

/-- **Lemma 4.5(a)** with the paper's OWN `Q_E` (lines 543–546): "the polyhedron in the `ζ`-space defined by the
inequalities of `B` that are tight at `u₀`, those tight on `E` taken as equalities" (`XSwitch.QEpaper`,
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

/-- **Lemma 4.6** (lines 601–604; with Lemma 4.5 inside its proof): for every face `E ⊇ E₀` of `B`, the hypotheses of
Lemma 4.2 hold at some `w ∈ relint E` (`CrossingAt` contains `w ∈ relint E`). -/
theorem lemma_4_6 {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) (E : Set (x.toSwitch.P' → ℝ))
    (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E) : ∃ w, CrossingAt x.toSwitch E w :=
  Proofs.lemma_4_6_of_3_6 x (fun E hE A => Proofs.lemma_3_6_proved x.toSwitch E hE A) E hE hE0

/-- **Lemma 4.7**, first part of its proof (lines 651–657): an `s`-polytope has at least `C(s+1, κ+1)` faces of
dimension `κ` (`0 ≤ κ ≤ s`). -/
theorem lemma_4_7_simplex {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (hne : Q.Nonempty)
    (κ : ℕ) (hκ : κ ≤ adim Q) : Nat.choose (adim Q + 1) (κ + 1) ≤ fNum Q κ :=
  Proofs.lemma_4_8_simplex_proved Q hQ hne κ hκ

/-- **Lemma 4.7** (lines 645–649): a nonempty `e`-face `E` of an `m`-polytope `B` lies in at least `C(m−e, j)` faces of
dimension `e + j`, for `0 ≤ j ≤ m − e`. -/
theorem lemma_4_7 {ι : Type*} [Fintype ι] (B : Set (ι → ℝ)) (hB : IsPolytope B) (E : Set (ι → ℝ))
    (hE : IsFace B E) (j : ℕ) (hj : j ≤ adim B - adim E) :
    Nat.choose (adim B - adim E) j ≤ {G | IsFace B G ∧ E ⊆ G ∧ adim G = adim E + j}.ncard :=
  Proofs.lemma_4_8_proved B hB E hE j hj

/-- Lines 667–679: for the switch of Section 4.2, the single step from `O_I(P)` to `O_{I∪{q}}(P)` already adds at least
`t^2 (1+t)^{n−3}`. -/
theorem switch_step_gap {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) (k : ℕ) :
    (gapPoly (Fintype.card P)).coeff k ≤
      (fNum (chainOrderPolytope P (insert x.q (Set.Ici x.q)ᶜ)) k : ℤ) - fNum (chainOrderPolytope P (Set.Ici x.q)ᶜ) k := by
  classical
  let s := x.toSwitch
  -- dimensions: B is an (n−1)-polytope (Fourier §2), E₀ a 4-face (Lemma 4.4)
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

/-- **Theorem 4.1** (lines 408–412), inequality: if `P` contains `X` then `F_C(P) − F_O(P) ≥ t^2 (1+t)^{n−3}`
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
  -- the monotone chain O(P) = O_∅ ≤ O_I and O_{I∪{q}} ≤ O_P = C(P) (Proposition 3.7, lines 680–689)
  have hmono : ∀ I I' : Set P, IsLowerSet I → IsLowerSet I' → I ⊆ I' →
      fNum (chainOrderPolytope P I) k ≤ fNum (chainOrderPolytope P I') k :=
    fun I I' hI hI' hII' => Proofs.mono_of_step (fun s k => prop_3_7 s k) I I' hI hI' hII' k
  have h1 := hmono ∅ s.I isLowerSet_empty s.isLowerSet (Set.empty_subset _)
  have h2 := hmono (insert s.q s.I) Set.univ (Proofs.insert_isLowerSet s) isLowerSet_univ (Set.subset_univ _)
  rw [(sec3_endpoints P).1] at h1
  rw [(sec3_endpoints P).2] at h2
  omega

/-- Theorem 4.1, as stated in the introduction (lines 135–138; also the abstract, lines 48–51, and the table, lines
76–78): for `2 ≤ k ≤ n − 1`, `C(P)` has at least `C(n−3, k−2)` more `k`-faces than `O(P)`. -/
theorem thm_4_1_binom (P : Type*) [Fintype P] [PartialOrder P] (hX : ContainsX P) (k : ℕ) (hk2 : 2 ≤ k)
    (_hkn : k ≤ Fintype.card P - 1) :
    fNum (orderPolytope P) k + Nat.choose (Fintype.card P - 3) (k - 2) ≤ fNum (chainPolytope P) k := by
  have h := thm_4_1 P hX k
  simp only [Proofs.gapPoly_coeff, hk2, ↓reduceIte] at h
  omega


/-! ## Section 5 (sharpness and the equality part) -/

/-- **Proposition 5.1** (lines 693–695): `F_C(X) − F_O(X) = t^2 + 2t^3 + t^4`. -/
theorem prop_5_1 :
    facePoly (chainPolytope XElem) - facePoly (orderPolytope XElem) = X ^ 2 + 2 * X ^ 3 + X ^ 4 := by
  ext k
  rw [coeff_sub, Proofs.facePoly_coeff, Proofs.facePoly_coeff, (ex_2_1 k).1, (ex_2_1 k).2]
  rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [coeff_X_pow]

/-- Proof of Proposition 5.1 "by hand" (lines 697–700), the switches other than `c` along `a, b, c, g, h`: at a
switch of `a` or `b`, `L ≡ 0` on `B`; at a switch of `g` or `h`, `U ≡ 1` on `B`; and every switch of an element
other than `c` leaves the face polynomial unchanged. -/
theorem prop_5_1_other_switches (s : Switch XElem) :
    ((s.q = XElem.a ∨ s.q = XElem.b) → ∀ u ∈ s.B, s.L u = 0) ∧
    ((s.q = XElem.g ∨ s.q = XElem.h) → ∀ u ∈ s.B, s.U u = 1) ∧
    (s.q ≠ XElem.c → facePoly (chainOrderPolytope XElem (insert s.q s.I)) = facePoly (chainOrderPolytope XElem s.I)) :=
  prop_5_1_other_switches_of s (Cited.fourier_lemma_4_1 s)

/-- Proof of Proposition 5.1 "by hand" (lines 702–717) and Figure 2 (lines 587–596): the switch of `c` in `X` exists;
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

/-- Figure 2 caption (lines 587–588) and proof of Proposition 5.1 (lines 702–704): for `P = X` (the switch of `c`,
`I = {a, b}`, `J′ = {g, h}`), `L = max(α, β)` and `U = min(γ, η)` on all of `B`. -/
theorem prop_5_1_X_LU : ∀ x : XSwitch XElem,
    x.q = XElem.c ∧ x.toSwitch.I = {XElem.a, XElem.b} ∧ x.toSwitch.Iᶜ \ {x.q} = {XElem.g, XElem.h} ∧
      ({x.a, x.b} : Set XElem) = {XElem.a, XElem.b} ∧ ({x.g', x.h'} : Set XElem) = {XElem.g, XElem.h} ∧
      ∀ u ∈ x.toSwitch.B, x.toSwitch.L u = max (u x.pa) (u x.pb) ∧ x.toSwitch.U u = min (u x.pg) (u x.ph) :=
  Proofs.prop_5_1_X_LU_proved

/-- **Proposition 5.2** (lines 720–724): `P_n` (here `sharpFamily (n−5)`) has `n` elements, contains `X`, and
`F_C(P_n) − F_O(P_n) = t^2 (1+t)^{n−3}`. -/
theorem prop_5_2 (m : ℕ) :
    Fintype.card (sharpFamily m) = m + 5 ∧ ContainsX (sharpFamily m) ∧
    facePoly (chainPolytope (sharpFamily m)) - facePoly (orderPolytope (sharpFamily m)) = gapPoly (m + 5) :=
  prop_5_2_proved m

/-- **Theorem 4.1**, attainment (lines 413–414): for every `n ≥ 5`, equality holds for some `n`-element poset `P`
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

/-- Lines 736–737: "For `n = 6`, seven of the sixteen posets containing `X` attain the bound, `P_6` among them".  The
sixteen posets `censusPoset i` (Defs/Census.lean) are a complete, irredundant list of the 6-element posets containing
`X` up to isomorphism; exactly seven of them have `F_C − F_O = t²(1+t)³`; one of them is `P_6 = sharpFamily 1`. -/
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

/-- **Corollary 5.3** (lines 740–744): for `2 ≤ k ≤ n − 1`, `f_k(O(P)) = f_k(C(P))` iff `P` does not contain `X`, iff
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

/-- Conjecture 1.1 resolved, in the PAPER's conventions (lines 145–147: "With Fourier's theorem for part (a) and
[HLSS] for k=1, this resolves Conjecture 1.1"; abstract lines 53–57): part (a) for every `1 ≤ i ≤ d − 1`; part (b)
for every `2 ≤ i ≤ d − 1`; and part (b) fails for `i = 1` (the poset `X`). -/
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

/-- **Conjecture 1.1 (lines 97–107; Hibi–Li 2016, Conjecture 2.4) is resolved — the HEADLINE, stated in Hibi–Li's own
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

end HibiLi.Paper
