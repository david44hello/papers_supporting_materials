/-
HibiLiLean — adjacent maximal refinement cells give incident bipartite edges.
-/
import HibiLi.Polytope.RefinementGraph
import HibiLi.Polytope.SharedFacet

namespace HibiLi.Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

theorem refinement_adjacent_pairs {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (transverse : switch.Transverse)
    (left right : MaxSubdivisionCell (switch.refinementCells face))
    (adjacent : (subdivisionDualGraph (switch.refinementCells face)).Adj left right) :
    (switch.refinementMaxPair hface left).1 = (switch.refinementMaxPair hface right).1 ∨
      (switch.refinementMaxPair hface left).2 = (switch.refinementMaxPair hface right).2 := by
  classical
  let pairL := switch.refinementMaxPair hface left
  let pairR := switch.refinementMaxPair hface right
  change pairL.1 = pairR.1 ∨ pairL.2 = pairR.2
  by_cases sameS : pairL.1 = pairR.1
  · exact Or.inl sameS
  by_cases sameT : pairL.2 = pairR.2
  · exact Or.inr sameT
  exfalso
  have left_top := switch.refinement_max_is_top hface left
  have right_top := switch.refinement_max_is_top hface right
  have leftR := switch.restrict_cellsR_subset hface left_top.1
  have rightR := switch.restrict_cellsR_subset hface right_top.1
  have representationL : pairL.1.1 ∩ pairL.2.1 = left.1 := switch.refinementMaxPair_inter hface left
  have representationR : pairR.1.1 ∩ pairR.2.1 = right.1 := switch.refinementMaxPair_inter hface right
  have facts : left ≠ right ∧ (left.1 ∩ right.1).Nonempty ∧
      IsFace left.1 (left.1 ∩ right.1) ∧ IsFace right.1 (left.1 ∩ right.1) ∧
      adim (left.1 ∩ right.1) + 1 = adim left.1 ∧
      adim (left.1 ∩ right.1) + 1 = adim right.1 := adjacent
  have facet_dim : adim (left.1 ∩ right.1) + 1 = adim face := facts.2.2.2.2.1.trans left_top.2
  have facet_insideS : left.1 ∩ right.1 ⊆ pairL.1.1 ∩ pairR.1.1 := by
    intro point member
    have first : point ∈ pairL.1.1 ∩ pairL.2.1 := by simpa only [representationL] using member.1
    have second : point ∈ pairR.1.1 ∩ pairR.2.1 := by simpa only [representationR] using member.2
    exact ⟨first.1, second.1⟩
  have facet_insideT : left.1 ∩ right.1 ⊆ pairL.2.1 ∩ pairR.2.1 := by
    intro point member
    have first : point ∈ pairL.1.1 ∩ pairL.2.1 := by simpa only [representationL] using member.1
    have second : point ∈ pairR.1.1 ∩ pairR.2.1 := by simpa only [representationR] using member.2
    exact ⟨first.2, second.2⟩
  have nonemptyS := facts.2.1.mono facet_insideS
  have nonemptyT := facts.2.1.mono facet_insideT
  have strictS : adim (pairL.1.1 ∩ pairR.1.1) < adim face := by
    have upper : adim (pairL.1.1 ∩ pairR.1.1) ≤ adim pairL.1.1 :=
      Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_left)
    refine lt_of_le_of_ne (upper.trans_eq pairL.1.2.2) ?_
    intro same
    exact sameS (Subtype.ext (switch.topCellsS_eq_of_full_inter hface pairL.1.2 pairR.1.2 nonemptyS same))
  have strictT : adim (pairL.2.1 ∩ pairR.2.1) < adim face := by
    have upper : adim (pairL.2.1 ∩ pairR.2.1) ≤ adim pairL.2.1 :=
      Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_left)
    refine lt_of_le_of_ne (upper.trans_eq pairL.2.2.2) ?_
    intro same
    exact sameT (Subtype.ext (switch.topCellsT_eq_of_full_inter hface pairL.2.2 pairR.2.2 nonemptyT same))
  have dimS : adim (pairL.1.1 ∩ pairR.1.1) = adim (left.1 ∩ right.1) := by
    have lower : adim (left.1 ∩ right.1) ≤ adim (pairL.1.1 ∩ pairR.1.1) :=
      Submodule.finrank_mono (vectorSpan_mono ℝ facet_insideS)
    omega
  have dimT : adim (pairL.2.1 ∩ pairR.2.1) = adim (left.1 ∩ right.1) := by
    have lower : adim (left.1 ∩ right.1) ≤ adim (pairL.2.1 ∩ pairR.2.1) :=
      Submodule.finrank_mono (vectorSpan_mono ℝ facet_insideT)
    omega
  obtain ⟨point, facet_interior⟩ := facts.2.1.intrinsicInterior
    (facts.2.2.1.2.convex (switch.cellsR_isPolytope leftR).convex)
  have interiorE := interior_shared_facet (switch.B_isPolytope.face hface)
    (switch.cellsR_isPolytope leftR) (switch.cellsR_isPolytope rightR)
    (switch.restrict_cell_subset left_top.1) (switch.restrict_cell_subset right_top.1)
    left_top.2 right_top.2 (fun same => facts.1 (Subtype.ext same))
    facts.2.2.1 facts.2.2.2.1 facet_dim facet_interior
  have interiorS := intrinsicInterior_mono_of_adim_eq facts.2.1 facet_insideS dimS.symm facet_interior
  have interiorT := intrinsicInterior_mono_of_adim_eq facts.2.1 facet_insideT dimT.symm facet_interior
  have leftS := switch.restrict_cellsS_subset hface pairL.1.2.1
  have rightS := switch.restrict_cellsS_subset hface pairR.1.2.1
  have leftT := switch.restrict_cellsT_subset hface pairL.2.2.1
  have rightT := switch.restrict_cellsT_subset hface pairR.2.2.1
  have commonS := switch.cellsS_face_closed leftS (switch.cellsS_inter_faces leftS rightS nonemptyS).1
  have commonT := switch.cellsT_face_closed leftT (switch.cellsT_inter_faces leftT rightT nonemptyT).1
  have insideS : pairL.1.1 ∩ pairR.1.1 ⊆ face :=
    Set.inter_subset_left.trans (switch.restrict_cell_subset pairL.1.2.1)
  have insideT : pairL.2.1 ∩ pairR.2.1 ⊆ face :=
    Set.inter_subset_left.trans (switch.restrict_cell_subset pairL.2.2.1)
  have restrictedS : pairL.1.1 ∩ pairR.1.1 ∈ switch.restrict switch.cellsS face :=
    ⟨nonemptyS, _, commonS, (Set.inter_eq_left.mpr insideS).symm⟩
  have restrictedT : pairL.2.1 ∩ pairR.2.1 ∈ switch.restrict switch.cellsT face :=
    ⟨nonemptyT, _, commonT, (Set.inter_eq_left.mpr insideT).symm⟩
  have common_eq : (pairL.1.1 ∩ pairR.1.1) ∩ (pairL.2.1 ∩ pairR.2.1) = left.1 ∩ right.1 := by
    rw [← representationL, ← representationR]
    ext candidate
    simp only [Set.mem_inter_iff]
    tauto
  have dimensions := transverse face hface point interiorE _ restrictedS _ restrictedT interiorS interiorT
  rw [common_eq, dimS, dimT] at dimensions
  omega

end HibiLi.Switch
