/-
HibiLiLean — paper Lemma 3.5(i), existence and carriers of refinement cells.
-/
import HibiLi.Polytope.DomainCover

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isCarrier_of_subset_of_intrinsicInterior {body face cell : Set E}
    (hface : IsFace body face) (inside : cell ⊆ face)
    (touches : ∃ point ∈ cell, point ∈ intrinsicInterior ℝ face) : IsCarrier body face cell := by
  obtain ⟨point, cell_member, interior⟩ := touches
  refine ⟨hface, inside, ?_⟩
  intro other hother contains
  obtain ⟨functional, representation⟩ := hother.2 hother.1
  have point_member := contains cell_member
  rw [representation] at point_member
  have flat := linear_eq_of_intrinsicInterior_max interior functional
    (fun candidate member => point_member.2 candidate (hface.subset member))
  intro candidate member
  rw [representation]
  exact ⟨hface.subset member,
    fun third inBody => (point_member.2 third inBody).trans_eq (flat candidate member).symm⟩

theorem lemma_3_5_i_cover_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (_hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E)
    (Y : Set (s.P' → ℝ)) (hY : Y ∈ s.cellsS ∨ Y ∈ s.cellsT) (hYE : IsCarrier s.B E Y)
    (_hdim : adim Y < adim E) :
    (s.RR Y).Nonempty ∧ ∀ R ∈ s.RR Y, IsCarrier s.B E R := by
  refine ⟨?_, ?_⟩
  · rcases hY with member | member
    · exact s.RR_nonempty_of_mem_cellsS member
    · exact s.RR_nonempty_of_mem_cellsT member
  · intro refinement member
    have nonempty : refinement.Nonempty := member.1.1
    obtain ⟨point, interior⟩ := nonempty.intrinsicInterior (s.cellsR_convex member.1)
    have interiorY := intrinsicInterior_mono_of_adim_eq nonempty member.2.1 member.2.2 interior
    have interiorE := hYE.intrinsicInterior_subset (chainOrderPolytope_halfspaces _ _) interiorY
    exact isCarrier_of_subset_of_intrinsicInterior hE (member.2.1.trans hYE.2.1)
      ⟨point, _root_.intrinsicInterior_subset interior, interiorE⟩

end HibiLi
