/-
HibiLiLean — paper Lemma 3.5(i), disjoint refinement families.
-/
import HibiLi.Polytope.CellGeometry

namespace HibiLi

theorem lemma_3_5_i_disjoint_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) (Y Y' : Set (s.P' → ℝ))
    (hYY' : (Y ∈ s.cellsS ∧ Y' ∈ s.cellsS ∧ Y ≠ Y') ∨ (Y ∈ s.cellsT ∧ Y' ∈ s.cellsT ∧ Y ≠ Y') ∨
      (Y ∈ s.cellsS ∧ Y' ∈ s.cellsT))
    (hYE : IsCarrier s.B E Y) (hY'E : IsCarrier s.B E Y') (hdim : adim Y = adim Y') (hlt : adim Y < adim E) :
    Disjoint (s.RR Y) (s.RR Y') := by
  apply Set.disjoint_left.mpr
  intro refinement left_member right_member
  have nonempty : refinement.Nonempty := left_member.1.1
  have inside : refinement ⊆ Y ∩ Y' := fun _ member =>
    ⟨left_member.2.1 member, right_member.2.1 member⟩
  have lower : adim refinement ≤ adim (Y ∩ Y') := Submodule.finrank_mono (vectorSpan_mono ℝ inside)
  have upper : adim (Y ∩ Y') ≤ adim Y := Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_left)
  have dim_left : adim (Y ∩ Y') = adim Y := by have := left_member.2.2; omega
  have dim_right : adim (Y ∩ Y') = adim Y' := dim_left.trans hdim
  rcases hYY' with ⟨leftS, rightS, distinct⟩ | ⟨leftT, rightT, distinct⟩ | ⟨leftS, rightT⟩
  · exact distinct (s.cellsS_eq_of_full_inter leftS rightS (nonempty.mono inside) dim_left dim_right)
  · exact distinct (s.cellsT_eq_of_full_inter leftT rightT (nonempty.mono inside) dim_left dim_right)
  · obtain ⟨point, interiorR⟩ := nonempty.intrinsicInterior (s.cellsR_convex left_member.1)
    have interiorY := intrinsicInterior_mono_of_adim_eq nonempty left_member.2.1 left_member.2.2 interiorR
    have interiorY' := intrinsicInterior_mono_of_adim_eq nonempty right_member.2.1 right_member.2.2 interiorR
    have interiorE := hYE.intrinsicInterior_subset (chainOrderPolytope_halfspaces _ _) interiorY
    have restrictY : Y ∈ s.restrict s.cellsS E :=
      ⟨(s.cellsS_properties leftS).1, Y, leftS, (Set.inter_eq_left.mpr hYE.2.1).symm⟩
    have restrictY' : Y' ∈ s.restrict s.cellsT E :=
      ⟨(s.cellsT_properties rightT).1, Y', rightT, (Set.inter_eq_left.mpr hY'E.2.1).symm⟩
    have transverse := hT E hE point interiorE Y restrictY Y' restrictY' interiorY interiorY'
    omega

end HibiLi
