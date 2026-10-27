/-
HibiLiLean — full-dimensional affinity domains cover the switch base.
-/
import HibiLi.Polytope.FiniteCover
import HibiLi.Polytope.Dimension

namespace HibiLi

variable {ι : Type*} [Fintype ι]

theorem adim_eq_card_of_nonempty_interior {body : Set (ι → ℝ)}
    (nonempty : (interior body).Nonempty) : adim body = Fintype.card ι := by
  have full : affineSpan ℝ body = ⊤ := by
    apply top_unique
    rw [← isOpen_interior.affineSpan_eq_top nonempty]
    exact affineSpan_mono ℝ interior_subset
  unfold adim
  rw [← direction_affineSpan, full, AffineSubspace.direction_top]
  simp

namespace Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

theorem B_interior_nonempty : (interior switch.B).Nonempty := by
  have zero_member : (0 : switch.P' → ℝ) ∈ switch.B := by simp [B, chainOrderPolytope]
  have dimension : adim switch.B = Fintype.card switch.P' := chainOrderPolytope_adim _ _
  have direction_top : vectorSpan ℝ switch.B = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [adim, Module.finrank_fintype_fun_eq_card] using dimension
  have nonempty_span : (affineSpan ℝ switch.B : Set (switch.P' → ℝ)).Nonempty :=
    ⟨0, subset_affineSpan ℝ switch.B zero_member⟩
  have span_top : affineSpan ℝ switch.B = ⊤ :=
    (AffineSubspace.direction_eq_top_iff_of_nonempty nonempty_span).mp
      (by simpa only [direction_affineSpan] using direction_top)
  exact switch.B_isPolytope.convex.interior_nonempty_iff_affineSpan_eq_top.mpr span_top

theorem cellsS_cover : switch.B ⊆ ⋃ cell : switch.cellsS, (cell : Set (switch.P' → ℝ)) := by
  classical
  let pieces : switch.lowBranches → Set (switch.P' → ℝ) := fun branch => switch.domL branch
  have covers : switch.B ⊆ ⋃ branch, pieces branch := by
    intro point member
    obtain ⟨branch, valid, attained⟩ :=
      Finset.exists_mem_eq_sup' switch.lowBranches_nonempty (fun branch => switch.chainSum branch point)
    exact Set.mem_iUnion.mpr ⟨⟨branch, valid⟩, member, attained⟩
  have full_cover := full_interior_pieces_cover switch.B_isPolytope.convex switch.B_interior_nonempty
    pieces (fun branch => (switch.domL_isPolytope branch branch.2).isClosed) covers
  intro point member
  obtain ⟨⟨branch, full⟩, in_domain⟩ := Set.mem_iUnion.mp (full_cover member)
  have cell_member : switch.domL branch ∈ switch.cellsS :=
    ⟨branch, branch.2, adim_eq_card_of_nonempty_interior full, IsFace.refl ⟨point, in_domain⟩⟩
  exact Set.mem_iUnion.mpr ⟨⟨switch.domL branch, cell_member⟩, in_domain⟩

theorem cellsT_cover : switch.B ⊆ ⋃ cell : switch.cellsT, (cell : Set (switch.P' → ℝ)) := by
  classical
  let pieces : switch.upBranches → Set (switch.P' → ℝ) := fun branch => switch.domU branch
  have covers : switch.B ⊆ ⋃ branch, pieces branch := by
    intro point member
    obtain ⟨branch, valid, attained⟩ :=
      Finset.exists_mem_eq_inf' switch.upBranches_nonempty (fun branch => switch.upVal branch point)
    exact Set.mem_iUnion.mpr ⟨⟨branch, valid⟩, member, attained⟩
  have full_cover := full_interior_pieces_cover switch.B_isPolytope.convex switch.B_interior_nonempty
    pieces (fun branch => (switch.domU_isPolytope branch branch.2).isClosed) covers
  intro point member
  obtain ⟨⟨branch, full⟩, in_domain⟩ := Set.mem_iUnion.mp (full_cover member)
  have cell_member : switch.domU branch ∈ switch.cellsT :=
    ⟨branch, branch.2, adim_eq_card_of_nonempty_interior full, IsFace.refl ⟨point, in_domain⟩⟩
  exact Set.mem_iUnion.mpr ⟨⟨switch.domU branch, cell_member⟩, in_domain⟩

theorem RR_nonempty_of_mem_cellsS {cell : Set (switch.P' → ℝ)} (member : cell ∈ switch.cellsS) :
    (switch.RR cell).Nonempty := by
  classical
  let := switch.cellsT_finite.fintype
  have properties := switch.cellsS_properties member
  obtain ⟨other, nonempty, dimension⟩ := exists_full_dim_intersection (switch.cellsS_isPolytope member)
    properties.1 (fun other : switch.cellsT => (other : Set (switch.P' → ℝ)))
    (fun other => (switch.cellsT_isPolytope other.2).isClosed)
    (properties.2.trans switch.cellsT_cover)
  refine ⟨cell ∩ other.1, ⟨nonempty, cell, member, other.1, other.2, rfl⟩, Set.inter_subset_left, dimension⟩

theorem RR_nonempty_of_mem_cellsT {cell : Set (switch.P' → ℝ)} (member : cell ∈ switch.cellsT) :
    (switch.RR cell).Nonempty := by
  classical
  let := switch.cellsS_finite.fintype
  have properties := switch.cellsT_properties member
  obtain ⟨other, nonempty, dimension⟩ := exists_full_dim_intersection (switch.cellsT_isPolytope member)
    properties.1 (fun other : switch.cellsS => (other : Set (switch.P' → ℝ)))
    (fun other => (switch.cellsS_isPolytope other.2).isClosed)
    (properties.2.trans switch.cellsS_cover)
  refine ⟨cell ∩ other.1, ⟨nonempty, other.1, other.2, cell, member, Set.inter_comm _ _⟩,
    Set.inter_subset_left, dimension⟩

end Switch
end HibiLi
