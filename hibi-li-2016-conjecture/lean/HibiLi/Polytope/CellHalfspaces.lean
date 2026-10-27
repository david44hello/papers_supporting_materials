/-
HibiLiLean — finite-halfspace descriptions of cells, faces, and intersections.
-/
import HibiLi.Polytope.DomainCover

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem HasFiniteHalfspaceRep.face {body face : Set E} (represented : HasFiniteHalfspaceRep body)
    (hface : IsFace body face) : HasFiniteHalfspaceRep face := by
  obtain ⟨functional, level, representation⟩ := hface.2.eq_inter_halfSpace' hface.1
  rw [representation]
  apply represented.inter
  change HasFiniteHalfspaceRep {point : E | level ≤ functional point}
  simpa using HasFiniteHalfspaceRep.halfspace (-functional) (-level)

namespace Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

theorem cellsS_halfspaces {cell : Set (switch.P' → ℝ)} (member : cell ∈ switch.cellsS) :
    HasFiniteHalfspaceRep cell := by
  obtain ⟨branch, valid, _, hface⟩ := member
  exact (switch.domL_halfspaces branch valid).face hface

theorem cellsT_halfspaces {cell : Set (switch.P' → ℝ)} (member : cell ∈ switch.cellsT) :
    HasFiniteHalfspaceRep cell := by
  obtain ⟨branch, valid, _, hface⟩ := member
  exact (switch.domU_halfspaces branch valid).face hface

theorem cellsR_halfspaces {cell : Set (switch.P' → ℝ)} (member : cell ∈ switch.cellsR) :
    HasFiniteHalfspaceRep cell := by
  obtain ⟨_, left, hleft, right, hright, rfl⟩ := member
  exact (switch.cellsS_halfspaces hleft).inter (switch.cellsT_halfspaces hright)

theorem cellsR_isPolytope {cell : Set (switch.P' → ℝ)} (member : cell ∈ switch.cellsR) : IsPolytope cell :=
  (switch.cellsR_halfspaces member).isPolytope
    ((chainOrderPolytope_bounded _ _).subset (switch.cellsR_properties member).2)

end Switch
end HibiLi
