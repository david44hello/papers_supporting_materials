/-
HibiLiLean — finiteness of geometric faces and existence of carriers.
-/
import HibiLi.Polytope.Faces
import HibiLi.Example21.FiniteHull

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsPolytope.finite_faces {body : Set E} (polytope : IsPolytope body) :
    {face | IsFace body face}.Finite := by
  rcases polytope with ⟨vertices, rfl⟩
  apply ((vertices.finite_toSet.powerset).image (convexHull ℝ)).subset
  intro face hface
  exact ⟨(vertices : Set E) ∩ face, Set.inter_subset_left,
    (hface.eq_convexHull_inter vertices.finite_toSet).symm⟩

theorem IsPolytope.faces_finite {body : Set E} (polytope : IsPolytope body) (dim : ℕ) :
    (faces body dim).Finite :=
  polytope.finite_faces.subset fun _ member => member.1

theorem IsPolytope.face {body face : Set E} (polytope : IsPolytope body)
    (hface : IsFace body face) : IsPolytope face := by
  classical
  rcases polytope with ⟨vertices, rfl⟩
  have finite : ((vertices : Set E) ∩ face).Finite := vertices.finite_toSet.inter_of_left _
  refine ⟨finite.toFinset, ?_⟩
  simpa only [Set.Finite.coe_toFinset] using hface.eq_convexHull_inter vertices.finite_toSet

theorem IsPolytope.existsUnique_carrier {body cell : Set E} (polytope : IsPolytope body)
    (nonempty : cell.Nonempty) (inside : cell ⊆ body) :
    ∃! carrier, IsCarrier body carrier cell := by
  classical
  let containers : Set (Set E) := {face | IsFace body face ∧ cell ⊆ face}
  have finite : containers.Finite := polytope.finite_faces.subset fun _ member => member.1
  have body_mem : body ∈ containers := ⟨IsFace.refl (nonempty.mono inside), inside⟩
  have containers_nonempty : containers.Nonempty := ⟨body, body_mem⟩
  have cell_inside : cell ⊆ ⋂₀ containers := by
    intro point member
    exact Set.mem_sInter.mpr fun face hface => hface.2 member
  have intersection_exposed : IsExposed ℝ body (⋂₀ containers) := by
    have exposed := IsExposed.sInter (𝕜 := ℝ) (A := body)
      (F := finite.toFinset) (by simpa using containers_nonempty)
      (fun face member => ((finite.mem_toFinset.mp member) : face ∈ containers).1.2)
    simpa only [Set.Finite.coe_toFinset] using exposed
  have carrier : IsCarrier body (⋂₀ containers) cell := by
    refine ⟨⟨nonempty.mono cell_inside, intersection_exposed⟩, cell_inside, ?_⟩
    intro face hface contains
    exact Set.sInter_subset_of_mem ⟨hface, contains⟩
  exact ⟨⋂₀ containers, carrier, fun _ other => other.unique carrier⟩

end HibiLi
