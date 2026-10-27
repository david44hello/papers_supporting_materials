/-
HibiLiLean — chain-order polytopes are bounded finite halfspace intersections.
-/
import HibiLi.Polytope.HalfspaceRep
import HibiLi.Polytope.Endpoints

namespace HibiLi

variable (P : Type*) [Fintype P] [PartialOrder P]

omit [Fintype P] in
theorem chainOrderPolytope_coordinate_bounds (ideal : Set P) {point : P → ℝ}
    (member : point ∈ chainOrderPolytope P ideal) (coord : P) :
    0 ≤ point coord ∧ point coord ≤ 1 := by
  classical
  by_cases inside : coord ∈ ideal
  · refine ⟨member.1 coord inside, ?_⟩
    have singleton_bound := member.2.2.2.2 {coord}
      (by simpa using inside) (by simp [IsChainSet])
    simpa using singleton_bound
  · exact member.2.1 coord inside

theorem chainOrderPolytope_bounded (ideal : Set P) :
    Bornology.IsBounded (chainOrderPolytope P ideal) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : P → ℝ) 1)).isBounded.subset
  intro point member
  exact ⟨fun coord => (chainOrderPolytope_coordinate_bounds P ideal member coord).1,
    fun coord => (chainOrderPolytope_coordinate_bounds P ideal member coord).2⟩

theorem chainOrderPolytope_halfspaces (ideal : Set P) :
    HasFiniteHalfspaceRep (chainOrderPolytope P ideal) := by
  classical
  let coordinate : P → StrongDual ℝ (P → ℝ) := fun coord => ContinuousLinearMap.proj coord
  change HasFiniteHalfspaceRep
    ({point : P → ℝ | ∀ coord ∈ ideal, 0 ≤ point coord} ∩
    ({point : P → ℝ | ∀ coord ∉ ideal, 0 ≤ point coord ∧ point coord ≤ 1} ∩
    ({point : P → ℝ | ∀ lower upper, lower ∉ ideal → upper ∉ ideal → lower ≤ upper → point lower ≤ point upper} ∩
    ({point : P → ℝ | ∀ upper ∉ ideal, ∀ chain : Finset P, (↑chain ⊆ ideal) → IsChainSet P chain →
      (∀ coord ∈ chain, coord < upper) → ∑ coord ∈ chain, point coord ≤ point upper} ∩
     {point : P → ℝ | ∀ chain : Finset P, (↑chain ⊆ ideal) → IsChainSet P chain →
       ∑ coord ∈ chain, point coord ≤ 1}))))
  refine HasFiniteHalfspaceRep.inter ?_ (HasFiniteHalfspaceRep.inter ?_
    (HasFiniteHalfspaceRep.inter ?_ (HasFiniteHalfspaceRep.inter ?_ ?_)))
  · apply HasFiniteHalfspaceRep.setOf_forall
    intro coord
    apply HasFiniteHalfspaceRep.imp
    change HasFiniteHalfspaceRep {point : P → ℝ | 0 ≤ point coord}
    simpa [coordinate] using HasFiniteHalfspaceRep.halfspace (-coordinate coord) 0
  · apply HasFiniteHalfspaceRep.setOf_forall
    intro coord
    apply HasFiniteHalfspaceRep.imp
    change HasFiniteHalfspaceRep ({point : P → ℝ | 0 ≤ point coord} ∩ {point : P → ℝ | point coord ≤ 1})
    refine HasFiniteHalfspaceRep.inter ?_ ?_
    · simpa [coordinate] using HasFiniteHalfspaceRep.halfspace (-coordinate coord) 0
    · simpa [coordinate] using HasFiniteHalfspaceRep.halfspace (coordinate coord) 1
  · apply HasFiniteHalfspaceRep.setOf_forall
    intro lower
    apply HasFiniteHalfspaceRep.setOf_forall
    intro upper
    apply HasFiniteHalfspaceRep.imp
    apply HasFiniteHalfspaceRep.imp
    apply HasFiniteHalfspaceRep.imp
    change HasFiniteHalfspaceRep {point : P → ℝ | point lower ≤ point upper}
    simpa [coordinate, sub_nonpos] using
      HasFiniteHalfspaceRep.halfspace (coordinate lower - coordinate upper) 0
  · apply HasFiniteHalfspaceRep.setOf_forall
    intro upper
    apply HasFiniteHalfspaceRep.imp
    apply HasFiniteHalfspaceRep.setOf_forall
    intro chain
    apply HasFiniteHalfspaceRep.imp
    apply HasFiniteHalfspaceRep.imp
    apply HasFiniteHalfspaceRep.imp
    change HasFiniteHalfspaceRep {point : P → ℝ | ∑ coord ∈ chain, point coord ≤ point upper}
    simpa [coordinate, sub_nonpos] using HasFiniteHalfspaceRep.halfspace
      ((∑ coord ∈ chain, coordinate coord) - coordinate upper) 0
  · apply HasFiniteHalfspaceRep.setOf_forall
    intro chain
    apply HasFiniteHalfspaceRep.imp
    apply HasFiniteHalfspaceRep.imp
    change HasFiniteHalfspaceRep {point : P → ℝ | ∑ coord ∈ chain, point coord ≤ 1}
    simpa [coordinate] using HasFiniteHalfspaceRep.halfspace (∑ coord ∈ chain, coordinate coord) 1

theorem chainOrderPolytope_isPolytope (ideal : Set P) :
    IsPolytope (chainOrderPolytope P ideal) :=
  (chainOrderPolytope_halfspaces P ideal).isPolytope (chainOrderPolytope_bounded P ideal)

theorem orderPolytope_isPolytope : IsPolytope (orderPolytope P) := by
  simpa using chainOrderPolytope_isPolytope P ∅

theorem chainPolytope_isPolytope : IsPolytope (chainPolytope P) := by
  simpa using chainOrderPolytope_isPolytope P Set.univ

end HibiLi
