/-
HibiLiLean — finite halfspace representations and closure operations.
-/
import HibiLi.Polytope.Halfspaces

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasFiniteHalfspaceRep (body : Set E) : Prop :=
  ∃ constraints : Finset (StrongDual ℝ E × ℝ),
    body = {point | ∀ constraint ∈ constraints, constraint.1 point ≤ constraint.2}

theorem HasFiniteHalfspaceRep.halfspace (linear : StrongDual ℝ E) (bound : ℝ) :
    HasFiniteHalfspaceRep {point | linear point ≤ bound} := by
  classical
  exact ⟨{(linear, bound)}, by ext point; simp⟩

theorem HasFiniteHalfspaceRep.univ : HasFiniteHalfspaceRep (Set.univ : Set E) := by
  exact ⟨∅, by ext point; simp⟩

theorem HasFiniteHalfspaceRep.inter {left right : Set E}
    (hleft : HasFiniteHalfspaceRep left) (hright : HasFiniteHalfspaceRep right) :
    HasFiniteHalfspaceRep (left ∩ right) := by
  classical
  rcases hleft with ⟨leftConstraints, rfl⟩
  rcases hright with ⟨rightConstraints, rfl⟩
  refine ⟨leftConstraints ∪ rightConstraints, ?_⟩
  ext point
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_union, or_imp, forall_and]

theorem HasFiniteHalfspaceRep.iInter {κ : Type*} [Finite κ] {bodies : κ → Set E}
    (represented : ∀ index, HasFiniteHalfspaceRep (bodies index)) :
    HasFiniteHalfspaceRep (⋂ index, bodies index) := by
  classical
  cases nonempty_fintype κ
  choose constraints representation using represented
  refine ⟨Finset.univ.biUnion constraints, ?_⟩
  ext point
  simp only [Set.mem_iInter, representation, Set.mem_ofPred_eq, Finset.mem_biUnion,
    Finset.mem_univ, true_and, forall_exists_index]
  constructor
  · intro all constraint index member
    exact all index constraint member
  · intro all index constraint member
    exact all constraint index member

theorem HasFiniteHalfspaceRep.setOf_forall {κ : Type*} [Finite κ] {predicate : κ → E → Prop}
    (represented : ∀ index, HasFiniteHalfspaceRep {point | predicate index point}) :
    HasFiniteHalfspaceRep {point | ∀ index, predicate index point} := by
  have result := HasFiniteHalfspaceRep.iInter represented
  simpa only [Set.iInter_ofPred] using result

theorem HasFiniteHalfspaceRep.imp (condition : Prop) (body : Set E)
    (represented : HasFiniteHalfspaceRep body) :
    HasFiniteHalfspaceRep {point | condition → point ∈ body} := by
  classical
  by_cases holds : condition
  · simpa [holds] using represented
  · simpa [holds] using (HasFiniteHalfspaceRep.univ (E := E))

theorem HasFiniteHalfspaceRep.isPolytope [FiniteDimensional ℝ E] {body : Set E}
    (represented : HasFiniteHalfspaceRep body) (bounded : Bornology.IsBounded body) :
    IsPolytope body := by
  classical
  rcases represented with ⟨constraints, rfl⟩
  have as_subtype : {point : E | ∀ constraint ∈ constraints, constraint.1 point ≤ constraint.2} =
      {point : E | ∀ constraint : constraints, constraint.1.1 point ≤ constraint.1.2} := by
    ext point
    simp
  rw [as_subtype] at bounded ⊢
  exact isPolytope_halfspaces (fun constraint : constraints => constraint.1.1)
    (fun constraint : constraints => constraint.1.2) bounded

end HibiLi
