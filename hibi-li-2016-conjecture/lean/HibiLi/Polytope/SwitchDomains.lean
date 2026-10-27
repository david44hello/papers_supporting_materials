/-
HibiLiLean — switch domains are polytopes and all switch cell families are finite.
-/
import HibiLi.Polytope.ChainOrder
import HibiLi.Defs.Switch

namespace HibiLi.Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

theorem B_isPolytope : IsPolytope switch.B := chainOrderPolytope_isPolytope _ _

theorem domL_halfspaces (branch : Finset switch.P') (valid : branch ∈ switch.lowBranches) :
    HasFiniteHalfspaceRep (switch.domL branch) := by
  classical
  let coordinate : switch.P' → StrongDual ℝ (switch.P' → ℝ) := fun coord => ContinuousLinearMap.proj coord
  have domain_eq : switch.domL branch = switch.B ∩
      {point | ∀ other ∈ switch.lowBranches, switch.chainSum other point ≤ switch.chainSum branch point} := by
    ext point
    change (_ ∧ switch.L point = _) ↔ (_ ∧ _)
    apply and_congr_right
    intro _
    constructor
    · intro same other member
      rw [← same]
      exact Finset.le_sup' (fun branch => switch.chainSum branch point) member
    · intro maximal
      exact le_antisymm (Finset.sup'_le _ _ maximal)
        (Finset.le_sup' (fun branch => switch.chainSum branch point) valid)
  rw [domain_eq]
  refine (chainOrderPolytope_halfspaces _ _).inter ?_
  apply HasFiniteHalfspaceRep.setOf_forall
  intro other
  apply HasFiniteHalfspaceRep.imp
  change HasFiniteHalfspaceRep {point : switch.P' → ℝ |
    switch.chainSum other point ≤ switch.chainSum branch point}
  simpa [coordinate, chainSum, sub_nonpos] using HasFiniteHalfspaceRep.halfspace
    ((∑ coord ∈ other, coordinate coord) - (∑ coord ∈ branch, coordinate coord)) 0

theorem domL_isPolytope (branch : Finset switch.P') (valid : branch ∈ switch.lowBranches) :
    IsPolytope (switch.domL branch) :=
  (switch.domL_halfspaces branch valid).isPolytope
    ((chainOrderPolytope_bounded _ _).subset (fun _ member => member.1))

theorem domU_halfspaces (branch : Option switch.P') (valid : branch ∈ switch.upBranches) :
    HasFiniteHalfspaceRep (switch.domU branch) := by
  classical
  let coordinate : switch.P' → StrongDual ℝ (switch.P' → ℝ) := fun coord => ContinuousLinearMap.proj coord
  have domain_eq : switch.domU branch = switch.B ∩
      {point | ∀ other ∈ switch.upBranches, switch.upVal branch point ≤ switch.upVal other point} := by
    ext point
    change (_ ∧ switch.U point = _) ↔ (_ ∧ _)
    apply and_congr_right
    intro _
    constructor
    · intro same other member
      rw [← same]
      exact Finset.inf'_le (fun branch => switch.upVal branch point) member
    · intro minimal
      exact le_antisymm (Finset.inf'_le (fun branch => switch.upVal branch point) valid)
        (Finset.le_inf' _ _ minimal)
  rw [domain_eq]
  refine (chainOrderPolytope_halfspaces _ _).inter ?_
  apply HasFiniteHalfspaceRep.setOf_forall
  intro other
  apply HasFiniteHalfspaceRep.imp
  change HasFiniteHalfspaceRep {point : switch.P' → ℝ |
    switch.upVal branch point ≤ switch.upVal other point}
  cases branch with
  | none =>
    cases other with
    | none => simpa [upVal] using (HasFiniteHalfspaceRep.univ (E := switch.P' → ℝ))
    | some coord =>
      simpa [upVal, coordinate] using HasFiniteHalfspaceRep.halfspace (-coordinate coord) (-1)
  | some coord =>
    cases other with
    | none =>
      simpa [upVal, coordinate] using HasFiniteHalfspaceRep.halfspace (coordinate coord) 1
    | some upper =>
      simpa [upVal, coordinate, sub_nonpos] using HasFiniteHalfspaceRep.halfspace
        (coordinate coord - coordinate upper) 0

theorem domU_isPolytope (branch : Option switch.P') (valid : branch ∈ switch.upBranches) :
    IsPolytope (switch.domU branch) :=
  (switch.domU_halfspaces branch valid).isPolytope
    ((chainOrderPolytope_bounded _ _).subset (fun _ member => member.1))

theorem cellsS_finite : switch.cellsS.Finite := by
  have finite := switch.lowBranches.finite_toSet.biUnion
    (fun branch member => (switch.domL_isPolytope branch member).finite_faces)
  apply finite.subset
  rintro cell ⟨branch, member, _, hface⟩
  exact Set.mem_iUnion.mpr ⟨branch, Set.mem_iUnion.mpr ⟨member, hface⟩⟩

theorem cellsT_finite : switch.cellsT.Finite := by
  have finite := switch.upBranches.finite_toSet.biUnion
    (fun branch member => (switch.domU_isPolytope branch member).finite_faces)
  apply finite.subset
  rintro cell ⟨branch, member, _, hface⟩
  exact Set.mem_iUnion.mpr ⟨branch, Set.mem_iUnion.mpr ⟨member, hface⟩⟩

theorem cellsR_finite : switch.cellsR.Finite := by
  apply ((switch.cellsS_finite.prod switch.cellsT_finite).image
    (fun pair => pair.1 ∩ pair.2)).subset
  rintro cell ⟨_, left, hleft, right, hright, rfl⟩
  exact ⟨(left, right), ⟨hleft, hright⟩, rfl⟩

theorem restrict_finite {family : Set (Set (switch.P' → ℝ))} (finite : family.Finite)
    (face : Set (switch.P' → ℝ)) : (switch.restrict family face).Finite := by
  apply (finite.image (fun cell => cell ∩ face)).subset
  rintro cell ⟨_, original, member, rfl⟩
  exact ⟨original, member, rfl⟩

theorem carrierCells_finite {family : Set (Set (switch.P' → ℝ))} (finite : family.Finite)
    (face : Set (switch.P' → ℝ)) (dim : ℕ) :
    {cell | cell ∈ family ∧ adim cell = dim ∧ IsCarrier switch.B face cell}.Finite :=
  finite.subset fun _ member => member.1

end HibiLi.Switch
