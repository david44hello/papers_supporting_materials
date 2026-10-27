/-
HibiLiLean — Lemma 3.5(iii), degree by degree.
-/
import HibiLi.Polytope.GraphCells
import HibiLi.Polytope.RefinementDisjoint
import HibiLi.Polytope.RefinementCover
import HibiLi.Polytope.Connectivity

namespace HibiLi
namespace Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

theorem carrierNum_eq_zero_of_adim_lt (family : Set (Set (switch.P' → ℝ)))
    (face : Set (switch.P' → ℝ)) (dim : ℕ) (above : adim face < dim) :
    switch.carrierNum family face dim = 0 := by
  have empty : {cell | cell ∈ family ∧ adim cell = dim ∧ IsCarrier switch.B face cell} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro cell ⟨_, dimension, carrier⟩
    have lower : adim cell ≤ adim face := Submodule.finrank_mono (vectorSpan_mono ℝ carrier.2.1)
    omega
  simp only [carrierNum, empty, Set.ncard_empty]

theorem low_carrier_count_bound (transverse : switch.Transverse)
    (face : Set (switch.P' → ℝ)) (hface : IsFace switch.B face) (dim : ℕ) (below : dim < adim face) :
    switch.carrierNum switch.cellsS face dim + switch.carrierNum switch.cellsT face dim ≤
      switch.carrierNum switch.cellsR face dim := by
  classical
  let sourceS := {cell | cell ∈ switch.cellsS ∧ adim cell = dim ∧ IsCarrier switch.B face cell}
  let sourceT := {cell | cell ∈ switch.cellsT ∧ adim cell = dim ∧ IsCarrier switch.B face cell}
  let target := {cell | cell ∈ switch.cellsR ∧ adim cell = dim ∧ IsCarrier switch.B face cell}
  let cellOf : sourceS ⊕ sourceT → Set (switch.P' → ℝ) := Sum.elim Subtype.val Subtype.val
  have source_member (index : sourceS ⊕ sourceT) : cellOf index ∈ switch.cellsS ∨ cellOf index ∈ switch.cellsT := by
    cases index with
    | inl cell => exact Or.inl cell.2.1
    | inr cell => exact Or.inr cell.2.1
  have source_dim (index : sourceS ⊕ sourceT) : adim (cellOf index) = dim := by
    cases index with
    | inl cell => exact cell.2.2.1
    | inr cell => exact cell.2.2.1
  have source_carrier (index : sourceS ⊕ sourceT) : IsCarrier switch.B face (cellOf index) := by
    cases index with
    | inl cell => exact cell.2.2.2
    | inr cell => exact cell.2.2.2
  have source_small (index : sourceS ⊕ sourceT) : adim (cellOf index) < adim face := by
    rw [source_dim]
    exact below
  have cover (index : sourceS ⊕ sourceT) :=
    lemma_3_5_i_cover_proved switch transverse face hface (cellOf index)
      (source_member index) (source_carrier index) (source_small index)
  have hit (index : sourceS ⊕ sourceT) : ∃ selected : target, selected.1 ∈ switch.RR (cellOf index) := by
    obtain ⟨selected, member⟩ := (cover index).1
    refine ⟨⟨selected, member.1, member.2.2.trans (source_dim index), (cover index).2 selected member⟩, member⟩
  choose selected selected_mem using hit
  have separated : Pairwise (fun first second : sourceS ⊕ sourceT =>
      Disjoint (switch.RR (cellOf first)) (switch.RR (cellOf second))) := by
    intro first second different
    cases first with
    | inl left =>
      cases second with
      | inl right =>
        have distinct : left.1 ≠ right.1 := fun same => different (congrArg Sum.inl (Subtype.ext same))
        exact lemma_3_5_i_disjoint_proved switch transverse face hface
          left.1 right.1 (Or.inl ⟨left.2.1, right.2.1, distinct⟩) left.2.2.2 right.2.2.2
          (left.2.2.1.trans right.2.2.1.symm) (by simpa only [left.2.2.1] using below)
      | inr right =>
        exact lemma_3_5_i_disjoint_proved switch transverse face hface
          left.1 right.1 (Or.inr (Or.inr ⟨left.2.1, right.2.1⟩)) left.2.2.2 right.2.2.2
          (left.2.2.1.trans right.2.2.1.symm) (by simpa only [left.2.2.1] using below)
    | inr left =>
      cases second with
      | inl right =>
        exact (lemma_3_5_i_disjoint_proved switch transverse face hface
          right.1 left.1 (Or.inr (Or.inr ⟨right.2.1, left.2.1⟩)) right.2.2.2 left.2.2.2
          (right.2.2.1.trans left.2.2.1.symm) (by simpa only [right.2.2.1] using below)).symm
      | inr right =>
        have distinct : left.1 ≠ right.1 := fun same => different (congrArg Sum.inr (Subtype.ext same))
        exact lemma_3_5_i_disjoint_proved switch transverse face hface
          left.1 right.1 (Or.inr (Or.inl ⟨left.2.1, right.2.1, distinct⟩)) left.2.2.2 right.2.2.2
          (left.2.2.1.trans right.2.2.1.symm) (by simpa only [left.2.2.1] using below)
  have injective : Function.Injective selected := by
    intro first second same
    by_contra different
    apply Set.disjoint_left.mp (separated different) (selected_mem first)
    rw [same]
    exact selected_mem second
  let := (switch.carrierCells_finite switch.cellsS_finite face dim).fintype
  let := (switch.carrierCells_finite switch.cellsT_finite face dim).fintype
  let := (switch.carrierCells_finite switch.cellsR_finite face dim).fintype
  have count := Nat.card_le_card_of_injective selected injective
  simpa only [Nat.card_sum, Nat.card_coe_set_eq, carrierNum, sourceS, sourceT, target] using count

end Switch

theorem lemma_3_5_iii_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) (k : ℕ) :
    0 ≤ s.deltaCoeff E k := by
  classical
  rcases lt_trichotomy k (adim E) with below | equal | above
  · have count := s.low_carrier_count_bound hT E hE k below
    unfold Switch.deltaCoeff
    rw [ite_eq_right (ne_of_lt below)]
    omega
  · subst k
    have count := s.top_carrier_count_bound hE
      (lemma_3_5_ii_proved s hT E hE)
    unfold Switch.deltaCoeff
    rw [ite_eq_left rfl]
    omega
  · simp [Switch.deltaCoeff, s.carrierNum_eq_zero_of_adim_lt _ E k above, ne_of_gt above]

end HibiLi
