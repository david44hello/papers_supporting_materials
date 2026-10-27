/-
HibiLiLean — finite cell counts partitioned by unique carrier.
-/
import HibiLi.Polytope.CarrierInterior

namespace HibiLi.Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

theorem cellNum_eq_sum_carrierNum (family : Set (Set (switch.P' → ℝ)))
    (finite : family.Finite) (properties : ∀ cell ∈ family, cell.Nonempty ∧ cell ⊆ switch.B)
    (dim : ℕ) :
    cellNum family dim = ∑ face ∈ switch.B_isPolytope.finite_faces.toFinset,
      switch.carrierNum family face dim := by
  classical
  let cells := finite.toFinset.filter (fun cell => adim cell = dim)
  let faces := switch.B_isPolytope.finite_faces.toFinset
  have member_cells (cell : Set (switch.P' → ℝ)) :
      cell ∈ cells ↔ cell ∈ family ∧ adim cell = dim := by simp [cells]
  have total_eq : cellNum family dim = cells.card := by
    have set_eq : {cell | cell ∈ family ∧ adim cell = dim} = (cells : Set (Set (switch.P' → ℝ))) := by
      ext cell
      simp only [Finset.mem_coe, member_cells, Set.mem_ofPred_eq]
    rw [cellNum, set_eq, Set.ncard_coe_finset]
  have carrier_eq (face : Set (switch.P' → ℝ)) : switch.carrierNum family face dim =
      (cells.filter (fun cell => IsCarrier switch.B face cell)).card := by
    have set_eq : {cell | cell ∈ family ∧ adim cell = dim ∧ IsCarrier switch.B face cell} =
        (cells.filter (fun cell => IsCarrier switch.B face cell) : Set (Set (switch.P' → ℝ))) := by
      ext cell
      simp only [Finset.mem_coe, Finset.mem_filter, member_cells, Set.mem_ofPred_eq, and_assoc]
    rw [carrierNum, set_eq, Set.ncard_coe_finset]
  have unique_sum (cell : Set (switch.P' → ℝ)) (member : cell ∈ cells) :
      ∑ face ∈ faces, (if IsCarrier switch.B face cell then 1 else 0 : ℕ) = 1 := by
    have cell_properties := properties cell (member_cells cell |>.mp member).1
    obtain ⟨carrier, hcarrier, _⟩ := switch.B_isPolytope.existsUnique_carrier cell_properties.1 cell_properties.2
    have carrier_mem : carrier ∈ faces := by simpa [faces] using hcarrier.1
    calc
      _ = ∑ face ∈ faces, (if face = carrier then 1 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro face _
        congr 1
        exact propext ⟨fun other => other.unique hcarrier, fun same => same ▸ hcarrier⟩
      _ = 1 := by simp [carrier_mem]
  rw [total_eq]
  change cells.card = ∑ face ∈ faces, switch.carrierNum family face dim
  simp_rw [carrier_eq, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  symm
  apply Finset.sum_congr rfl
  exact unique_sum

theorem cellsS_properties {cell : Set (switch.P' → ℝ)} (member : cell ∈ switch.cellsS) :
    cell.Nonempty ∧ cell ⊆ switch.B := by
  rcases member with ⟨_, _, _, hface⟩
  exact ⟨hface.1, fun _ member => (hface.subset member).1⟩

theorem cellsT_properties {cell : Set (switch.P' → ℝ)} (member : cell ∈ switch.cellsT) :
    cell.Nonempty ∧ cell ⊆ switch.B := by
  rcases member with ⟨_, _, _, hface⟩
  exact ⟨hface.1, fun _ member => (hface.subset member).1⟩

theorem cellsR_properties {cell : Set (switch.P' → ℝ)} (member : cell ∈ switch.cellsR) :
    cell.Nonempty ∧ cell ⊆ switch.B := by
  rcases member with ⟨nonempty, left, hleft, right, _, rfl⟩
  exact ⟨nonempty, fun _ member => (switch.cellsS_properties hleft).2 member.1⟩

end HibiLi.Switch
