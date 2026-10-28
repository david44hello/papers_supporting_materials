/-
Extended diameters of nonempty Cartesian graph products.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Basic

namespace LeeDiam

open SimpleGraph

theorem box_ediam_eq_add {V W : Type*} [Nonempty V] [Nonempty W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (G □ H).ediam = G.ediam + H.ediam := by
  apply le_antisymm
  · rw [SimpleGraph.ediam_le_iff]
    intro left right
    rw [SimpleGraph.edist_boxProd]
    exact add_le_add SimpleGraph.edist_le_ediam SimpleGraph.edist_le_ediam
  · rw [SimpleGraph.ediam_eq_iSup_iSup_edist, SimpleGraph.ediam_eq_iSup_iSup_edist]
    apply ENat.iSup_add_iSup_le
    intro left_left left_right
    apply ENat.iSup_add_iSup_le
    intro right_left right_right
    rw [← SimpleGraph.edist_boxProd (G := G) (H := H)
      (left_left, left_right) (right_left, right_right)]
    exact SimpleGraph.edist_le_ediam

theorem orderPolytope_sum_iff (P Q : Type) [Fintype P] [PartialOrder P]
    [Fintype Q] [PartialOrder Q] (point : P ⊕ Q → ℝ) :
    point ∈ orderPolytope (P ⊕ Q) ↔
      point ∘ Sum.inl ∈ orderPolytope P ∧ point ∘ Sum.inr ∈ orderPolytope Q := by
  constructor
  · intro member
    constructor
    · exact ⟨fun coord => member.1 (Sum.inl coord), fun lower upper relation =>
        member.2 (Sum.inl lower) (Sum.inl upper) (Sum.inl_le_inl_iff.mpr relation)⟩
    · exact ⟨fun coord => member.1 (Sum.inr coord), fun lower upper relation =>
        member.2 (Sum.inr lower) (Sum.inr upper) (Sum.inr_le_inr_iff.mpr relation)⟩
  · rintro ⟨left, right⟩
    refine ⟨?_, ?_⟩
    · intro coord
      cases coord with
      | inl coord => exact left.1 coord
      | inr coord => exact right.1 coord
    · intro lower upper relation
      cases lower with
      | inl lower =>
        cases upper with
        | inl upper => exact left.2 lower upper (Sum.inl_le_inl_iff.mp relation)
        | inr upper => exact False.elim (Sum.not_inl_le_inr relation)
      | inr lower =>
        cases upper with
        | inl upper => exact False.elim (Sum.not_inr_le_inl relation)
        | inr upper => exact right.2 lower upper (Sum.inr_le_inr_iff.mp relation)

theorem chainPolytope_sum_iff (P Q : Type) [Fintype P] [PartialOrder P]
    [Fintype Q] [PartialOrder Q] (point : P ⊕ Q → ℝ) :
    point ∈ chainPolytope (P ⊕ Q) ↔
      point ∘ Sum.inl ∈ chainPolytope P ∧ point ∘ Sum.inr ∈ chainPolytope Q := by
  classical
  constructor
  · intro member
    constructor
    · refine ⟨fun coord => member.1 (Sum.inl coord), ?_⟩
      intro chain ordered
      have lifted : HibiLi.IsChainSet (P ⊕ Q) (chain.map Function.Embedding.inl) := by
        intro left left_mem right right_mem _
        obtain ⟨lower, lower_mem, lower_eq⟩ := Finset.mem_map.mp left_mem
        obtain ⟨upper, upper_mem, upper_eq⟩ := Finset.mem_map.mp right_mem
        rw [← lower_eq, ← upper_eq]
        simpa only [Function.Embedding.inl_apply, Sum.inl_le_inl_iff] using ordered.total lower_mem upper_mem
      simpa only [Finset.sum_map, Function.Embedding.inl_apply, Function.comp_def] using member.2 _ lifted
    · refine ⟨fun coord => member.1 (Sum.inr coord), ?_⟩
      intro chain ordered
      have lifted : HibiLi.IsChainSet (P ⊕ Q) (chain.map Function.Embedding.inr) := by
        intro left left_mem right right_mem _
        obtain ⟨lower, lower_mem, lower_eq⟩ := Finset.mem_map.mp left_mem
        obtain ⟨upper, upper_mem, upper_eq⟩ := Finset.mem_map.mp right_mem
        rw [← lower_eq, ← upper_eq]
        simpa only [Function.Embedding.inr_apply, Sum.inr_le_inr_iff] using ordered.total lower_mem upper_mem
      simpa only [Finset.sum_map, Function.Embedding.inr_apply, Function.comp_def] using member.2 _ lifted
  · rintro ⟨left, right⟩
    refine ⟨?_, ?_⟩
    · intro coord
      cases coord with
      | inl coord => exact left.1 coord
      | inr coord => exact right.1 coord
    · intro chain ordered
      have left_chain : HibiLi.IsChainSet P chain.toLeft := by
        intro lower lower_mem upper upper_mem _
        simpa only [Sum.inl_le_inl_iff] using ordered.total
          (Finset.mem_toLeft.mp lower_mem) (Finset.mem_toLeft.mp upper_mem)
      have right_chain : HibiLi.IsChainSet Q chain.toRight := by
        intro lower lower_mem upper upper_mem _
        simpa only [Sum.inr_le_inr_iff] using ordered.total
          (Finset.mem_toRight.mp lower_mem) (Finset.mem_toRight.mp upper_mem)
      have empty_side : chain.toLeft = ∅ ∨ chain.toRight = ∅ := by
        by_cases empty_left : chain.toLeft = ∅
        · exact Or.inl empty_left
        · right
          obtain ⟨lower, lower_mem⟩ := Finset.nonempty_iff_ne_empty.mpr empty_left
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro upper upper_mem
          have compared := ordered.total (Finset.mem_toLeft.mp lower_mem) (Finset.mem_toRight.mp upper_mem)
          simp only [Sum.not_inl_le_inr, Sum.not_inr_le_inl, or_self] at compared
      rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
      rcases empty_side with empty_left | empty_right
      · rw [empty_left, Finset.sum_empty, zero_add]
        exact right.2 _ right_chain
      · rw [empty_right, Finset.sum_empty, add_zero]
        exact left.2 _ left_chain

end LeeDiam
