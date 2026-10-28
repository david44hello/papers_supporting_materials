/-
Finiteness of the vertex sets of order and chain polytopes.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Bridge.Graphs

namespace LeeDiam

theorem polytope_vertices_finite (P : Type) [Fintype P] [PartialOrder P] :
    Finite {v : P → ℝ // HibiLi.IsFace (orderPolytope P) {v}} ∧
      Finite {v : P → ℝ // HibiLi.IsFace (chainPolytope P) {v}} := by
  classical
  constructor
  · let f : {I : Set P // IsIdeal I} → {v : P → ℝ // HibiLi.IsFace (orderPolytope P) {v}} :=
      fun I => ⟨HibiLi.setVector I.1, (order_vertex_iff_ideal _).mpr ⟨I.1, I.2, rfl⟩⟩
    apply Finite.of_surjective f
    rintro ⟨v, hv⟩
    obtain ⟨I, hI, equal⟩ := (order_vertex_iff_ideal v).mp hv
    exact ⟨⟨I, hI⟩, Subtype.ext equal.symm⟩
  · let f : {A : Set P // IsAntichainSet A} → {v : P → ℝ // HibiLi.IsFace (chainPolytope P) {v}} :=
      fun A => ⟨HibiLi.setVector A.1, (chain_vertex_iff_antichain _).mpr ⟨A.1, A.2, rfl⟩⟩
    apply Finite.of_surjective f
    rintro ⟨v, hv⟩
    obtain ⟨A, hA, equal⟩ := (chain_vertex_iff_antichain v).mp hv
    exact ⟨⟨A, hA⟩, Subtype.ext equal.symm⟩

end LeeDiam

