/-
Antichain projections and split reductions.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Bridge.Graphs
import LeeDiam.Sec4.Comps

namespace LeeDiam

section Projection

variable {P : Type} [PartialOrder P]

theorem proj_antichain (R S : Set P) (hR : IsAntichainSet R) (hS : IsAntichainSet S) :
    IsAntichainSet (proj R S) := by
  rw [S4.isAntichainSet_iff_comp] at hR hS ⊢
  intro x hx y hy comparable
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hS x hx y hy comparable
  · exact hy.2 ⟨x, hx, S4.comp_symm comparable⟩
  · exact hx.2 ⟨y, hy, comparable⟩
  · exact hR x hx.1 y hy.1 comparable

theorem proj_difference_retains (R S T : Set P) (hS : IsAntichainSet S)
    (hT : IsAntichainSet T) {x : P} (hx : x ∈ symmDiff S T)
    (retained : x ∉ R ∨ ∃ y ∈ symmDiff S T, Comp x y) :
    x ∈ symmDiff (proj R S) (proj R T) := by
  have directed : ∀ (A B : Set P), IsAntichainSet A →
      x ∈ A → x ∉ B → (x ∉ R ∨ ∃ y ∈ symmDiff A B, Comp x y) →
      x ∈ proj R A ∧ x ∉ proj R B := by
    intro A B hA hxA hxB condition
    refine ⟨Or.inl hxA, ?_⟩
    rintro (member | member)
    · exact hxB member
    · rcases condition with outside | ⟨y, hy, comparable⟩
      · exact outside member.1
      · have hyA : y ∉ A := fun inside => (S4.isAntichainSet_iff_comp.mp hA) x hxA y inside comparable
        have hyB : y ∈ B := by
          rcases Set.mem_symmDiff.mp hy with hy | hy
          · exact False.elim (hyA hy.1)
          · exact hy.1
        exact member.2 ⟨y, hyB, comparable⟩
  rcases Set.mem_symmDiff.mp hx with hx | hx
  · exact Set.mem_symmDiff.mpr (Or.inl (directed S T hS hx.1 hx.2 retained))
  · have retained' : x ∉ R ∨ ∃ y ∈ symmDiff T S, Comp x y := by
      simpa only [symmDiff_comm] using retained
    exact Set.mem_symmDiff.mpr (Or.inr (directed T S hT hx.1 hx.2 retained'))

theorem proj_difference_extra (R S T : Set P) {x : P}
    (hx : x ∈ symmDiff (proj R S) (proj R T)) (outside : x ∉ symmDiff S T) :
    x ∈ R ∧ ∃ y ∈ symmDiff S T, Comp x y := by
  have neither : x ∉ S ∧ x ∉ T := by
    simp only [Set.mem_symmDiff, proj, Set.mem_union, Set.mem_sdiff] at hx outside
    tauto
  have directed : ∀ (A B : Set P), x ∉ A → x ∉ B →
      x ∈ proj R A → x ∉ proj R B → x ∈ R ∧ ∃ y ∈ symmDiff A B, Comp x y := by
    intro A B hxA hxB inA outB
    have added : x ∈ R ∧ x ∉ nbhd A := by
      rcases inA with inside | added
      · exact False.elim (hxA inside)
      · exact added
    have neighbor : x ∈ nbhd B := by
      by_contra no_neighbor
      exact outB (Or.inr ⟨added.1, no_neighbor⟩)
    obtain ⟨y, hyB, comparable⟩ := neighbor
    have hyA : y ∉ A := fun member => added.2 ⟨y, member, comparable⟩
    exact ⟨added.1, y, Set.mem_symmDiff.mpr (Or.inr ⟨hyB, hyA⟩), comparable⟩
  rcases Set.mem_symmDiff.mp hx with hx | hx
  · exact directed S T neither.1 neither.2 hx.1 hx.2
  · simpa only [symmDiff_comm] using directed T S neither.2 neither.1 hx.1 hx.2

theorem projection_edge (R S T : Set P) (hR : IsAntichainSet R) (hS : IsAntichainSet S)
    (hT : IsAntichainSet T) (connected : IsConnSet (symmDiff S T)) :
    proj R S = proj R T ∨ IsConnSet (symmDiff (proj R S) (proj R T)) := by
  classical
  let F := symmDiff S T
  let F' := symmDiff (proj R S) (proj R T)
  by_cases core : F ⊆ F'
  · right
    obtain ⟨anchor⟩ := connected.nonempty
    apply S4.isConnSet_of_rtg (core anchor.2)
    intro y hy
    by_cases original : y ∈ F
    · exact S4.rtg_of_isConnSet connected core anchor.2 original
    · obtain ⟨_, z, hz, comparable⟩ := proj_difference_extra R S T hy original
      exact (S4.rtg_of_isConnSet connected core anchor.2 hz).tail
        ⟨core hz, hy, S4.comp_symm comparable⟩
  · obtain ⟨x, hx, erased⟩ := Set.not_subset.mp core
    have inR : x ∈ R := by
      by_contra outside
      exact erased (proj_difference_retains R S T hS hT hx (Or.inl outside))
    have isolated : ∀ y ∈ F, ¬ Comp x y := by
      intro y hy comparable
      exact erased (proj_difference_retains R S T hS hT hx (Or.inr ⟨y, hy, comparable⟩))
    have singleton : ∀ y ∈ F, y = x := by
      intro y hy
      by_contra different
      have reachable := connected.preconnected ⟨x, hx⟩ ⟨y, hy⟩
      have unequal : (⟨x, hx⟩ : F) ≠ ⟨y, hy⟩ := fun equal => different (congrArg Subtype.val equal).symm
      obtain ⟨z, edge⟩ := reachable.nonempty_neighborSet_left unequal
      exact isolated z.1 z.2 edge
    have empty : ∀ y, y ∉ F' := by
      intro y hy
      by_cases original : y ∈ F
      · exact erased ((singleton y original) ▸ hy)
      · obtain ⟨hyR, z, hz, comparable⟩ := proj_difference_extra R S T hy original
        rw [singleton z hz] at comparable
        exact (S4.isAntichainSet_iff_comp.mp hR) y hyR x inR comparable
    left
    ext y
    have := empty y
    change y ∉ symmDiff (proj R S) (proj R T) at this
    rw [Set.mem_symmDiff] at this
    constructor
    · intro member
      by_contra outside
      exact this (Or.inl ⟨member, outside⟩)
    · intro member
      by_contra outside
      exact this (Or.inr ⟨member, outside⟩)

theorem graph_edge_map_edist_le {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (edges : ∀ u v, G.Adj u v → H.edist (f u) (f v) ≤ 1) (u v : V) :
    H.edist (f u) (f v) ≤ G.edist u v := by
  change H.edist (f u) (f v) ≤ ⨅ walk : G.Walk u v, (walk.length : ℕ∞)
  apply le_iInf
  intro walk
  induction walk with
  | nil => simp
  | @cons a b c edge walk ih =>
    calc
      H.edist (f a) (f c) ≤ H.edist (f a) (f b) + H.edist (f b) (f c) := H.edist_triangle
      _ ≤ 1 + (walk.length : ℕ∞) := add_le_add (edges a b edge) ih
      _ = _ := by simp [SimpleGraph.Walk.length_cons, add_comm]

theorem projection_distance [Fintype P] (R S T : Set P) (hR : IsAntichainSet R)
    (hS : IsAntichainSet S) (hT : IsAntichainSet T) :
    dC (proj R S) (proj R T) (proj_antichain R S hR hS) (proj_antichain R T hR hT) ≤ dC S T hS hT := by
  rw [dC_eq, dC_eq]
  let f : {A : Set P // IsAntichainSet A} → {A : Set P // IsAntichainSet A} :=
    fun A => ⟨proj R A.1, proj_antichain R A.1 hR A.2⟩
  refine graph_edge_map_edist_le (G := antichainGraph P) (H := antichainGraph P) f ?_ ⟨S, hS⟩ ⟨T, hT⟩
  intro A B edge
  rcases projection_edge R A.1 B.1 hR A.2 B.2 edge with equal | adjacent
  · have same : f A = f B := Subtype.ext equal
    simp [same]
  · exact SimpleGraph.edist_le_one_iff_adj_or_eq.mpr (Or.inl adjacent)

end Projection

end LeeDiam


namespace LeeDiam

section SplitReduction

variable {P : Type} [PartialOrder P]

theorem proj_eq_union (R S : Set P) (h : IsAntichainSet (R ∪ S)) : proj R S = R ∪ S := by
  have no_neighbor : ∀ x ∈ R, x ∉ nbhd S := by
    rintro x hx ⟨y, hy, comparable⟩
    exact (S4.isAntichainSet_iff_comp.mp h) x (Or.inl hx) y (Or.inr hy) comparable
  ext x
  change (x ∈ S ∨ x ∈ R ∧ x ∉ nbhd S) ↔ x ∈ R ∨ x ∈ S
  constructor
  · tauto
  · rintro (member | member)
    · exact Or.inr ⟨member, no_neighbor x member⟩
    · exact Or.inl member

theorem proj_absorbed (R S : Set P) (h : R ⊆ nbhd S) : proj R S = S := by
  ext x
  change (x ∈ S ∨ x ∈ R ∧ x ∉ nbhd S) ↔ x ∈ S
  constructor
  · rintro (inside | added)
    · exact inside
    · exact False.elim (added.2 (h added.1))
  · exact Or.inl

theorem split_reduction [Fintype P] (X Y : Set P) (hX : IsAntichainSet X) (hY : IsAntichainSet Y) :
    ∃ (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B),
      A ⊆ X ∧ B ⊆ Y ∧ IsSplit A B (A ∪ B) ∧ dC X Y hX hY ≤ dC A B hA hB := by
  classical
  let K := X ∩ Y
  let X1 := X \ Y
  let B := Y \ X
  let R := X1 ∩ nbhd B
  let A := X1 \ R
  have hK : IsAntichainSet K := hX.subset Set.inter_subset_left
  have hX1 : IsAntichainSet X1 := hX.subset Set.sdiff_subset
  have hB : IsAntichainSet B := hY.subset Set.sdiff_subset
  have hR : IsAntichainSet R := hX1.subset Set.inter_subset_left
  have hA : IsAntichainSet A := hX1.subset Set.sdiff_subset
  have unionX : K ∪ X1 = X := by
    ext x
    simp only [K, X1, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  have unionY : K ∪ B = Y := by
    ext x
    simp only [K, B, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  have unionR : R ∪ A = X1 := by
    ext x
    simp only [R, A, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  have restoreX : proj K X1 = X := by
    rw [proj_eq_union K X1 (unionX ▸ hX), unionX]
  have restoreY : proj K B = Y := by
    rw [proj_eq_union K B (unionY ▸ hY), unionY]
  have restoreR : proj R A = X1 := by
    rw [proj_eq_union R A (unionR ▸ hX1), unionR]
  have restoreB : proj R B = B := proj_absorbed R B Set.inter_subset_right
  have first : dC X Y hX hY ≤ dC X1 B hX1 hB := by
    simpa only [restoreX, restoreY] using projection_distance K X1 B hK hX1 hB
  have second : dC X1 B hX1 hB ≤ dC A B hA hB := by
    simpa only [restoreR, restoreB] using projection_distance R A B hR hA hB
  have union_antichain : IsAntichainSet (A ∪ B) := by
    rw [S4.isAntichainSet_iff_comp]
    have cross : ∀ x ∈ A, ∀ y ∈ B, ¬ Comp x y := by
      intro x hx y hy comparable
      exact hx.2 ⟨hx.1, y, hy, comparable⟩
    intro x hx y hy comparable
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (S4.isAntichainSet_iff_comp.mp hA) x hx y hy comparable
    · exact cross x hx y hy comparable
    · exact cross y hy x hx (S4.comp_symm comparable)
    · exact (S4.isAntichainSet_iff_comp.mp hB) x hx y hy comparable
  refine ⟨A, B, hA, hB, ?_, Set.sdiff_subset, ?_, first.trans second⟩
  · exact Set.Subset.trans Set.sdiff_subset Set.sdiff_subset
  · refine ⟨Set.disjoint_left.mpr ?_, rfl, union_antichain⟩
    intro x hx hy
    exact hx.1.2 hy.1

theorem split_diameter [Fintype P] :
    chainDiam P = sSup {d | ∃ (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B),
      IsSplit A B (A ∪ B) ∧ d = dC A B hA hB} := by
  apply le_antisymm
  · apply (chainDiam_le_iff _).mpr
    intro X Y hX hY
    obtain ⟨A, B, hA, hB, _, _, split, distance⟩ := split_reduction X Y hX hY
    exact distance.trans (le_sSup ⟨A, B, hA, hB, split, rfl⟩)
  · apply sSup_le
    rintro d ⟨A, B, hA, hB, _, rfl⟩
    rw [dC_eq, chainDiam_eq]
    exact SimpleGraph.edist_le_ediam

theorem split_reduction_all (P : Type) [Fintype P] [PartialOrder P] :
    (∀ (X Y : Set P) (hX : IsAntichainSet X) (hY : IsAntichainSet Y),
      ∃ (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B),
        A ⊆ X ∧ B ⊆ Y ∧ IsSplit A B (A ∪ B) ∧ dC X Y hX hY ≤ dC A B hA hB) ∧
    chainDiam P = sSup {d | ∃ (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B),
      IsSplit A B (A ∪ B) ∧ d = dC A B hA hB} :=
  ⟨split_reduction, split_diameter⟩

end SplitReduction

end LeeDiam


