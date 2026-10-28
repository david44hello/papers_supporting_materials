/-
Cartesian graph products for disjoint sums of posets.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Bridge.Graphs
import LeeDiam.Sec4.Comps
import LeeDiam.Sec1.Products
import LeeDiam.Sec2.ComponentPaths

namespace LeeDiam

open SimpleGraph

section SumGraphs

variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

theorem isConnSet_image_iff (f : P → Q) (injective : Function.Injective f)
    (comp_iff : ∀ x y, Comp (f x) (f y) ↔ Comp x y) (D : Set P) :
    IsConnSet (f '' D) ↔ IsConnSet D := by
  classical
  let equiv : ((compGraph P).induce D) ≃g ((compGraph Q).induce (f '' D)) :=
    { toEquiv := Equiv.Set.image f D injective
      map_rel_iff' := fun {x y} => comp_iff x.1 y.1 }
  exact equiv.connected_iff.symm

theorem isConnSet_sum_iff (D : Set (P ⊕ Q)) :
    IsConnSet D ↔
      (IsConnSet (Sum.inl ⁻¹' D) ∧ Sum.inr ⁻¹' D = ∅) ∨
      (IsConnSet (Sum.inr ⁻¹' D) ∧ Sum.inl ⁻¹' D = ∅) := by
  classical
  have left_image : ∀ A : Set P,
      IsConnSet ((Sum.inl : P → P ⊕ Q) '' A) ↔ IsConnSet A := by
    intro A
    apply isConnSet_image_iff _ Sum.inl_injective
    intro x y
    simp [Comp]
  have right_image : ∀ B : Set Q,
      IsConnSet ((Sum.inr : Q → P ⊕ Q) '' B) ↔ IsConnSet B := by
    intro B
    apply isConnSet_image_iff _ Sum.inr_injective
    intro x y
    simp [Comp]
  have left_equal : Sum.inr ⁻¹' D = ∅ → (Sum.inl : P → P ⊕ Q) '' (Sum.inl ⁻¹' D) = D := by
    intro empty
    ext x
    cases x with
    | inl x => simp
    | inr x =>
      have absent : Sum.inr x ∉ D := by change x ∉ Sum.inr ⁻¹' D; rw [empty]; simp
      simp [absent]
  have right_equal : Sum.inl ⁻¹' D = ∅ → (Sum.inr : Q → P ⊕ Q) '' (Sum.inr ⁻¹' D) = D := by
    intro empty
    ext x
    cases x with
    | inl x =>
      have absent : Sum.inl x ∉ D := by change x ∉ Sum.inl ⁻¹' D; rw [empty]; simp
      simp [absent]
    | inr x => simp
  constructor
  · intro connected
    obtain ⟨anchor⟩ := connected.nonempty
    have same_side : ∀ y ∈ D, (anchor.1.isLeft ↔ y.isLeft) := by
      intro y hy
      have path := S4.rtg_of_isConnSet connected Set.Subset.rfl anchor.2 hy
      clear hy
      induction path with
      | refl => rfl
      | @tail middle endpoint path edge ih =>
        have step : middle.isLeft ↔ endpoint.isLeft := by
          cases middle <;> cases endpoint <;> simp_all [Comp]
        exact ih.trans step
    cases equation : anchor.1 with
    | inl x =>
      have empty : Sum.inr ⁻¹' D = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have := same_side (Sum.inr y) hy
        simp [equation] at this
      left
      exact ⟨(left_image _).mp ((left_equal empty).symm ▸ connected), empty⟩
    | inr x =>
      have empty : Sum.inl ⁻¹' D = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have := same_side (Sum.inl y) hy
        simp [equation] at this
      right
      exact ⟨(right_image _).mp ((right_equal empty).symm ▸ connected), empty⟩
  · rintro (⟨left, empty⟩ | ⟨right, empty⟩)
    · exact left_equal empty ▸ (left_image _).mpr left
    · exact right_equal empty ▸ (right_image _).mpr right

theorem ideal_sum_iff (D : Set (P ⊕ Q)) :
    IsIdeal D ↔ IsIdeal (Sum.inl ⁻¹' D) ∧ IsIdeal (Sum.inr ⁻¹' D) := by
  constructor
  · intro ideal
    exact ⟨fun _ _ relation member => ideal (Sum.inl_le_inl_iff.mpr relation) member,
      fun _ _ relation member => ideal (Sum.inr_le_inr_iff.mpr relation) member⟩
  · rintro ⟨left, right⟩ x y relation member
    cases x <;> cases y <;> simp only [Sum.inl_le_inl_iff, Sum.inr_le_inr_iff,
      Sum.not_inl_le_inr, Sum.not_inr_le_inl] at relation
    · exact left relation member
    · exact right relation member

theorem antichain_sum_iff (D : Set (P ⊕ Q)) :
    IsAntichainSet D ↔ IsAntichainSet (Sum.inl ⁻¹' D) ∧ IsAntichainSet (Sum.inr ⁻¹' D) := by
  simp only [S4.isAntichainSet_iff_comp]
  constructor
  · intro antichain
    constructor
    · intro x hx y hy comparable
      exact antichain (Sum.inl x) hx (Sum.inl y) hy (by simpa [Comp] using comparable)
    · intro x hx y hy comparable
      exact antichain (Sum.inr x) hx (Sum.inr y) hy (by simpa [Comp] using comparable)
  · rintro ⟨left, right⟩ x hx y hy comparable
    cases x <;> cases y <;> simp only [Comp, Sum.inl_lt_inl_iff, Sum.inr_lt_inr_iff,
      Sum.not_inl_lt_inr, Sum.not_inr_lt_inl, or_self] at comparable
    · exact left _ hx _ hy comparable
    · exact right _ hx _ hy comparable

def sumSet (A : Set P) (B : Set Q) : Set (P ⊕ Q) := {x | Sum.elim (· ∈ A) (· ∈ B) x}

omit [PartialOrder P] [PartialOrder Q] in
theorem sumSet_left (A : Set P) (B : Set Q) : Sum.inl ⁻¹' sumSet A B = A := rfl
omit [PartialOrder P] [PartialOrder Q] in
theorem sumSet_right (A : Set P) (B : Set Q) : Sum.inr ⁻¹' sumSet A B = B := rfl

omit [PartialOrder P] [PartialOrder Q] in
theorem sumSet_preimages (D : Set (P ⊕ Q)) : sumSet (Sum.inl ⁻¹' D) (Sum.inr ⁻¹' D) = D := by
  ext x
  cases x <;> rfl

def idealSumEquiv : {D : Set (P ⊕ Q) // IsIdeal D} ≃
    ({A : Set P // IsIdeal A} × {B : Set Q // IsIdeal B}) where
  toFun D := (⟨Sum.inl ⁻¹' D.1, (ideal_sum_iff D.1).mp D.2 |>.1⟩,
    ⟨Sum.inr ⁻¹' D.1, (ideal_sum_iff D.1).mp D.2 |>.2⟩)
  invFun pair := ⟨sumSet pair.1.1 pair.2.1, (ideal_sum_iff _).mpr ⟨pair.1.2, pair.2.2⟩⟩
  left_inv D := Subtype.ext (sumSet_preimages D.1)
  right_inv _pair := rfl

def antichainSumEquiv : {D : Set (P ⊕ Q) // IsAntichainSet D} ≃
    ({A : Set P // IsAntichainSet A} × {B : Set Q // IsAntichainSet B}) where
  toFun D := (⟨Sum.inl ⁻¹' D.1, (antichain_sum_iff D.1).mp D.2 |>.1⟩,
    ⟨Sum.inr ⁻¹' D.1, (antichain_sum_iff D.1).mp D.2 |>.2⟩)
  invFun pair := ⟨sumSet pair.1.1 pair.2.1, (antichain_sum_iff _).mpr ⟨pair.1.2, pair.2.2⟩⟩
  left_inv D := Subtype.ext (sumSet_preimages D.1)
  right_inv _pair := rfl

def antichainGraph_sum_iso : antichainGraph (P ⊕ Q) ≃g antichainGraph P □ antichainGraph Q where
  toEquiv := antichainSumEquiv
  map_rel_iff' := by
    intro A B
    change (IsConnSet (symmDiff (Sum.inl ⁻¹' A.1) (Sum.inl ⁻¹' B.1)) ∧ _ = _ ∨
      IsConnSet (symmDiff (Sum.inr ⁻¹' A.1) (Sum.inr ⁻¹' B.1)) ∧ _ = _) ↔
      IsConnSet (symmDiff A.1 B.1)
    rw [isConnSet_sum_iff]
    simp only [Set.preimage_symmDiff, Set.symmDiff_eq_empty]
    have left_equal : (antichainSumEquiv A).1 = (antichainSumEquiv B).1 ↔
        Sum.inl ⁻¹' A.1 = Sum.inl ⁻¹' B.1 := Subtype.ext_iff
    have right_equal : (antichainSumEquiv A).2 = (antichainSumEquiv B).2 ↔
        Sum.inr ⁻¹' A.1 = Sum.inr ⁻¹' B.1 := Subtype.ext_iff
    rw [left_equal, right_equal]

theorem idealGraph_adj_iff_connected (I J : {D : Set P // IsIdeal D}) :
    (idealGraph P).Adj I J ↔ IsConnSet (symmDiff I.1 J.1) := by
  constructor
  · rintro (⟨subset, connected⟩ | ⟨subset, connected⟩)
    · have equal : symmDiff I.1 J.1 = J.1 \ I.1 := by
        ext x
        simp only [Set.mem_symmDiff, Set.mem_sdiff]
        have := @subset x
        tauto
      rwa [equal]
    · have equal : symmDiff I.1 J.1 = I.1 \ J.1 := by
        ext x
        simp only [Set.mem_symmDiff, Set.mem_sdiff]
        have := @subset x
        tauto
      rwa [equal]
  · exact ideal_adj_of_connected_difference I.2 J.2

def idealGraph_sum_iso : idealGraph (P ⊕ Q) ≃g idealGraph P □ idealGraph Q where
  toEquiv := idealSumEquiv
  map_rel_iff' := by
    intro I J
    rw [SimpleGraph.boxProd_adj, idealGraph_adj_iff_connected,
      idealGraph_adj_iff_connected, idealGraph_adj_iff_connected]
    change (IsConnSet (symmDiff (Sum.inl ⁻¹' I.1) (Sum.inl ⁻¹' J.1)) ∧ _ = _ ∨
      IsConnSet (symmDiff (Sum.inr ⁻¹' I.1) (Sum.inr ⁻¹' J.1)) ∧ _ = _) ↔
      IsConnSet (symmDiff I.1 J.1)
    rw [isConnSet_sum_iff]
    simp only [Set.preimage_symmDiff, Set.symmDiff_eq_empty]
    have left_equal : (idealSumEquiv I).1 = (idealSumEquiv J).1 ↔
        Sum.inl ⁻¹' I.1 = Sum.inl ⁻¹' J.1 := Subtype.ext_iff
    have right_equal : (idealSumEquiv I).2 = (idealSumEquiv J).2 ↔
        Sum.inr ⁻¹' I.1 = Sum.inr ⁻¹' J.1 := Subtype.ext_iff
    rw [left_equal, right_equal]

theorem order_diameter_sum [Fintype P] [Fintype Q] :
    orderDiam (P ⊕ Q) = orderDiam P + orderDiam Q := by
  let : Nonempty {D : Set P // IsIdeal D} := ⟨⟨∅, isLowerSet_empty⟩⟩
  let : Nonempty {D : Set Q // IsIdeal D} := ⟨⟨∅, isLowerSet_empty⟩⟩
  rw [orderDiam_eq, orderDiam_eq, orderDiam_eq,
    ← graphIso_ediam (idealGraph_sum_iso (P := P) (Q := Q)), box_ediam_eq_add]

theorem chain_diameter_sum [Fintype P] [Fintype Q] :
    chainDiam (P ⊕ Q) = chainDiam P + chainDiam Q := by
  let : Nonempty {D : Set P // IsAntichainSet D} := ⟨⟨∅, IsAntichain.empty⟩⟩
  let : Nonempty {D : Set Q // IsAntichainSet D} := ⟨⟨∅, IsAntichain.empty⟩⟩
  rw [chainDiam_eq, chainDiam_eq, chainDiam_eq,
    ← graphIso_ediam (antichainGraph_sum_iso (P := P) (Q := Q)), box_ediam_eq_add]

end SumGraphs

end LeeDiam
