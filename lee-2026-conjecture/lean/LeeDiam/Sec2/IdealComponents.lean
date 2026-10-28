/-
LeeDiam/Sec2/IdealComponents.lean — the first step of the paper's proof of Proposition 2.3 (main l. 160): for ideals
`I, J`, no element of `I \ J` is comparable to an element of `J \ I`, so the components of `I △ J` are those of
`I \ J` and those of `J \ I`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Sec4.BandOrder

namespace LeeDiam

namespace S2

variable {P : Type} [PartialOrder P]

/-- A connected subset of `A ∪ B`, with no element of `A` comparable to an element of `B`, lies in `A` or in `B`. -/
theorem conn_sub_of_sep {A B C : Set P} (hsep : ∀ x ∈ A, ∀ y ∈ B, ¬ Comp x y) (hC : IsConnSet C) (hCAB : C ⊆ A ∪ B) :
    C ⊆ A ∨ C ⊆ B := by
  by_cases hA : ∃ x ∈ C, x ∈ A
  · obtain ⟨x, hxC, hxA⟩ := hA
    left
    intro y hyC
    by_contra hyA
    obtain ⟨u, huC, v, hvC, huA, hvA, huv⟩ := S4.isConnSet_cross hC (· ∈ A) hxC hyC hxA hyA
    exact hsep u huA v ((hCAB hvC).resolve_left hvA) huv
  · simp only [not_exists, not_and] at hA
    exact Or.inr fun y hyC => (hCAB hyC).resolve_left (hA y hyC)

/-- The components of `A ∪ B` (disjoint, no comparable pair across) are the components of `A` and those of `B`. -/
theorem isComponent_union_iff {A B C : Set P} (hdisj : Disjoint A B) (hsep : ∀ x ∈ A, ∀ y ∈ B, ¬ Comp x y) :
    IsComponent C (A ∪ B) ↔ IsComponent C A ∨ IsComponent C B := by
  have hsep' : ∀ x ∈ B, ∀ y ∈ A, ¬ Comp x y := fun x hx y hy hxy => hsep y hy x hx (S4.comp_symm hxy)
  constructor
  · rintro ⟨hC, hCS, hmax⟩
    rcases conn_sub_of_sep hsep hC hCS with hCA | hCB
    · exact Or.inl ⟨hC, hCA, fun C' hC' hCC' hC'A => hmax C' hC' hCC' (hC'A.trans Set.subset_union_left)⟩
    · exact Or.inr ⟨hC, hCB, fun C' hC' hCC' hC'B => hmax C' hC' hCC' (hC'B.trans Set.subset_union_right)⟩
  · rintro (⟨hC, hCA, hmax⟩ | ⟨hC, hCB, hmax⟩)
    · refine ⟨hC, hCA.trans Set.subset_union_left, fun C' hC' hCC' hC'S => ?_⟩
      rcases conn_sub_of_sep hsep hC' hC'S with hC'A | hC'B
      · exact hmax C' hC' hCC' hC'A
      · obtain ⟨x, hx⟩ := S4.isConnSet_nonempty hC
        exact absurd (hC'B (hCC' hx)) (Set.disjoint_left.1 hdisj (hCA hx))
    · refine ⟨hC, hCB.trans Set.subset_union_right, fun C' hC' hCC' hC'S => ?_⟩
      rcases conn_sub_of_sep hsep hC' hC'S with hC'A | hC'B
      · obtain ⟨x, hx⟩ := S4.isConnSet_nonempty hC
        exact absurd (hC'A (hCC' hx)) (Set.disjoint_right.1 hdisj (hCB hx))
      · exact hmax C' hC' hCC' hC'B

end S2

theorem prop_2_3_components_proved (P : Type) [Fintype P] [PartialOrder P] (I J : Set P) (hI : IsIdeal I)
    (hJ : IsIdeal J) :
    (∀ x ∈ I \ J, ∀ y ∈ J \ I, ¬ Comp x y) ∧
    ∀ C : Set P, IsComponent C (symmDiff I J) ↔ IsComponent C (I \ J) ∨ IsComponent C (J \ I) := by
  have hsep : ∀ x ∈ I \ J, ∀ y ∈ J \ I, ¬ Comp x y := by
    rintro x ⟨hxI, hxJ⟩ y ⟨hyJ, hyI⟩ (hxy | hyx)
    · exact hxJ (hJ hxy.le hyJ)
    · exact hyI (hI hyx.le hxI)
  refine ⟨hsep, fun C => ?_⟩
  rw [Set.symmDiff_def]
  exact S2.isComponent_union_iff disjoint_sdiff_sdiff hsep

end LeeDiam
