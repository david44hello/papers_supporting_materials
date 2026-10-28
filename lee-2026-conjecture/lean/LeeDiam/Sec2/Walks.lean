/-
Walks, component unions, and distance estimates.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Bridge.Graphs
import LeeDiam.Sec4.Comps
import LeeDiam.Sec2.ComponentPaths
import LeeDiam.Sec2.Projections
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Vertices
import LeeDiam.Defs.Walks
import LeeDiam.Defs.Band
import LeeDiam.Defs.Pn
import LeeDiam.Cited.Lee26

namespace LeeDiam

open Finset

theorem sec2_walk_dist_proved {P : Type} [Fintype P] [PartialOrder P] (W : List (Set P)) (X Y : Set P)
    (hX : IsAntichainSet X) (hY : IsAntichainSet Y) (hW : IsWalkFromTo W X Y) :
    dC X Y hX hY ≤ ((W.length - 1 : ℕ) : ℕ∞) := by
  exact (dC_le_iff X Y hX hY (W.length - 1)).mpr ⟨W, hW, le_rfl⟩

theorem sec2_walk_reverse_proved {P : Type} [PartialOrder P] (W : List (Set P)) (hW : IsWalk W) : IsWalk W.reverse := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using hW.1
  · intro state member
    exact hW.2.1 state (List.mem_reverse.mp member)
  · apply List.isChain_reverse.mpr
    exact hW.2.2.imp (fun left right adjacent => by
      simpa only [symmDiff_comm] using adjacent)

theorem isCompUnion_iff_proved {P : Type} [Fintype P] [PartialOrder P] (C D : Set P) :
    IsCompUnion C D ↔ C ⊆ D ∧ ∀ x ∈ C, ∃ K, IsComponent K D ∧ x ∈ K ∧ K ⊆ C := by
  constructor
  · rintro ⟨subset, closed⟩
    refine ⟨subset, ?_⟩
    intro point member
    obtain ⟨component, is_component, in_component⟩ := S4.comp_exists (subset member)
    refine ⟨component, is_component, in_component, ?_⟩
    intro other other_member
    have reaches := S4.rtg_of_isConnSet is_component.1 is_component.2.1 in_component other_member
    clear other_member
    induction reaches with
    | refl => exact member
    | @tail middle endpoint _ step ih => exact closed middle ih endpoint step.2.1 step.2.2
  · rintro ⟨subset, covered⟩
    refine ⟨subset, ?_⟩
    intro point member other other_member comparable
    obtain ⟨component, is_component, in_component, inside⟩ := covered point member
    exact inside (S4.comp_closed is_component in_component other_member comparable)

theorem lem_2_2_proved {P : Type} [PartialOrder P] (I J C : Set P) (hI : IsIdeal I) (hJ : IsIdeal J) (_hJI : J ⊆ I)
    (hC : IsCompUnion C (I \ J)) : IsIdeal (J ∪ C) ∧ IsIdeal (I \ C) := by
  constructor
  · intro upper lower relation member
    rcases member with in_ideal | in_component
    · exact Or.inl (hJ relation in_ideal)
    · by_cases in_lower_ideal : lower ∈ J
      · exact Or.inl in_lower_ideal
      · right
        by_cases same : lower = upper
        · simpa only [same] using in_component
        · exact hC.2 upper in_component lower
            ⟨hI relation (hC.1 in_component).1, in_lower_ideal⟩
            (Or.inr (lt_of_le_of_ne relation same))
  · intro upper lower relation member
    refine ⟨hI relation member.1, ?_⟩
    intro lower_in_component
    by_cases same : lower = upper
    · exact member.2 (same ▸ lower_in_component)
    · have upper_outside : upper ∉ J := fun in_ideal =>
        (hC.1 lower_in_component).2 (hJ relation in_ideal)
      exact member.2 (hC.2 lower lower_in_component upper ⟨member.1, upper_outside⟩
        (Or.inl (lt_of_le_of_ne relation same)))

theorem prop_2_3_proved (P : Type) [Fintype P] [PartialOrder P] :
    (∀ (I J : Set P) (hI : IsIdeal I) (hJ : IsIdeal J), dO I J hI hJ ≤ numComp (symmDiff I J)) ∧
    (∀ (A B : Set P), IsAntichainSet A → IsAntichainSet B → ∀ L : List (Set P), L.Nodup →
      (∀ C, C ∈ L ↔ IsComponent C (symmDiff A B)) → IsWalkFromTo (L.scanl symmDiff A) A B) ∧
    (∀ (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B), dC A B hA hB ≤ numComp (symmDiff A B)) ∧
    orderDiam P ≤ width P ∧ chainDiam P ≤ width P := by
  exact component_bounds_all P

theorem lem_2_4_proj_proved {P : Type} [PartialOrder P] (R S S' : Set P) (hR : IsAntichainSet R) (hS : IsAntichainSet S)
    (hS' : IsAntichainSet S') (hSS' : IsConnSet (symmDiff S S')) :
    IsAntichainSet (proj R S) ∧ (proj R S = proj R S' ∨ IsConnSet (symmDiff (proj R S) (proj R S'))) := by
  exact ⟨proj_antichain R S hR hS, projection_edge R S S' hR hS hS' hSS'⟩

theorem lem_2_4_proj_dist_proved {P : Type} [Fintype P] [PartialOrder P] (R S S' : Set P)
    (hR : IsAntichainSet R) (hS : IsAntichainSet S) (hS' : IsAntichainSet S')
    (hp : IsAntichainSet (proj R S)) (hp' : IsAntichainSet (proj R S')) :
    dC (proj R S) (proj R S') hp hp' ≤ dC S S' hS hS' := by
  exact projection_distance R S S' hR hS hS'

theorem lem_2_4_proved (P : Type) [Fintype P] [PartialOrder P] :
    (∀ (X Y : Set P) (hX : IsAntichainSet X) (hY : IsAntichainSet Y), ∃ (A B : Set P) (hA : IsAntichainSet A)
      (hB : IsAntichainSet B), A ⊆ X ∧ B ⊆ Y ∧ IsSplit A B (A ∪ B) ∧ dC X Y hX hY ≤ dC A B hA hB) ∧
    chainDiam P = sSup {d | ∃ (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B),
      IsSplit A B (A ∪ B) ∧ d = dC A B hA hB} := by
  exact split_reduction_all P

end LeeDiam

