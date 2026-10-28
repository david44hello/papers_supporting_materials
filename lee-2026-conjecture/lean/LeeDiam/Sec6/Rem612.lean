/-
The three-step chain-polytope walk for the two small posets.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Sec6.ChainHelp
import LeeDiam.Sec5.Upper

namespace LeeDiam.S6C

open PnSets PnOrder

variable {n : ℕ}

theorem small_retained_mem_pair (hn : n = 2 ∨ n = 3) (E : Pair n)
    (hE : E.1 = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩}) (i : Fin n) (hi : i ≠ ⟨0, by omega⟩) :
    i ∈ E.1 := by
  rw [hE, Finset.mem_insert, Finset.mem_singleton]
  have nonzero : i.val ≠ 0 := fun equal => hi (Fin.ext equal)
  have cases : i.val = n - 2 ∨ i.val = n - 1 := by rcases hn with rfl | rfl <;> omega
  exact cases.elim (fun equal => Or.inl (Fin.ext equal)) (fun equal => Or.inr (Fin.ext equal))

theorem row_state_antichain (i : Fin n) :
    IsAntichainSet ((tgtA n \ {PnElem.a i}) ∪ {x | ∃ j, x = PnElem.t i j}) := by
  obtain ⟨hA, _, _, _, _⟩ := sec6_antichains_proved n
  rw [S4.isAntichainSet_iff_comp]
  intro x hx y hy comparable
  rcases hx with ⟨⟨k, rfl⟩, excluded⟩ | ⟨j, rfl⟩ <;>
    rcases hy with ⟨⟨l, rfl⟩, excluded'⟩ | ⟨q, rfl⟩
  · exact (S4.isAntichainSet_iff_comp.mp hA) _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ comparable
  · have equal : k = i := by simpa [comp_iff_ple, ple] using comparable
    exact excluded (by simp [equal])
  · have equal : l = i := by simpa [comp_iff_ple, ple, eq_comm] using comparable
    exact excluded' (by simp [equal])
  · simp [comp_iff_ple, ple, eq_comm] at comparable

theorem inserted_min_antichain (E : Pair n) : IsAntichainSet (insert (PnElem.m E) (tgtB n)) := by
  obtain ⟨_, hB, _, _, _⟩ := sec6_antichains_proved n
  rw [S4.isAntichainSet_iff_comp]
  intro x hx y hy comparable
  rcases hx with rfl | ⟨j, rfl⟩ <;> rcases hy with rfl | ⟨q, rfl⟩
  · simp [comp_iff_ple, ple] at comparable
  · simp [comp_iff_ple, ple] at comparable
  · simp [comp_iff_ple, ple] at comparable
  · exact (S4.isAntichainSet_iff_comp.mp hB) _ ⟨j, rfl⟩ _ ⟨q, rfl⟩ comparable

theorem row_first_difference (i : Fin n) :
    symmDiff (tgtA n) ((tgtA n \ {PnElem.a i}) ∪ {x | ∃ j, x = PnElem.t i j}) =
      insert (PnElem.a i) {x | ∃ j, x = PnElem.t i j} := by
  ext x
  cases x <;> simp [tgtA, Set.mem_symmDiff]

theorem row_first_connected (i : Fin n) :
    IsConnSet (symmDiff (tgtA n) ((tgtA n \ {PnElem.a i}) ∪ {x | ∃ j, x = PnElem.t i j})) := by
  rw [row_first_difference]
  apply S4.isConnSet_of_rtg (Set.mem_insert _ _)
  intro x hx
  rcases hx with rfl | ⟨j, rfl⟩
  · exact .refl
  · exact Relation.ReflTransGen.single ⟨Set.mem_insert _ _, Or.inr ⟨j, rfl⟩,
      Or.inl (lt_iff_ple.mpr ⟨by simp [ple], by intro equal; cases equal⟩)⟩

theorem inserted_min_difference (E : Pair n) :
    symmDiff (insert (PnElem.m E) (tgtB n)) (tgtB n) = {PnElem.m E} := by
  ext x
  cases x <;> simp [tgtB, Set.mem_symmDiff]

theorem row_middle_connected (hn : n = 2 ∨ n = 3) (E : Pair n)
    (hE : E.1 = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩}) :
    IsConnSet (symmDiff
      ((tgtA n \ {PnElem.a ⟨0, by omega⟩}) ∪ {x | ∃ j, x = PnElem.t ⟨0, by omega⟩ j})
      (insert (PnElem.m E) (tgtB n))) := by
  let i0 : Fin n := ⟨0, by omega⟩
  let X := (tgtA n \ {PnElem.a i0}) ∪ {x | ∃ j, x = PnElem.t i0 j}
  let Y := insert (PnElem.m E) (tgtB n)
  let D := symmDiff X Y
  have memM : (PnElem.m E : Pn n) ∈ D := by simp [D, X, Y, tgtA, tgtB, Set.mem_symmDiff]
  have memT : ∀ j, (PnElem.t i0 j : Pn n) ∈ D := by
    intro j
    simp [D, X, Y, tgtA, tgtB, Set.mem_symmDiff]
  have memB : ∀ j, (PnElem.b j : Pn n) ∈ D := by
    intro j
    simp [D, X, Y, tgtA, tgtB, Set.mem_symmDiff]
  have compMT : ∀ j, Comp (PnElem.m E : Pn n) (PnElem.t i0 j) := by
    intro j
    exact Or.inl (lt_iff_ple.mpr ⟨by simp [ple], by intro equal; cases equal⟩)
  have compBT : ∀ j, Comp (PnElem.b j : Pn n) (PnElem.t i0 j) := by
    intro j
    exact Or.inl (lt_iff_ple.mpr ⟨by simp [ple], by intro equal; cases equal⟩)
  apply S4.isConnSet_of_rtg memM
  intro x hx
  change x ∈ D at hx
  rcases Set.mem_symmDiff.mp hx with ⟨hx, _⟩ | ⟨hx, _⟩
  · rcases hx with ⟨⟨i, rfl⟩, excluded⟩ | ⟨j, rfl⟩
    · have different : i ≠ i0 := by intro equal; exact excluded (by simp [equal])
      exact Relation.ReflTransGen.single ⟨memM, hx, comp_m_a E i (small_retained_mem_pair hn E hE i different)⟩
    · exact Relation.ReflTransGen.single ⟨memM, memT j, compMT j⟩
  · rcases hx with rfl | ⟨j, rfl⟩
    · exact .refl
    · exact Relation.ReflTransGen.head ⟨memM, memT j, compMT j⟩
        (Relation.ReflTransGen.single ⟨memT j, memB j, S4.comp_symm (compBT j)⟩)

theorem rem_6_12 (n : ℕ) (hn : n = 2 ∨ n = 3) :
    (∃ E : Pair n, E.1 = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩}) ∧
    ∀ E : Pair n, E.1 = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} →
      IsWalkFromTo [tgtA n, (tgtA n \ {PnElem.a ⟨0, by omega⟩}) ∪ {x | ∃ j, x = PnElem.t ⟨0, by omega⟩ j},
          insert (PnElem.m E) (tgtB n), tgtB n] (tgtA n) (tgtB n) ∧
        IsTypeH n ((tgtA n \ {PnElem.a ⟨0, by omega⟩}) ∪ {x | ∃ j, x = PnElem.t ⟨0, by omega⟩ j}) ∧
        (tgtA n \ {PnElem.a ⟨0, by omega⟩}) ∪ {x | ∃ j, x = PnElem.t ⟨0, by omega⟩ j} ∈ nbhdC (tgtA n) ∧
        IsTypeE' n (insert (PnElem.m E) (tgtB n)) ∧ insert (PnElem.m E) (tgtB n) ∈ nbhdC (tgtB n) := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  constructor
  · refine ⟨pr ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ ?_, rfl⟩
    intro equal
    have := congrArg Fin.val equal
    dsimp at this
    omega
  · intro E hE
    let X := (tgtA n \ {PnElem.a i0}) ∪ {x | ∃ j, x = PnElem.t i0 j}
    let Y := insert (PnElem.m E) (tgtB n)
    obtain ⟨hA, hB, _, _, _⟩ := sec6_antichains_proved n
    have hX : IsAntichainSet X := row_state_antichain i0
    have hY : IsAntichainSet Y := inserted_min_antichain E
    have connAX : IsConnSet (symmDiff (tgtA n) X) := row_first_connected i0
    have connXY : IsConnSet (symmDiff X Y) := row_middle_connected hn E hE
    have connYB : IsConnSet (symmDiff Y (tgtB n)) := by
      rw [inserted_min_difference]
      apply S4.isConnSet_of_rtg (show PnElem.m E ∈ ({PnElem.m E} : Set (Pn n)) from rfl)
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨⟨by simp, ?_, ?_⟩, rfl, rfl⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro state (rfl | rfl | rfl | rfl)
        exacts [hA, hX, hY, hB]
      · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
        exact ⟨connAX, connXY, connYB⟩
    · exact ⟨i0, {x | ∃ j, x = PnElem.t i0 j}, Or.inr ⟨⟨PnElem.t i0 i0, i0, rfl⟩, Set.Subset.rfl⟩, rfl⟩
    · exact ⟨hA, hX, S5.dC_le_one _ _ hA hX (Or.inr connAX)⟩
    · refine ⟨PnElem.m E, ?_, rfl⟩
      constructor
      · rintro ⟨j, equal⟩; cases equal
      · rintro u ⟨j, rfl⟩ comparable
        simp [comp_iff_ple, ple] at comparable
    · refine ⟨hB, hY, S5.dC_le_one _ _ hB hY (Or.inr ?_)⟩
      simpa only [symmDiff_comm] using connYB

end LeeDiam.S6C

