/-
LeeDiam/Sec6/Sets.lean — two in-text facts of Section 6 of paper 004 about the poset P_n: the elements below y_i are
the pair minima m_E with i ∈ E, and there are n - 1 of them; and the explicit up-set of y_i and down-sets of w_i and
t_ij. All from the explicit order table `ple` (LeeDiam/Sec6/PnOrder.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Pn
import LeeDiam.Defs.PnSets
import LeeDiam.Sec6.PnOrder

namespace LeeDiam

open PnSets PnOrder

/-- The pair `{i, k}` for `k ≠ i`. -/
def S6.pairWith {n : ℕ} (i : Fin n) (k : {k : Fin n // k ≠ i}) : Pair n :=
  ⟨{i, k.1}, Finset.card_pair (Ne.symm k.2)⟩

theorem S6.pairWith_injective {n : ℕ} (i : Fin n) : Function.Injective (S6.pairWith i) := by
  intro k₁ k₂ h
  have hmem : k₁.1 ∈ ({i, k₂.1} : Finset (Fin n)) := by
    have := congrArg Subtype.val h
    simp only [S6.pairWith] at this
    rw [← this]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rcases Finset.mem_insert.1 hmem with h1 | h1
  · exact absurd h1 k₁.2
  · exact Subtype.ext (Finset.mem_singleton.1 h1)

/-- The pairs that contain `i` are exactly the pairs `{i, k}`, `k ≠ i`. -/
theorem S6.mem_range_pairWith {n : ℕ} (i : Fin n) (E : Pair n) : i ∈ E.1 ↔ E ∈ Set.range (S6.pairWith i) := by
  constructor
  · intro hi
    obtain ⟨x, z, hxz, hE⟩ := Finset.card_eq_two.1 E.2
    rw [hE, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨⟨z, Ne.symm hxz⟩, Subtype.ext (by simp [S6.pairWith, hE])⟩
    · exact ⟨⟨x, hxz⟩, Subtype.ext (by simp [S6.pairWith, hE, Finset.pair_comm])⟩
  · rintro ⟨k, rfl⟩
    exact Finset.mem_insert_self _ _

/-- tex l.85: the elements below `y_i` are the pair minima `m_E` with `i ∈ E`; there are `n - 1` of them. -/
theorem S6.l85 (n : ℕ) (i : Fin n) :
    {x : Pn n | x < PnElem.y i} = {x | ∃ E : Pair n, i ∈ E.1 ∧ x = PnElem.m E} ∧
    {x : Pn n | x < PnElem.y i}.ncard = n - 1 := by
  have hset : {x : Pn n | x < PnElem.y i} = {x | ∃ E : Pair n, i ∈ E.1 ∧ x = PnElem.m E} := by
    ext x
    cases x <;> simp [lt_iff_ple, ple, -Subtype.exists]
  refine ⟨hset, ?_⟩
  have hrange : {x : Pn n | ∃ E : Pair n, i ∈ E.1 ∧ x = PnElem.m E} =
      Set.range (fun k : {k : Fin n // k ≠ i} => (PnElem.m (S6.pairWith i k) : Pn n)) := by
    ext x
    constructor
    · rintro ⟨E, hi, rfl⟩
      obtain ⟨k, hk⟩ := (S6.mem_range_pairWith i E).1 hi
      exact ⟨k, congrArg PnElem.m hk⟩
    · rintro ⟨k, rfl⟩
      exact ⟨S6.pairWith i k, (S6.mem_range_pairWith i _).2 ⟨k, rfl⟩, rfl⟩
  have hinj : Function.Injective (fun k : {k : Fin n // k ≠ i} => (PnElem.m (S6.pairWith i k) : Pn n)) :=
    fun k₁ k₂ h => S6.pairWith_injective i (PnElem.m.inj h)
  rw [hset, hrange, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, Fintype.card_fin]

/-- tex l.105: the up-set of `y_i` and the down-sets of `w_i` and of `t_ij`. -/
theorem S6.updown (n : ℕ) (i j : Fin n) :
    {x : Pn n | PnElem.y i ≤ x} = {PnElem.y i, PnElem.a i} ∪ {x | PnElem.h ≤ x} ∧
    {x : Pn n | x ≤ PnElem.w i} = {PnElem.w i, PnElem.a i, PnElem.h} ∪ qSet n ∧
    {x : Pn n | x ≤ PnElem.t i j} =
      {PnElem.t i j, PnElem.w i, PnElem.w' j, PnElem.a i, PnElem.b j, PnElem.h} ∪ qSet n := by
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;> cases x <;>
    simp [le_iff_ple, ple, qSet, pairMinA, pairMinB, lowA, lowB, -Subtype.exists, eq_comm]

end LeeDiam
