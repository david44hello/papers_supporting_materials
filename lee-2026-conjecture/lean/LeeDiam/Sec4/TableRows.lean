/-
LeeDiam/Sec4/TableRows.lean — Section 4 rows from review r1: Table 2 (tame bases), the walks `V` of Lemma 4.9 and the
column walks of Lemma 4.12 (sec_chain.tex v1.50 l. 82-94, 107-111, 141-142).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

The walks come from Sec4/Tame.lean (`base_one_walk`, `line2_walk`, `line3_walk`, `line4_walk`) and from the two column
walks below; every listed comparable pair is one case of `lt_iff_val`.
-/
import LeeDiam.Defs.Chain
import LeeDiam.Sec4.Tame

namespace LeeDiam.S4

open Band

section TableRows

variable {k : ℕ}

theorem symmDiff_singletons {x y : Band k} (hxy : x ≠ y) : symmDiff ({x} : Set (Band k)) {y} = {x, y} := by
  ext z
  simp only [Set.mem_symmDiff, Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, hxy⟩
    · exact Or.inr ⟨rfl, hxy.symm⟩

/-- The column walk of Lemma 4.12, Part 1, when `b` is initial: `b → c → a → -`. -/
theorem col_walk_init (q : Fin k) : IsWalkFromTo ([{b q}, {c q}, {a q}, ∅] : List (Set (Band k))) {b q} ∅ := by
  refine walk_four (isAntichainSet_singleton' _) (isAntichainSet_singleton' _) (isAntichainSet_singleton' _)
    (isAntichainSet_row 0 _ (by simp)) ?_ ?_ ?_
  · rw [symmDiff_singletons (b_ne_c q q)]
    exact isConnSet_pair (comp_bc_same q)
  · rw [symmDiff_singletons (a_ne_c q q).symm]
    exact isConnSet_pair (comp_symm (comp_ac_same q))
  · rw [← Set.bot_eq_empty, symmDiff_bot]
    exact isConnSet_singleton _

/-- The column walk of Lemma 4.12, Part 1, when `b` is final: `- → c → a → b`. -/
theorem col_walk_final (q : Fin k) : IsWalkFromTo ([∅, {c q}, {a q}, {b q}] : List (Set (Band k))) ∅ {b q} := by
  refine walk_four (isAntichainSet_row 0 _ (by simp)) (isAntichainSet_singleton' _) (isAntichainSet_singleton' _)
    (isAntichainSet_singleton' _) ?_ ?_ ?_
  · rw [← Set.bot_eq_empty, bot_symmDiff]
    exact isConnSet_singleton _
  · rw [symmDiff_singletons (a_ne_c q q).symm]
    exact isConnSet_pair (comp_symm (comp_ac_same q))
  · rw [symmDiff_singletons (a_ne_b q q)]
    exact isConnSet_pair (comp_ab_same q)

/-- Table 2, line 1: `b → c → -` on the first column is a walk with outer trace `(-, c_1, -)`. -/
theorem table_2_line1 (hk : 1 ≤ k) :
    IsWalk [{b ⟨0, hk⟩}, {c ⟨0, hk⟩}, (∅ : Set (Band k))] ∧
    outerTrace [{b ⟨0, hk⟩}, {c ⟨0, hk⟩}, (∅ : Set (Band k))] ⟨0, hk⟩ = [none, some (c ⟨0, hk⟩), none] :=
  ⟨(base_one_walk ⟨0, hk⟩).1.1, (base_one_walk ⟨0, hk⟩).2.2.2.2⟩

/-- Table 2, lines 2 and 3: walks with outer trace `(-, c_2, -)` at the second column; `a_1 < c_2` and `b_2 < c_1`. -/
theorem table_2_lines23 (hk : 2 ≤ k) :
    IsWalk [∅, {a ⟨0, by omega⟩}, {c ⟨0, by omega⟩, c ⟨1, hk⟩}, ({b ⟨0, by omega⟩, b ⟨1, hk⟩} : Set (Band k))] ∧
    outerTrace [∅, {a ⟨0, by omega⟩}, {c ⟨0, by omega⟩, c ⟨1, hk⟩},
      ({b ⟨0, by omega⟩, b ⟨1, hk⟩} : Set (Band k))] ⟨1, hk⟩ = [none, some (c ⟨1, hk⟩), none] ∧
    IsWalk [{b ⟨0, by omega⟩}, {a ⟨0, by omega⟩}, {c ⟨0, by omega⟩, c ⟨1, hk⟩}, ({b ⟨1, hk⟩} : Set (Band k))] ∧
    outerTrace [{b ⟨0, by omega⟩}, {a ⟨0, by omega⟩}, {c ⟨0, by omega⟩, c ⟨1, hk⟩},
      ({b ⟨1, hk⟩} : Set (Band k))] ⟨1, hk⟩ = [none, some (c ⟨1, hk⟩), none] ∧
    a ⟨0, by omega⟩ < (c ⟨1, hk⟩ : Band k) ∧ b ⟨1, hk⟩ < (c ⟨0, by omega⟩ : Band k) := by
  have h2 := line2_walk (i := (⟨0, by omega⟩ : Fin k)) (j := ⟨1, hk⟩) rfl
  have h3 := line3_walk (i := (⟨0, by omega⟩ : Fin k)) (j := ⟨1, hk⟩) rfl
  exact ⟨h2.1.1, h2.2.2.2.2, h3.1.1, h3.2.2.2.2, (lt_iff_val _ _).2 (Or.inr (Or.inr ⟨rfl, rfl, Or.inr (Or.inr rfl)⟩)),
    (lt_iff_val _ _).2 (Or.inr (Or.inl ⟨rfl, rfl, Or.inr rfl⟩))⟩

/-- The two walks `V` of the proof of Lemma 4.9 (l. 108-112) and the comparable pairs listed there. -/
theorem lem_4_9_V (q r : Fin k) (hqr : r.val = q.val + 1) :
    IsWalk [∅, {a q}, {c q, c r}, ({b q, b r} : Set (Band k))] ∧
    IsWalk [{b r}, {a q, a r}, {c q}, ({b q} : Set (Band k))] ∧
    a q < c q ∧ a q < c r ∧ b q < c q ∧ b r < c q ∧
    b r < c r ∧ a q < b r ∧ a r < b r ∧ a r < c q :=
  ⟨(line2_walk hqr).1.1, (line4_walk hqr).1.1,
    (lt_iff_val _ _).2 (Or.inr (Or.inr ⟨rfl, rfl, Or.inr (Or.inl rfl)⟩)),
    (lt_iff_val _ _).2 (Or.inr (Or.inr ⟨rfl, rfl, Or.inr (Or.inr hqr)⟩)),
    (lt_iff_val _ _).2 (Or.inr (Or.inl ⟨rfl, rfl, Or.inl rfl⟩)),
    (lt_iff_val _ _).2 (Or.inr (Or.inl ⟨rfl, rfl, Or.inr hqr.symm⟩)),
    (lt_iff_val _ _).2 (Or.inr (Or.inl ⟨rfl, rfl, Or.inl rfl⟩)),
    (lt_iff_val _ _).2 (Or.inl ⟨rfl, rfl, Or.inr hqr⟩),
    (lt_iff_val _ _).2 (Or.inl ⟨rfl, rfl, Or.inl rfl⟩),
    (lt_iff_val _ _).2 (Or.inr (Or.inr ⟨rfl, rfl, Or.inl hqr.symm⟩))⟩

/-- The two column walks of Lemma 4.12, Part 1 (l. 142-143). -/
theorem lem_4_12_columns (e : Fin k) :
    IsWalk [{b e}, {c e}, {a e}, (∅ : Set (Band k))] ∧ IsWalk [∅, {c e}, {a e}, ({b e} : Set (Band k))] :=
  ⟨(col_walk_init e).1, (col_walk_final e).1⟩

end TableRows

end LeeDiam.S4

