/-
LeeDiam/Sec6/PnOrder.lean — the order of the poset P_n of Section 6 of paper 004 as an explicit table, with the
basic consequences used by Sections 6.1-6.3 (comparability, the level function, one-level antichains).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Vertices
import LeeDiam.Defs.Pn

namespace LeeDiam.PnOrder

open PnElem

variable {n : ℕ}

/-- The order of `P_n` as an explicit table (reflexive): `ple x z ↔ x ≤ z` (`le_iff_ple`). -/
def ple : PnElem n → PnElem n → Prop
  | m E, m F => E = F | m E, y i => i ∈ E.1 | m E, a i => i ∈ E.1
  | m _, h => True | m _, w _ => True | m _, w' _ => True | m _, t _ _ => True
  | m' E, m' F => E = F | m' E, y' j => j ∈ E.1 | m' E, b j => j ∈ E.1
  | m' _, h => True | m' _, w _ => True | m' _, w' _ => True | m' _, t _ _ => True
  | y i, y k => i = k | y i, a k => i = k | y _, h => True | y _, w _ => True | y _, w' _ => True
  | y _, t _ _ => True
  | y' j, y' l => j = l | y' j, b l => j = l | y' _, h => True | y' _, w _ => True | y' _, w' _ => True
  | y' _, t _ _ => True
  | a i, a k => i = k | a i, w k => i = k | a i, t k _ => i = k
  | b j, b l => j = l | b j, w' l => j = l | b j, t _ l => j = l
  | h, h => True | h, w _ => True | h, w' _ => True | h, t _ _ => True
  | w i, w k => i = k | w i, t k _ => i = k | w' j, w' l => j = l | w' j, t _ l => j = l
  | t i j, t k l => i = k ∧ j = l
  | _, _ => False

instance (x z : PnElem n) : Decidable (ple x z) := by
  cases x <;> cases z <;> dsimp only [ple] <;> infer_instance

/-- A pair `E` (two elements) is nonempty. -/
theorem pair_nonempty (E : Pair n) : ∃ i, i ∈ E.1 :=
  Finset.card_pos.1 (by rw [E.2]; norm_num)

theorem rel_le {x z : PnElem n} (hr : Rel x z) : (x : Pn n) ≤ z := Relation.ReflTransGen.single hr

theorem m_le_h (E : Pair n) : (m E : Pn n) ≤ h := by
  obtain ⟨i, hi⟩ := pair_nonempty E
  exact (rel_le (.m_y E i hi)).trans (rel_le (.y_h i))

theorem m'_le_h (E : Pair n) : (m' E : Pn n) ≤ h := by
  obtain ⟨i, hi⟩ := pair_nonempty E
  exact (rel_le (.m'_y' E i hi)).trans (rel_le (.y'_h i))

theorem h_le_t (i j : Fin n) : (h : Pn n) ≤ t i j := (rel_le (.h_w i)).trans (rel_le (.w_t i j))

theorem ple_le {x z : PnElem n} (hp : ple x z) : (x : Pn n) ≤ z := by
  cases x <;> cases z <;> simp only [ple] at hp
  all_goals (try subst hp)
  all_goals first
    | exact le_rfl
    | (obtain ⟨rfl, rfl⟩ := hp; exact le_rfl)
    | exact rel_le (.m_y _ _ hp)
    | exact (rel_le (.m_y _ _ hp)).trans (rel_le (.y_a _))
    | exact m_le_h _
    | exact (m_le_h _).trans (rel_le (.h_w _))
    | exact (m_le_h _).trans (rel_le (.h_w' _))
    | exact (m_le_h _).trans (h_le_t _ _)
    | exact rel_le (.m'_y' _ _ hp)
    | exact (rel_le (.m'_y' _ _ hp)).trans (rel_le (.y'_b _))
    | exact m'_le_h _
    | exact (m'_le_h _).trans (rel_le (.h_w _))
    | exact (m'_le_h _).trans (rel_le (.h_w' _))
    | exact (m'_le_h _).trans (h_le_t _ _)
    | exact rel_le (.y_a _)
    | exact rel_le (.y_h _)
    | exact (rel_le (.y_h _)).trans (rel_le (.h_w _))
    | exact (rel_le (.y_h _)).trans (rel_le (.h_w' _))
    | exact (rel_le (.y_h _)).trans (h_le_t _ _)
    | exact rel_le (.y'_b _)
    | exact rel_le (.y'_h _)
    | exact (rel_le (.y'_h _)).trans (rel_le (.h_w _))
    | exact (rel_le (.y'_h _)).trans (rel_le (.h_w' _))
    | exact (rel_le (.y'_h _)).trans (h_le_t _ _)
    | exact rel_le (.a_w _)
    | exact (rel_le (.a_w _)).trans (rel_le (.w_t _ _))
    | exact rel_le (.b_w' _)
    | exact (rel_le (.b_w' _)).trans (rel_le (.w'_t _ _))
    | exact rel_le (.h_w _)
    | exact rel_le (.h_w' _)
    | exact h_le_t _ _
    | exact rel_le (.w_t _ _)
    | exact rel_le (.w'_t _ _)

theorem le_ple {x z : PnElem n} (hle : (x : Pn n) ≤ z) : ple x z := by
  change Relation.ReflTransGen Rel x z at hle
  induction hle with
  | refl => cases x <;> simp [ple]
  | tail _ hr ih => cases hr <;> cases x <;> simp_all [ple]

/-- The order of `P_n` is the explicit table `ple`. -/
theorem le_iff_ple {x z : PnElem n} : (x : Pn n) ≤ z ↔ ple x z := ⟨le_ple, ple_le⟩

theorem lt_iff_ple {x z : PnElem n} : (x : Pn n) < z ↔ ple x z ∧ x ≠ z := by
  rw [lt_iff_le_and_ne, le_iff_ple]

theorem comp_iff_ple {x z : PnElem n} : Comp (x : Pn n) z ↔ (ple x z ∨ ple z x) ∧ x ≠ z := by
  unfold Comp
  rw [lt_iff_ple, lt_iff_ple]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, fun e => h2 e.symm⟩
  · rintro ⟨h1 | h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, fun e => h2 e.symm⟩

/-- The level rises strictly along `<`. -/
theorem lt_level {x z : PnElem n} (hlt : (x : Pn n) < z) : level x < level z := by
  rcases rtc_level hlt.le with e | e
  · exact absurd e hlt.ne
  · exact e

/-- A set of elements of one level is an antichain. -/
theorem isAntichainSet_of_level (S : Set (Pn n)) (c : ℕ) (hS : ∀ x ∈ S, level x = c) : IsAntichainSet S := by
  intro x hx z hz hne hle
  have hl := lt_level (lt_of_le_of_ne hle hne)
  rw [hS x hx, hS z hz] at hl
  exact lt_irrefl _ hl

end LeeDiam.PnOrder
