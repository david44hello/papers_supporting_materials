/-
LeeDiam/Defs/Pn.lean — the posets P_n of paper 004 (short v1.50, Definition 6.1, sec_reverse.tex l. 35-52).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

TRUST SURFACE. Elements (indices `i, j ∈ [n]` are `Fin n`, 0-based): targets `a i`, `b j`; pair minima `m E`, `m' E` for
each 2-element subset `E ⊆ [n]`; lower connectors `y i`, `y' j`; the hub `h`; upper connectors `w i`, `w' j`; tops
`t i j`. The order is the reflexive and transitive closure of the relations of Definition 6.1:
  m_E < y_i (i ∈ E), y_i < a_i, y_i < h, m'_E < y'_j (j ∈ E), y'_j < b_j, y'_j < h,
  a_i < w_i, h < w_i, b_j < w'_j, h < w'_j, w_i < t_ij, w'_j < t_ij.
Antisymmetry is proved from a level function (0 for pair minima, 1 for lower connectors, 2 for targets and the hub,
3 for upper connectors, 4 for tops), which every generating relation raises.
-/
import Mathlib

namespace LeeDiam

/-- The 2-element subsets of `[n]`. -/
abbrev Pair (n : ℕ) : Type := {E : Finset (Fin n) // E.card = 2}

/-- The elements of `P_n` (Definition 6.1). -/
inductive PnElem (n : ℕ) where
  | a : Fin n → PnElem n
  | b : Fin n → PnElem n
  | m : Pair n → PnElem n
  | m' : Pair n → PnElem n
  | y : Fin n → PnElem n
  | y' : Fin n → PnElem n
  | h : PnElem n
  | w : Fin n → PnElem n
  | w' : Fin n → PnElem n
  | t : Fin n → Fin n → PnElem n
  deriving DecidableEq, Fintype

namespace PnElem

variable {n : ℕ}

/-- The generating relations of Definition 6.1. -/
inductive Rel : PnElem n → PnElem n → Prop
  | m_y (E : Pair n) (i : Fin n) (hi : i ∈ E.1) : Rel (m E) (y i)
  | y_a (i : Fin n) : Rel (y i) (a i)
  | y_h (i : Fin n) : Rel (y i) h
  | m'_y' (E : Pair n) (j : Fin n) (hj : j ∈ E.1) : Rel (m' E) (y' j)
  | y'_b (j : Fin n) : Rel (y' j) (b j)
  | y'_h (j : Fin n) : Rel (y' j) h
  | a_w (i : Fin n) : Rel (a i) (w i)
  | h_w (i : Fin n) : Rel h (w i)
  | b_w' (j : Fin n) : Rel (b j) (w' j)
  | h_w' (j : Fin n) : Rel h (w' j)
  | w_t (i j : Fin n) : Rel (w i) (t i j)
  | w'_t (i j : Fin n) : Rel (w' j) (t i j)

/-- The level used for antisymmetry. -/
def level : PnElem n → ℕ
  | m _ | m' _ => 0
  | y _ | y' _ => 1
  | a _ | b _ | h => 2
  | w _ | w' _ => 3
  | t _ _ => 4

theorem level_lt_of_rel {x z : PnElem n} (hr : Rel x z) : level x < level z := by
  cases hr <;> simp [level]

theorem rtc_level {x z : PnElem n} (hr : Relation.ReflTransGen Rel x z) : x = z ∨ level x < level z := by
  induction hr with
  | refl => exact Or.inl rfl
  | tail _ hyz ih =>
    have := level_lt_of_rel hyz
    rcases ih with rfl | hlt
    · exact Or.inr this
    · exact Or.inr (by omega)

end PnElem

/-- The poset `P_n` (Definition 6.1) as a type (reducible, so the order below also applies to the constructors
`PnElem.a i`, … written in statements). -/
abbrev Pn (n : ℕ) : Type := PnElem n

instance (n : ℕ) : Fintype (Pn n) := inferInstanceAs (Fintype (PnElem n))
instance (n : ℕ) : DecidableEq (Pn n) := inferInstanceAs (DecidableEq (PnElem n))

/-- The order of `P_n`: the reflexive and transitive closure of the relations of Definition 6.1. -/
instance (n : ℕ) : PartialOrder (Pn n) where
  le := Relation.ReflTransGen (PnElem.Rel (n := n))
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm x z hxz hzx := by
    rcases PnElem.rtc_level hxz with hh | hh
    · exact hh
    · rcases PnElem.rtc_level hzx with hh' | hh'
      · exact hh'.symm
      · omega

end LeeDiam
