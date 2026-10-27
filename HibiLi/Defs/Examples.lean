/-
HibiLi/Defs/Examples.lean — the concrete posets of the paper: the poset X, the 2-chain, and the sharpness family P_n.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Poset

namespace HibiLi

/-- The five elements of the poset `X` (paper Figure 1): `a, b < c < g, h`. -/
inductive XElem
  | a | b | c | g | h
  deriving DecidableEq, Repr

namespace XElem

instance : Fintype XElem :=
  ⟨{a, b, c, g, h}, by intro x; cases x <;> simp⟩

/-- Rank of an element of `X` (0 for `a, b`; 1 for `c`; 2 for `g, h`). -/
def rank : XElem → ℕ
  | a => 0 | b => 0 | c => 1 | g => 2 | h => 2

/-- The order of `X`: `x ≤ y` iff `x = y` or `rank x < rank y`.  With ranks `a, b ↦ 0`, `c ↦ 1`, `g, h ↦ 2` this is
exactly `a, b < c < g, h` with `a, b` incomparable and `g, h` incomparable (equal rank, distinct). -/
def le (x y : XElem) : Prop := x = y ∨ x.rank < y.rank

instance : DecidableRel le := fun x y => by unfold le; infer_instance

instance : PartialOrder XElem where
  le := le
  le_refl x := Or.inl rfl
  le_trans x y z := by
    unfold le; cases x <;> cases y <;> cases z <;> decide
  le_antisymm x y := by
    unfold le; cases x <;> cases y <;> decide

instance : DecidableRel (α := XElem) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (le x y))

end XElem

/-- The chain `a < b` of the paper (line 190). -/
abbrev Chain2 := Fin 2

/-- The sharpness family (Proposition 5.2): `sharpFamily 0 = X` (that is `P_5`), and `sharpFamily (m+1)` adjoins a new
element below all elements of `sharpFamily m` (so `sharpFamily m = P_{m+5}`). -/
def sharpFamily : ℕ → Type
  | 0 => XElem
  | m + 1 => WithBot (sharpFamily m)

instance sharpFamily.instPartialOrder : (m : ℕ) → PartialOrder (sharpFamily m)
  | 0 => inferInstanceAs (PartialOrder XElem)
  | m + 1 => letI := sharpFamily.instPartialOrder m; inferInstanceAs (PartialOrder (WithBot (sharpFamily m)))

instance sharpFamily.instFintype : (m : ℕ) → Fintype (sharpFamily m)
  | 0 => inferInstanceAs (Fintype XElem)
  | m + 1 => letI := sharpFamily.instFintype m; inferInstanceAs (Fintype (WithBot (sharpFamily m)))

end HibiLi
