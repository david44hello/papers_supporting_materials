/-
HibiLi/Defs/Census.lean — the sixteen 6-element posets that contain X (paper v0.70, lines 736–737; data from
the output of scripts/census/census_n6.py, same row order).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Every census poset is `X` plus one extra element `f`, all on the carrier `Fin 6`:
  0 = a, 1 = b, 2 = c, 3 = g, 4 = h (the poset `X`: a, b < c < g, h), and 5 = f.
Row `i` is fixed by `D` = the elements of `X` below `f` and `U` = the elements of `X` above `f`
(the "below f" and "above f" columns of CENSUS_n6.md).
-/
import HibiLi.Defs.Examples

namespace HibiLi

/-- Rank inside `X` (a, b ↦ 0; c ↦ 1; g, h ↦ 2), on `Fin 6`; the value at `5 = f` is never used. -/
def censusXRank : Fin 6 → ℕ := ![0, 0, 1, 2, 2, 0]

/-- `D`: the elements of `X` below `f` (0 = a, 1 = b, 2 = c, 3 = g, 4 = h), CENSUS_n6.md rows 1..16. -/
def censusBelow : Fin 16 → List ℕ :=
  ![[0, 1], [0, 1], [], [0], [], [0, 1], [0, 1, 2, 3, 4], [0, 1],
    [], [0], [], [0], [0, 1, 2], [], [0, 1, 2], []]

/-- `U`: the elements of `X` above `f`, CENSUS_n6.md rows 1..16. -/
def censusAbove : Fin 16 → List ℕ :=
  ![[], [3], [3, 4], [3, 4], [0, 1, 2, 3, 4], [2, 3, 4], [], [3, 4],
    [], [], [3], [3], [3], [0, 2, 3, 4], [], [2, 3, 4]]

/-- The order of census row `i` on `Fin 6`: `x ≤ y` iff `x = y`, or both lie in `X` and `x` has smaller rank, or
`y = f` and `x ∈ D`, or `x = f` and `y ∈ U`. -/
def censusLe (i : Fin 16) (x y : Fin 6) : Bool :=
  decide (x = y) ||
  (decide (x.val < 5) && decide (y.val < 5) && decide (censusXRank x < censusXRank y)) ||
  (decide (y.val = 5) && decide (x.val < 5) && decide (x.val ∈ censusBelow i)) ||
  (decide (x.val = 5) && decide (y.val < 5) && decide (y.val ∈ censusAbove i))

theorem censusLe_refl : ∀ (i : Fin 16) (x : Fin 6), censusLe i x x = true := by decide

theorem censusLe_trans : ∀ (i : Fin 16) (x y z : Fin 6),
    censusLe i x y = true → censusLe i y z = true → censusLe i x z = true := by decide

theorem censusLe_antisymm : ∀ (i : Fin 16) (x y : Fin 6),
    censusLe i x y = true → censusLe i y x = true → x = y := by decide

/-- The census poset of row `i + 1` of CENSUS_n6.md (carrier `Fin 6`, order `censusLe i`). -/
def censusPoset (_i : Fin 16) : Type := Fin 6

namespace censusPoset

variable (i : Fin 16)

instance : Fintype (censusPoset i) := inferInstanceAs (Fintype (Fin 6))

instance : DecidableEq (censusPoset i) := inferInstanceAs (DecidableEq (Fin 6))

instance : PartialOrder (censusPoset i) where
  le x y := censusLe i x y = true
  le_refl x := censusLe_refl i x
  le_trans x y z := censusLe_trans i x y z
  le_antisymm x y := censusLe_antisymm i x y

instance : DecidableRel (α := censusPoset i) (· ≤ ·) :=
  fun x y => inferInstanceAs (Decidable (censusLe i x y = true))

end censusPoset

end HibiLi
