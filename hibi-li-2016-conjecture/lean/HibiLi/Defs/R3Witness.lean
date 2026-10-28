/-
HibiLi/Defs/R3Witness.lean — the 7-element poset for the remark "Fix two upper covers g′ and h′ of q; they
need not be g and h" (paper v2.10 line 706; fresh review r3, finding F5).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Poset

namespace HibiLi

/-- The seven elements `a, b, c, d, g', h', g` (written `gp` for `g'` and `hp` for `h'`) of the poset
`a, b < c < d < g', h'` and `g' < g`, used for the remark at paper line 706.  Its elements `a, b, c, g, h'` form a
copy of `X`; the element `q` of Section 4.2 is `d`, whose upper covers are `g', h'`. -/
inductive R3Elem
  | a | b | c | d | gp | hp | g
  deriving DecidableEq, Repr

namespace R3Elem

instance : Fintype R3Elem :=
  ⟨{a, b, c, d, gp, hp, g}, by intro x; cases x <;> simp⟩

/-- The strict order, listed pair by pair: `a, b` lie below `c, d, g', h', g`; `c` below `d, g', h', g`; `d` below
`g', h', g`; `g'` below `g`.  No other pair is related (`a, b` incomparable; `g', h'` incomparable; `h', g`
incomparable). -/
def ltB : R3Elem → R3Elem → Bool
  | a, c | a, d | a, gp | a, hp | a, g => true
  | b, c | b, d | b, gp | b, hp | b, g => true
  | c, d | c, gp | c, hp | c, g => true
  | d, gp | d, hp | d, g => true
  | gp, g => true
  | _, _ => false

/-- `x ≤ y` iff `x = y` or `x` lies strictly below `y` in the list of `ltB`. -/
def le (x y : R3Elem) : Prop := x = y ∨ ltB x y = true

instance : DecidableRel le := fun x y => by unfold le; infer_instance

instance : PartialOrder R3Elem where
  le := le
  le_refl x := Or.inl rfl
  le_trans x y z := by
    unfold le; cases x <;> cases y <;> cases z <;> decide
  le_antisymm x y := by
    unfold le; cases x <;> cases y <;> decide

instance : DecidableRel (α := R3Elem) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (le x y))

end R3Elem

end HibiLi
