/-
HibiLi/Defs/ExtraDefs.lean — two small definitions for in-text claims of the paper (fresh review r2, list (C)).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Examples
import HibiLi.Defs.PaperDefs

namespace HibiLi

/-- The poset `a, b < c < d < g, h` (`X` with `d` inserted between `c` and `g, h`): an `X`-copy whose `c` has only
one upper cover, for the remark "q = c would not do in general" (paper lines 476–477). -/
inductive XdElem
  | a | b | c | d | g | h
  deriving DecidableEq, Repr

namespace XdElem

instance : Fintype XdElem :=
  ⟨{a, b, c, d, g, h}, by intro x; cases x <;> simp⟩

/-- Rank: 0 for `a, b`; 1 for `c`; 2 for `d`; 3 for `g, h`. -/
def rank : XdElem → ℕ
  | a => 0 | b => 0 | c => 1 | d => 2 | g => 3 | h => 3

/-- `x ≤ y` iff `x = y` or `rank x < rank y` (the same construction as for `X` in Examples.lean). -/
def le (x y : XdElem) : Prop := x = y ∨ x.rank < y.rank

instance : DecidableRel le := fun x y => by unfold le; infer_instance

instance : PartialOrder XdElem where
  le := le
  le_refl x := Or.inl rfl
  le_trans x y z := by
    unfold le; cases x <;> cases y <;> cases z <;> decide
  le_antisymm x y := by
    unfold le; cases x <;> cases y <;> decide

instance : DecidableRel (α := XdElem) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (le x y))

end XdElem

namespace XSwitch

variable {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)

/-- `Q_E` of Lemma 4.5(a), as a set: the `ζ`-section of `E` at `(α,β,γ,η) = (1/4,1/4,3/4,3/4)`.  The paper describes
it by the inequalities of `B` tight at `u₀` (`XSwitch.QEpaper`, Defs/QEPaper.lean); near `ζ₀` the two sets agree
(`Proofs.QEPaper.QE_iff_QEpaper`), and Lemma 4.5(a) only speaks of them inside the neighbourhood `V_ζ` of `ζ₀`. -/
def QE (E : Set (x.toSwitch.P' → ℝ)) : Set ({p // p ∉ x.special} → ℝ) :=
  {ζ | ∃ v ∈ E, x.alphaPart v = x.alphaPart x.u0 ∧ x.zeta v = ζ}

end XSwitch

end HibiLi
