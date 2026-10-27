/-
HibiLi/Defs/QEPaper.lean — the defining inequalities of `B`, and the paper's own `Q_E` of Lemma 4.5(a)
(paper v0.70 lines 543–546), cut out by the inequalities of `B` tight at `u₀`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.PaperDefs

namespace HibiLi

namespace Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- The defining inequalities of `B = O_I(P')`: the five families of `chainOrderPolytope` (paper lines 227–240), each
written `0 ≤ g u` with `g` an affine function of `B`'s coordinates (its slack), in the paper's order:
(1) `x_p ≥ 0` (`p ∈ I`); (2) `y_r ≥ 0` and `y_r ≤ 1` (`r ∈ J`); (3) `y_r ≤ y_r'` (`r ≤ r'` in `J`);
(4) `Σ_{p∈K} x_p ≤ y_r` (`r ∈ J`, `K ⊆ I` a chain with `p < r` for all `p ∈ K`); (5) `Σ_{p∈K} x_p ≤ 1`
(`K ⊆ I` a chain).  `B = {u | ∀ g ∈ ineqs, 0 ≤ g u}` is `Proofs.QEPaper.mem_B_iff_ineqs`. -/
def ineqs : Set ((s.P' → ℝ) → ℝ) :=
  {g | (∃ p, p ∈ s.I' ∧ g = fun u => u p) ∨
       (∃ r, r ∉ s.I' ∧ g = fun u => u r) ∨
       (∃ r, r ∉ s.I' ∧ g = fun u => 1 - u r) ∨
       (∃ r r', r ∉ s.I' ∧ r' ∉ s.I' ∧ r ≤ r' ∧ g = fun u => u r' - u r) ∨
       (∃ r K, r ∉ s.I' ∧ ↑K ⊆ s.I' ∧ IsChainSet s.P' K ∧ (∀ p ∈ K, p < r) ∧
          g = fun u => u r - ∑ p ∈ K, u p) ∨
       (∃ K : Finset s.P', ↑K ⊆ s.I' ∧ IsChainSet s.P' K ∧ g = fun u => 1 - ∑ p ∈ K, u p)}

end Switch

namespace XSwitch

variable {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)

/-- The point `(α, β, γ, η; ζ)` with `(α, β, γ, η) = (1/4, 1/4, 3/4, 3/4)` taken from `u₀` and the given `ζ`. -/
noncomputable def withZeta (ζ : {p // p ∉ x.special} → ℝ) : x.toSwitch.P' → ℝ := by
  classical
  exact fun p => if hp : p ∈ x.special then x.u0 p else ζ ⟨p, hp⟩

/-- `Q_E` as the paper defines it (Lemma 4.5(a), lines 543–546): "the polyhedron in the `ζ`-space defined by the
inequalities of `B` that are tight at `u₀`, those tight on `E` taken as equalities".  An inequality `0 ≤ g` of `B` is
tight at `u₀` when `g u₀ = 0`, and tight on `E` when `g = 0` on all of `E`.  The inequalities tight at `u₀` involve
only `ζ` (`Proofs.QEPaper.tight_ineq_zeta`), so they are read at the point `(α, β, γ, η) = (1/4, 1/4, 3/4, 3/4)`. -/
def QEpaper (E : Set (x.toSwitch.P' → ℝ)) : Set ({p // p ∉ x.special} → ℝ) :=
  {ζ | ∀ g ∈ x.toSwitch.ineqs, g x.u0 = 0 →
    0 ≤ g (x.withZeta ζ) ∧ ((∀ u ∈ E, g u = 0) → g (x.withZeta ζ) = 0)}

end XSwitch

end HibiLi
