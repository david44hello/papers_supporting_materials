/-
HibiLi/Proofs/StepRows.lean — in-text and proof-step claims of review 006 coverage item B10 (rows a-j).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.PaperDefs
import HibiLi.Defs.Examples
import HibiLi.Polytope.CellGeometry
import HibiLi.Example21.SharpFamily

namespace HibiLi.Proofs

open Polynomial

/-- B10 a, l. 176-177, 960-961: each pyramid step of the sharp family multiplies `F_C − F_O` by `1 + t`. -/
theorem sec5_pyramid_step (m : ℕ) :
    facePoly (chainPolytope (sharpFamily (m + 1))) - facePoly (orderPolytope (sharpFamily (m + 1))) =
      (1 + X) * (facePoly (chainPolytope (sharpFamily m)) - facePoly (orderPolytope (sharpFamily m))) := by
  rw [(prop_5_2_proved (m + 1)).2.2, (prop_5_2_proved m).2.2, gapPoly, gapPoly,
    show m + 1 + 5 - 3 = (m + 5 - 3) + 1 by omega, pow_succ]
  ring

/-- B10 b, l. 246-247: `t² + 2t³ + t⁴ = t²(1+t)²` is the bound of Theorem 4.1 for `n = 5 = |X|`. -/
theorem sec5_x_gap : (X ^ 2 + 2 * X ^ 3 + X ^ 4 : ℤ[X]) = gapPoly 5 ∧ Fintype.card XElem = 5 := by
  refine ⟨?_, by decide⟩
  rw [gapPoly, show (5 : ℕ) - 3 = 2 from rfl]
  ring

/-- B10 e, l. 332-334: every element comparable to `q` is in `I` and below `q`, or in `J` and above `q`. -/
theorem sec3_q_comparable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    ∀ p : P, (p < s.q ∨ s.q < p) → (p ∈ s.I ∧ p < s.q) ∨ (p ∉ s.I ∧ s.q < p) := by
  rintro p (h | h)
  · exact Or.inl ⟨s.q_minimal p h, h⟩
  · exact Or.inr ⟨fun hp => s.q_notMem (s.isLowerSet h.le hp), h⟩

/-- B10 f, l. 336-337: `q` is maximal in `I ∪ {q}`, so in a chain of `I ∪ {q}` through `q` every other element lies
in `I` below `q`. -/
theorem sec3_chains_through_q {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    ∀ K : Finset P, ↑K ⊆ insert s.q s.I → IsChainSet P K → s.q ∈ K → ∀ p ∈ K, p ≠ s.q → p ∈ s.I ∧ p < s.q := by
  intro K hK hchain hq p hp hpq
  have hpI : p ∈ s.I := by
    rcases hK (Finset.mem_coe.2 hp) with h | h
    · exact absurd h hpq
    · exact h
  refine ⟨hpI, ?_⟩
  rcases hchain (Finset.mem_coe.2 hp) (Finset.mem_coe.2 hq) hpq with h | h
  · exact lt_of_le_of_ne h hpq
  · exact absurd (s.isLowerSet h hpI) s.q_notMem

/-- B10 j, l. 480-482: a member `R` of `R(Y)` has `relint R ⊆ relint Y`. -/
theorem lemma_3_5_i_relint {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) {Y R : Set (s.P' → ℝ)} :
    (Y ∈ s.cellsS ∨ Y ∈ s.cellsT) → R ∈ s.RR Y → intrinsicInterior ℝ R ⊆ intrinsicInterior ℝ Y := by
  rintro - hR
  exact intrinsicInterior_mono_of_adim_eq hR.1.1 hR.2.1 hR.2.2

end HibiLi.Proofs
