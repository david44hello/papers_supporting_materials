/-
HibiLi/Proofs/LUPiecewise.lean — L is a max of finitely many affine maps, U a min of finitely many (paper Section 3).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Switch

namespace HibiLi.Proofs

open HibiLi Finset

section Branches

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- The chain sum `ℓ_K` as an affine map. -/
noncomputable def chainSumAff (K : Finset s.P') : (s.P' → ℝ) →ᵃ[ℝ] ℝ :=
  (∑ p ∈ K, LinearMap.proj (R := ℝ) (φ := fun _ : s.P' => ℝ) p).toAffineMap

lemma chainSumAff_apply (K : Finset s.P') (u : s.P' → ℝ) : chainSumAff s K u = s.chainSum K u := by
  simp [chainSumAff, Switch.chainSum]

/-- An upper branch as an affine map: the constant `1` or a coordinate. -/
noncomputable def upAff : Option s.P' → (s.P' → ℝ) →ᵃ[ℝ] ℝ
  | none => AffineMap.const ℝ (s.P' → ℝ) (1 : ℝ)
  | some r => (LinearMap.proj (R := ℝ) (φ := fun _ : s.P' => ℝ) r).toAffineMap

lemma upAff_apply (j : Option s.P') (u : s.P' → ℝ) : upAff s j u = s.upVal j u := by
  cases j <;> simp [upAff, Switch.upVal]

end Branches

theorem sec3_L_U_piecewise_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∃ (fs : Finset ((s.P' → ℝ) →ᵃ[ℝ] ℝ)) (h : fs.Nonempty), ∀ u, s.L u = fs.sup' h (fun f => f u)) ∧
    (∃ (gs : Finset ((s.P' → ℝ) →ᵃ[ℝ] ℝ)) (h : gs.Nonempty), ∀ u, s.U u = gs.inf' h (fun g => g u)) := by
  classical
  refine ⟨⟨s.lowBranches.image (chainSumAff s), s.lowBranches_nonempty.image _, fun u => ?_⟩,
    ⟨s.upBranches.image (upAff s), s.upBranches_nonempty.image _, fun u => ?_⟩⟩
  · rw [sup'_image]
    exact sup'_congr _ rfl fun K _ => (chainSumAff_apply s K u).symm
  · rw [inf'_image]
    exact inf'_congr _ rfl fun j _ => (upAff_apply s j u).symm

end HibiLi.Proofs
