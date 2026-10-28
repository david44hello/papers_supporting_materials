/-
Rem72d.lean — multiplicity rows and block rotation, paper 013, Remark 7.2.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Rem72dCounts
import Osserman.Proofs.Rem72dRotation
import Osserman.Proofs.Rem72b

namespace Osserman.Proofs.Rem72d

open Osserman Matrix

theorem rem_7_2_rotate_of_inner_const
    (hInner : ∀ (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
      (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (_h : Rem72Hyp R R' J c Jα μ),
      ∀ α, ∃ d : ℝ, ∀ x : Vec 16, (Jα α *ᵥ x) ⬝ᵥ (J *ᵥ x) = d * (x ⬝ᵥ x))
    (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin ν) ℝ, (∀ α β, O α β ≠ 0 → μ α = μ β) ∧
      ∃ d : Fin ν → ℝ, (∀ α (x : Vec 16), ((∑ β, O α β • Jα β) *ᵥ x) ⬝ᵥ (J *ᵥ x) = d α * (x ⬝ᵥ x)) ∧
        ∀ α β, α ≠ β → μ α = μ β → d α = 0 ∨ d β = 0 := by
  classical
  choose e he using hInner R R' J c Jα μ h
  obtain ⟨O, hO, block, sparse⟩ := concentrate_blocks μ e
  refine ⟨O, hO, fun a b nonzero => by
    by_contra different
    exact nonzero (block a b different),
    O *ᵥ e, ?_, sparse⟩
  intro a x
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, sum_dotProduct, smul_dotProduct, he, smul_eq_mul]
  change (∑ b, O a b * (e b * (x ⬝ᵥ x))) = (∑ b, O a b * e b) * (x ⬝ᵥ x)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem rem_7_2_rotate_proved (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin ν) ℝ, (∀ α β, O α β ≠ 0 → μ α = μ β) ∧
      ∃ d : Fin ν → ℝ, (∀ α (x : Vec 16), ((∑ β, O α β • Jα β) *ᵥ x) ⬝ᵥ (J *ᵥ x) = d α * (x ⬝ᵥ x)) ∧
        ∀ α β, α ≠ β → μ α = μ β → d α = 0 ∨ d β = 0 :=
  rem_7_2_rotate_of_inner_const Osserman.Proofs.Rem72b.rem_7_2_inner_const_proved R R' J c Jα μ h

end Osserman.Proofs.Rem72d
