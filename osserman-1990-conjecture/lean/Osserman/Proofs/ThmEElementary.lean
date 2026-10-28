/-
ThmEElementary.lean — multiplicity patterns and scalar shifts in Theorem E, paper 013, lines 740–758.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.ThreeRoot
import Osserman.Proofs.Curv

namespace Osserman.Proofs.ThmEElementary

open Osserman Matrix Osserman.Proofs.Curv

theorem thm_E_smallest_proved (m : Fin 3 → ℕ) (hm : IsThmEPattern m) :
    (m 2 = 1 ∨ m 2 = 2) ∧ m 2 < m 0 ∧ m 2 < m 1 ∧ m 0 + m 1 + m 2 = 15 := by
  rcases hm with rfl | rfl | rfl | rfl <;> norm_num

theorem thm_E_merge_proved (m : Fin 3 → ℕ) (hm : IsThmEPattern m) :
    (m 0 = 7 ∧ m 1 + m 2 = 8) ∨ (m 0 = 8 ∧ m 1 + m 2 = 7) := by
  rcases hm with rfl | rfl | rfl | rfl <;> norm_num

theorem thm_E_c_ne_zero_proved (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) (h : ThmEFrame R m ev J) : ev 2 - ev 1 ≠ 0 := by
  apply sub_ne_zero.mpr
  intro equal
  have impossible : (2 : Fin 3) = 1 := h.2.1 equal
  norm_num at impossible

theorem thm_E_apply_C_proved (Rt : CurvTensor 16) (μ₀ μ₁ : ℝ) (hne : μ₀ ≠ μ₁) (a b : ℕ)
    (hab : (a = 7 ∧ b = 8) ∨ (a = 8 ∧ b = 7))
    (hpat : ∀ x : Vec 16, x ⬝ᵥ x = 1 → Rt.redMult x μ₀ = a ∧ Rt.redMult x μ₁ = b) :
    ∃ μ₁' μ₂' : ℝ, μ₁' ≠ μ₂' ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → Rt.redMult x μ₁' = 8 ∧ Rt.redMult x μ₂' = 7 := by
  rcases hab with h | h
  · refine ⟨μ₁, μ₀, Ne.symm hne, ?_⟩
    intro x hx
    simpa only [h.1, h.2] using (hpat x hx).symm
  · refine ⟨μ₀, μ₁, hne, ?_⟩
    intro x hx
    simpa only [h.1, h.2] using hpat x hx

theorem thm_E_shift_eigenspaces_proved {n : ℕ} (R R0 : CurvTensor n) (c : ℝ)
    (h0 : ∀ u v w, R0.op u v w = R.op u v w - c • R1fun u v w) :
    ∀ (x : Vec n) (μ : ℝ), Module.End.eigenspace (R0.jacobiMap x) (μ - c * (x ⬝ᵥ x)) ⊓ perp x =
      Module.End.eigenspace (R.jacobiMap x) μ ⊓ perp x := by
  intro x μ
  ext y
  simp only [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
  change (R0.op y x x = (μ - c * (x ⬝ᵥ x)) • y ∧ x ⬝ᵥ y = 0) ↔
    (R.op y x x = μ • y ∧ x ⬝ᵥ y = 0)
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    have equation := h.1
    rw [h0, R1fun, dotProduct_comm y x, h.2, zero_smul, sub_zero, smul_smul] at equation
    calc
      R.op y x x = (R.op y x x - (c * (x ⬝ᵥ x)) • y) + (c * (x ⬝ᵥ x)) • y := by module
      _ = μ • y := by rw [equation]; module
  · intro h
    refine ⟨?_, h.2⟩
    rw [h0, R1fun, dotProduct_comm y x, h.2, zero_smul, sub_zero, h.1]
    module

theorem thm_E_shift_proved {n : ℕ} (R R0 : CurvTensor n) (c : ℝ)
    (h0 : ∀ u v w, R0.op u v w = R.op u v w - c • R1fun u v w) :
    ∀ x : Vec n, x ⬝ᵥ x = 1 → ∀ μ : ℝ, R0.redMult x (μ - c) = R.redMult x μ := by
  intro x hx μ
  have equal := thm_E_shift_eigenspaces_proved R R0 c h0 x μ
  rw [hx, mul_one] at equal
  exact congrArg (fun W : Submodule ℝ (Vec n) => Module.finrank ℝ W) equal

end Osserman.Proofs.ThmEElementary

