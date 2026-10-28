/-
Osserman/Defs/Basic.lean — vectors, orthogonal complements, Π(x), Clifford structures and symmetric Clifford systems
(paper 013, §1 "Notation", l. 165-192).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE. `ℝ^n` is `Fin n → ℝ` with the dot product `⬝ᵥ` (the paper's ⟨·,·⟩); linear maps are `n × n` real
matrices; `uvᵀ` is `vecMulVec u v` (the paper's "uvᵀ denotes the map z ↦ ⟨v,z⟩u", l. 178-179).
-/
import Mathlib

namespace Osserman

open Matrix

/-- `ℝ^n` with the dot product. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- The orthogonal complement `x^⊥ = {y | ⟨x, y⟩ = 0}`. -/
def perp {n : ℕ} (x : Vec n) : Submodule ℝ (Vec n) where
  carrier := {y | x ⬝ᵥ y = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [dotProduct_add, ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    rw [dotProduct_smul, hy, smul_zero]

/-- `Π(x) = |x|² I - xxᵀ` (l. 176). -/
def Pi {n : ℕ} (x : Vec n) : Matrix (Fin n) (Fin n) ℝ := (x ⬝ᵥ x) • (1 : Matrix (Fin n) (Fin n) ℝ) - vecMulVec x x

/-- A `Cl(ν)`-structure (l. 182-184): skew-symmetric `J_1, …, J_ν` with `J_iJ_j + J_jJ_i = -2δ_ij I`. -/
def IsCliffordStr {n ν : ℕ} (J : Fin ν → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, (J i)ᵀ = -J i) ∧ ∀ i j, J i * J j + J j * J i = if i = j then -2 else 0

/-- A symmetric Clifford system (l. 188-190): symmetric `H_0, …, H_m` with `H_iH_j + H_jH_i = 2δ_ij I`. -/
def IsSymmCliffordSystem {n k : ℕ} (H : Fin k → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, (H i)ᵀ = H i) ∧ ∀ i j, H i * H j + H j * H i = if i = j then 2 else 0

end Osserman
