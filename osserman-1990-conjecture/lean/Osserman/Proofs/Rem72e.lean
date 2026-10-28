/-
Rem72e.lean — Remark 7.2 of paper 013: the multiplicity of λ₀ and when the two choices of base eigenvalue differ.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Rem72dCounts
import Osserman.Proofs.Rem72d

namespace Osserman.Proofs.Rem72e

open Osserman Matrix

/-- No generator has zero coefficient, so no generator contributes to the eigenvalue `λ₀` itself. -/
lemma base_count {ν : ℕ} (l0 : ℝ) (μ : Fin ν → ℝ) (hμ : ∀ α, μ α ≠ 0) :
    Fintype.card {a : Fin ν // l0 + μ a = l0} = 0 :=
  Fintype.card_eq_zero_iff.mpr ⟨fun a => hμ a.1 (by linarith [a.2])⟩

/-- Away from `λ₀`, the reduced multiplicity is the number of generators with `λ₀ + μ_a = ℓ`. -/
lemma other_mult (R' : CurvTensor 16) {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : IsCliffordStr Jα) (l0 : ℝ) (μ : Fin ν → ℝ)
    (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, μ α • jfam (Jα α) x) (x : Vec 16) (hx : x ⬝ᵥ x = 1)
    (ℓ : ℝ) (different : ℓ ≠ l0) :
    R'.redMult x ℓ = Fintype.card {a : Fin ν // l0 + μ a = ℓ} := by
  have formula := Osserman.Proofs.Rem72d.clifford_multiplicity R' Jα hJ l0 μ hjac x hx ℓ
  rwa [ite_eq_right different, add_zero] at formula

theorem rem_7_2_base_mult_proved (R' : CurvTensor 16) {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : IsCliffordStr Jα) (l0 : ℝ) (μ : Fin ν → ℝ) (hμ : ∀ α, μ α ≠ 0)
    (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, μ α • jfam (Jα α) x) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 → R'.redMult x l0 = 15 - ν := by
  intro x hx
  have formula := Osserman.Proofs.Rem72d.clifford_multiplicity R' Jα hJ l0 μ hjac x hx l0
  rwa [base_count l0 μ hμ, ite_eq_left rfl, zero_add] at formula

lemma inj2 {a b : ℝ} (hab : a ≠ b) : Function.Injective ![a, b] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

lemma inj3 {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Function.Injective ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- If all but one generator share the value `ℓ`, the remaining value `λ₀ + μ_{a₀}` is carried by one generator. -/
lemma lone_count {ν : ℕ} (l0 ℓ : ℝ) (μ : Fin ν → ℝ)
    (one : Fintype.card {a : Fin ν // ¬ (l0 + μ a = ℓ)} = 1) :
    ∃ a0 : Fin ν, l0 + μ a0 ≠ ℓ ∧ Fintype.card {a : Fin ν // l0 + μ a = l0 + μ a0} = 1 := by
  obtain ⟨⟨a0, ha0⟩, unique⟩ := Fintype.card_eq_one_iff.mp one
  refine ⟨a0, ha0, (Fintype.card_congr (Equiv.subtypeEquivRight fun a => ⟨?_, ?_⟩)).trans one⟩
  · exact fun same hits => ha0 (same.symm.trans hits)
  · exact fun misses => congrArg (fun b => l0 + μ b) (congrArg Subtype.val (unique ⟨a, misses⟩))

theorem rem_7_2_differ_only_proved (R' : CurvTensor 16) {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : IsCliffordStr Jα) (l0 : ℝ) (μ : Fin ν → ℝ) (hμ : ∀ α, μ α ≠ 0)
    (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, μ α • jfam (Jα α) x) (x : Vec 16) (hx : x ⬝ᵥ x = 1)
    (hdiff : ∃ ℓ : ℝ, ℓ ≠ l0 ∧ R'.redMult x l0 ≤ R'.redMult x ℓ) :
    ν = 8 ∧ R'.redMult x l0 = 7 ∧ (∃ ℓ : ℝ, ℓ ≠ l0 ∧ 7 ≤ R'.redMult x ℓ) ∧
      (HasPattern R' ![8, 7] ∨ HasPattern R' ![7, 7, 1]) := by
  obtain ⟨ℓ, different, le⟩ := hdiff
  have base := rem_7_2_base_mult_proved R' Jα hJ l0 μ hμ hjac x hx
  have other := other_mult R' Jα hJ l0 μ hjac x hx ℓ different
  have count := Fintype.card_subtype_le (fun a : Fin ν => l0 + μ a = ℓ)
  rw [Fintype.card_fin] at count
  have upper := Osserman.Proofs.HurwitzRadon.rem_7_2_nu_le_8_proved Jα hJ
  have eight : ν = 8 := by omega
  have seven : 7 ≤ Fintype.card {a : Fin ν // l0 + μ a = ℓ} := by omega
  refine ⟨eight, by omega, ⟨ℓ, different, by omega⟩, ?_⟩
  -- The counts do not depend on the unit vector, so they hold at every unit `y`.
  have multAt (y : Vec 16) (hy : y ⬝ᵥ y = 1) (k : ℝ) (hk : k ≠ l0) :
      R'.redMult y k = Fintype.card {a : Fin ν // l0 + μ a = k} :=
    other_mult R' Jα hJ l0 μ hjac y hy k hk
  have baseAt (y : Vec 16) (hy : y ⬝ᵥ y = 1) : R'.redMult y l0 = 7 := by
    rw [rem_7_2_base_mult_proved R' Jα hJ l0 μ hμ hjac y hy]
    omega
  rcases Nat.lt_or_ge (Fintype.card {a : Fin ν // l0 + μ a = ℓ}) 8 with fewer | full
  · -- Seven generators carry `ℓ`; the last one carries a third value with multiplicity one.
    right
    have compl := Fintype.card_subtype_compl (fun a : Fin ν => l0 + μ a = ℓ)
    rw [Fintype.card_fin] at compl
    obtain ⟨a0, misses, single⟩ := lone_count l0 ℓ μ (by omega)
    have moved : l0 + μ a0 ≠ l0 := fun h => hμ a0 (by linarith)
    refine ⟨![ℓ, l0, l0 + μ a0], inj3 different (Ne.symm misses) (Ne.symm moved), ?_⟩
    intro y hy i
    fin_cases i
    · show R'.redMult y ℓ = 7
      rw [multAt y hy ℓ different]
      omega
    · show R'.redMult y l0 = 7
      exact baseAt y hy
    · show R'.redMult y (l0 + μ a0) = 1
      rw [multAt y hy _ moved, single]
  · -- All eight generators carry `ℓ`: the endpoint pattern (8, 7).
    left
    refine ⟨![ℓ, l0], inj2 different, ?_⟩
    intro y hy i
    fin_cases i
    · show R'.redMult y ℓ = 8
      rw [multAt y hy ℓ different]
      omega
    · show R'.redMult y l0 = 7
      exact baseAt y hy

end Osserman.Proofs.Rem72e

