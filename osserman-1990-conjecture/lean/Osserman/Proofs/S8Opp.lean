/-
Osserman/Proofs/S8Opp.lean — paper 013, Section 8: non-vacuity rows s8_3_opposite_nonvacuous and
s8_4_opposite_nonvacuous (Lean-only rows, review a3 SHOULD-1), from the Clifford examples of S8Example.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Both examples are `R = ∑_a η_a R_{Jcl a}` with natural-number weights (counts decided by `decide`, as in
`S8Example.pattern_of_counts`), eigenvalues `ev = (0, λ, μ, σ) = (0, 2, 3, 1)` and fields `P_i = qJcl_ax`.
§8.3: `η = (2,2,2,2,2,2,3,1)`, pattern `(7,6,1,1)`, `μ(μ - λ) = 3 > 0`, `σ(σ - λ) = -1 < 0`.
§8.4: `η = (2,2,2,2,2,3,3,1)`, pattern `(7,5,2,1)` with `μ` double; the product `3·(-1) < 0`; the three fields are
mutually orthogonal with squared norm `q³` (`frame_dot`).
-/
import Osserman.Proofs.S8Witness

namespace Osserman.Proofs.S8Opp

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Example Osserman.Proofs.CorDNonvacuous

/-- Products of the fields `qJcl_ax`: `q³δ_ab`. -/
lemma qfield_dot (a b : Fin 8) (x : Vec 16) :
    evalField (qfield (Jcl a)) x ⬝ᵥ evalField (qfield (Jcl b)) x = if a = b then (x ⬝ᵥ x) ^ 3 else 0 := by
  rw [qfield_eval, qfield_eval, smul_dotProduct, dotProduct_smul, frame_dot, smul_eq_mul, smul_eq_mul]
  split_ifs <;> ring

/-- Row `s8_3_opposite_nonvacuous`. -/
theorem s8_3_opposite_nonvacuous_proved :
    ∃ (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ),
      Sec83Data R M N ev P ∧ 0 < ev 2 * (ev 2 - ev 1) ∧ ev 3 * (ev 3 - ev 1) < 0 := by
  obtain ⟨R, hR⟩ := exists_sum_RJ Jcl (fun a => Jcl_skew a)
    (fun a => (((![2, 2, 2, 2, 2, 2, 3, 1] : Fin 8 → ℕ) a : ℕ) : ℝ))
  refine ⟨R, 7, 6, fun i => (((![0, 2, 3, 1] : Fin 4 → ℕ) i : ℕ) : ℝ), ![qfield (Jcl 6), qfield (Jcl 7)],
    ⟨Or.inl ⟨rfl, rfl⟩, pattern_of_counts _ hR _ _ (by decide) (by decide), Nat.cast_zero, fun i j => ?_,
      fun i => ?_, qfield_eig _ hR 6, qfield_eig _ hR 7⟩, ?_, ?_⟩
  · fin_cases i <;> exact qfield_homog _ j
  · fin_cases i <;> exact qfield_cubic (Jcl_skew _) (jcl_clifford.2 _)
  · norm_num
  · norm_num

/-- Row `s8_4_opposite_nonvacuous`. -/
theorem s8_4_opposite_nonvacuous_proved :
    ∃ (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ),
      Sec84Data R M N ev P ∧ (ev 2 * (ev 2 - ev 1)) * (ev 3 * (ev 3 - ev 1)) < 0 := by
  obtain ⟨R, hR⟩ := exists_sum_RJ Jcl (fun a => Jcl_skew a)
    (fun a => (((![2, 2, 2, 2, 2, 3, 3, 1] : Fin 8 → ℕ) a : ℕ) : ℝ))
  refine ⟨R, 7, 5, fun i => (((![0, 2, 3, 1] : Fin 4 → ℕ) i : ℕ) : ℝ),
    ![qfield (Jcl 5), qfield (Jcl 6), qfield (Jcl 7)],
    ⟨Or.inl ⟨rfl, rfl⟩, pattern_of_counts _ hR _ _ (by decide) (by decide), Nat.cast_zero, fun i j => ?_,
      fun x i k => ?_, qfield_eig _ hR 5, qfield_eig _ hR 6, qfield_eig _ hR 7,
      qfield_cubic (Jcl_skew _) (jcl_clifford.2 _)⟩, ?_⟩
  · fin_cases i <;> exact qfield_homog _ j
  · have hP : ∀ i : Fin 3, (![qfield (Jcl 5), qfield (Jcl 6), qfield (Jcl 7)] :
        Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) i = qfield (Jcl ((![5, 6, 7] : Fin 3 → Fin 8) i)) := by
      intro i
      fin_cases i <;> rfl
    have hinj : Function.Injective (![5, 6, 7] : Fin 3 → Fin 8) := by decide
    rw [hP, hP, qfield_dot]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hinj h1) h2
    · exact absurd (congrArg _ h2) h1
    · rfl
  · norm_num

end Osserman.Proofs.S8Opp

