/-
S8Witness.lean — paper 013, Section 8: non-vacuity rows s8_5_mixed_nonvacuous and thm_F_hyp_nonvacuous (Lean-only rows,
review a3 SHOULD-1 and R4), from the Clifford examples of S8Example.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Every example is `R = ∑_a η_a R_{Jcl a}` with natural-number weights `η`: the reduced multiplicity of `t` is
`#{a : η_a = t}`, plus `7` at `t = 0` (`S8Example.nat_mult`), so the counts are decided by `decide`. One zero weight
gives base multiplicity `8`. The mixed-sign example of §8.5 is `η = (2,2,2,2,2,3,4,1)`: pattern `(7,5,1,1,1)` with
`λ = 2` and simple eigenvalues `3, 4, 1` (weights `3, 8, -1`), fields `P_i = qJcl_{5+i}x`.
-/
import Osserman.Proofs.S8Example
import Osserman.Proofs.S83Move

namespace Osserman.Proofs.S8Example

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Tools Osserman.Proofs.CorDNonvacuous

/-- A tensor with natural-number weights `ηn` has the pattern `m` with eigenvalues `evn` when the counts agree. -/
lemma pattern_of_counts {k : ℕ} (ηn : Fin 8 → ℕ) {R : CurvTensor 16}
    (hR : ∀ x, R.jacobi x = ∑ a, ((ηn a : ℕ) : ℝ) • jfam (Jcl a) x) (m evn : Fin k → ℕ)
    (hinj : Function.Injective evn)
    (hcount : ∀ i, Fintype.card {a : Fin 8 // ηn a = evn i} + (if evn i = 0 then 7 else 0) = m i) :
    PatternEv R m (fun i => ((evn i : ℕ) : ℝ)) :=
  ⟨fun _ _ h => hinj (Nat.cast_injective h), fun x hx i => (nat_mult ηn hR x hx (evn i)).trans (hcount i)⟩

lemma has_pattern {k : ℕ} (ηn : Fin 8 → ℕ) (m evn : Fin k → ℕ) (hinj : Function.Injective evn)
    (hcount : ∀ i, Fintype.card {a : Fin 8 // ηn a = evn i} + (if evn i = 0 then 7 else 0) = m i) :
    ∃ R : CurvTensor 16, HasPattern R m := by
  obtain ⟨R, hR⟩ := exists_sum_RJ Jcl (fun a => Jcl_skew a) (fun a => ((ηn a : ℕ) : ℝ))
  exact ⟨R, _, pattern_of_counts ηn hR m evn hinj hcount⟩

/-! ### §8.5, mixed signs -/

/-- **§8.5, mixed signs, non-vacuity** (Lean-only row), row `s8_5_mixed_nonvacuous`. -/
theorem s8_5_mixed_nonvacuous_proved :
    ∃ (R : CurvTensor 16) (M N : ℕ) (ev : Fin 5 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ),
      Sec85Data R M N ev P ∧
        ¬ ((∀ i, 0 < (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i * ((![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i - ev 1)) ∨
          ∀ i, (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i * ((![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i - ev 1) < 0) := by
  obtain ⟨R, hR⟩ := exists_sum_RJ Jcl (fun a => Jcl_skew a)
    (fun a => (((![2, 2, 2, 2, 2, 3, 4, 1] : Fin 8 → ℕ) a : ℕ) : ℝ))
  refine ⟨R, 7, 5, fun i => (((![0, 2, 3, 4, 1] : Fin 5 → ℕ) i : ℕ) : ℝ),
    ![qfield (Jcl 5), qfield (Jcl 6), qfield (Jcl 7)],
    ⟨Or.inl ⟨rfl, rfl⟩, pattern_of_counts _ hR _ _ (by decide) (by decide), Nat.cast_zero, fun i j => ?_,
      fun i => ?_, qfield_eig _ hR 5, qfield_eig _ hR 6, qfield_eig _ hR 7⟩, ?_⟩
  · fin_cases i <;> exact qfield_homog _ j
  · fin_cases i <;> exact qfield_cubic (Jcl_skew _) (jcl_clifford.2 _)
  · rintro (h | h)
    · have h2 := h 2
      norm_num at h2
    · have h0 := h 0
      norm_num at h0

/-! ### Theorem F, non-vacuity -/

/-- The weights `(1,1,2,2,3,3,4,4)`: every fiber has at most two points. -/
lemma fiber_le_two : ∀ b : Fin 8, Fintype.card {a : Fin 8 // (![1, 1, 2, 2, 3, 3, 4, 4] : Fin 8 → ℕ) a =
    (![1, 1, 2, 2, 3, 3, 4, 4] : Fin 8 → ℕ) b} ≤ 2 := by
  decide

/-- A tensor with `SmallMultHyp`: base multiplicity `7` at `0`, every other multiplicity at most `2`. -/
lemma small_mult_example : ∃ (R : CurvTensor 16) (μ0 : ℝ) (M : ℕ), SmallMultHyp R μ0 M := by
  let ηn : Fin 8 → ℕ := ![1, 1, 2, 2, 3, 3, 4, 4]
  obtain ⟨R, hR⟩ := exists_sum_RJ Jcl (fun a => Jcl_skew a) (fun a => ((ηn a : ℕ) : ℝ))
  have hjac : ∀ x, R.jacobi x = (0 : ℝ) • Pi x + ∑ a, ((ηn a : ℕ) : ℝ) • jfam (Jcl a) x := fun x => by
    rw [hR, zero_smul, zero_add]
  have hC : R.IsClifford := ⟨8, Jcl, jcl_clifford.1, 0, _, hjac⟩
  refine ⟨R, 0, 7, S83.clifford_osserman hC, Or.inl rfl, fun x hx => ?_, fun x hx μ hμ => ?_⟩
  · have h := nat_mult ηn hR x hx 0
    rw [Nat.cast_zero] at h
    rw [h]
    decide
  · rw [Rem72d.clifford_multiplicity R Jcl jcl_clifford.1 0 _ hjac x hx μ, ite_eq_right hμ, add_zero]
    by_cases hin : ∃ b, (0 : ℝ) + ((ηn b : ℕ) : ℝ) = μ
    · obtain ⟨b, hb⟩ := hin
      rw [Fintype.card_congr (Equiv.subtypeEquivRight fun a => show (0 : ℝ) + ((ηn a : ℕ) : ℝ) = μ ↔ ηn a = ηn b by
        rw [← hb, add_right_inj, Nat.cast_inj])]
      exact fiber_le_two b
    · have : IsEmpty {a : Fin 8 // (0 : ℝ) + ((ηn a : ℕ) : ℝ) = μ} := ⟨fun a => hin ⟨a.1, a.2⟩⟩
      rw [Fintype.card_eq_zero]
      omega

/-- **Theorem F, non-vacuity** (Lean-only row, review a3 R4), row `thm_F_hyp_nonvacuous`. -/
theorem thm_F_hyp_nonvacuous_proved :
    (∃ R : CurvTensor 16, HasPattern R ![7, 6, 1, 1]) ∧ (∃ R : CurvTensor 16, HasPattern R ![8, 5, 1, 1]) ∧
      (∃ R : CurvTensor 16, HasPattern R ![7, 5, 2, 1]) ∧ (∃ R : CurvTensor 16, HasPattern R ![8, 4, 2, 1]) ∧
      (∃ R : CurvTensor 16, HasPattern R ![7, 5, 1, 1, 1]) ∧ (∃ R : CurvTensor 16, HasPattern R ![8, 4, 1, 1, 1]) ∧
      ∃ (R : CurvTensor 16) (μ0 : ℝ) (M : ℕ), SmallMultHyp R μ0 M :=
  ⟨has_pattern ![2, 2, 2, 2, 2, 2, 3, 1] _ ![0, 2, 3, 1] (by decide) (by decide),
    has_pattern ![0, 2, 2, 2, 2, 2, 3, 1] _ ![0, 2, 3, 1] (by decide) (by decide),
    has_pattern ![2, 2, 2, 2, 2, 3, 3, 1] _ ![0, 2, 3, 1] (by decide) (by decide),
    has_pattern ![0, 2, 2, 2, 2, 3, 3, 1] _ ![0, 2, 3, 1] (by decide) (by decide),
    has_pattern ![2, 2, 2, 2, 2, 3, 4, 1] _ ![0, 2, 3, 4, 1] (by decide) (by decide),
    has_pattern ![0, 2, 2, 2, 2, 3, 4, 1] _ ![0, 2, 3, 4, 1] (by decide) (by decide),
    small_mult_example⟩

end Osserman.Proofs.S8Example
