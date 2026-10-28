/-
Smale/Proofs/Star.lean — Section 4 facts next to Lemma 4.3 (tex l.238-239, l.288-289, l.299-301): `h₁ = P_c(0) ≠ 0`;
`P_c* = (P_c)*` at formal degree `n - 1`; a zero of `P_c` on the circle is a common zero of `P_c` and `P_c*`, so the
resultant at formal degrees `(n - 1, n - 1)` vanishes (Mathlib's Bézout identity for the resultant).
-/
import Smale.Proofs.Schur
import Smale.Proofs.Dieudonne

namespace Smale

open Polynomial Complex Metric ComplexConjugate

theorem natDegree_dieudonne_le (H : ℂ[X]) (n : ℕ) (c : ℝ) : (dieudonne H n c).natDegree ≤ n - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_dieudonne, ite_eq_right (by omega)]

theorem natDegree_conjRev_le (f : ℂ[X]) (n : ℕ) : (conjRev f n).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_conjRev, ite_eq_right (by omega)]

/-- tex l.238-239, exactly the Statements type: the hypothesis of Dieudonné's criterion gives `h₁ = P_c(0) ≠ 0`. -/
theorem sec4_dieudonne_h1_proved (H : ℂ[X])
    (hP : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w ∈ disk, (dieudonne H H.natDegree c).eval w ≠ 0) :
    H.coeff 1 ≠ 0 := by
  have h0 : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  have h1 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  rcases Nat.eq_zero_or_pos H.natDegree with hd | hd
  · exact absurd (by simp [dieudonne, hd] : (dieudonne H H.natDegree 1).eval 0 = 0) (hP 1 h1 0 h0)
  · rw [← dieudonne_eval_zero H _ hd 1]
    exact hP 1 h1 0 h0

/-- Lemma 4.3 (R) (tex l.288-289), exactly the Statements type: `P_c*` is `(P_c)*` at formal degree `n - 1`. -/
theorem lem_4_3_Pstar_proved (H : ℂ[X]) (n : ℕ) (c : ℝ) :
    dieudonneStar H n c = conjRev (dieudonne H n c) (n - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [dieudonneStar, conjRev, dieudonne]
  rw [dieudonneStar, conjRev, show n - 1 + 1 = n by omega, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l < n := Finset.mem_range.1 hl
  rw [coeff_dieudonne, ite_eq_left (by omega), map_mul (starRingEnd ℂ), Complex.conj_ofReal, show n - 1 - (n - 1 - l) = l by omega]

/-- Lemma 4.3, proof (tex l.299-301), exactly the Statements type: a zero `w₀` of `P_c` on the circle is a zero of
`P_c*`, and the resultant at formal degrees `(n - 1, n - 1)` vanishes. -/
theorem lem_4_3_common_zero_proved (H : ℂ[X]) (n : ℕ) (hn : 2 ≤ n) (c : ℝ) (w : ℂ) (hw : ‖w‖ = 1)
    (h0 : (dieudonne H n c).eval w = 0) :
    (dieudonneStar H n c).eval w = 0 ∧ resultant (dieudonne H n c) (dieudonneStar H n c) (n - 1) (n - 1) = 0 := by
  have hdeg := natDegree_dieudonne_le H n c
  have hstar : (dieudonneStar H n c).eval w = 0 := by
    rw [lem_4_3_Pstar_proved, conjRev_eval_circle _ _ hdeg (conj_mul_self_of_norm_eq_one hw), h0, map_zero,
      mul_zero]
  refine ⟨hstar, ?_⟩
  have hdeg' : (dieudonneStar H n c).natDegree ≤ n - 1 := by
    rw [lem_4_3_Pstar_proved]
    exact natDegree_conjRev_le _ _
  obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant _ _ hdeg hdeg' (Or.inl (by omega))
  have h := congrArg (eval w) hpq
  simpa [eval_add, eval_mul, h0, hstar] using h.symm

end Smale
