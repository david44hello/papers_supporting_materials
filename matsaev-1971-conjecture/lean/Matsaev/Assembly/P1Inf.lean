/-
Matsaev/Assembly/P1Inf.lean — the cases `p = 1` and `p = ∞`: "(1) holds trivially, since then `‖P(T)‖_p ≤ Σ|c_k| = ‖P(S)‖_p`"
(Section 1, Background) and "`‖P(J)‖_∞ ≤ Σ|c_k| = ‖P(S)‖_∞`" (end of the proof of Lemma 2.2). Author: Dave Goel.

`Σ|c_k|` is `∑ k ∈ range (deg P + 1), ‖c_k‖`. Upper bound: the triangle inequality (`norm_aeval_le_sum`). Lower bounds:
`P(S) e₀ = (c_0, c_1, …)` in `ℓ¹`, and in `ℓ^∞` the vector `x_j = conj(c_{d-j})/|c_{d-j}|` (`j ≤ d = deg P`) gives
`(P(S) x)_d = Σ|c_k|`.
-/
import Matsaev.Ops.JLower
import Matsaev.ThmB.Basic

namespace Matsaev.P1Inf

open Matsaev
open scoped ENNReal
open Polynomial

/-- `‖P(T)‖ ≤ Σ|c_k|` for every contraction `T` of a complex normed space. -/
theorem norm_aeval_le_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1)
    (P : ℂ[X]) : ‖aeval T P‖ ≤ ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ := by
  have hpow : ∀ k : ℕ, ‖T ^ k‖ ≤ 1 := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact ContinuousLinearMap.norm_id_le
    | succ k ih =>
      rw [pow_succ]
      calc ‖T ^ k * T‖ ≤ ‖T ^ k‖ * ‖T‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul ih hT (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  rw [aeval_eq_sum_range]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  calc ‖P.coeff k • T ^ k‖ ≤ ‖P.coeff k‖ * ‖T ^ k‖ := (norm_smul _ _).le
    _ ≤ ‖P.coeff k‖ * 1 := mul_le_mul_of_nonneg_left (hpow k) (norm_nonneg _)
    _ = ‖P.coeff k‖ := mul_one _

/-- `(P(S) x)_n = ∑_{k ≤ n} c_k x_{n-k}` (`c_k = 0` for `k > deg P`). -/
theorem aeval_shift_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (P : ℂ[X]) (x : lp (fun _ : ℕ => ℂ) p) (n : ℕ) :
    aeval (shiftOp p ℂ) P x n =
      ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * (if k ≤ n then x (n - k) else 0) := by
  rw [JLower.aeval_shiftOp_apply]
  simp only [JLower.shiftOp_pow_apply]

/-- `‖P(S)‖_1 = Σ|c_k|`. -/
theorem shiftNorm_one (P : ℂ[X]) :
    shiftNorm 1 ℂ P = ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ := by
  refine le_antisymm (norm_aeval_le_sum _ (ThmB.norm_shiftOp_le 1) P) ?_
  set e₀ : lp (fun _ : ℕ => ℂ) 1 := lp.single 1 0 (1 : ℂ) with he₀
  have he : ‖e₀‖ = 1 := by rw [he₀, lp.norm_single (by norm_num), norm_one]
  have hy : ∀ n, aeval (shiftOp 1 ℂ) P e₀ n = P.coeff n := by
    intro n
    rw [aeval_shift_apply]
    by_cases hn : n ≤ P.natDegree
    · rw [Finset.sum_eq_single n]
      · simp [he₀, lp.single_apply]
      · intro k _ hkn
        by_cases hk : k ≤ n
        · have : n - k ≠ 0 := by omega
          simp [hk, he₀, lp.single_apply, this]
        · simp [hk]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk' : k < n := by rw [Finset.mem_range] at hk; omega
      have : n - k ≠ 0 := by omega
      simp [hk'.le, he₀, lp.single_apply, this]
  have hnorm : ‖aeval (shiftOp 1 ℂ) P e₀‖ = ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num)]
    simp only [ENNReal.toReal_one, Real.rpow_one, div_one, hy]
    exact tsum_eq_sum fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
  rw [← hnorm, shiftNorm]
  calc ‖aeval (shiftOp 1 ℂ) P e₀‖ ≤ ‖aeval (shiftOp 1 ℂ) P‖ * ‖e₀‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖aeval (shiftOp 1 ℂ) P‖ := by rw [he, mul_one]

/-- `c · (c̄ / |c|) = |c|`. -/
lemma mul_conj_div_norm (c : ℂ) : c * ((starRingEnd ℂ) c / (‖c‖ : ℂ)) = (‖c‖ : ℂ) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hc
    rw [← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    field_simp
    push_cast
    ring

/-- `‖P(S)‖_∞ = Σ|c_k|`. -/
theorem shiftNorm_top (P : ℂ[X]) :
    shiftNorm ⊤ ℂ P = ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ := by
  refine le_antisymm (norm_aeval_le_sum _ (ThmB.norm_shiftOp_le ⊤) P) ?_
  set d := P.natDegree with hd
  set f : ℕ → ℂ := fun j => if j ≤ d then (starRingEnd ℂ) (P.coeff (d - j)) / (‖P.coeff (d - j)‖ : ℂ) else 0
    with hfdef
  have hf1 : ∀ j, ‖f j‖ ≤ 1 := by
    intro j
    simp only [hfdef]
    split_ifs
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm]
      exact div_self_le_one _
    · simp
  set x : lp (fun _ : ℕ => ℂ) ⊤ := ⟨f, memℓp_infty ⟨1, by rintro _ ⟨j, rfl⟩; exact hf1 j⟩⟩ with hxdef
  have hx : ‖x‖ ≤ 1 := lp.norm_le_of_forall_le zero_le_one hf1
  have hyd : aeval (shiftOp ⊤ ℂ) P x d = ((∑ k ∈ Finset.range (d + 1), ‖P.coeff k‖ : ℝ) : ℂ) := by
    rw [aeval_shift_apply]
    push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkd : k ≤ d := by rw [Finset.mem_range] at hk; omega
    have hx' : x (d - k) = (starRingEnd ℂ) (P.coeff k) / (‖P.coeff k‖ : ℂ) := by
      change f (d - k) = _
      simp only [hfdef, Nat.sub_le, ite_true, Nat.sub_sub_self hkd]
    simp only [hkd, ite_true]
    rw [hx', mul_conj_div_norm]
  have hpos : 0 ≤ ∑ k ∈ Finset.range (d + 1), ‖P.coeff k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ∑ k ∈ Finset.range (d + 1), ‖P.coeff k‖ = ‖aeval (shiftOp ⊤ ℂ) P x d‖ := by
        rw [hyd, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
    _ ≤ ‖aeval (shiftOp ⊤ ℂ) P x‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero _ _
    _ ≤ ‖aeval (shiftOp ⊤ ℂ) P‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖aeval (shiftOp ⊤ ℂ) P‖ := by
        nlinarith [norm_nonneg (aeval (shiftOp ⊤ ℂ) P), norm_nonneg x]

end Matsaev.P1Inf
