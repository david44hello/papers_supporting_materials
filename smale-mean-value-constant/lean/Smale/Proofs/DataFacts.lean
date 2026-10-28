/-
Smale/Proofs/DataFacts.lean — the exact facts about the data of Section 5 that the main chain uses: (D) for b, a₁, a₂;
`Q' = (z - 1)⁵ V`; `J(a₁, b) J(a₂, b) = Λ`; `√Λ > 1.1559837` and its digits; the margin `Λ - 1.1559837²`; the sizes
of the denominators of `g₀, g₁`.
-/
import Smale.Proofs.DataPoly

namespace Smale.Exact

open Polynomial Complex ComplexConjugate

/-- `|a|²` of a Gaussian rational, in `ℚ`. -/
def nsq (a : GQ) : ℚ := a.re * a.re + a.im * a.im

theorem sq_norm_toC (a : GQ) : ‖a.toC‖ ^ 2 = (nsq a : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, GQ.toC_re, GQ.toC_im, nsq]; push_cast; ring

theorem norm_toC_lt_one {a : GQ} (h : nsq a < 1) : ‖a.toC‖ < 1 := by
  have h2 : ‖a.toC‖ ^ 2 < 1 := by rw [sq_norm_toC]; exact_mod_cast h
  nlinarith [norm_nonneg a.toC]

/-- `J(a, b)` in `ℚ`. -/
def jabQ (a b : GQ) : ℚ := 1 + (1 - nsq a) * (1 - nsq b) / nsq (GQ.add a (GQ.neg b))

theorem Jab_toC (a b : GQ) : Jab a.toC b.toC = (jabQ a b : ℝ) := by
  have hsub : a.toC - b.toC = (GQ.add a (GQ.neg b)).toC := by rw [GQ.toC_add, GQ.toC_neg, sub_eq_add_neg]
  rw [Jab, jabQ, hsub, sq_norm_toC, sq_norm_toC, sq_norm_toC]
  push_cast; ring

/-- (D) for our data: `b, a₁, a₂` are distinct zeros of `Q` in `𝔻`. -/
theorem data_D :
    (∀ a ∈ [bD, a1D, a2D], ‖a‖ < 1) ∧ [bD, a1D, a2D].Nodup ∧ ∀ a ∈ [bD, a1D, a2D], Qdata.eval a = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, bD_eq, a1D_eq, a2D_eq]
    exact ⟨norm_toC_lt_one (by decide +kernel), norm_toC_lt_one (by decide +kernel),
      norm_toC_lt_one (by decide +kernel)⟩
  · simp only [bD_eq, a1D_eq, a2D_eq, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      GQ.toC_injective.eq_iff, List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨?_, ?_⟩ <;> decide +kernel
  · have hb : peval qGQ bGQ = GQ.zero := by decide +kernel
    have h1 : peval qGQ a1GQ = GQ.zero := by decide +kernel
    have h2 : peval qGQ a2GQ = GQ.zero := by decide +kernel
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, bD_eq, a1D_eq, a2D_eq,
      Qdata_eq, eval_toPoly, hb, h1, h2, GQ.toC_zero, and_self]

theorem data_Jab : Jab a1D bD * Jab a2D bD = (LambdaQ : ℝ) := by
  have h : jabQ a1GQ bGQ * jabQ a2GQ bGQ = LambdaQ := by decide +kernel
  rw [a1D_eq, a2D_eq, bD_eq, Jab_toC, Jab_toC, ← h]; push_cast; ring

theorem data_margin :
    (6.75e-8 : ℝ) ≤ (LambdaQ : ℝ) - 1.1559837 ^ 2 ∧ (LambdaQ : ℝ) - 1.1559837 ^ 2 < 6.76e-8 := by
  constructor <;> norm_num [LambdaQ]

theorem data_sqrt_gt : (1.1559837 : ℝ) < Real.sqrt LambdaQ := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num [LambdaQ]

theorem data_sqrt_digits : (1.15598372919 : ℝ) ≤ Real.sqrt LambdaQ ∧ Real.sqrt LambdaQ < 1.1559837292 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num [LambdaQ])]; norm_num [LambdaQ]
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num [LambdaQ]

theorem data_g_digits :
    ∃ x y u v : ℚ, g0D = gq x y ∧ g1D = gq u v ∧ ∀ q ∈ [x, y, u, v], 10 ^ 450 ≤ q.den ∧ q.den < 10 ^ 458 :=
  ⟨g0GQ.re, g0GQ.im, g1GQ.re, g1GQ.im, rfl, rfl, by decide +kernel⟩

end Smale.Exact
