-- Matsaev/Ops/JLower.lean — proves Lemma 2.2 (lem:J): ‖P(J)‖ on ℓ^p_2 ≤ ‖P(S)‖ on ℓ^p(ℕ), every polynomial P, 1 ≤ p ≤ ∞.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
/-
Paper: short v2.00 (md5 a9b3c6be), Lemma 2.2 (`lem:J`).
Target: `lemma_2_2` of `Matsaev/Paper/Statements.lean`, stated here verbatim as `lemma_2_2_proved`.

Route (paper). Put `R = J⁻¹ = -J`, `z_n = R^n w = (x_n, x_{n-1})`, `d = deg P`, and truncate `x` to `0 ≤ n < L`.
1. `J^k R^n = R^(n-k)` and `P(J) R^n = R^n P(J)`, so `(P(S) x)_n = (R^n P(J) w)₀` for `d ≤ n < L`.
2. `R^4 = 1` and the first coordinates of `R^i v` (`i = 0..3`) are `v₀, -v₁, -v₀, v₁`.
3. `p < ∞`, `L = 4(d+m)`, `r = p.toReal`: `‖x‖^r = 2(d+m)‖w‖^r` and `‖P(S) x‖^r ≥ 2m‖P(J) w‖^r` (periods in `[4d, L)`);
   so `m ‖P(J)w‖^r ≤ (m+d) (‖P(S)‖ ‖w‖)^r` for all `m`, hence `‖P(J)w‖ ≤ ‖P(S)‖ ‖w‖`.
4. `p = ∞`, `L = 4(d+1)`: `‖x‖_∞ ≤ ‖w‖_∞`, and `(P(S)x)_{4d} = (P(J)w)₀`, `(P(S)x)_{4d+3} = (P(J)w)₁`.
-/
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.Defs.Spaces
import Matsaev.Bridge.Basic

namespace Matsaev

open scoped ENNReal Matrix
open Polynomial

namespace JLower

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `R = J⁻¹ = -J`. The 4-periodic sequence of the paper is `z_n = (x_n, x_{n-1}) = R^n w`. -/
def Rmat : Matrix (Fin 2) (Fin 2) 𝕜 := -Jmat

theorem Rmat_sq : (Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ 2 = -1 := by
  simp [Rmat, sq, Jmat_mul_Jmat]

theorem Rmat_pow_four_mul_add (d i : ℕ) : (Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ (4 * d + i) = Rmat ^ i := by
  rw [pow_add, show 4 * d = 2 * (2 * d) by ring, pow_mul, Rmat_sq, pow_mul, neg_one_sq, one_pow, one_mul]

theorem Rmat_pow_four_mul (d : ℕ) : (Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ (4 * d) = 1 := by
  simpa using Rmat_pow_four_mul_add (𝕜 := 𝕜) d 0

theorem Jmat_mul_Rmat : (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) * Rmat = 1 := by
  simp [Rmat, Jmat_mul_Jmat]

/-- `J^k R^n = R^(n-k)` for `k ≤ n`, i.e. `J^k z_n = z_{n-k}`. -/
theorem Jmat_pow_mul_Rmat_pow {k n : ℕ} (hkn : k ≤ n) :
    (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ k * Rmat ^ n = Rmat ^ (n - k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
  have hc : Commute (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) Rmat := (Commute.refl _).neg_right
  rw [pow_add, ← mul_assoc, ← hc.mul_pow, Jmat_mul_Rmat, one_pow, one_mul, Nat.add_sub_cancel_left]

/-- `P(J)` commutes with `R^n` (both are polynomials in `J`). -/
theorem aeval_Jmat_mul_Rmat_pow (P : 𝕜[X]) (n : ℕ) :
    aeval (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) P * Rmat ^ n = Rmat ^ n * aeval Jmat P := by
  have hR : (Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ n = aeval Jmat ((-X : 𝕜[X]) ^ n) := by simp [Rmat]
  rw [hR, ← map_mul, ← map_mul, mul_comm]

theorem Rmat_mulVec_zero (v : Fin 2 → 𝕜) : ((Rmat : Matrix (Fin 2) (Fin 2) 𝕜) *ᵥ v) 0 = -v 1 := by
  simp [Rmat, Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- First coordinates of `R^i v`, `i = 0, 1, 2, 3`: `v₀, -v₁, -v₀, v₁`. -/
theorem Rmat_pow_mulVec_zero (v : Fin 2 → 𝕜) :
    ((Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ 0 *ᵥ v) 0 = v 0 ∧ ((Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ 1 *ᵥ v) 0 = -v 1 ∧
      ((Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ 2 *ᵥ v) 0 = -v 0 ∧ ((Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ 3 *ᵥ v) 0 = v 1 := by
  refine ⟨by simp, by simp [Rmat_mulVec_zero], by simp [Rmat_sq], ?_⟩
  rw [pow_succ', Rmat_sq, ← Matrix.mulVec_mulVec]
  simp [Rmat_mulVec_zero]

/-- Each first coordinate of `R^i v` is `±v₀` or `±v₁`, so its norm is at most `‖v‖_p`. -/
theorem norm_Rmat_pow_mulVec_zero_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (v : Fin 2 → 𝕜) (i : ℕ) :
    ‖((Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ i *ᵥ v) 0‖ ≤ ‖WithLp.toLp p v‖ := by
  have h0 : ‖v 0‖ ≤ ‖WithLp.toLp p v‖ := PiLp.norm_apply_le (WithLp.toLp p v) 0
  have h1 : ‖v 1‖ ≤ ‖WithLp.toLp p v‖ := PiLp.norm_apply_le (WithLp.toLp p v) 1
  obtain ⟨e0, e1, e2, e3⟩ := Rmat_pow_mulVec_zero v
  rw [← Nat.div_add_mod i 4, Rmat_pow_four_mul_add]
  have hlt := Nat.mod_lt i (show 0 < 4 by norm_num)
  interval_cases (i % 4) <;> simp_all

/-- Over one period, `∑_{i<4} ‖(R^i v)₀‖^r = 2 (‖v₀‖^r + ‖v₁‖^r)`; over `m` periods, `2m` times that. -/
theorem sum_norm_Rmat_pow_mulVec_zero (r : ℝ) (v : Fin 2 → 𝕜) (m : ℕ) :
    ∑ i ∈ Finset.range (4 * m), ‖((Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ i *ᵥ v) 0‖ ^ r =
      2 * m * (‖v 0‖ ^ r + ‖v 1‖ ^ r) := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨e0, e1, e2, e3⟩ := Rmat_pow_mulVec_zero v
    rw [show 4 * (m + 1) = 4 * m + 3 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [Rmat_pow_four_mul_add, Rmat_pow_four_mul, Matrix.one_mulVec, e1, e2, e3, norm_neg]
    push_cast
    ring


/-! ### The shift side -/

section Shift

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- `(S^k x)_n = x_{n-k}` for `k ≤ n`, and `0` otherwise. -/
theorem shiftOp_pow_apply (k : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) (n : ℕ) :
    ((shiftOp p 𝕜) ^ k) x n = if k ≤ n then x (n - k) else 0 := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change shiftOp p 𝕜 ((shiftOp p 𝕜 ^ k) x) n = _
    rw [shiftOp_apply]
    cases n with
    | zero => simp [shiftSeq]
    | succ n =>
      rw [show shiftSeq (⇑((shiftOp p 𝕜 ^ k) x)) (n + 1) = ((shiftOp p 𝕜 ^ k) x) n from rfl, ih]
      simp only [Nat.add_le_add_iff_right, Nat.add_sub_add_right]

/-- `(P(S) x)_n = ∑_k c_k (S^k x)_n`. -/
theorem aeval_shiftOp_apply (P : 𝕜[X]) (x : lp (fun _ : ℕ => 𝕜) p) (n : ℕ) :
    aeval (shiftOp p 𝕜) P x n = ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * ((shiftOp p 𝕜) ^ k) x n := by
  rw [aeval_eq_sum_range, _root_.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  simp

/-- `(P(J) v)_i = ∑_k c_k (J^k v)_i`. -/
theorem aeval_Jmat_mulVec_apply (P : 𝕜[X]) (v : Fin 2 → 𝕜) (i : Fin 2) :
    (aeval (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) P *ᵥ v) i =
      ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * ((Jmat ^ k : Matrix (Fin 2) (Fin 2) 𝕜) *ᵥ v) i := by
  rw [aeval_eq_sum_range, Matrix.sum_mulVec, Finset.sum_apply]
  simp [Matrix.smul_mulVec]

/-- The paper's sequence `x_n = (R^n w)₀`, truncated to `0 ≤ n < L`; finitely supported, so in `ℓ^p(ℕ)`. -/
noncomputable def truncSeq (w : Fin 2 → 𝕜) (L : ℕ) : lp (fun _ : ℕ => 𝕜) p :=
  ⟨fun n => if n < L then ((Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ n *ᵥ w) 0 else 0,
    (memℓp_zero ((Finset.range L).finite_toSet.subset fun n hn => by
      by_contra h
      exact hn (ite_eq_right (by simpa using h)))).of_exponent_ge zero_le⟩

omit [Fact (1 ≤ p)] in
theorem truncSeq_apply (w : Fin 2 → 𝕜) (L n : ℕ) :
    truncSeq p w L n = if n < L then ((Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ n *ᵥ w) 0 else 0 :=
  rfl

/-- The key identity `(P(S) x)_n = (R^n P(J) w)₀` for `deg P ≤ n < L` (paper: `(P(S)x)_n = (P(J) z_n)_1`). -/
theorem aeval_shiftOp_truncSeq_apply (P : 𝕜[X]) (w : Fin 2 → 𝕜) {L n : ℕ} (hdn : P.natDegree ≤ n) (hnL : n < L) :
    aeval (shiftOp p 𝕜) P (truncSeq p w L) n =
      ((Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ n *ᵥ (aeval Jmat P *ᵥ w)) 0 := by
  rw [Matrix.mulVec_mulVec, ← aeval_Jmat_mul_Rmat_pow, ← Matrix.mulVec_mulVec, aeval_Jmat_mulVec_apply,
    aeval_shiftOp_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hdn
  rw [shiftOp_pow_apply, ite_eq_left hkn, truncSeq_apply, ite_eq_left (by omega), Matrix.mulVec_mulVec,
    Jmat_pow_mul_Rmat_pow hkn]

end Shift

/-! ### The bound for `1 ≤ p < ∞` (sums over whole periods) -/

/-- If `m A ≤ (m + d) B` for every `m : ℕ`, then `A ≤ B` (the paper's limit `m → ∞`). -/
theorem le_of_forall_nat_mul_le {A B d : ℝ} (h : ∀ m : ℕ, (m : ℝ) * A ≤ (m + d) * B) : A ≤ B := by
  by_contra hlt
  push Not at hlt
  obtain ⟨m, hm⟩ := exists_nat_gt (d * B / (A - B))
  rw [div_lt_iff₀ (sub_pos.mpr hlt)] at hm
  have hmAB := h m
  linarith

section Finite

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem toReal_pos_of_ne_top (hp : p ≠ ⊤) : 0 < p.toReal :=
  ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp

/-- `‖x^{(L)}‖^r = ∑_{n<L} ‖(R^n w)₀‖^r` with `r = p.toReal`. -/
theorem norm_truncSeq_rpow (hp : p ≠ ⊤) (w : Fin 2 → 𝕜) (L : ℕ) :
    ‖truncSeq p w L‖ ^ p.toReal =
      ∑ n ∈ Finset.range L, ‖((Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ n *ᵥ w) 0‖ ^ p.toReal := by
  have hr := toReal_pos_of_ne_top p hp
  rw [lp.norm_rpow_eq_tsum hr, tsum_eq_sum (s := Finset.range L)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [truncSeq_apply, ite_eq_left (Finset.mem_range.mp hn)]
  · intro n hn
    rw [truncSeq_apply, ite_eq_right (by simpa using hn), norm_zero, Real.zero_rpow hr.ne']

/-- Lower bound from the `m` whole periods `4d ≤ n < 4(d + m)`, `d = deg P`:
`2m ‖P(J) w‖^r ≤ ‖P(S) x^{(4(d+m))}‖^r`. -/
theorem rpow_le_norm_aeval_truncSeq (hp : p ≠ ⊤) (P : 𝕜[X]) (w : Fin 2 → 𝕜) (m : ℕ) :
    2 * m * ‖WithLp.toLp p (aeval (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) P *ᵥ w)‖ ^ p.toReal ≤
      ‖aeval (shiftOp p 𝕜) P (truncSeq p w (4 * (P.natDegree + m)))‖ ^ p.toReal := by
  have hr := toReal_pos_of_ne_top p hp
  set d := P.natDegree
  set v := aeval (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) P *ᵥ w
  set y := aeval (shiftOp p 𝕜) P (truncSeq p w (4 * (d + m)))
  have hs : Summable fun n => ‖y n‖ ^ p.toReal := (lp.memℓp y).summable hr
  rw [lp.norm_rpow_eq_tsum hr y]
  calc 2 * m * ‖WithLp.toLp p v‖ ^ p.toReal
      = ∑ i ∈ Finset.range (4 * m), ‖((Rmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ i *ᵥ v) 0‖ ^ p.toReal := by
        rw [sum_norm_Rmat_pow_mulVec_zero, norm_toLp_rpow p hp, Fin.sum_univ_two]
    _ = ∑ n ∈ Finset.Ico (4 * d) (4 * d + 4 * m), ‖y n‖ ^ p.toReal := by
        rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.mp hi
        rw [aeval_shiftOp_truncSeq_apply p P w (by omega) (by omega), Rmat_pow_four_mul_add]
    _ ≤ ∑' n, ‖y n‖ ^ p.toReal := hs.sum_le_tsum _ fun n _ => by positivity

/-- **Lemma 2.2 for `1 ≤ p < ∞`**, vector form: `‖P(J) w‖_p ≤ ‖P(S)‖ ‖w‖_p`. -/
theorem norm_aeval_Jmat_mulVec_le (hp : p ≠ ⊤) (P : 𝕜[X]) (w : Fin 2 → 𝕜) :
    ‖WithLp.toLp p (aeval (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) P *ᵥ w)‖ ≤ shiftNorm p 𝕜 P * ‖WithLp.toLp p w‖ := by
  have hr := toReal_pos_of_ne_top p hp
  have hS : 0 ≤ shiftNorm p 𝕜 P := norm_nonneg _
  have key : ∀ m : ℕ, (m : ℝ) * ‖WithLp.toLp p (aeval (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) P *ᵥ w)‖ ^ p.toReal ≤
      (m + P.natDegree) * (shiftNorm p 𝕜 P * ‖WithLp.toLp p w‖) ^ p.toReal := by
    intro m
    have h1 := rpow_le_norm_aeval_truncSeq p hp P w m
    have hop : ‖aeval (shiftOp p 𝕜) P (truncSeq p w (4 * (P.natDegree + m)))‖ ≤
        shiftNorm p 𝕜 P * ‖truncSeq p w (4 * (P.natDegree + m))‖ := (aeval (shiftOp p 𝕜) P).le_opNorm _
    have h2 := Real.rpow_le_rpow (norm_nonneg _) hop hr.le
    rw [Real.mul_rpow hS (norm_nonneg _), norm_truncSeq_rpow p hp, sum_norm_Rmat_pow_mulVec_zero,
      ← Fin.sum_univ_two (fun i => ‖w i‖ ^ p.toReal), ← norm_toLp_rpow p hp] at h2
    rw [Real.mul_rpow hS (norm_nonneg _)]
    push_cast at h2
    linarith
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hr).mp
    (le_of_forall_nat_mul_le key)

end Finite

/-! ### The bound for `p = ∞` (maxima) -/

/-- **Lemma 2.2 for `p = ∞`**, vector form (proof of Lemma 2.2): `‖x^{(4(d+1))}‖_∞ ≤ ‖w‖_∞`, and the values of
`P(S) x^{(4(d+1))}` at `n = 4d` and `n = 4d + 3` are `(P(J) w)₀` and `(P(J) w)₁`. -/
theorem norm_aeval_Jmat_mulVec_le_top (P : 𝕜[X]) (w : Fin 2 → 𝕜) :
    ‖WithLp.toLp ⊤ (aeval (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) P *ᵥ w)‖ ≤ shiftNorm ⊤ 𝕜 P * ‖WithLp.toLp ⊤ w‖ := by
  set d := P.natDegree
  set v := aeval (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) P *ᵥ w
  set y := truncSeq ⊤ w (4 * (d + 1))
  have hy : ‖y‖ ≤ ‖WithLp.toLp ⊤ w‖ := by
    refine lp.norm_le_of_forall_le (norm_nonneg _) fun n => ?_
    rw [truncSeq_apply]
    split_ifs
    · exact norm_Rmat_pow_mulVec_zero_le ⊤ w n
    · simp
  obtain ⟨-, -, -, e3⟩ := Rmat_pow_mulVec_zero v
  have hv0 : ‖v 0‖ ≤ ‖aeval (shiftOp ⊤ 𝕜) P y‖ := by
    have h := lp.norm_apply_le_norm ENNReal.top_ne_zero (aeval (shiftOp ⊤ 𝕜) P y) (4 * d)
    rwa [aeval_shiftOp_truncSeq_apply ⊤ P w (by omega) (by omega), Rmat_pow_four_mul,
      Matrix.one_mulVec] at h
  have hv1 : ‖v 1‖ ≤ ‖aeval (shiftOp ⊤ 𝕜) P y‖ := by
    have h := lp.norm_apply_le_norm ENNReal.top_ne_zero (aeval (shiftOp ⊤ 𝕜) P y) (4 * d + 3)
    rwa [aeval_shiftOp_truncSeq_apply ⊤ P w (by omega) (by omega), Rmat_pow_four_mul_add, e3] at h
  have hv : ‖WithLp.toLp ⊤ v‖ ≤ ‖aeval (shiftOp ⊤ 𝕜) P y‖ := by
    rw [PiLp.norm_eq_ciSup]
    refine ciSup_le fun i => ?_
    fin_cases i
    exacts [hv0, hv1]
  calc ‖WithLp.toLp ⊤ v‖ ≤ ‖aeval (shiftOp ⊤ 𝕜) P y‖ := hv
    _ ≤ shiftNorm ⊤ 𝕜 P * ‖y‖ := (aeval (shiftOp ⊤ 𝕜) P).le_opNorm y
    _ ≤ shiftNorm ⊤ 𝕜 P * ‖WithLp.toLp ⊤ w‖ := mul_le_mul_of_nonneg_left hy (norm_nonneg _)

end JLower

/-- **Lemma 2.2** (`lem:J`): for every polynomial `P` and `1 ≤ p ≤ ∞`, `‖P(J)‖_{ℓ^p_2} ≤ ‖P(S)‖_{ℓ^p}`.
Exactly the statement `Matsaev.Paper.lemma_2_2`. -/
theorem lemma_2_2_proved {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (P : 𝕜[X]) :
    matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) P) ≤ shiftNorm p 𝕜 P := by
  rw [matNorm_le_iff p _ (show 0 ≤ shiftNorm p 𝕜 P from norm_nonneg _)]
  intro w
  obtain rfl | hp := eq_or_ne p ⊤
  · exact JLower.norm_aeval_Jmat_mulVec_le_top P w
  · exact JLower.norm_aeval_Jmat_mulVec_le p hp P w

end Matsaev
