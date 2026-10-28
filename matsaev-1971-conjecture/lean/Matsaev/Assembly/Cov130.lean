/-
Matsaev/Assembly/Cov130.lean — claims of the short paper v1.30 (kept in v2.00) that v0.90 did not state:
the truncations of `x_{n+2} = -x_n` almost maximise `P_0(S)` (Idea of the proof of Theorem A).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route. For `2 ≤ n < L` the truncation `y` of `x` has `(P_0(S)y)_n = x_n - B x_{n-2} = (1+B) x_n`, so
`‖P_0(S)y‖^p ≥ (1+B)^p (‖y‖^p - |x_0|^p - |x_1|^p)`; and `‖y‖^p ≥ k (|x_0|^p + |x_1|^p)` once `L ≥ 2k`. The upper bound
`‖P_0(S)y‖ ≤ (1+B)‖y‖` is the triangle inequality (`S` is an isometry).
-/
import Matsaev.Ops.JLower
import Matsaev.Bridge.Basic
import Matsaev.Assembly.Gamma
import Matsaev.ThmB.Basic

namespace Matsaev.Cov130

open Polynomial Finset
open scoped ENNReal Matrix

variable {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- `|x_{2k}| = |x_0|` and `|x_{2k+1}| = |x_1|` when `x_{n+2} = -x_n`. -/
lemma norm_antiperiodic {x : ℕ → 𝕜} (hx : ∀ n, x (n + 2) = -x n) (k : ℕ) :
    ‖x (2 * k)‖ = ‖x 0‖ ∧ ‖x (2 * k + 1)‖ = ‖x 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * k + 2 + 1 = (2 * k + 1) + 2 by ring, hx, hx, norm_neg,
      norm_neg]
    exact ih

/-- `∑_{n < 2k} |x_n|^r = k (|x_0|^r + |x_1|^r)`. -/
lemma sum_two_mul {x : ℕ → 𝕜} (hx : ∀ n, x (n + 2) = -x n) (r : ℝ) (k : ℕ) :
    ∑ n ∈ range (2 * k), ‖x n‖ ^ r = k * (‖x 0‖ ^ r + ‖x 1‖ ^ r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      (norm_antiperiodic hx k).1, (norm_antiperiodic hx k).2]
    push_cast
    ring

/-- `‖y‖^r = ∑_{n < L} |x_n|^r` for the truncation `y` of `x`. -/
lemma norm_trunc_rpow (hp : p ≠ ⊤) {x : ℕ → 𝕜} {L : ℕ} (y : lp (fun _ : ℕ => 𝕜) p)
    (hy : ∀ n, y n = if n < L then x n else 0) :
    ‖y‖ ^ p.toReal = ∑ n ∈ range L, ‖x n‖ ^ p.toReal := by
  have hr := JLower.toReal_pos_of_ne_top p hp
  rw [lp.norm_rpow_eq_tsum hr, tsum_eq_sum (s := range L)]
  · refine sum_congr rfl fun n hn => ?_
    rw [hy, ite_eq_left (mem_range.mp hn)]
  · intro n hn
    rw [hy, ite_eq_right (by simpa using hn), norm_zero, Real.zero_rpow hr.ne']

/-- `P_0(S) = 1 - B S²` applied at `n`. -/
lemma aeval_P0_apply (B : ℝ) (y : lp (fun _ : ℕ => 𝕜) p) (n : ℕ) :
    aeval (shiftOp p 𝕜) (Pa (0 : 𝕜) (B : 𝕜)) y n = y n - B * (if 2 ≤ n then y (n - 2) else 0) := by
  have h2 : (shiftOp p 𝕜 (shiftOp p 𝕜 y)) n = if 2 ≤ n then y (n - 2) else 0 := by
    simpa [sq] using JLower.shiftOp_pow_apply p 2 y n
  have hop : aeval (shiftOp p 𝕜) (Pa (0 : 𝕜) (B : 𝕜)) y = y - (B : 𝕜) • (shiftOp p 𝕜 (shiftOp p 𝕜 y)) := by
    simp [Pa, Algebra.algebraMap_eq_smul_one, sq]
  rw [hop, ← h2]
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- The lower bound `‖P_0(S)y‖^r ≥ (1+B)^r (‖y‖^r - |x_0|^r - |x_1|^r)` for `L ≥ 2`. -/
lemma rpow_lower (hp : p ≠ ⊤) {B : ℝ} (hB : 0 ≤ B) {x : ℕ → 𝕜} (hx : ∀ n, x (n + 2) = -x n) {L : ℕ} (hL : 2 ≤ L)
    (y : lp (fun _ : ℕ => 𝕜) p) (hy : ∀ n, y n = if n < L then x n else 0) :
    (1 + B) ^ p.toReal * (‖y‖ ^ p.toReal - (‖x 0‖ ^ p.toReal + ‖x 1‖ ^ p.toReal)) ≤
      ‖aeval (shiftOp p 𝕜) (Pa (0 : 𝕜) (B : 𝕜)) y‖ ^ p.toReal := by
  have hr := JLower.toReal_pos_of_ne_top p hp
  set z := aeval (shiftOp p 𝕜) (Pa (0 : 𝕜) (B : 𝕜)) y
  have hs : Summable fun n => ‖z n‖ ^ p.toReal := (lp.memℓp z).summable hr
  have hz : ∀ n ∈ Ico 2 L, ‖z n‖ ^ p.toReal = (1 + B) ^ p.toReal * ‖x n‖ ^ p.toReal := by
    intro n hn
    obtain ⟨h2, hnL⟩ := mem_Ico.mp hn
    have hxn : x n = -x (n - 2) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h2
      rw [add_comm, hx, Nat.add_sub_cancel]
    rw [show z n = _ from aeval_P0_apply p B y n, ite_eq_left h2, hy, hy, ite_eq_left hnL, ite_eq_left (by omega), hxn]
    rw [show -x (n - 2) - (B : 𝕜) * x (n - 2) = -((1 + B : ℝ) : 𝕜) * x (n - 2) by push_cast; ring, norm_mul,
      norm_neg, RCLike.norm_ofReal, abs_of_nonneg (by linarith), Real.mul_rpow (by linarith) (norm_nonneg _),
      norm_neg]
  have hsplit : ∑ n ∈ range L, ‖x n‖ ^ p.toReal =
      ‖x 0‖ ^ p.toReal + ‖x 1‖ ^ p.toReal + ∑ n ∈ Ico 2 L, ‖x n‖ ^ p.toReal := by
    rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le 2) hL, sum_Ico_succ_top (Nat.zero_le 1),
      sum_Ico_succ_top (le_refl 0), Ico_self, sum_empty, zero_add]
  rw [norm_trunc_rpow p hp y hy, hsplit, lp.norm_rpow_eq_tsum hr z]
  calc (1 + B) ^ p.toReal * (‖x 0‖ ^ p.toReal + ‖x 1‖ ^ p.toReal + ∑ n ∈ Ico 2 L, ‖x n‖ ^ p.toReal -
        (‖x 0‖ ^ p.toReal + ‖x 1‖ ^ p.toReal))
      = ∑ n ∈ Ico 2 L, ‖z n‖ ^ p.toReal := by
        rw [sum_congr rfl hz, ← mul_sum]
        ring
    _ ≤ ∑' n, ‖z n‖ ^ p.toReal := hs.sum_le_tsum _ fun n _ => by positivity

/-- The upper bound `‖P_0(S)y‖ ≤ (1+B)‖y‖`. -/
lemma norm_upper {B : ℝ} (hB : 0 ≤ B) (y : lp (fun _ : ℕ => 𝕜) p) :
    ‖aeval (shiftOp p 𝕜) (Pa (0 : 𝕜) (B : 𝕜)) y‖ ≤ (1 + B) * ‖y‖ := by
  have hop : aeval (shiftOp p 𝕜) (Pa (0 : 𝕜) (B : 𝕜)) y = y - (B : 𝕜) • (shiftOp p 𝕜 (shiftOp p 𝕜 y)) := by
    simp [Pa, Algebra.algebraMap_eq_smul_one, sq]
  rw [hop]
  calc ‖y - (B : 𝕜) • shiftOp p 𝕜 (shiftOp p 𝕜 y)‖ ≤ ‖y‖ + ‖(B : 𝕜) • shiftOp p 𝕜 (shiftOp p 𝕜 y)‖ :=
        norm_sub_le _ _
    _ = (1 + B) * ‖y‖ := by
        rw [norm_smul, norm_shiftOp_apply, norm_shiftOp_apply, RCLike.norm_ofReal, abs_of_nonneg hB]
        ring

/-- **Idea of the proof of Theorem A**: long truncations `y` of every nonzero sequence with `x_{n+2} = -x_n` give
`‖P_0(S)y‖_p/‖y‖_p` within `ε` of `1 + B` (and never above it), `1 ≤ p < ∞`, `B ≥ 0`. -/
theorem truncations_almost_maximise (hp : p ≠ ⊤) {B : ℝ} (hB : 0 ≤ B) {x : ℕ → 𝕜} (hx : ∀ n, x (n + 2) = -x n)
    (hx0 : x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ y : lp (fun _ : ℕ => 𝕜) p, (∀ n, y n = if n < L then x n else 0) →
      1 + B - ε < ‖aeval (shiftOp p 𝕜) (Pa (0 : 𝕜) (B : 𝕜)) y‖ / ‖y‖ ∧
        ‖aeval (shiftOp p 𝕜) (Pa (0 : 𝕜) (B : 𝕜)) y‖ / ‖y‖ ≤ 1 + B := by
  have hr := JLower.toReal_pos_of_ne_top p hp
  have hr1 : 1 ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp (Fact.out : (1 : ℝ≥0∞) ≤ p)
    simpa using h
  set m := ‖x 0‖ ^ p.toReal + ‖x 1‖ ^ p.toReal with hm
  -- `m > 0`: otherwise `x_0 = x_1 = 0` and so `x = 0`
  have hmpos : 0 < m := by
    by_contra hle
    have h0 : x 0 = 0 ∧ x 1 = 0 := by
      have a0 := Real.rpow_nonneg (norm_nonneg (x 0)) p.toReal
      have a1 := Real.rpow_nonneg (norm_nonneg (x 1)) p.toReal
      have e0 : ‖x 0‖ ^ p.toReal = 0 := by linarith
      have e1 : ‖x 1‖ ^ p.toReal = 0 := by linarith
      rw [Real.rpow_eq_zero (norm_nonneg _) hr.ne', norm_eq_zero] at e0 e1
      exact ⟨e0, e1⟩
    apply hx0
    funext n
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact norm_eq_zero.mp (by rw [(norm_antiperiodic hx k).1, h0.1, norm_zero])
    · exact norm_eq_zero.mp (by rw [(norm_antiperiodic hx k).2, h0.2, norm_zero])
  obtain ⟨k, hk⟩ := exists_nat_gt (max 2 ((1 + B) / ε))
  have hk2 : (2 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hkε : (1 + B) / k < ε := by
    rw [div_lt_iff₀ (by linarith)]
    have := lt_of_le_of_lt (le_max_right _ _) hk
    rw [div_lt_iff₀ hε] at this
    linarith
  refine ⟨2 * k, fun L hL y hy => ?_⟩
  have hL2 : 2 ≤ L := by
    have : (2 : ℝ) ≤ L := by
      have h := (Nat.cast_le (α := ℝ)).mpr hL
      push_cast at h
      linarith
    exact_mod_cast this
  -- `‖y‖^r ≥ k m > 0`
  have hN : (k : ℝ) * m ≤ ‖y‖ ^ p.toReal := by
    rw [norm_trunc_rpow p hp y hy, ← sum_two_mul hx]
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hL) fun n _ _ => by positivity
  have hNpos : 0 < ‖y‖ ^ p.toReal := lt_of_lt_of_le (mul_pos (by linarith) hmpos) hN
  have hypos : 0 < ‖y‖ := by
    rcases (norm_nonneg y).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.zero_rpow hr.ne'] at hNpos
      exact absurd hNpos (lt_irrefl 0)
  have hup := norm_upper p hB y
  refine ⟨?_, (div_le_iff₀ hypos).mpr hup⟩
  -- `‖P_0(S)y‖^r ≥ ((1+B)(1-1/k))^r ‖y‖^r`
  set δ := 1 - 1 / (k : ℝ) with hδ
  have hδ0 : 0 < δ := by rw [hδ, sub_pos, div_lt_one (by linarith)]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδ]; linarith [show (0 : ℝ) < 1 / (k : ℝ) by positivity]
  have hlow := rpow_lower p hp hB hx hL2 y hy
  have hmN : m ≤ ‖y‖ ^ p.toReal / k := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have h1 : (1 + B) ^ p.toReal * (δ * ‖y‖ ^ p.toReal) ≤
      ‖aeval (shiftOp p 𝕜) (Pa (0 : 𝕜) (B : 𝕜)) y‖ ^ p.toReal := by
    refine le_trans ?_ hlow
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hδ]
    have : ‖y‖ ^ p.toReal / k = 1 / k * ‖y‖ ^ p.toReal := by ring
    nlinarith
  have hδr : δ ^ p.toReal ≤ δ := by
    calc δ ^ p.toReal ≤ δ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hr1
      _ = δ := Real.rpow_one δ
  have h2 : ((1 + B) * δ * ‖y‖) ^ p.toReal ≤ ‖aeval (shiftOp p 𝕜) (Pa (0 : 𝕜) (B : 𝕜)) y‖ ^ p.toReal := by
    rw [Real.mul_rpow (by positivity) hypos.le, Real.mul_rpow (by linarith) hδ0.le]
    refine le_trans ?_ h1
    have hc := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + B) p.toReal
    have hn := Real.rpow_nonneg hypos.le p.toReal
    calc (1 + B) ^ p.toReal * δ ^ p.toReal * ‖y‖ ^ p.toReal = (1 + B) ^ p.toReal * (δ ^ p.toReal * ‖y‖ ^ p.toReal) := by
          ring
      _ ≤ (1 + B) ^ p.toReal * (δ * ‖y‖ ^ p.toReal) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδr hn) hc
  have h3 : (1 + B) * δ * ‖y‖ ≤ ‖aeval (shiftOp p 𝕜) (Pa (0 : 𝕜) (B : 𝕜)) y‖ :=
    (Real.rpow_le_rpow_iff (by positivity) (norm_nonneg _) hr).mp h2
  rw [lt_div_iff₀ hypos]
  have : (1 + B - ε) * ‖y‖ < (1 + B) * δ * ‖y‖ := by
    apply mul_lt_mul_of_pos_right _ hypos
    rw [hδ]
    have : (1 + B) * (1 - 1 / (k : ℝ)) = 1 + B - (1 + B) / k := by ring
    linarith
  linarith

/-! ### The small rotation `R_(ε/2)` (Idea of the proof of Theorem A) and `R_θᵀ = R_(-θ)` (Theorem A) -/

/-- `R_θᵀ = R_(-θ)`. -/
lemma rot_transpose (θ : ℝ) : (Rot θ)ᵀ = Rot (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rot, Jmat, Real.cos_neg, Real.sin_neg]

/-- `R_(ε/2) (u, v)` in coordinates (the `D = 0` case of `Gamma.ex1`, `Gamma.ex2`). -/
lemma rot_mulVec (u v ε : ℝ) :
    Rot (ε / 2) *ᵥ ![u, v] = ![Gamma.ex1 0 u v ε, Gamma.ex2 0 u v ε] := by
  rw [Rot, TK.smul_one_add_smul_J_mulVec]
  ext i
  fin_cases i <;> simp [Gamma.ex1, Gamma.ex2]

/-- `‖R_(ε/2)(u, v)‖_p^p` has derivative `(p/2)(φ(u) v - φ(v) u)` at `ε = 0`. -/
lemma hasDerivAt_rot_rpow {q : ℝ} (hq : 1 < q) (u v : ℝ) :
    HasDerivAt (fun ε => |Gamma.ex1 0 u v ε| ^ q + |Gamma.ex2 0 u v ε| ^ q)
      (q * (phi q u * v - phi q v * u) / 2) 0 := by
  have g1 := (Matsaev.Angle.hasDerivAt_absRpow hq (Gamma.ex1 0 u v 0)).comp (0 : ℝ) (Gamma.hasDerivAt_ex1 0 u v 0)
  have g2 := (Matsaev.Angle.hasDerivAt_absRpow hq (Gamma.ex2 0 u v 0)).comp (0 : ℝ) (Gamma.hasDerivAt_ex2 0 u v 0)
  convert g1.add g2 using 1
  · funext x
    simp only [Pi.add_apply, Function.comp_apply]
  · simp [Gamma.ex1, Gamma.ex2]
    ring

/-- `d/dε ‖R_(ε/2) ξ‖_p |₀ = ½ Q(ξ) ‖ξ‖_p` for every real `ξ` (`1 < p < ∞`). -/
lemma hasDerivAt_rot_norm (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal) (hptop : p ≠ ⊤) (ξ : Fin 2 → ℝ) :
    HasDerivAt (fun ε => ‖WithLp.toLp p (Rot (ε / 2) *ᵥ ξ)‖)
      (1 / 2 * Qf p.toReal (ξ 0) (ξ 1) * ‖WithLp.toLp p ξ‖) 0 := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : ℝ, ξ = ![u, v] := ⟨ξ 0, ξ 1, by ext i; fin_cases i <;> rfl⟩
  have hq0 : 0 < p.toReal := by linarith
  by_cases h0 : (u, v) = (0, 0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    have hz : ∀ ε : ℝ, Rot (ε / 2) *ᵥ (![0, 0] : Fin 2 → ℝ) = 0 := fun ε => by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct]
    simp only [hz, WithLp.toLp_zero, norm_zero]
    have h00 : (![0, 0] : Fin 2 → ℝ) = 0 := by
      ext i
      fin_cases i <;> rfl
    rw [h00, WithLp.toLp_zero, norm_zero, mul_zero]
    exact hasDerivAt_const 0 0
  · have hM : 0 < |u| ^ p.toReal + |v| ^ p.toReal := Gamma.normq_pos h0
    have hfun : (fun ε => ‖WithLp.toLp p (Rot (ε / 2) *ᵥ ![u, v])‖) =
        fun ε => (|Gamma.ex1 0 u v ε| ^ p.toReal + |Gamma.ex2 0 u v ε| ^ p.toReal) ^ p.toReal⁻¹ := by
      funext ε
      rw [rot_mulVec, ← norm_toLp_fin2_rpow p hptop, Real.rpow_rpow_inv (norm_nonneg _) hq0.ne']
    have h00 : |Gamma.ex1 0 u v 0| ^ p.toReal + |Gamma.ex2 0 u v 0| ^ p.toReal = |u| ^ p.toReal + |v| ^ p.toReal := by
      simp [Gamma.ex1, Gamma.ex2]
    have hD := (hasDerivAt_rot_rpow hp u v).rpow_const (p := p.toReal⁻¹) (Or.inl (h00 ▸ hM.ne'))
    rw [hfun]
    convert hD using 1
    have hnorm : ‖WithLp.toLp p (![u, v] : Fin 2 → ℝ)‖ = (|u| ^ p.toReal + |v| ^ p.toReal) ^ p.toReal⁻¹ := by
      rw [← norm_toLp_fin2_rpow p hptop, Real.rpow_rpow_inv (norm_nonneg _) hq0.ne']
    rw [h00, hnorm, Real.rpow_sub_one hM.ne']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    unfold Qf
    field_simp


/-- `‖P(S)‖_p ≤ |c₀| + |c₁|` for `P = c₀ + c₁X`: `S` is a contraction. -/
theorem shiftNorm_deg_one_le (c₀ c₁ : ℂ) :
    shiftNorm p ℂ (C c₀ + C c₁ * X) ≤ ‖c₀‖ + ‖c₁‖ := by
  have hS : ‖shiftOp p ℂ‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hA : aeval (shiftOp p ℂ) (C c₀ + C c₁ * X) = c₀ • (1 : _) + c₁ • shiftOp p ℂ := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [shiftNorm, hA]
  calc ‖c₀ • (1 : lp (fun _ : ℕ => ℂ) p →L[ℂ] lp (fun _ : ℕ => ℂ) p) + c₁ • shiftOp p ℂ‖
      ≤ ‖c₀‖ * ‖(1 : lp (fun _ : ℕ => ℂ) p →L[ℂ] lp (fun _ : ℕ => ℂ) p)‖ + ‖c₁‖ * ‖shiftOp p ℂ‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ ‖c₀‖ * 1 + ‖c₁‖ * 1 := by
        gcongr
        exact ContinuousLinearMap.norm_id_le
    _ = ‖c₀‖ + ‖c₁‖ := by ring

/-- `J (1, i) = i (1, i)`, so `P(μJ)(1, i) = (c₀ + c₁ μ i)(1, i)` for `P = c₀ + c₁X`. -/
theorem aeval_deg_one_smul_J_mulVec (c₀ c₁ μ : ℂ) :
    aeval (μ • (Jmat : Matrix (Fin 2) (Fin 2) ℂ)) (C c₀ + C c₁ * X) *ᵥ ![1, Complex.I] =
      (c₀ + c₁ * μ * Complex.I) • ![1, Complex.I] := by
  ext i
  fin_cases i
  · simp [Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one]
  · simp [Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one]
    linear_combination (-(c₁ * μ)) * Complex.I_sq

/-- A unit `u` with `c = |c| u` (`u = 1` when `c = 0`). -/
theorem exists_unit_polar (c : ℂ) : ∃ u : ℂ, ‖u‖ = 1 ∧ c = (‖c‖ : ℂ) * u := by
  by_cases hc : c = 0
  · exact ⟨1, by simp, by simp [hc]⟩
  · refine ⟨c / (‖c‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hc)]
    · have : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hc
      field_simp

/-- The table's "`deg P ≤ 1`" (Section 1, the table): `‖c₀ + c₁S‖_p = |c₀| + |c₁|` for complex `c_k` and every `1 ≤ p ≤ ∞`. -/
theorem shiftNorm_deg_one (c₀ c₁ : ℂ) :
    shiftNorm p ℂ (C c₀ + C c₁ * X) = ‖c₀‖ + ‖c₁‖ := by
  refine le_antisymm (shiftNorm_deg_one_le p c₀ c₁) ?_
  obtain ⟨u, hu, hc₀⟩ := exists_unit_polar c₀
  -- choose `|μ| = 1` with `c₁ μ i = |c₁| u`
  obtain ⟨μ, hμ, hc₁⟩ : ∃ μ : ℂ, ‖μ‖ = 1 ∧ c₁ * μ * Complex.I = (‖c₁‖ : ℂ) * u := by
    by_cases h1 : c₁ = 0
    · exact ⟨1, by simp, by simp [h1]⟩
    · refine ⟨(‖c₁‖ : ℂ) * u / (Complex.I * c₁), ?_, ?_⟩
      · rw [norm_div, norm_mul, norm_mul, Complex.norm_real, norm_norm, hu, Complex.norm_I, one_mul, mul_one,
          div_self (norm_ne_zero_iff.mpr h1)]
      · field_simp
  have hval : ‖c₀ + c₁ * μ * Complex.I‖ = ‖c₀‖ + ‖c₁‖ := by
    rw [hc₁]
    nth_rewrite 1 [hc₀]
    rw [← add_mul, norm_mul, hu, mul_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hv := norm_mulVec_le_matNorm p (aeval (μ • (Jmat : Matrix (Fin 2) (Fin 2) ℂ)) (C c₀ + C c₁ * X))
    ![1, Complex.I]
  rw [aeval_deg_one_smul_J_mulVec, WithLp.toLp_smul, norm_smul, hval] at hv
  have hpos : 0 < ‖WithLp.toLp p (![1, Complex.I] : Fin 2 → ℂ)‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have := congrFun (congrArg WithLp.ofLp h) 0
    simp at this
  exact (le_of_mul_le_mul_right hv hpos).trans (Matsaev.ThmB.matNorm_aeval_smul_Jmat_le p _ μ hμ)

end Matsaev.Cov130
