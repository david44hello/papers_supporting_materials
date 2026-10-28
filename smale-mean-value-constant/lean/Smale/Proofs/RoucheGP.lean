/-
Smale/Proofs/RoucheGP.lean — tools for Remark 5.2 and the control (paper 009, tex l.433-442): composition of
coefficient lists, Chebyshev values at a rational point and P_c as a list, and a Rouché certificate: a zero of P
within R of z₀, from exact bounds on the Taylor coefficients of P at z₀ (via the argument principle of
ArgPrinciple.lean).
-/
import Smale.Proofs.ArgPrinciple
import Smale.Proofs.SchurList
import Smale.Proofs.DataPoly

namespace Smale.Exact

open Polynomial Complex ComplexConjugate Metric

/-! ### Composition of coefficient lists -/

/-- `p ∘ q` on coefficient lists (Horner). -/
def pcomp (p q : GP) : GP := p.foldr (fun c acc => padd [c] (pmul q acc)) []

theorem toPoly_pcomp (p q : GP) : toPoly (pcomp p q) = (toPoly p).comp (toPoly q) := by
  induction p with
  | nil => simp [pcomp, toPoly]
  | cons c p ih =>
    have e : pcomp (c :: p) q = padd [c] (pmul q (pcomp p q)) := rfl
    rw [e, toPoly_padd, toPoly_pmul, ih, toPoly_cons, toPoly_cons, toPoly_nil]
    simp only [mul_zero, add_zero, add_comp, C_comp, mul_comp, X_comp]

/-- `(toPoly [z₀, 1]).eval u = z₀ + u`. -/
theorem toPoly_shift (z₀ : GQ) : toPoly [z₀, ⟨1, 0⟩] = X + C z₀.toC := by
  rw [toPoly_cons, toPoly_cons, toPoly_nil]
  have h1 : (⟨1, 0⟩ : GQ).toC = 1 := by simp [GQ.toC, gq]
  rw [h1, map_one]; ring

/-- `(toPoly [0, r]) = C r * X`. -/
theorem toPoly_scale (r : GQ) : toPoly [GQ.zero, r] = C r.toC * X := by
  rw [toPoly_cons, toPoly_cons, toPoly_nil, GQ.toC_zero, map_zero]; ring

/-- The Taylor coefficients at `z₀`: `(toPoly (pcomp p [z₀, 1])).eval u = (toPoly p).eval (z₀ + u)`. -/
theorem eval_pcomp_shift (p : GP) (z₀ : GQ) (u : ℂ) :
    (toPoly (pcomp p [z₀, ⟨1, 0⟩])).eval u = (toPoly p).eval (z₀.toC + u) := by
  rw [toPoly_pcomp, eval_comp, toPoly_shift, eval_add, eval_X, eval_C, add_comm]

/-! ### Chebyshev values at a rational point, and `P_c` as a list -/

/-- `U_l(c)` for rational `c`, by the recurrence `U_{l+2} = 2c U_{l+1} - U_l`. -/
def uQ (c : ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => 2 * c
  | l + 2 => 2 * c * uQ c (l + 1) - uQ c l

theorem uQ_eq (c : ℚ) : ∀ l : ℕ, (Chebyshev.U ℝ (l : ℤ)).eval (c : ℝ) = (uQ c l : ℝ)
  | 0 => by simp [uQ, Chebyshev.U_zero]
  | 1 => by simp [uQ, Chebyshev.U_one]
  | l + 2 => by
    have h := Chebyshev.U_add_two ℝ (l : ℤ)
    rw [show ((l + 2 : ℕ) : ℤ) = (l : ℤ) + 2 by push_cast; ring, h,
      show (l : ℤ) + 1 = ((l + 1 : ℕ) : ℤ) by push_cast; ring]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    rw [uQ_eq c (l + 1), uQ_eq c l, uQ]
    push_cast; ring

/-- `P_c` at formal degree `n` for `H = toPoly h` and rational `c`, as a list. -/
def pdieu (h : GP) (n : ℕ) (c : ℚ) : GP :=
  (List.range n).map fun l => GQ.mul (h.getD (l + 1) GQ.zero) (GQ.ofQ (uQ c l))

theorem dieudonne_toPoly (h : GP) (n : ℕ) (c : ℚ) : dieudonne (toPoly h) n (c : ℝ) = toPoly (pdieu h n c) := by
  rw [pdieu, toPoly_map_range, dieudonne]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [coeff_toPoly, GQ.toC_mul, GQ.toC_ofQ, uQ_eq]
  push_cast; ring_nf

/-! ### A Rouché certificate -/

/-- `re² + im²`. -/
def GQ.nsq (a : GQ) : ℚ := a.re * a.re + a.im * a.im

theorem GQ.norm_sq_toC (a : GQ) : ‖a.toC‖ ^ 2 = (a.nsq : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, GQ.toC_re, GQ.toC_im, GQ.nsq]; push_cast; ring

theorem GQ.norm_le_of_nsq {a : GQ} {u : ℚ} (hu : 0 ≤ u) (h : a.nsq ≤ u * u) : ‖a.toC‖ ≤ u := by
  have hu' : (0 : ℝ) ≤ u := by exact_mod_cast hu
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hu' two_ne_zero, GQ.norm_sq_toC]
  exact_mod_cast (show a.nsq ≤ u ^ 2 by rw [sq]; exact h)

theorem GQ.le_norm_of_nsq {a : GQ} {l : ℚ} (hl : 0 ≤ l) (h : l * l ≤ a.nsq) : (l : ℝ) ≤ ‖a.toC‖ := by
  have hl' : (0 : ℝ) ≤ l := by exact_mod_cast hl
  rw [← pow_le_pow_iff_left₀ hl' (norm_nonneg _) two_ne_zero, GQ.norm_sq_toC]
  exact_mod_cast (show l ^ 2 ≤ a.nsq by rw [sq]; exact h)

/-- The value of `toPoly T` at `u`, with the linear term split off. -/
theorem eval_toPoly_split (T : GP) (h1 : 1 < T.length) (u : ℂ) :
    (toPoly T).eval u = (T.getD 1 GQ.zero).toC * u +
      ∑ k ∈ Finset.range T.length, (if k = 1 then 0 else (T.getD k GQ.zero).toC * u ^ k) := by
  rw [toPoly_eq_sum, eval_finsetSum]
  have e : ∀ k ∈ Finset.range T.length, (C (T.getD k GQ.zero).toC * X ^ k).eval u =
      (if k = 1 then (T.getD k GQ.zero).toC * u ^ k else 0) +
        (if k = 1 then 0 else (T.getD k GQ.zero).toC * u ^ k) := by
    intro k _; split_ifs <;> simp
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range T.length) 1,
    ite_eq_left (Finset.mem_range.2 h1), pow_one]

/-- Rouché with a certificate: if `T` is the Taylor expansion of `P` at `z₀` (`P(z₀ + u) = T(u)`), `uₖ ≥ |tₖ|`
(`k ≠ 1`), `0 ≤ l ≤ |t₁|` and `Σ_{k ≠ 1} uₖ Rᵏ < l R`, then `P` has a zero `z` with `|z - z₀| < R`. -/
theorem exists_root_of_cert (T : GP) (us : List ℚ) (l R : ℚ) (hR : 0 < R) (hl : 0 ≤ l)
    (hl1 : l * l ≤ (T.getD 1 GQ.zero).nsq)
    (hus : ∀ k ∈ Finset.range T.length, k ≠ 1 → 0 ≤ us.getD k 0 ∧ (T.getD k GQ.zero).nsq ≤ us.getD k 0 * us.getD k 0)
    (hsum : ∑ k ∈ Finset.range T.length, (if k = 1 then 0 else us.getD k 0 * R ^ k) < l * R)
    (P : ℂ[X]) (z₀ : ℂ) (hT : ∀ u : ℂ, P.eval (z₀ + u) = (toPoly T).eval u) :
    ∃ z : ℂ, P.eval z = 0 ∧ ‖z - z₀‖ < R := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  -- the bound sum is nonnegative, so `l > 0`, `t₁ ≠ 0` and `T` has length at least 2
  have hsum0 : (0 : ℚ) ≤ ∑ k ∈ Finset.range T.length, (if k = 1 then 0 else us.getD k 0 * R ^ k) := by
    refine Finset.sum_nonneg fun k hk => ?_
    split_ifs with h
    · exact le_rfl
    · exact mul_nonneg (hus k hk h).1 (pow_nonneg hR.le k)
  have hlpos : 0 < l := by
    by_contra h
    have : l = 0 := le_antisymm (not_lt.1 h) hl
    rw [this, zero_mul] at hsum; linarith
  set t1 := T.getD 1 GQ.zero with ht1
  have ht1n : (l : ℝ) ≤ ‖t1.toC‖ := GQ.le_norm_of_nsq hl hl1
  have hlen : 1 < T.length := by
    by_contra h
    have h0 : t1 = GQ.zero := List.getD_eq_default _ _ (by omega)
    rw [h0, GQ.toC_zero, norm_zero] at ht1n
    have : (0 : ℝ) < l := by exact_mod_cast hlpos
    linarith
  have ht1ne : t1.toC ≠ 0 := by
    intro h; rw [h, norm_zero] at ht1n
    have : (0 : ℝ) < l := by exact_mod_cast hlpos
    linarith
  -- f = t₁ (X - z₀), g = P - f
  set f : ℂ[X] := (X - C z₀) * C t1.toC with hf
  have hbound : ∀ w : ℂ, ‖w - z₀‖ = R → ‖(P - f).eval w‖ < ‖f.eval w‖ := by
    intro w hw
    have hPw : P.eval w = (toPoly T).eval (w - z₀) := by rw [← hT]; ring_nf
    have hfw : f.eval w = t1.toC * (w - z₀) := by rw [hf]; simp [mul_comm]
    rw [eval_sub, hPw, eval_toPoly_split T hlen, hfw, add_sub_cancel_left, norm_mul, hw]
    calc ‖∑ k ∈ Finset.range T.length, (if k = 1 then 0 else (T.getD k GQ.zero).toC * (w - z₀) ^ k)‖
        ≤ ∑ k ∈ Finset.range T.length, ‖(if k = 1 then 0 else (T.getD k GQ.zero).toC * (w - z₀) ^ k)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range T.length, ((if k = 1 then 0 else us.getD k 0 * R ^ k : ℚ) : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          split_ifs with h
          · simp
          · rw [norm_mul, norm_pow, hw]; push_cast
            exact mul_le_mul_of_nonneg_right (GQ.norm_le_of_nsq (hus k hk h).1 (hus k hk h).2)
              (pow_nonneg hR'.le k)
      _ < (l : ℝ) * R := by rw [← Rat.cast_sum]; exact_mod_cast hsum
      _ ≤ ‖t1.toC‖ * R := mul_le_mul_of_nonneg_right ht1n hR'.le
  have hcount := zerosInBall_add_of_norm_lt f (P - f) z₀ hR' hbound
  rw [add_sub_cancel, hf, zerosInBall_X_sub_C_mul z₀ z₀ R (C_ne_zero.2 ht1ne), sub_self, norm_zero,
    ite_eq_left hR'] at hcount
  have hpos : 0 < zerosInBall P z₀ R := by rw [hcount]; omega
  unfold zerosInBall at hpos
  obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  rw [Multiset.mem_filter] at hz
  have hP0 : P ≠ 0 := fun h => by simp [h] at hz
  exact ⟨z, (mem_roots hP0).1 hz.1, hz.2⟩

end Smale.Exact
