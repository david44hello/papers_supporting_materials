-- Matsaev/SJ/BellmanAlg.lean — algebra of the Bellman function (Steps F1-F5 of Theorem 3.6): homogeneity, decomposition, λ-system.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.Defs.Spaces
import Matsaev.Bridge.Basic
import Matsaev.Angle.Defs
import Matsaev.SJ.Interface
import Matsaev.SJ.BellmanDefs

/-!
Definitions: `Matsaev/SJ/BellmanDefs.lean` (read its docstring first). Do NOT change any statement below; fill the proofs.
-/

namespace Matsaev.SJ

open Real
open scoped Matrix

/-! Private helpers. -/

/-- `|r x|^q = r^q |x|^q` for `r ≥ 0`. -/
private lemma abs_mul_rpow_of_nonneg {q r : ℝ} (hr : 0 ≤ r) (x : ℝ) : |r * x| ^ q = r ^ q * |x| ^ q := by
  rw [abs_mul, abs_of_nonneg hr, mul_rpow hr (abs_nonneg x)]

/-- `φ` is odd. -/
private lemma phi_neg' (q x : ℝ) : phi q (-x) = -phi q x := by
  unfold phi
  rw [Left.sign_neg, abs_neg, SignType.coe_neg]
  ring

private lemma k1_mul {q r : ℝ} (hr : 0 ≤ r) (s t : ℝ) : k1 q (r * s) (r * t) = r ^ q * k1 q s t := by
  unfold k1
  rw [show (r * s) ^ 2 + (r * t) ^ 2 = r ^ 2 * (s ^ 2 + t ^ 2) by ring, mul_rpow (by positivity) (by positivity)]
  congr 1
  rw [← rpow_natCast, ← rpow_mul hr]
  congr 1
  push_cast
  ring

private lemma Gab_mul {q a B C l1 l2 r : ℝ} (hr : 0 ≤ r) (s t : ℝ) :
    Gab q a B C l1 l2 (r * s) (r * t) = r ^ q * Gab q a B C l1 l2 s t := by
  unfold Gab G0 Da k2
  rw [k1_mul hr, abs_mul_rpow_of_nonneg hr s, abs_mul_rpow_of_nonneg hr t,
    show (1 + B) * (r * s) + a * (r * t) = r * ((1 + B) * s + a * t) by ring, abs_mul_rpow_of_nonneg hr]
  ring

private lemma bellmanF_mul {q a B C l1 l2 r : ℝ} (hr : 0 ≤ r) (u v w : ℝ) :
    bellmanF q a B C (Gab q a B C l1 l2) (r * u) (r * v) (r * w) =
      r ^ q * bellmanF q a B C (Gab q a B C l1 l2) u v w := by
  unfold bellmanF
  rw [Gab_mul hr, Gab_mul hr, abs_mul_rpow_of_nonneg hr u,
    show r * u + a * (r * v) - B * (r * w) = r * (u + a * v - B * w) by ring, abs_mul_rpow_of_nonneg hr]
  ring

/-- Polar coordinates of a nonzero point of `ℝ²`. -/
private lemma exists_polar_uv {u v : ℝ} (huv : ¬(u = 0 ∧ v = 0)) :
    ∃ r : ℝ, 0 < r ∧ ∃ θ : ℝ, u = r * Real.cos θ ∧ v = r * Real.sin θ := by
  have hz : (⟨u, v⟩ : ℂ) ≠ 0 := fun h => huv ⟨congrArg Complex.re h, congrArg Complex.im h⟩
  exact ⟨‖(⟨u, v⟩ : ℂ)‖, norm_pos_iff.mpr hz, Complex.arg ⟨u, v⟩,
    (Complex.norm_mul_cos_arg (⟨u, v⟩ : ℂ)).symm, (Complex.norm_mul_sin_arg (⟨u, v⟩ : ℂ)).symm⟩

/-- F1 (homogeneity, Theorem 3.6, Step 6): `F(r x) = r^q F(x)` for `r > 0`, so `F ≥ 0` on `ℝ³` follows from `F ≥ 0` at `s = (u, v) = 0`
and on the unit circle `(u, v) = (cos θ, sin θ)` (any `w`, written `w = -cos θ + ν`). Hint: `r = √(u² + v²)`,
`θ = Complex.arg ⟨u, v⟩` (`Complex.cos_arg`, `Complex.sin_arg`), `|r x|^q = r^q |x|^q`, `((r s)² + (r t)²)^(q/2) = r^q (s² + t²)^(q/2)`. -/
theorem bellmanF_nonneg_of_circle {q a B C l1 l2 : ℝ} (hq : 0 < q)
    (h0 : ∀ w : ℝ, 0 ≤ bellmanF q a B C (Gab q a B C l1 l2) 0 0 w)
    (hc : ∀ θ ν : ℝ, 0 ≤ fcirc q a B C l1 l2 θ ν) :
    ∀ u v w : ℝ, 0 ≤ bellmanF q a B C (Gab q a B C l1 l2) u v w := by
  intro u v w
  by_cases huv : u = 0 ∧ v = 0
  · obtain ⟨rfl, rfl⟩ := huv
    exact h0 w
  · obtain ⟨r, hr, θ, rfl, rfl⟩ := exists_polar_uv huv
    have hw : w = r * (-Real.cos θ + (w / r + Real.cos θ)) := by
      field_simp
      ring
    rw [hw, bellmanF_mul hr.le]
    exact mul_nonneg (rpow_nonneg hr.le q) (hc θ (w / r + Real.cos θ))

/-- F2 (the decomposition on the circle, for EVERY `λ`): `f(θ, ν) = F₀(u, -u + ν) + Σ_a(θ)/4 + Δ(u, v, ν)`, `u = cos θ`,
`v = sin θ`. Uses `(1+B)^(q-1) (1+B) = (1+B)^q` (`Matsaev.one_add_rpow_eq` in Scalar/B0), `|(1+B) x|^q = (1+B)^q |x|^q`,
`|-x|^q = |x|^q`, `k₁(cos θ, sin θ) = k₁(sin θ, -cos θ) = 1`. -/
theorem fcirc_eq (q a B C l1 l2 θ ν : ℝ) (hB : 0 < B) :
    fcirc q a B C l1 l2 θ ν =
      F0 q B (Real.cos θ) (-Real.cos θ + ν) + Angle.SigmaAng q a B C θ / 4 +
        DeltaUV q a B l1 l2 (Real.cos θ) (Real.sin θ) ν := by
  unfold fcirc bellmanF Gab DeltaUV Angle.SigmaAng Angle.Nang G0 Da k1 k2 F0
  have hc : (Real.cos θ ^ 2 + Real.sin θ ^ 2) ^ (q / 2) = 1 := by rw [cos_sq_add_sin_sq, one_rpow]
  have hA : (1 + B) ^ (q - 1) * (1 + B) = (1 + B) ^ q := by
    rw [← rpow_add_one (by linarith : (1 : ℝ) + B ≠ 0), sub_add_cancel]
  have hAu : |(1 + B) * Real.cos θ| ^ q = (1 + B) ^ q * |Real.cos θ| ^ q :=
    abs_mul_rpow_of_nonneg (by linarith) _
  rw [show Real.cos θ + a * Real.sin θ - B * (-Real.cos θ + ν) = (1 + B) * Real.cos θ + a * Real.sin θ - B * ν by ring,
    show (1 + B) * Real.sin θ + a * (-Real.cos θ + ν) = (1 + B) * Real.sin θ - a * Real.cos θ + a * ν by ring,
    show Real.cos θ - B * (-Real.cos θ + ν) = (1 + B) * Real.cos θ - B * ν by ring, hc]
  linear_combination hAu - |Real.cos θ| ^ q * hA

/-- The window at `s = 0` (Theorem 3.6, Step 6): `F(0, 0, w) = (B(1+B)^(q-1) - B^q - a^q/2 + λ₁ + λ₂) |w|^q`. -/
theorem bellmanF_zero_zero (q a B C l1 l2 w : ℝ) (hq : 0 < q) (ha : 0 ≤ a) (hB : 0 < B) :
    bellmanF q a B C (Gab q a B C l1 l2) 0 0 w = (B * (1 + B) ^ (q - 1) - B ^ q - a ^ q / 2 + l1 + l2) * |w| ^ q := by
  unfold bellmanF Gab G0 Da k1 k2
  have h0 : |(0 : ℝ)| ^ q = 0 := by rw [abs_zero, zero_rpow hq.ne']
  have hk : ((0 : ℝ) ^ 2 + w ^ 2) ^ (q / 2) = |w| ^ q := by
    rw [zero_pow two_ne_zero, zero_add, ← sq_abs, ← rpow_natCast, ← rpow_mul (abs_nonneg w)]
    congr 1
    push_cast
    ring
  have hk0 : ((0 : ℝ) ^ 2 + 0 ^ 2) ^ (q / 2) = 0 := by
    rw [zero_pow two_ne_zero, add_zero, zero_rpow (by positivity)]
  have haw : |(1 + B) * 0 + a * w| ^ q = a ^ q * |w| ^ q := by
    rw [mul_zero, zero_add, abs_mul_rpow_of_nonneg ha]
  have h00 : |(1 + B) * 0 + a * 0| ^ q = 0 := by
    rw [mul_zero, mul_zero, add_zero, h0]
  have hBw : |0 + a * 0 - B * w| ^ q = B ^ q * |w| ^ q := by
    rw [show (0 : ℝ) + a * 0 - B * w = -(B * w) by ring, abs_neg, abs_mul_rpow_of_nonneg hB.le]
  rw [hk, hk0, haw, h00, hBw, h0]
  ring

/-- `G_{a,λ}` is continuous (Lemma 3.1 needs it). -/
theorem continuous_Gab (q a B C l1 l2 : ℝ) (hq : 0 < q) : Continuous (Function.uncurry (Gab q a B C l1 l2)) := by
  have hpow : ∀ {f : ℝ × ℝ → ℝ}, Continuous f → Continuous fun x => |f x| ^ q := fun hf =>
    hf.abs.rpow_const fun _ => Or.inr hq.le
  have h1 : Continuous fun x : ℝ × ℝ => x.1 := continuous_fst
  have h2 : Continuous fun x : ℝ × ℝ => x.2 := continuous_snd
  have hk1 : Continuous fun x : ℝ × ℝ => (x.1 ^ 2 + x.2 ^ 2) ^ (q / 2) :=
    ((h1.pow 2).add (h2.pow 2)).rpow_const fun _ => Or.inr (by positivity)
  have hG0 : Continuous fun x : ℝ × ℝ => G0 q B x.1 x.2 :=
    continuous_const.mul ((hpow h1).add (hpow h2))
  have hDa : Continuous fun x : ℝ × ℝ => Da q a B C x.1 x.2 :=
    (continuous_const.mul (hpow h1)).sub (hpow ((continuous_const.mul h1).add (continuous_const.mul h2)))
  have hk2 : Continuous fun x : ℝ × ℝ => k2 q x.1 x.2 := (hpow h1).add (hpow h2)
  exact ((hG0.add (hDa.div_const 2)).add (continuous_const.mul hk1)).add (continuous_const.mul hk2)

/-- `G_{a,λ}(0, 0) = 0` (Lemma 3.1 needs it). -/
theorem Gab_zero (q a B C l1 l2 : ℝ) (hq : 0 < q) : Gab q a B C l1 l2 0 0 = 0 := by
  unfold Gab G0 Da k1 k2
  have h0 : |(0 : ℝ)| ^ q = 0 := by rw [abs_zero, zero_rpow hq.ne']
  have hk0 : ((0 : ℝ) ^ 2 + 0 ^ 2) ^ (q / 2) = 0 := by
    rw [zero_pow two_ne_zero, add_zero, zero_rpow (by positivity)]
  rw [mul_zero, mul_zero, add_zero, hk0, h0]
  ring

/-- `n` is odd (φ is odd): `n(-u, -v) = -n(u, v)`; with it, `n(e(θ + π)) = -n(e(θ))`. -/
theorem nUV_neg (q a B l1 l2 u v : ℝ) : nUV q a B l1 l2 (-u) (-v) = -nUV q a B l1 l2 u v := by
  unfold nUV R1
  rw [show (1 + B) * -u + a * -v = -((1 + B) * u + a * v) by ring, show (1 + B) * -u = -((1 + B) * u) by ring,
    show (1 + B) * -v - a * -u = -((1 + B) * v - a * u) by ring, phi_neg', phi_neg', phi_neg', phi_neg']
  ring

/-- F5 (Theorem 3.6, Step 4, the λ-system): with `λ = (lam1, lam2)` (Cramer), `n = 0` at `(u, v)` and at `(v, -u)`
(`(v, -u) = e(θ - π/2)` when `(u, v) = e(θ)`; note `R₁(v, -u) = R₂(u, v)` as φ is odd). -/
theorem nUV_lam (q a B u v : ℝ) (hdet : detL q u v ≠ 0) :
    nUV q a B (lam1 q a B u v) (lam2 q a B u v) u v = 0 ∧
      nUV q a B (lam1 q a B u v) (lam2 q a B u v) v (-u) = 0 := by
  have hR : R1 q a B v (-u) = R2 q a B u v := by
    unfold R1 R2
    rw [show (1 + B) * v + a * -u = (1 + B) * v - a * u by ring,
      show (1 + B) * -u - a * v = -((1 + B) * u + a * v) by ring, phi_neg']
    ring
  have k1 : lam1 q a B u v * u + lam2 q a B u v * phi q u = R1 q a B u v := by
    unfold lam1 lam2
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdet]
    unfold detL
    ring
  have k2 : lam1 q a B u v * v + lam2 q a B u v * phi q v = R2 q a B u v := by
    unfold lam1 lam2
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdet]
    unfold detL
    ring
  unfold nUV
  rw [hR]
  constructor <;> linarith

/-- `a = 0` (proof of Theorem 3.6, first paragraph): `C_0 = ‖(1 + B) I‖_p ≥ 1 + B` (test vector `(1, 0)`; `aeval_Jmat_Pa_proved`,
`norm_mulVec_le_matNorm`, `norm_toLp_fin2_rpow` in Bridge/Basic). -/
theorem one_add_le_Ca_zero (p : ENNReal) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B) : 1 + B ≤ Ca p 0 B := by
  unfold Ca
  rw [aeval_Jmat_Pa_proved]
  have hv := norm_mulVec_le_matNorm p ((1 + B) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (0 : ℝ) • Jmat) ![1, 0]
  have hmv : ((1 + B) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (0 : ℝ) • Jmat) *ᵥ ![1, 0] = (1 + B) • ![(1 : ℝ), 0] := by
    ext i
    fin_cases i <;> simp
  rw [hmv, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)] at hv
  have hpos : 0 < ‖WithLp.toLp p ![(1 : ℝ), 0]‖ := by
    have h := norm_toLp_fin2_rpow p hptop 1 0
    rw [abs_one, one_rpow, abs_zero, zero_rpow (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hptop).ne',
      add_zero] at h
    rcases (norm_nonneg (WithLp.toLp p ![(1 : ℝ), 0])).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_rpow (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hptop).ne'] at h
      exact absurd h zero_ne_one
  exact le_of_mul_le_mul_right hv hpos

end Matsaev.SJ
