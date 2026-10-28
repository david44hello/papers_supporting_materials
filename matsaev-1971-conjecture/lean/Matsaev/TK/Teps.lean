-- Matsaev/TK/Teps.lean — Lemma 4.1 (`lem:TK`): `T_ε = exp(ε K_*) J` and `‖T_ε‖_p ≤ 1` given `Q ≤ D_*`.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.Defs.Spaces

/-!
Part 1 (`teps_eq_exp_proved`): the ℝ-algebra map `ℂ → M₂(ℝ)`, `I ↦ J` (`J² = -1`), is continuous, so it commutes with
`exp`; `ε K_*` is the image of `z = -(εD_*/2) + (ε/2) i`, and `exp z = e^(-εD_*/2) (cos(ε/2) + i sin(ε/2))`.

Part 2 (`teps_contraction_of`): for `w = (a, b)`, `g(ε) = e^(-εD_* r/2) (|A|^r + |B|^r)` with `(A, B) = R_(ε/2) w` has
`g' = e^(..) (r/2) (⟨φ(A,B), J(A,B)⟩ - D_* ‖(A,B)‖_r^r) ≤ 0` (proof of Lemma 4.1), so `g(ε) ≤ g(0)`; and `T_ε = e^(-εD_*/2) R_(ε/2) J`.
-/

namespace Matsaev

open scoped ENNReal Matrix

/-! ### Part 1: the closed form equals the matrix exponential -/

private theorem jmat_mul_jmat : (Jmat : Matrix (Fin 2) (Fin 2) ℝ) * Jmat = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jmat, Matrix.mul_apply, Fin.sum_univ_two]

private noncomputable def cplxHom : ℂ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ := Complex.liftAux Jmat jmat_mul_jmat

private theorem cplxHom_apply (z : ℂ) : cplxHom z = z.re • (1 : Matrix (Fin 2) (Fin 2) ℝ) + z.im • Jmat := by
  rw [cplxHom, Complex.liftAux_apply, Algebra.algebraMap_eq_smul_one]

private theorem continuous_cplxHom : Continuous cplxHom :=
  cplxHom.toLinearMap.continuous_of_finiteDimensional

open scoped Matrix.Norms.Operator in
private theorem exp_cplxHom (z : ℂ) : NormedSpace.exp (cplxHom z) = cplxHom (Complex.exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact (NormedSpace.map_exp cplxHom continuous_cplxHom z).symm

theorem teps_eq_exp_proved (p ε : ℝ) : Teps p ε = NormedSpace.exp (ε • Kstar p) * Jmat := by
  have hz : ε • Kstar p = cplxHom ⟨-(ε * Dstar p / 2), ε / 2⟩ := by
    rw [cplxHom_apply, Kstar]
    module
  rw [hz, exp_cplxHom, cplxHom_apply, Complex.exp_re, Complex.exp_im, Teps, Rot]
  congr 1
  module

/-! ### Part 2: `T_ε` is a contraction of `ℓ^p_2` -/

/-- `φ(t) = |t|^(r-2) t`, the form in which Mathlib states the derivative of `|t|^r`. -/
private theorem phi_eq (r t : ℝ) : phi r t = |t| ^ (r - 2) * t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [phi]
  · have hab : |t| ≠ 0 := abs_ne_zero.mpr ht
    have h1 : |t| ^ (r - 1) = |t| ^ (r - 2) * |t| := by
      rw [show r - 1 = (r - 2) + 1 by ring, Real.rpow_add_one hab]
    rw [phi, h1]
    linear_combination |t| ^ (r - 2) * sign_mul_abs t

/-- `Q ≤ D_*`, cleared of the denominator; also true at the origin. -/
private theorem cross_le (r : ℝ) (hr : 0 < r)
    (hQ : ∀ u v : ℝ, (u, v) ≠ (0, 0) → Qf r u v ≤ Dstar r) (a b : ℝ) :
    |a| ^ (r - 2) * a * b - |b| ^ (r - 2) * b * a ≤ Dstar r * (|a| ^ r + |b| ^ r) := by
  by_cases hab : (a, b) = (0, 0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
    simp [Real.zero_rpow hr.ne']
  · have hN : 0 < |a| ^ r + |b| ^ r := by
      rcases eq_or_ne a 0 with rfl | ha
      · have hb : b ≠ 0 := fun hb => hab (by rw [hb])
        simp only [abs_zero, Real.zero_rpow hr.ne', zero_add]
        exact Real.rpow_pos_of_pos (abs_pos.mpr hb) r
      · exact add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos (abs_pos.mpr ha) r)
          (Real.rpow_nonneg (abs_nonneg b) r)
    have h := hQ a b hab
    rw [Qf, div_le_iff₀ hN, phi_eq, phi_eq] at h
    linarith

/-- First coordinate of `R_(ε/2) (a, b)`. -/
private noncomputable def rotA (a b ε : ℝ) : ℝ := a * Real.cos (ε / 2) + b * Real.sin (ε / 2)

/-- Second coordinate of `R_(ε/2) (a, b)`. -/
private noncomputable def rotB (a b ε : ℝ) : ℝ := b * Real.cos (ε / 2) - a * Real.sin (ε / 2)

private theorem hasDerivAt_rotA (a b ε : ℝ) : HasDerivAt (rotA a b) (rotB a b ε / 2) ε := by
  have hθ : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) ε := (hasDerivAt_id' ε).div_const 2
  have h := (hθ.cos.const_mul a).add (hθ.sin.const_mul b)
  unfold rotA rotB
  convert h using 1
  ring

private theorem hasDerivAt_rotB (a b ε : ℝ) : HasDerivAt (rotB a b) (-(rotA a b ε / 2)) ε := by
  have hθ : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) ε := (hasDerivAt_id' ε).div_const 2
  have h := (hθ.cos.const_mul b).sub (hθ.sin.const_mul a)
  unfold rotA rotB
  convert h using 1
  ring

/-- `g(ε) = ‖exp(ε K_*) (a, b)‖_r^r = e^(-ε D r / 2) (|A(ε)|^r + |B(ε)|^r)`. -/
private noncomputable def gfun (r D a b ε : ℝ) : ℝ :=
  Real.exp (-(ε * D / 2) * r) * (|rotA a b ε| ^ r + |rotB a b ε| ^ r)

private theorem hasDerivAt_gfun (r D a b ε : ℝ) (hr : 1 < r) :
    HasDerivAt (gfun r D a b)
      (Real.exp (-(ε * D / 2) * r) * (r / 2) *
        ((|rotA a b ε| ^ (r - 2) * rotA a b ε * rotB a b ε
          - |rotB a b ε| ^ (r - 2) * rotB a b ε * rotA a b ε)
          - D * (|rotA a b ε| ^ r + |rotB a b ε| ^ r))) ε := by
  have he : HasDerivAt (fun ε => Real.exp (-(ε * D / 2) * r))
      (Real.exp (-(ε * D / 2) * r) * (-(D / 2) * r)) ε := by
    have hl : HasDerivAt (fun ε : ℝ => -(ε * D / 2) * r) (-(D / 2) * r) ε := by
      convert (((hasDerivAt_id' ε).mul_const D).div_const 2).neg.mul_const r using 1
      ring
    exact hl.exp
  have hA := (hasDerivAt_abs_rpow (rotA a b ε) hr).comp ε (hasDerivAt_rotA a b ε)
  have hB := (hasDerivAt_abs_rpow (rotB a b ε) hr).comp ε (hasDerivAt_rotB a b ε)
  convert he.mul (hA.add hB) using 1
  · rfl
  · simp only [Pi.add_apply, Function.comp_apply]
    ring

private theorem gfun_le (r : ℝ) (hr : 1 < r)
    (hQ : ∀ u v : ℝ, (u, v) ≠ (0, 0) → Qf r u v ≤ Dstar r) (a b ε : ℝ) (hε : 0 ≤ ε) :
    gfun r (Dstar r) a b ε ≤ |a| ^ r + |b| ^ r := by
  have hanti : Antitone (gfun r (Dstar r) a b) := by
    refine antitone_of_hasDerivAt_nonpos (fun x => hasDerivAt_gfun r (Dstar r) a b x hr) ?_
    intro x
    have hc := cross_le r (by linarith) hQ (rotA a b x) (rotB a b x)
    have hpos : 0 ≤ Real.exp (-(x * Dstar r / 2) * r) * (r / 2) :=
      mul_nonneg (Real.exp_pos _).le (by linarith)
    exact mul_nonpos_of_nonneg_of_nonpos hpos (by linarith)
  have h0 : gfun r (Dstar r) a b 0 = |a| ^ r + |b| ^ r := by
    simp [gfun, rotA, rotB]
  exact h0 ▸ hanti hε

/-- `T_ε w = e^(-ε D/2) (A(ε), B(ε))` with `(a, b) = J w = (w₁, -w₀)`. -/
private theorem teps_mulVec (p ε : ℝ) (w : Fin 2 → ℝ) :
    Teps p ε *ᵥ w = Real.exp (-(ε * Dstar p / 2)) •
      ![rotA (w 1) (-w 0) ε, rotB (w 1) (-w 0) ε] := by
  ext i
  fin_cases i <;>
    simp [Teps, Rot, Jmat, rotA, rotB, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.mul_apply] <;> ring

private theorem sum_teps_le (r : ℝ) (hr : 1 < r)
    (hQ : ∀ u v : ℝ, (u, v) ≠ (0, 0) → Qf r u v ≤ Dstar r) (ε : ℝ) (hε : 0 ≤ ε) (w : Fin 2 → ℝ) :
    ∑ i, |(Teps r ε *ᵥ w) i| ^ r ≤ ∑ i, |w i| ^ r := by
  have hg := gfun_le r hr hQ (w 1) (-w 0) ε hε
  have hE := (Real.exp_pos (-(ε * Dstar r / 2))).le
  rw [gfun, Real.exp_mul] at hg
  rw [teps_mulVec, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    abs_mul, abs_of_nonneg hE, Real.mul_rpow hE (abs_nonneg _), abs_neg] at hg ⊢
  linarith

theorem teps_contraction_of (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤)
    (hQ : ∀ u v : ℝ, (u, v) ≠ (0, 0) → Qf p.toReal u v ≤ Dstar p.toReal) (ε : ℝ) (hε : 0 ≤ ε) :
    matNorm p (Teps p.toReal ε) ≤ 1 := by
  have hr : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono hptop hp
  have hr0 : 0 < p.toReal := by linarith
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, matOp, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
    PiLp.norm_eq_sum hr0, PiLp.norm_eq_sum hr0]
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) ?_
    (by positivity)
  simpa [Real.norm_eq_abs] using sum_teps_le p.toReal hr hQ ε hε (WithLp.ofLp x)

end Matsaev
