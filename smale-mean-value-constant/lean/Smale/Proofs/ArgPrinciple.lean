/-
Smale/Proofs/ArgPrinciple.lean — the argument principle and Rouché's theorem for POLYNOMIALS on a circle
`|w - c| = R`, proved from Mathlib's circle integrals (no new assumption): for `f` with no zero on the circle,
`∮ f'/f = 2πi · #(zeros of f in |w - c| < R)`; and `|g| < |f|` on the circle gives the same number of zeros for
`f + g` and `f`. The unit-circle forms (used for Lemmas 4.1, 4.2) are the case `c = 0`, `R = 1`; the small circles are
used for the Hurwitz step of Lemma 5.3.
-/
import Smale.Defs.Basic

namespace Smale

open Polynomial Complex Metric

/-- `zerosInDisk f` counts the roots `w` of `f` with `‖w‖ < 1`. -/
theorem zerosInDisk_eq (f : ℂ[X]) : zerosInDisk f = (f.roots.filter fun w => ‖w‖ < 1).card := by
  unfold zerosInDisk zerosInBall
  congr 1
  exact Multiset.filter_congr fun w _ => by rw [sub_zero]

/-- One more root `r`: `zerosInBall ((X - C r) g) c R = zerosInBall g c R + [|r - c| < R]`. -/
theorem zerosInBall_X_sub_C_mul (r c : ℂ) (R : ℝ) {g : ℂ[X]} (hg : g ≠ 0) :
    zerosInBall ((X - C r) * g) c R = zerosInBall g c R + if ‖r - c‖ < R then 1 else 0 := by
  unfold zerosInBall
  rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hg), roots_X_sub_C, Multiset.singleton_add]
  by_cases h : ‖r - c‖ < R
  · rw [Multiset.filter_cons_of_pos (p := fun w : ℂ => ‖w - c‖ < R) _ h]
    simp [h]
  · rw [Multiset.filter_cons_of_neg (p := fun w : ℂ => ‖w - c‖ < R) _ h]
    simp [h]

/-- `∮_{|w-c|=R} (w - r)⁻¹ = 2πi` if `|r - c| < R`, and `0` if `|r - c| > R`. -/
theorem circleIntegral_inv_sub_ball (r c : ℂ) {R : ℝ} (hR : 0 < R) (hr : ‖r - c‖ ≠ R) :
    circleIntegral (fun w => (w - r)⁻¹) c R = if ‖r - c‖ < R then 2 * Real.pi * I else 0 := by
  split_ifs with h
  · exact circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_iff_norm.2 h)
  · have h1 : R < ‖r - c‖ := lt_of_le_of_ne (not_lt.1 h) (Ne.symm hr)
    have hne : ∀ w ∈ closedBall c R, w - r ≠ 0 := fun w hw =>
      sub_ne_zero.2 fun hwr => by
        rw [mem_closedBall_iff_norm, hwr] at hw
        linarith
    exact circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty
      ((continuousOn_id.sub continuousOn_const).inv₀ hne)
      fun w hw => (differentiableAt_id.sub (differentiableAt_const r)).inv (hne w (ball_subset_closedBall hw.1))

theorem circleIntegrable_inv_sub_ball {r c : ℂ} {R : ℝ} (hR : 0 < R) (hr : ‖r - c‖ ≠ R) :
    CircleIntegrable (fun w => (w - r)⁻¹) c R :=
  ContinuousOn.circleIntegrable hR.le ((continuousOn_id.sub continuousOn_const).inv₀ fun w hw =>
    sub_ne_zero.2 fun hwr => hr (by simp only [id] at hwr; rw [← hwr]; exact mem_sphere_iff_norm.1 hw))

theorem circleIntegrable_logDeriv_ball (f : ℂ[X]) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hc : ∀ w : ℂ, ‖w - c‖ = R → f.eval w ≠ 0) :
    CircleIntegrable (fun w => f.derivative.eval w / f.eval w) c R :=
  ContinuousOn.circleIntegrable hR.le (f.derivative.continuous.continuousOn.div f.continuous.continuousOn
    fun w hw => hc w (mem_sphere_iff_norm.1 hw))

/-- The argument principle for polynomials of degree `k`, by induction on `k` (one root at a time). -/
theorem circleIntegral_logDeriv_ball_aux (c : ℂ) {R : ℝ} (hR : 0 < R) (k : ℕ) : ∀ f : ℂ[X], f.natDegree = k → f ≠ 0 →
    (∀ w : ℂ, ‖w - c‖ = R → f.eval w ≠ 0) →
    circleIntegral (fun w => f.derivative.eval w / f.eval w) c R = 2 * Real.pi * I * zerosInBall f c R := by
  induction k with
  | zero =>
    intro f hk _ _
    rw [eq_C_of_natDegree_eq_zero hk]
    simp [circleIntegral, zerosInBall]
  | succ k ih =>
    intro f hk hf hc
    obtain ⟨r, hr⟩ := Complex.exists_root (natDegree_pos_iff_degree_pos.1 (by omega : 0 < f.natDegree))
    obtain ⟨g, hfg⟩ : ∃ g, f = (X - C r) * g := ⟨_, (mul_divByMonic_eq_iff_isRoot.2 hr).symm⟩
    have hg0 : g ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hfg
      exact hf hfg
    have hgk : g.natDegree = k := by
      have h := congrArg natDegree hfg
      rw [natDegree_mul (X_sub_C_ne_zero r) hg0, natDegree_X_sub_C] at h
      omega
    have hrc : ‖r - c‖ ≠ R := fun h => hc r h hr.eq_zero
    have hgc : ∀ w : ℂ, ‖w - c‖ = R → g.eval w ≠ 0 := fun w hw h0 =>
      hc w hw (by rw [hfg, eval_mul, h0, mul_zero])
    have hsplit : Set.EqOn (fun w => f.derivative.eval w / f.eval w)
        (fun w => (w - r)⁻¹ + g.derivative.eval w / g.eval w) (sphere c R) := by
      intro w hw
      have hw1 : ‖w - c‖ = R := mem_sphere_iff_norm.1 hw
      have hwr : w - r ≠ 0 := sub_ne_zero.2 fun h => hrc (by rw [← h]; exact hw1)
      have hgw := hgc w hw1
      simp only [hfg, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add,
        eval_mul, eval_sub, eval_X, eval_C]
      field_simp
    have hz : zerosInBall f c R = zerosInBall g c R + if ‖r - c‖ < R then 1 else 0 := by
      rw [hfg]
      exact zerosInBall_X_sub_C_mul r c R hg0
    rw [circleIntegral.integral_congr hR.le hsplit,
      circleIntegral.integral_add (circleIntegrable_inv_sub_ball hR hrc) (circleIntegrable_logDeriv_ball g c hR hgc),
      circleIntegral_inv_sub_ball r c hR hrc, ih g hgk hg0 hgc, hz]
    split_ifs <;> push_cast <;> ring

/-- A polynomial with no zero on a circle of positive radius is not `0`. -/
theorem ne_zero_of_sphere {p : ℂ[X]} (c : ℂ) {R : ℝ} (hR : 0 < R) (hp : ∀ w : ℂ, ‖w - c‖ = R → p.eval w ≠ 0) :
    p ≠ 0 := fun h0 =>
  hp (c + R) (by simp [abs_of_pos hR]) (by rw [h0, eval_zero])

/-- **Argument principle for polynomials**: if `f` has no zero on `|w - c| = R`, then
`∮_{|w-c|=R} f'/f = 2πi · zerosInBall f c R`. -/
theorem circleIntegral_logDeriv_ball (f : ℂ[X]) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hc : ∀ w : ℂ, ‖w - c‖ = R → f.eval w ≠ 0) :
    circleIntegral (fun w => f.derivative.eval w / f.eval w) c R = 2 * Real.pi * I * zerosInBall f c R :=
  circleIntegral_logDeriv_ball_aux c hR _ f rfl (ne_zero_of_sphere c hR hc) hc

/-- **Rouché's theorem for polynomials**: if `|g| < |f|` on `|w - c| = R`, then `f + g` and `f` have the same number
of zeros in `|w - c| < R`. The two integrals differ by the integral of the derivative of `log((f + g)/f)`, and
`(f + g)/f = 1 + g/f` stays in the right half plane on the circle. -/
theorem zerosInBall_add_of_norm_lt (f g : ℂ[X]) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hlt : ∀ w : ℂ, ‖w - c‖ = R → ‖g.eval w‖ < ‖f.eval w‖) :
    zerosInBall (f + g) c R = zerosInBall f c R := by
  have hf : ∀ w : ℂ, ‖w - c‖ = R → f.eval w ≠ 0 := fun w hw h0 => by
    have h := hlt w hw
    rw [h0, norm_zero] at h
    exact (norm_nonneg _).not_gt h
  have hfg : ∀ w : ℂ, ‖w - c‖ = R → (f + g).eval w ≠ 0 := fun w hw h0 => by
    have h := hlt w hw
    rw [eval_add, add_eq_zero_iff_eq_neg] at h0
    rw [h0, norm_neg] at h
    exact lt_irrefl _ h
  have hderiv : ∀ w ∈ sphere c |R|, HasDerivWithinAt (fun w => Complex.log ((f + g).eval w / f.eval w))
      ((fun w => (f + g).derivative.eval w / (f + g).eval w - f.derivative.eval w / f.eval w) w)
      (sphere c |R|) w := by
    intro w hw
    rw [abs_of_pos hR] at hw
    have hw1 : ‖w - c‖ = R := mem_sphere_iff_norm.1 hw
    have hfw := hf w hw1
    have hfgw := hfg w hw1
    have hq := ((f + g).hasDerivAt w).div (f.hasDerivAt w) hfw
    have hslit : (f + g).eval w / f.eval w ∈ slitPlane := by
      rw [eval_add, add_div, div_self hfw]
      apply mem_slitPlane_of_norm_lt_one
      rw [norm_div, div_lt_one (norm_pos_iff.2 hfw)]
      exact hlt w hw1
    refine (hq.clog hslit).hasDerivWithinAt.congr_deriv ?_
    simp only [Pi.div_apply]
    field_simp
  have hzero := circleIntegral.integral_eq_zero_of_hasDerivWithinAt' hderiv
  have hsub : circleIntegral
      (fun w => (f + g).derivative.eval w / (f + g).eval w - f.derivative.eval w / f.eval w) c R =
      circleIntegral (fun w => (f + g).derivative.eval w / (f + g).eval w) c R -
        circleIntegral (fun w => f.derivative.eval w / f.eval w) c R :=
    circleIntegral.integral_sub (circleIntegrable_logDeriv_ball _ c hR hfg) (circleIntegrable_logDeriv_ball _ c hR hf)
  rw [hsub, circleIntegral_logDeriv_ball _ c hR hfg, circleIntegral_logDeriv_ball _ c hR hf, sub_eq_zero] at hzero
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  exact_mod_cast mul_left_cancel₀ h2pi hzero

/-! ### The unit circle (`c = 0`, `R = 1`): the names and types of version 0.11 -/

/-- One more root `r`: `zerosInDisk ((X - C r) g) = zerosInDisk g + [|r| < 1]`. -/
theorem zerosInDisk_X_sub_C_mul (r : ℂ) {g : ℂ[X]} (hg : g ≠ 0) :
    zerosInDisk ((X - C r) * g) = zerosInDisk g + if ‖r‖ < 1 then 1 else 0 := by
  simpa only [zerosInDisk, sub_zero] using zerosInBall_X_sub_C_mul r 0 1 hg

/-- `∮_{|w|=1} (w - r)⁻¹ = 2πi` if `|r| < 1`, and `0` if `|r| > 1`. -/
theorem circleIntegral_inv_sub (r : ℂ) (hr : ‖r‖ ≠ 1) :
    circleIntegral (fun w => (w - r)⁻¹) 0 1 = if ‖r‖ < 1 then 2 * Real.pi * I else 0 := by
  simpa only [sub_zero] using circleIntegral_inv_sub_ball r 0 one_pos (by rwa [sub_zero])

theorem circleIntegrable_inv_sub {r : ℂ} (hr : ‖r‖ ≠ 1) : CircleIntegrable (fun w => (w - r)⁻¹) 0 1 :=
  circleIntegrable_inv_sub_ball one_pos (by rwa [sub_zero])

theorem circleIntegrable_logDeriv (f : ℂ[X]) (hc : ∀ w : ℂ, ‖w‖ = 1 → f.eval w ≠ 0) :
    CircleIntegrable (fun w => f.derivative.eval w / f.eval w) 0 1 :=
  circleIntegrable_logDeriv_ball f 0 one_pos fun w hw => hc w (by rwa [sub_zero] at hw)

/-- The argument principle for polynomials of degree `k` on the unit circle. -/
theorem circleIntegral_logDeriv_aux (k : ℕ) : ∀ f : ℂ[X], f.natDegree = k → f ≠ 0 →
    (∀ w : ℂ, ‖w‖ = 1 → f.eval w ≠ 0) →
    circleIntegral (fun w => f.derivative.eval w / f.eval w) 0 1 = 2 * Real.pi * I * zerosInDisk f :=
  fun f hk hf hc => circleIntegral_logDeriv_ball_aux 0 one_pos k f hk hf fun w hw => hc w (by rwa [sub_zero] at hw)

/-- A polynomial with no zero on the unit circle is not `0`. -/
theorem ne_zero_of_circle {p : ℂ[X]} (hp : ∀ w : ℂ, ‖w‖ = 1 → p.eval w ≠ 0) : p ≠ 0 :=
  ne_zero_of_sphere 0 one_pos fun w hw => hp w (by rwa [sub_zero] at hw)

/-- **Argument principle for polynomials** on the unit circle: `∮_{|w|=1} f'/f = 2πi · zerosInDisk f`. -/
theorem circleIntegral_logDeriv (f : ℂ[X]) (hc : ∀ w : ℂ, ‖w‖ = 1 → f.eval w ≠ 0) :
    circleIntegral (fun w => f.derivative.eval w / f.eval w) 0 1 = 2 * Real.pi * I * zerosInDisk f :=
  circleIntegral_logDeriv_ball f 0 one_pos fun w hw => hc w (by rwa [sub_zero] at hw)

/-- **Rouché's theorem for polynomials** on the unit circle. -/
theorem zerosInDisk_add_of_norm_lt (f g : ℂ[X]) (hlt : ∀ w : ℂ, ‖w‖ = 1 → ‖g.eval w‖ < ‖f.eval w‖) :
    zerosInDisk (f + g) = zerosInDisk f :=
  zerosInBall_add_of_norm_lt f g 0 one_pos fun w hw => hlt w (by rwa [sub_zero] at hw)

end Smale
