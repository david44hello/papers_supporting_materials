-- Matsaev/SJ/Sigma.lean — Steps D/E (Σ-interface) of Theorem 3.6: for small a, Σ_a vanishes at an angle θa within a of θs and grows quadratically away from θa + (π/2)ℤ.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.Defs.Spaces
import Matsaev.Angle.Defs
import Matsaev.Bridge.Basic
import Matsaev.Scalar.N1

namespace Matsaev.SJ

open Real Set Matsaev Matsaev.Angle
open scoped ENNReal Matrix

/-! ## Facts on the unit circle: `N`, `q` and `log N` -/

section Circle

variable {q : ℝ}

lemma abs_rpow_eq_sq_rpow (q x : ℝ) : |x| ^ q = (x ^ 2) ^ (q / 2) := by
  rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg x)]
  congr 1; ring

lemma Nang_eq (q θ : ℝ) : Nang q θ = (cos θ ^ 2) ^ (q / 2) + (sin θ ^ 2) ^ (q / 2) := by
  simp only [Nang, abs_rpow_eq_sq_rpow]

/-- `N ≥ 2^(-q/2)`: one of `cos² θ, sin² θ` is `≥ 1/2`. -/
lemma Nang_ge (hq : 0 ≤ q) (θ : ℝ) : (1 / 2 : ℝ) ^ (q / 2) ≤ Nang q θ := by
  rw [Nang_eq]
  have h1 := sin_sq_add_cos_sq θ
  have hc := Real.rpow_nonneg (sq_nonneg (cos θ)) (q / 2)
  have hs := Real.rpow_nonneg (sq_nonneg (sin θ)) (q / 2)
  rcases le_total (1 / 2 : ℝ) (cos θ ^ 2) with h | h
  · have := Real.rpow_le_rpow (by norm_num) h (by linarith : 0 ≤ q / 2)
    linarith
  · have := Real.rpow_le_rpow (by norm_num) (by linarith : (1 / 2 : ℝ) ≤ sin θ ^ 2) (by linarith : 0 ≤ q / 2)
    linarith

lemma Nang_pos (hq : 0 ≤ q) (θ : ℝ) : 0 < Nang q θ :=
  lt_of_lt_of_le (by positivity) (Nang_ge hq θ)

lemma Nang_periodic (q : ℝ) : Function.Periodic (Nang q) (π / 2) := by
  intro θ
  simp only [Nang, cos_add_pi_div_two, sin_add_pi_div_two, abs_neg]
  ring

lemma qang_periodic (q : ℝ) : Function.Periodic (qang q) (π / 2) := by
  intro θ
  simp only [qang, cos_add_pi_div_two, sin_add_pi_div_two]
  have h := Qf_neg q (sin θ) (-cos θ)
  rw [neg_neg] at h
  rw [h, Qf_J]

lemma phi_eq (q y : ℝ) : phi q y = y * |y| ^ (q - 2) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [phi]
  · have hy' : 0 < |y| := abs_pos.mpr hy
    rw [phi, show q - 1 = (q - 2) + 1 by ring, Real.rpow_add hy', Real.rpow_one]
    calc (SignType.sign y : ℝ) * (|y| ^ (q - 2) * |y|) = ((SignType.sign y : ℝ) * |y|) * |y| ^ (q - 2) := by ring
      _ = y * |y| ^ (q - 2) := by rw [sign_mul_abs]

lemma qang_mul_Nang (hq : 0 ≤ q) (θ : ℝ) :
    qang q θ * Nang q θ = cos θ * sin θ * ((cos θ ^ 2) ^ (q / 2 - 1) - (sin θ ^ 2) ^ (q / 2 - 1)) := by
  have hN : Nang q θ ≠ 0 := (Nang_pos hq θ).ne'
  have hsub : ∀ y : ℝ, |y| ^ (q - 2) = (y ^ 2) ^ (q / 2 - 1) := fun y => by
    rw [abs_rpow_eq_sq_rpow]; congr 1; ring
  rw [qang, Qf, show |cos θ| ^ q + |sin θ| ^ q = Nang q θ from rfl, div_mul_cancel₀ _ hN, phi_eq, phi_eq,
    hsub, hsub]
  ring

/-- `N' = -q · q(θ) · N` (needs `q ≥ 2` for the derivative of `(cos²)^(q/2)` at the zeros of `cos`). -/
lemma hasDerivAt_Nang (hq : 2 ≤ q) (θ : ℝ) : HasDerivAt (Nang q) (-q * (qang q θ * Nang q θ)) θ := by
  have e1 : HasDerivAt (fun x => (cos x ^ 2) ^ (q / 2))
      ((2 * cos θ * -sin θ) * (q / 2) * (cos θ ^ 2) ^ (q / 2 - 1)) θ := by
    have := ((hasDerivAt_cos θ).pow 2).rpow_const (p := q / 2) (Or.inr (by linarith))
    simp only [Pi.pow_apply] at this
    convert this using 1; push_cast; ring
  have e2 : HasDerivAt (fun x => (sin x ^ 2) ^ (q / 2))
      ((2 * sin θ * cos θ) * (q / 2) * (sin θ ^ 2) ^ (q / 2 - 1)) θ := by
    have := ((hasDerivAt_sin θ).pow 2).rpow_const (p := q / 2) (Or.inr (by linarith))
    simp only [Pi.pow_apply] at this
    convert this using 1; push_cast; ring
  have hfun : Nang q = fun x => (cos x ^ 2) ^ (q / 2) + (sin x ^ 2) ^ (q / 2) := funext (Nang_eq q)
  have h : HasDerivAt (fun x => (cos x ^ 2) ^ (q / 2) + (sin x ^ 2) ^ (q / 2)) _ θ := e1.add e2
  rw [← hfun] at h
  convert h using 1
  rw [qang_mul_Nang (by linarith)]
  ring

lemma hasDerivAt_logNang (hq : 2 ≤ q) (θ : ℝ) :
    HasDerivAt (fun x => Real.log (Nang q x)) (-q * qang q θ) θ := by
  have hN : Nang q θ ≠ 0 := (Nang_pos (by linarith) θ).ne'
  convert (hasDerivAt_Nang hq θ).log hN using 1
  field_simp

/-- The window function `W_β(θ) = log N(θ - β) - log N(θ)` (plan R2; equal to `Wmov q β θ`, not needed here). -/
noncomputable def Wl (q β θ : ℝ) : ℝ := Real.log (Nang q (θ - β)) - Real.log (Nang q θ)

lemma hasDerivAt_Wl (hq : 2 ≤ q) (β θ : ℝ) :
    HasDerivAt (Wl q β) (q * (qang q θ - qang q (θ - β))) θ := by
  have h1 := (hasDerivAt_logNang hq (θ - β)).comp_sub_const θ β
  have h2 := hasDerivAt_logNang hq θ
  have h : HasDerivAt (fun x => Real.log (Nang q (x - β)) - Real.log (Nang q x))
      (-q * qang q (θ - β) - -q * qang q θ) θ := h1.sub h2
  show HasDerivAt (fun x => Real.log (Nang q (x - β)) - Real.log (Nang q x)) _ θ
  convert h using 1
  ring

lemma Wl_periodic (q β θ : ℝ) (k : ℤ) : Wl q β (θ - k * (π / 2)) = Wl q β θ := by
  have hper := (Nang_periodic q).int_mul k
  unfold Wl
  rw [show θ - k * (π / 2) - β = (θ - β) - k * (π / 2) by ring, hper.sub_eq, hper.sub_eq]

/-- Mean value form: `W_β(θ) = q β q(ξ)` for some `ξ ∈ [θ - β, θ]`. -/
lemma Wl_mvt (hq : 2 ≤ q) {β : ℝ} (hβ : 0 < β) (θ : ℝ) :
    ∃ ξ ∈ Icc (θ - β) θ, Wl q β θ = q * β * qang q ξ := by
  have hd : ∀ x, HasDerivAt (fun x => Real.log (Nang q x)) (-q * qang q x) x := hasDerivAt_logNang hq
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope (fun x => Real.log (Nang q x)) (fun x => -q * qang q x)
    (by linarith : θ - β < θ) (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
  refine ⟨ξ, Ioo_subset_Icc_self hξ, ?_⟩
  rw [sub_sub_cancel, eq_div_iff hβ.ne'] at h
  unfold Wl
  linear_combination h

end Circle

/-! ## The angular distance to a coset `θ' + (π/2)ℤ` -/

lemma angDist_nonneg (θ θ' : ℝ) : 0 ≤ angDist θ θ' := by
  unfold angDist
  have h1 := Int.fract_nonneg ((θ - θ') / (π / 2))
  have h2 := Int.fract_lt_one ((θ - θ') / (π / 2))
  have := pi_pos
  exact mul_nonneg (by positivity) (le_min h1 (by linarith))

/-- Some translate `θ - k π/2` of `θ` is at distance exactly `angDist θ θ' ≤ π/4` from `θ'`. -/
lemma exists_angDist (θ θ' : ℝ) :
    ∃ k : ℤ, |θ - k * (π / 2) - θ'| = angDist θ θ' ∧ angDist θ θ' ≤ π / 4 := by
  unfold angDist
  set x := (θ - θ') / (π / 2) with hx
  have hpi : 0 < π / 2 := by positivity
  have hθ : θ - θ' = π / 2 * x := by rw [hx]; field_simp
  have hfl := Int.floor_add_fract x
  have h1 := Int.fract_nonneg x
  have h2 := Int.fract_lt_one x
  rcases le_total (Int.fract x) (1 - Int.fract x) with h | h
  · refine ⟨⌊x⌋, ?_, ?_⟩
    · rw [min_eq_left h]
      have e : θ - ⌊x⌋ * (π / 2) - θ' = π / 2 * Int.fract x := by linear_combination hθ - (π / 2) * hfl
      rw [e, abs_of_nonneg (by positivity)]
    · rw [min_eq_left h]; nlinarith
  · refine ⟨⌊x⌋ + 1, ?_, ?_⟩
    · rw [min_eq_right h]
      have e : θ - ((⌊x⌋ + 1 : ℤ) : ℝ) * (π / 2) - θ' = -(π / 2 * (1 - Int.fract x)) := by
        push_cast; linear_combination hθ - (π / 2) * hfl
      rw [e, abs_neg, abs_of_nonneg (by nlinarith)]
    · rw [min_eq_right h]; nlinarith

/-! ## The moving window: abstract analysis (plan Step D) -/

section Window

variable {g W : ℝ → ℝ} {q D θs m ρ₁ β : ℝ}

/-- `g'` decreases at rate `≥ m` where `g'' ≤ -m`. -/
lemma deriv_sub_le
    (hconc : ∀ θ ∈ Icc (θs - ρ₁) (θs + ρ₁), DifferentiableAt ℝ (deriv g) θ ∧ deriv (deriv g) θ ≤ -m)
    {x y : ℝ} (hx : x ∈ Icc (θs - ρ₁) (θs + ρ₁)) (hy : y ∈ Icc (θs - ρ₁) (θs + ρ₁)) (hxy : x ≤ y) :
    deriv g y - deriv g x ≤ -m * (y - x) :=
  (convex_Icc _ _).image_sub_le_mul_sub_of_deriv_le
    (fun t ht => (hconc t ht).1.continuousAt.continuousWithinAt)
    (fun t ht => (hconc t (interior_subset ht)).1.differentiableWithinAt)
    (fun t ht => (hconc t (interior_subset ht)).2) x hx y hy hxy

/-- `h(t) = g(t) - g(t - β)` decreases at rate `≥ m β` on `[θs - ρ₁ + β, θs + ρ₁]`. -/
lemma window_sub_le (hg : Differentiable ℝ g) (hβ : 0 ≤ β)
    (hconc : ∀ θ ∈ Icc (θs - ρ₁) (θs + ρ₁), DifferentiableAt ℝ (deriv g) θ ∧ deriv (deriv g) θ ≤ -m)
    {s t : ℝ} (hs : s ∈ Icc (θs - ρ₁ + β) (θs + ρ₁)) (ht : t ∈ Icc (θs - ρ₁ + β) (θs + ρ₁)) (hst : s ≤ t) :
    (g t - g (t - β)) - (g s - g (s - β)) ≤ -m * β * (t - s) := by
  have hd : ∀ u, HasDerivAt (fun u => g u - g (u - β)) (deriv g u - deriv g (u - β)) u := fun u =>
    (hg u).hasDerivAt.sub ((hg (u - β)).hasDerivAt.comp_sub_const u β)
  refine (convex_Icc _ _).image_sub_le_mul_sub_of_deriv_le (f := fun u => g u - g (u - β))
    (fun u _ => (hd u).continuousAt.continuousWithinAt)
    (fun u _ => (hd u).differentiableAt.differentiableWithinAt) (fun u hu => ?_) s hs t ht hst
  have hu' := interior_subset hu
  rw [(hd u).deriv]
  have := deriv_sub_le hconc (x := u - β) (y := u) ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
    ⟨by linarith [hu'.1], hu'.2⟩ (by linarith)
  linarith

/-- Local quadratic decay of `W` (plan (W3)/(W4)): if `W' = q (g(t) - g(t - β))` and the window derivative vanishes
at `θβ`, then `W(θ) + q m β/2 · (θ - θβ)² ≤ W(θβ)` on `[θs - ρ₁ + β, θs + ρ₁]`. -/
lemma local_quad (hq : 0 ≤ q) (hβ : 0 ≤ β) (hg : Differentiable ℝ g)
    (hconc : ∀ θ ∈ Icc (θs - ρ₁) (θs + ρ₁), DifferentiableAt ℝ (deriv g) θ ∧ deriv (deriv g) θ ≤ -m)
    (hW : ∀ t, HasDerivAt W (q * (g t - g (t - β))) t)
    {θβ : ℝ} (hθβ : θβ ∈ Icc (θs - ρ₁ + β) (θs + ρ₁)) (h0 : g θβ - g (θβ - β) = 0)
    {θ : ℝ} (hθ : θ ∈ Icc (θs - ρ₁ + β) (θs + ρ₁)) :
    W θ + q * m * β / 2 * (θ - θβ) ^ 2 ≤ W θβ := by
  set φ : ℝ → ℝ := fun t => W t + q * m * β / 2 * (t - θβ) ^ 2 with hφdef
  have hφ : ∀ t, HasDerivAt φ (q * (g t - g (t - β)) + q * m * β * (t - θβ)) t := fun t => by
    have h2 := (((hasDerivAt_id t).sub_const θβ).pow 2).const_mul (q * m * β / 2)
    have h3 : HasDerivAt (fun t => W t + q * m * β / 2 * (t - θβ) ^ 2) _ t := (hW t).add h2
    convert h3 using 1
    simp; ring
  have hcont : ∀ s : Set ℝ, ContinuousOn φ s := fun s u _ => (hφ u).continuousAt.continuousWithinAt
  have hdiff : ∀ s : Set ℝ, DifferentiableOn ℝ φ s := fun s u _ => (hφ u).differentiableAt.differentiableWithinAt
  have hφθβ : φ θβ = W θβ := by simp [hφdef]
  suffices φ θ ≤ φ θβ by rw [hφθβ] at this; exact this
  rcases le_total θβ θ with h | h
  · have := (convex_Icc θβ (θs + ρ₁)).image_sub_le_mul_sub_of_deriv_le (hcont _) (hdiff _) (C := 0)
      (fun t ht => ?_) θβ ⟨le_rfl, hθβ.2⟩ θ ⟨h, hθ.2⟩ h
    · linarith
    · have ht' := interior_subset ht
      rw [(hφ t).deriv]
      have hw := window_sub_le hg hβ hconc hθβ ⟨by linarith [hθβ.1, ht'.1], ht'.2⟩ ht'.1
      rw [h0, sub_zero] at hw
      have := mul_le_mul_of_nonneg_left hw hq
      nlinarith
  · have := (convex_Icc (θs - ρ₁ + β) θβ).mul_sub_le_image_sub_of_le_deriv (hcont _) (hdiff _) (C := 0)
      (fun t ht => ?_) θ ⟨hθ.1, h⟩ θβ ⟨hθβ.1, le_rfl⟩ h
    · linarith
    · have ht' := interior_subset ht
      rw [(hφ t).deriv]
      have hw := window_sub_le hg hβ hconc ⟨ht'.1, by linarith [hθβ.2, ht'.2]⟩ hθβ ht'.2
      rw [h0, zero_sub] at hw
      have := mul_le_mul_of_nonneg_left hw hq
      nlinarith

/-- The window derivative `g(t) - g(t - β)` vanishes at some `θβ ∈ [θs, θs + β]` (plan (W4)): it is `≥ 0` at `θs` and
`≤ 0` at `θs + β` because `g` is maximal at `θs`. -/
lemma exists_window_zero (hg : Continuous g) (hle : ∀ θ, g θ ≤ D) (heq : g θs = D) (hβ : 0 ≤ β) :
    ∃ θβ ∈ Icc θs (θs + β), g θβ - g (θβ - β) = 0 := by
  have hcont : ContinuousOn (fun t => g t - g (t - β)) (Icc θs (θs + β)) :=
    (hg.sub (hg.comp (continuous_sub_right β))).continuousOn
  have h0 : (0 : ℝ) ∈ Icc ((fun t => g t - g (t - β)) (θs + β)) ((fun t => g t - g (t - β)) θs) := by
    simp only [add_sub_cancel_right]
    constructor <;> linarith [hle (θs + β), hle (θs - β)]
  obtain ⟨θβ, hmem, h⟩ := intermediate_value_Icc' (by linarith) hcont h0
  exact ⟨θβ, hmem, h⟩

/-- Away from the maximisers, `g` stays below its maximum by a fixed gap `γ₀` (plan Step 0'). -/
lemma exists_gap {ρ : ℝ} (hg : Continuous g) (hle : ∀ θ, g θ ≤ D)
    (hiff : ∀ θ, g θ = D ↔ ∃ k : ℤ, θ = θs + k * (π / 2)) (hρ : 0 < ρ) (hρ' : ρ < π / 2) :
    ∃ γ₀ > 0, ∀ ξ ∈ Icc (θs + ρ / 2) (θs + π / 2 - ρ / 2), g ξ ≤ D - γ₀ := by
  obtain ⟨ξ₀, hξ₀, hmax⟩ :=
    (isCompact_Icc (a := θs + ρ / 2) (b := θs + π / 2 - ρ / 2)).exists_isMaxOn
      (nonempty_Icc.2 (by linarith)) hg.continuousOn
  refine ⟨D - g ξ₀, ?_, fun ξ hξ => by linarith [isMaxOn_iff.mp hmax ξ hξ]⟩
  have hne : g ξ₀ ≠ D := by
    intro h
    obtain ⟨k, hk⟩ := (hiff ξ₀).1 h
    have hpi := pi_pos
    have h1 : (0 : ℝ) < k := by
      by_contra hk0; replace hk0 := not_lt.mp hk0
      have := hξ₀.1; nlinarith
    have h2 : (k : ℝ) < 1 := by
      by_contra hk1; replace hk1 := not_lt.mp hk1
      have := hξ₀.2; nlinarith
    have h1' : (0 : ℤ) < k := by exact_mod_cast h1
    have h2' : k < 1 := by exact_mod_cast h2
    omega
  exact sub_pos.2 (lt_of_le_of_ne (hle ξ₀) hne)

end Window


/-! ## The key estimate for the window function (plan Step D) -/

section Key

variable {g W : ℝ → ℝ} {q D θs m ρ₁ β : ℝ}

/-- Plan (W1)-(W4) in one statement: some `θβ ∈ [θs, θs + β]` maximises `W`, with
`W(θ) + c β min(ρ, angDist θ θβ)² ≤ W(θβ)` for all `θ`, where `c = min(q m/2, q γ₀/(2ρ²))`. -/
lemma window_key {γ₀ ρ : ℝ} (hq : 0 < q) (hβ : 0 < β)
    (hg : Differentiable ℝ g) (hgper : Function.Periodic g (π / 2))
    (hle : ∀ θ, g θ ≤ D) (heq : g θs = D)
    (hconc : ∀ θ ∈ Icc (θs - ρ₁) (θs + ρ₁), DifferentiableAt ℝ (deriv g) θ ∧ deriv (deriv g) θ ≤ -m)
    (hρ : 0 < ρ) (hρρ₁ : ρ ≤ ρ₁ / 2) (hρπ : ρ ≤ π / 8)
    (hgap : ∀ ξ ∈ Icc (θs + ρ / 2) (θs + π / 2 - ρ / 2), g ξ ≤ D - γ₀)
    (hnear : ∀ ξ, |ξ - θs| ≤ β → D - γ₀ / 2 ≤ g ξ) (hβρ : β ≤ ρ / 2)
    (hW : ∀ t, HasDerivAt W (q * (g t - g (t - β))) t)
    (hWper : ∀ θ (k : ℤ), W (θ - k * (π / 2)) = W θ)
    (hWmvt : ∀ θ, ∃ ξ ∈ Icc (θ - β) θ, W θ = q * β * g ξ) :
    ∃ θβ ∈ Icc θs (θs + β), ∀ θ,
      W θ + min (q * m / 2) (q * γ₀ / (2 * ρ ^ 2)) * β * (min ρ (angDist θ θβ)) ^ 2 ≤ W θβ := by
  obtain ⟨θβ, hθβ, h0⟩ := exists_window_zero hg.continuous hle heq hβ.le
  refine ⟨θβ, hθβ, fun θ => ?_⟩
  obtain ⟨k, hk, hk4⟩ := exists_angDist θ θβ
  rw [← hWper θ k]
  set θ' := θ - k * (π / 2) with hθ'
  set d := angDist θ θβ with hd
  set c := min (q * m / 2) (q * γ₀ / (2 * ρ ^ 2)) with hc
  have hpi := pi_pos
  rcases le_total d ρ with hdρ | hdρ
  · -- near `θβ`: the local quadratic decay
    rw [min_eq_right hdρ]
    have hdist : |θ' - θβ| ≤ ρ := by rw [hk]; exact hdρ
    have habs := abs_le.mp hdist
    have hloc := local_quad hq.le hβ.le hg hconc hW (θβ := θβ)
      ⟨by linarith [hθβ.1], by linarith [hθβ.2]⟩ h0 (θ := θ')
      ⟨by linarith [hθβ.1, habs.1], by linarith [hθβ.2, habs.2]⟩
    have hd2 : (θ' - θβ) ^ 2 = d ^ 2 := by rw [← hk, sq_abs]
    rw [hd2] at hloc
    have hcd : c * β * d ^ 2 ≤ q * m / 2 * β * d ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hβ.le) (sq_nonneg d)
    linarith
  · -- far from `θβ`: the window misses the maximisers, so `W(θ') ≤ qβ(D - γ₀) < qβ(D - γ₀/2) ≤ W(θβ)`
    rw [min_eq_left hdρ]
    obtain ⟨ξ, hξ, hWξ⟩ := hWmvt θ'
    obtain ⟨ξβ, hξβ, hWξβ⟩ := hWmvt θβ
    have hgξ : g ξ ≤ D - γ₀ := by
      rcases le_total 0 (θ' - θβ) with hs | hs
      · rw [abs_of_nonneg hs] at hk
        exact hgap ξ ⟨by linarith [hξ.1, hθβ.1], by linarith [hξ.2, hθβ.2]⟩
      · rw [abs_of_nonpos hs] at hk
        rw [← hgper ξ]
        exact hgap (ξ + π / 2) ⟨by linarith [hξ.1, hθβ.1], by linarith [hξ.2, hθβ.2]⟩
    have hgξβ : D - γ₀ / 2 ≤ g ξβ :=
      hnear ξβ (abs_le.mpr ⟨by linarith [hξβ.1, hθβ.1], by linarith [hξβ.2, hθβ.2]⟩)
    have hcρ : c * ρ ^ 2 ≤ q * γ₀ / 2 := by
      calc c * ρ ^ 2 ≤ q * γ₀ / (2 * ρ ^ 2) * ρ ^ 2 :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
        _ = q * γ₀ / 2 := by field_simp
    have h1 := mul_le_mul_of_nonneg_left hgξ (by positivity : 0 ≤ q * β)
    have h2 := mul_le_mul_of_nonneg_left hgξβ (by positivity : 0 ≤ q * β)
    have h3 := mul_le_mul_of_nonneg_left hcρ hβ.le
    rw [hWξ, hWξβ]
    linarith

end Key

/-! ## From the window function to `Σ_a` (plan Step E) -/

/-- `C^q N(θ) - r^q N(θ - β) = r^q N(θ) (e^V - e^W) ≥ r^q N(θ - β) (V - W) ≥ n₀ (V - W)`. -/
lemma sigma_lower_of_W {Cq rq n₀ V Wθ Nθ Nθβ : ℝ} (hrq : 1 ≤ rq) (hn : n₀ ≤ Nθβ) (hn0 : 0 ≤ n₀)
    (hNθβ : Nθβ = exp Wθ * Nθ) (hCq : Cq = rq * exp V) (hWV : Wθ ≤ V) (hNθ : 0 < Nθ) :
    2 * n₀ * (V - Wθ) ≤ 2 * (Cq * Nθ - rq * Nθβ) := by
  have h1 : exp Wθ * (V - Wθ) ≤ exp V - exp Wθ := by
    have h2 : exp V = exp Wθ * exp (V - Wθ) := by rw [← Real.exp_add]; congr 1; ring
    have h3 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (V - Wθ)) (Real.exp_pos Wθ).le
    rw [h2]
    linarith
  have h4 : Cq * Nθ - rq * Nθβ = rq * Nθ * (exp V - exp Wθ) := by rw [hCq, hNθβ]; ring
  have h5 : rq * Nθ * (exp Wθ * (V - Wθ)) ≤ rq * Nθ * (exp V - exp Wθ) :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg (by linarith) hNθ.le)
  have h6 : n₀ ≤ rq * Nθβ := by
    have := mul_le_mul_of_nonneg_right hrq (hn0.trans hn)
    linarith
  have h7 : n₀ * (V - Wθ) ≤ rq * Nθβ * (V - Wθ) := mul_le_mul_of_nonneg_right h6 (by linarith)
  have h8 : rq * Nθ * (exp Wθ * (V - Wθ)) = rq * Nθβ * (V - Wθ) := by rw [hNθβ]; ring
  rw [h4]
  linarith

/-- `M(θ) = ‖P_a(J) e(θ)‖_q^q = |(1+B) cos θ + a sin θ|^q + |(1+B) sin θ - a cos θ|^q`. -/
noncomputable def Mf (q a B θ : ℝ) : ℝ :=
  |(1 + B) * cos θ + a * sin θ| ^ q + |(1 + B) * sin θ - a * cos θ| ^ q

lemma SigmaAng_eq (q a B C θ : ℝ) : SigmaAng q a B C θ = 2 * (C ^ q * Nang q θ - Mf q a B θ) := rfl

/-- Plan R1: `P_a(J) = r R_β`, so `M(θ) = r^q N(θ - β)`. -/
lemma Mf_eq {q a B r β : ℝ} (hr : 0 ≤ r) (hrc : r * cos β = 1 + B) (hrs : r * sin β = a) (θ : ℝ) :
    Mf q a B θ = r ^ q * Nang q (θ - β) := by
  have e1 : (1 + B) * cos θ + a * sin θ = r * cos (θ - β) := by rw [← hrc, ← hrs, cos_sub]; ring
  have e2 : (1 + B) * sin θ - a * cos θ = r * sin (θ - β) := by rw [← hrc, ← hrs, sin_sub]; ring
  rw [Mf, e1, e2, abs_mul_rpow, abs_mul_rpow, abs_of_nonneg hr, Nang]
  ring

/-! ## The core statement, for any constant `C` with the two properties of `C_a = ‖P_a(J)‖` -/

/-- Steps D/E with `C` abstract: `C^q = max_θ M(θ)/N(θ)` (given as `M ≤ C^q N` everywhere, with equality somewhere). -/
theorem sigma_core (q : ℝ) (hq2 : 2 < q) (B : ℝ) (hB : 0 < B) (θs : ℝ) (hθs : IsThetaStar q θs) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ a₁ η : ℝ, 0 < a₁ ∧ 0 < η ∧ ∀ a : ℝ, 0 < a → a < a₁ →
      ∀ C : ℝ, (∀ θ, Mf q a B θ ≤ C ^ q * Nang q θ) → (∃ θ₀, C ^ q * Nang q θ₀ = Mf q a B θ₀) →
      ∃ θa : ℝ, |θa - θs| ≤ a ∧ SigmaAng q a B C θa = 0 ∧
        ∀ θ : ℝ, a * η * (min ρ (angDist θ θa)) ^ 2 ≤ SigmaAng q a B C θ := by
  have hq0 : 0 ≤ q := by linarith
  have hpi := pi_pos
  obtain ⟨ρ₁, m, hρ₁, hm, hconc⟩ := hθs.concave_near
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = min (ρ₁ / 2) (π / 8) := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; exact lt_min (by linarith) (by positivity)
  have hρρ₁ : ρ ≤ ρ₁ / 2 := hρdef ▸ min_le_left _ _
  have hρπ : ρ ≤ π / 8 := hρdef ▸ min_le_right _ _
  have hg : Differentiable ℝ (qang q) := hθs.differentiable
  obtain ⟨γ₀, hγ, hgap⟩ := exists_gap hg.continuous hθs.le_dstar hθs.eq_iff hρ (by linarith)
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hg.continuous.continuousAt (γ₀ / 2) (half_pos hγ)
  have hnear : ∀ ξ, |ξ - θs| ≤ δ / 2 → Dstar q - γ₀ / 2 ≤ qang q ξ := fun ξ hξ => by
    have := hball (show dist ξ θs < δ by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq, hθs.eq_at] at this
    linarith [(abs_lt.mp this).1]
  obtain ⟨c, hcdef⟩ : ∃ c, c = min (q * m / 2) (q * γ₀ / (2 * ρ ^ 2)) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact lt_min (by positivity) (by positivity)
  obtain ⟨n₀, hn₀def⟩ : ∃ n₀ : ℝ, n₀ = (1 / 2 : ℝ) ^ (q / 2) := ⟨_, rfl⟩
  have hn₀ : 0 < n₀ := by rw [hn₀def]; positivity
  refine ⟨ρ, hρ, fun ρ' hρ' hρ'ρ => ?_⟩
  obtain ⟨β₁, hβ₁def⟩ : ∃ β₁, β₁ = min 1 (min (ρ / 2) (δ / 2)) := ⟨_, rfl⟩
  have hβ₁ : 0 < β₁ := by rw [hβ₁def]; exact lt_min one_pos (lt_min (by linarith) (by linarith))
  have hβ₁1 : β₁ ≤ 1 := hβ₁def ▸ min_le_left _ _
  have hβ₁ρ : β₁ ≤ ρ / 2 := hβ₁def ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hβ₁δ : β₁ ≤ δ / 2 := hβ₁def ▸ (min_le_right _ _).trans (min_le_right _ _)
  have hB1 : 0 < 1 + B := by linarith
  refine ⟨(1 + B) * β₁, n₀ * c / (1 + B), by positivity, by positivity, fun a ha haa₁ C hCle hCeq => ?_⟩
  -- the angle `β = arctan (a/(1+B))` and the radius `r`: `P_a(J) = r R_β`
  obtain ⟨x, hxdef⟩ : ∃ x, x = a / (1 + B) := ⟨_, rfl⟩
  have hx : 0 < x := by rw [hxdef]; exact div_pos ha hB1
  have hxβ₁ : x < β₁ := by rw [hxdef, div_lt_iff₀ hB1]; linarith
  have hxa : x ≤ a := by rw [hxdef]; exact div_le_self ha.le (by linarith)
  obtain ⟨β, hβdef⟩ : ∃ β, β = arctan x := ⟨_, rfl⟩
  have hβ : 0 < β := by rw [hβdef]; exact arctan_pos.2 hx
  have hβx : β ≤ x := by rw [hβdef]; exact arctan_le_self hx.le
  have hsq : 0 < √(1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨r, hrdef⟩ : ∃ r, r = (1 + B) * √(1 + x ^ 2) := ⟨_, rfl⟩
  have hrc : r * cos β = 1 + B := by
    rw [hβdef, cos_arctan, hrdef, mul_assoc, mul_one_div_cancel hsq.ne', mul_one]
  have hrs : r * sin β = a := by
    have e : √(1 + x ^ 2) * (x / √(1 + x ^ 2)) = x := by field_simp
    rw [hβdef, sin_arctan, hrdef, mul_assoc, e, hxdef]
    field_simp
  have hr1 : 1 ≤ r := by
    have : 1 ≤ √(1 + x ^ 2) := Real.one_le_sqrt.2 (by nlinarith)
    rw [hrdef]; nlinarith
  have hβlow : x / 2 ≤ β := by
    have h1 : sin β ≤ β := sin_le hβ.le
    have h2 : √(1 + x ^ 2) ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; nlinarith
    have h3 : x / 2 ≤ x / √(1 + x ^ 2) := div_le_div_of_nonneg_left hx.le hsq h2
    rw [hβdef, sin_arctan] at h1
    rw [hβdef]; linarith
  -- the window function `W = Wl q β` and its maximiser `θβ`
  obtain ⟨θβ, hθβ, hkey⟩ := window_key (g := qang q) (W := Wl q β) (by linarith) hβ hg (qang_periodic q)
    hθs.le_dstar hθs.eq_at hconc hρ hρρ₁ hρπ hgap (fun ξ hξ => hnear ξ (by linarith)) (by linarith)
    (hasDerivAt_Wl hq2.le β) (Wl_periodic q β) (Wl_mvt hq2.le hβ)
  rw [← hcdef] at hkey
  have hM : ∀ θ, Mf q a B θ = r ^ q * Nang q (θ - β) := Mf_eq (by linarith) hrc hrs
  have hNexp : ∀ θ, Nang q (θ - β) = exp (Wl q β θ) * Nang q θ := fun θ => by
    rw [Wl, exp_sub, exp_log (Nang_pos hq0 _), exp_log (Nang_pos hq0 _)]
    field_simp [(Nang_pos hq0 θ).ne']
  have hWmax : ∀ θ, Wl q β θ ≤ Wl q β θβ := fun θ => by
    have h1 := hkey θ
    have h2 : 0 ≤ c * β * (min ρ (angDist θ θβ)) ^ 2 := by positivity
    linarith
  -- `C^q = r^q e^V` with `V = W(θβ) = max W`
  have hCq : C ^ q = r ^ q * exp (Wl q β θβ) := by
    obtain ⟨θ₀, h₀⟩ := hCeq
    have hle := hCle θβ
    rw [hM, hNexp] at h₀ hle
    have hN0 := Nang_pos hq0 θ₀
    have hNβ := Nang_pos hq0 θβ
    have e1 : C ^ q = r ^ q * exp (Wl q β θ₀) := by
      apply mul_right_cancel₀ hN0.ne'
      rw [h₀]; ring
    apply le_antisymm
    · rw [e1]
      exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (hWmax θ₀)) (by positivity)
    · exact le_of_mul_le_mul_right (by rw [mul_assoc]; exact hle) hNβ
  refine ⟨θβ, ?_, ?_, fun θ => ?_⟩
  · rw [abs_le]; constructor <;> linarith [hθβ.1, hθβ.2]
  · rw [SigmaAng_eq, hM, hNexp, hCq]; ring
  · rw [SigmaAng_eq, hM]
    have hlow := sigma_lower_of_W (Cq := C ^ q) (rq := r ^ q) (n₀ := n₀) (V := Wl q β θβ) (Wθ := Wl q β θ)
      (Nθ := Nang q θ) (Nθβ := Nang q (θ - β)) (Real.one_le_rpow hr1 hq0) (hn₀def ▸ Nang_ge hq0 _) hn₀.le
      (hNexp θ) hCq (hWmax θ) (Nang_pos hq0 θ)
    have hk := hkey θ
    have hd0 := angDist_nonneg θ θβ
    have hmin : (min ρ' (angDist θ θβ)) ^ 2 ≤ (min ρ (angDist θ θβ)) ^ 2 :=
      pow_le_pow_left₀ (le_min hρ'.le hd0) (min_le_min_right _ hρ'ρ) 2
    have hm0 : 0 ≤ (min ρ (angDist θ θβ)) ^ 2 := sq_nonneg _
    have e : a * (n₀ * c / (1 + B)) = n₀ * c * x := by rw [hxdef]; field_simp
    have h1 : a * (n₀ * c / (1 + B)) * (min ρ' (angDist θ θβ)) ^ 2 ≤
        n₀ * c * x * (min ρ (angDist θ θβ)) ^ 2 := by
      rw [e]; exact mul_le_mul_of_nonneg_left hmin (by positivity)
    have h2 : n₀ * c * x * (min ρ (angDist θ θβ)) ^ 2 ≤ n₀ * c * (2 * β) * (min ρ (angDist θ θβ)) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hm0
    have h3 : 2 * n₀ * (c * β * (min ρ (angDist θ θβ)) ^ 2) ≤ 2 * n₀ * (Wl q β θβ - Wl q β θ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

/-! ## The norm `C_a = ‖P_a(J)‖_{ℓ^p_2}` in angle form -/

section Norm

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

lemma PaJ_mulVec (a B u v : ℝ) :
    (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) *ᵥ ![u, v] =
      ![(1 + B) * u + a * v, (1 + B) * v - a * u] := by
  rw [aeval_Jmat_Pa_proved]
  ext i
  fin_cases i
  · simp [Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

/-- `M(θ) ≤ C_a^q N(θ)`: `‖P_a(J) e(θ)‖ ≤ C_a ‖e(θ)‖`. -/
lemma Mf_le_matNorm (hptop : p ≠ ⊤) (a B θ : ℝ) :
    Mf p.toReal a B θ ≤
      matNorm p (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) ^ p.toReal * Nang p.toReal θ := by
  have h := norm_mulVec_le_matNorm p (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) ![cos θ, sin θ]
  rw [PaJ_mulVec] at h
  have h2 := Real.rpow_le_rpow (norm_nonneg _) h (ENNReal.toReal_nonneg (a := p))
  rw [Real.mul_rpow (matNorm_nonneg _ _) (norm_nonneg _), norm_toLp_fin2_rpow p hptop,
    norm_toLp_fin2_rpow p hptop] at h2
  exact h2

/-- `C_a` is attained: `C_a^q N(θ₀) = M(θ₀)` for some angle `θ₀` (polar form of a norming vector). -/
lemma exists_Mf_eq_matNorm (hptop : p ≠ ⊤) (a B : ℝ) : ∃ θ₀ : ℝ,
    matNorm p (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) ^ p.toReal * Nang p.toReal θ₀ =
      Mf p.toReal a B θ₀ := by
  obtain ⟨x, hx1, hxA⟩ := exists_eq_matNorm p (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))
  obtain ⟨R, θ₀, hR, rfl⟩ : ∃ R θ₀ : ℝ, 0 ≤ R ∧ x = ![R * cos θ₀, R * sin θ₀] := by
    refine ⟨‖(⟨x 0, x 1⟩ : ℂ)‖, Complex.arg ⟨x 0, x 1⟩, norm_nonneg _, ?_⟩
    rw [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
    ext i; fin_cases i <;> rfl
  refine ⟨θ₀, ?_⟩
  have h1 : R ^ p.toReal * Nang p.toReal θ₀ = 1 := by
    have := norm_toLp_fin2_rpow p hptop (R * cos θ₀) (R * sin θ₀)
    rw [hx1, Real.one_rpow, abs_mul_rpow, abs_mul_rpow, abs_of_nonneg hR] at this
    rw [Nang, mul_add]; linarith
  have h2 : matNorm p (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) ^ p.toReal =
      R ^ p.toReal * Mf p.toReal a B θ₀ := by
    rw [← hxA, PaJ_mulVec, norm_toLp_fin2_rpow p hptop,
      show (1 + B) * (R * cos θ₀) + a * (R * sin θ₀) = R * ((1 + B) * cos θ₀ + a * sin θ₀) by ring,
      show (1 + B) * (R * sin θ₀) - a * (R * cos θ₀) = R * ((1 + B) * sin θ₀ - a * cos θ₀) by ring,
      abs_mul_rpow, abs_mul_rpow, abs_of_nonneg hR, Mf, mul_add]
  rw [h2]
  calc R ^ p.toReal * Mf p.toReal a B θ₀ * Nang p.toReal θ₀ =
      Mf p.toReal a B θ₀ * (R ^ p.toReal * Nang p.toReal θ₀) := by ring
    _ = Mf p.toReal a B θ₀ := by rw [h1, mul_one]

end Norm

/-! ## The Σ-interface -/

open Matsaev.Angle in
/-- **The Σ-interface (Steps D/E of the plan).** For small `a > 0`, `Σ_a` vanishes at an angle `θa` within `a` of `θs`,
and `Σ_a(e(θ)) ≥ a η · min(ρ, dist(θ, θa + (π/2)ℤ))²`. -/
theorem sigma_interface (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B)
    (θs : ℝ) (hθs : IsThetaStar p.toReal θs) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ a₁ η : ℝ, 0 < a₁ ∧ 0 < η ∧ ∀ a : ℝ, 0 < a → a < a₁ →
      ∃ θa : ℝ, |θa - θs| ≤ a ∧
        SigmaAng p.toReal a B (matNorm p (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θa = 0 ∧
        ∀ θ : ℝ, a * η * (min ρ (angDist θ θa)) ^ 2 ≤
          SigmaAng p.toReal a B (matNorm p (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ := by
  have hq2 : 2 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (by simp) hptop).2 hp
    simpa using this
  obtain ⟨ρ₀, hρ₀, h⟩ := sigma_core p.toReal hq2 B hB θs hθs
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρρ₀ => ?_⟩
  obtain ⟨a₁, η, ha₁, hη, h'⟩ := h ρ hρ hρρ₀
  exact ⟨a₁, η, ha₁, hη, fun a ha haa =>
    h' a ha haa _ (Mf_le_matNorm p hptop a B) (exists_Mf_eq_matNorm p hptop a B)⟩

end Matsaev.SJ
