/-
Matsaev/Assembly/Lem35iv.lean — Lemma 3.5 (iv) (`lem:SJmax`): `a ↦ s_a` and `a ↦ C_a^p` are real-analytic on `[0, a₁)`.
Route: near `θ_*`, `D_* - q(θ) = h(θ)²` with `h` analytic, `h'(θ_*) > 0` (Morse factor, by `dslope` twice); a zero `θ_a` of
`Σ_a` solves `q(θ) = q(θ - γ)`, `γ = arctan(a/(1+B))`, hence `h(θ) + h(θ - γ) = 0`, which Mathlib's analytic implicit
function theorem (`ContDiffAt.implicitFunction`, order `ω`) solves as `θ = ψ(γ)`; then `C_a^p = r^p N(θ_a - γ)/N(θ_a)`.
Author: Dave Goel.
-/
import Matsaev.Angle.Basic
import Matsaev.SJ.Sigma

namespace Matsaev.Lem35iv

open Real Set Filter Topology Matsaev Matsaev.Angle
open scoped ContDiff ENNReal

variable {q : ℝ}

lemma contDiffAt_dfun_omega {s : ℝ} (hs : 0 < s) : ContDiffAt ℝ ω (dfun q) s := by
  have h1 : ContDiffAt ℝ ω (fun x : ℝ => x ^ (q - 1)) s := contDiffAt_rpow_const_of_ne hs.ne'
  have h2 : ContDiffAt ℝ ω (fun x : ℝ => x ^ q) s := contDiffAt_rpow_const_of_ne hs.ne'
  have hden : 1 + s ^ q ≠ 0 := by positivity
  exact (contDiffAt_id.sub h1).div (contDiffAt_const.add h2) hden

/-- `q(θ)` is real-analytic on `(0, π/2)`. -/
lemma contDiffAt_qang (hq : 1 < q) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) : ContDiffAt ℝ ω (qang q) θ := by
  have hc : Real.cos θ ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, pi_pos], hθ.2⟩).ne'
  have hcomp : ContDiffAt ℝ ω (fun x => dfun q (Real.tan x)) θ :=
    (contDiffAt_dfun_omega (tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2)).comp θ (contDiffAt_tan.mpr hc)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
  exact qang_eq_dfun_tan hq hx.1 hx.2

/-- `N(θ)` is real-analytic on `(0, π/2)`. -/
lemma contDiffAt_Nang {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) : ContDiffAt ℝ ω (Nang q) θ := by
  have hc : 0 < Real.cos θ := cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, pi_pos], hθ.2⟩
  have hs : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, pi_pos])
  have h1 : ContDiffAt ℝ ω (fun x => Real.cos x ^ q) θ :=
    (contDiffAt_rpow_const_of_ne hc.ne').comp θ contDiff_cos.contDiffAt
  have h2 : ContDiffAt ℝ ω (fun x => Real.sin x ^ q) θ :=
    (contDiffAt_rpow_const_of_ne hs.ne').comp θ contDiff_sin.contDiffAt
  refine (h1.add h2).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
  have hcx : 0 < Real.cos x := cos_pos_of_mem_Ioo ⟨by linarith [hx.1, pi_pos], hx.2⟩
  have hsx : 0 < Real.sin x := sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, pi_pos])
  simp only [Nang, abs_of_pos hcx, abs_of_pos hsx]

lemma mem_Ioo_of_isThetaStar {θs : ℝ} (hθs : IsThetaStar q θs) : θs ∈ Ioo 0 (π / 2) :=
  ⟨hθs.mem.1, by linarith [hθs.mem.2, pi_pos]⟩

/-- `θ_* = arctan t_*`: the maximum angle of `IsThetaStar` is `arctan` of the critical point of Lemma 3.4. -/
lemma thetaStar_eq_arctan (hq : 2 < q) {θs t : ℝ} (hθs : IsThetaStar q θs) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcrit : ∀ s ∈ Ioo (0 : ℝ) 1, deriv (dfun q) s = 0 ↔ s = t) : θs = arctan t := by
  obtain ⟨t', ht', hcrit', -, -, -, hD, hatt, -⟩ := lemma_3_3_proved q hq
  have htt : t = t' := (hcrit' t ht).mp ((hcrit t ht).mpr rfl)
  subst htt
  obtain ⟨hθ0, hθ4⟩ := hθs.mem
  have hc : 0 < Real.cos θs := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hs : 0 < Real.sin θs := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hne : (Real.cos θs, Real.sin θs) ≠ ((0 : ℝ), (0 : ℝ)) := fun h => by
    simp only [Prod.mk.injEq] at h; linarith [h.1]
  have hQ : Qf q (Real.cos θs) (Real.sin θs) = dfun q t := by
    rw [← hD]; exact hθs.eq_at
  obtain ⟨r, -, hr⟩ := (hatt _ _ hne).1 hQ
  rcases hr with hr | hr
  · simp only [Prod.mk.injEq] at hr
    have htan : Real.tan θs = t := by
      rw [Real.tan_eq_sin_div_cos, hr.1, hr.2]; field_simp [hr.1 ▸ hc.ne']
    rw [← htan, Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  · simp only [Prod.mk.injEq] at hr
    exfalso
    nlinarith [ht.1, hr.1, hr.2, hc, hs]

/-- Quadratic decay at the maximum: `q(θ) ≤ D_* - (m/2)(θ - θ_*)²` near `θ_*`. -/
lemma qang_le_quad {θs : ℝ} (hθs : IsThetaStar q θs) :
    ∃ ρ m : ℝ, 0 < ρ ∧ 0 < m ∧ ∀ θ ∈ Icc (θs - ρ) (θs + ρ), qang q θ ≤ Dstar q - m / 2 * (θ - θs) ^ 2 := by
  obtain ⟨ρ, m, hρ, hm, hconc⟩ := hθs.concave_near
  refine ⟨ρ, m, hρ, hm, fun θ hθ => ?_⟩
  have hd0 : deriv (qang q) θs = 0 := (hθs.crit_iff θs).mpr ⟨0, Or.inl (by simp)⟩
  set φ : ℝ → ℝ := fun t => qang q t + m / 2 * (t - θs) ^ 2 with hφdef
  have hφ : ∀ t, HasDerivAt φ (deriv (qang q) t + m * (t - θs)) t := fun t => by
    have h2 : HasDerivAt (fun y => m / 2 * (y - θs) ^ 2) (m * (t - θs)) t := by
      have h := (((hasDerivAt_id' t).sub_const θs).mul ((hasDerivAt_id' t).sub_const θs)).const_mul (m / 2)
      convert h using 1
      · funext y; simp only [Pi.mul_apply]; ring
      · ring
    exact (hθs.differentiable t).hasDerivAt.add h2
  have hcont : ∀ s : Set ℝ, ContinuousOn φ s := fun s u _ => (hφ u).continuousAt.continuousWithinAt
  have hdiff : ∀ s : Set ℝ, DifferentiableOn ℝ φ s := fun s u _ => (hφ u).differentiableAt.differentiableWithinAt
  have hmem : θs ∈ Icc (θs - ρ) (θs + ρ) := ⟨by linarith, by linarith⟩
  suffices φ θ ≤ φ θs by
    simp only [hφdef, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at this
    rw [hθs.eq_at] at this
    linarith
  rcases le_total θs θ with h | h
  · refine antitoneOn_of_deriv_nonpos (convex_Icc θs (θs + ρ)) (hcont _) (hdiff _) (fun t ht => ?_)
      ⟨le_rfl, by linarith [hmem.2]⟩ ⟨h, hθ.2⟩ h
    rw [interior_Icc] at ht
    rw [(hφ t).deriv]
    have := Matsaev.SJ.deriv_sub_le hconc hmem ⟨by linarith [ht.1], ht.2.le⟩ ht.1.le
    linarith
  · refine monotoneOn_of_deriv_nonneg (convex_Icc (θs - ρ) θs) (hcont _) (hdiff _) (fun t ht => ?_)
      ⟨hθ.1, h⟩ ⟨by linarith [hmem.1], le_rfl⟩ h
    rw [interior_Icc] at ht
    rw [(hφ t).deriv]
    have := Matsaev.SJ.deriv_sub_le hconc ⟨ht.1.le, by linarith [ht.2]⟩ hmem ht.2.le
    linarith

/-- **Morse factor.** Near `θ_*`, `D_* - q(θ) = h(θ)²` with `h` real-analytic, `h(θ_*) = 0`, `h'(θ_*) > 0`. -/
theorem morse_factor (hq : 2 < q) {θs : ℝ} (hθs : IsThetaStar q θs) :
    ∃ h : ℝ → ℝ, ∃ d : ℝ, 0 < d ∧ ContDiffAt ℝ ω h θs ∧ h θs = 0 ∧ HasDerivAt h d θs ∧
      ∀ᶠ θ in 𝓝 θs, Dstar q - qang q θ = h θ ^ 2 := by
  have hq1 : 1 < q := by linarith
  set f : ℝ → ℝ := fun θ => Dstar q - qang q θ with hfdef
  have hfA : AnalyticAt ℝ f θs :=
    (contDiffAt_const.sub (contDiffAt_qang hq1 (mem_Ioo_of_isThetaStar hθs))).analyticAt
  obtain ⟨P, hP⟩ := hfA
  have hP2 := hP.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope
  set g1 := dslope f θs with hg1def
  set u := dslope g1 θs with hudef
  have hf0 : f θs = 0 := by simp [hfdef, hθs.eq_at]
  have hg10 : g1 θs = 0 := by
    rw [hg1def, dslope_same, hfdef, deriv_const_sub, (hθs.crit_iff θs).mpr ⟨0, Or.inl (by simp)⟩, neg_zero]
  have hfac : ∀ θ, f θ = (θ - θs) ^ 2 * u θ := by
    intro θ
    have e1 := sub_smul_dslope f θs θ
    have e2 := sub_smul_dslope g1 θs θ
    rw [smul_eq_mul] at e1 e2
    rw [hf0] at e1
    rw [hg10] at e2
    linear_combination (-1 : ℝ) * e1 - (θ - θs) * e2
  have huA : AnalyticAt ℝ u θs := hP2.analyticAt
  obtain ⟨ρ, m, hρ, hm, hquad⟩ := qang_le_quad hθs
  have hu_ge : m / 2 ≤ u θs := by
    have ht : Tendsto u (𝓝[≠] θs) (𝓝 (u θs)) := huA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    have hI : Icc (θs - ρ) (θs + ρ) ∈ 𝓝[≠] θs :=
      nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith))
    filter_upwards [hI, self_mem_nhdsWithin] with θ hθ hne
    have hpos : 0 < (θ - θs) ^ 2 := by
      have : θ - θs ≠ 0 := sub_ne_zero.mpr hne
      positivity
    have := hquad θ hθ
    have h2 : m / 2 * (θ - θs) ^ 2 ≤ (θ - θs) ^ 2 * u θ := by
      rw [← hfac θ, hfdef]; linarith
    nlinarith
  have hu0 : 0 < u θs := by linarith
  have hsq : ContDiffAt ℝ ω (fun θ => √(u θ)) θs := (contDiffAt_sqrt hu0.ne').comp θs huA.contDiffAt
  refine ⟨fun θ => (θ - θs) * √(u θ), √(u θs), Real.sqrt_pos.mpr hu0,
    (contDiffAt_id.sub contDiffAt_const).mul hsq, by simp, ?_, ?_⟩
  · have := ((hasDerivAt_id' θs).sub_const θs).mul (hsq.differentiableAt (by simp)).hasDerivAt
    convert this using 1
    simp
  · filter_upwards [huA.continuousAt.eventually (lt_mem_nhds hu0)] with θ hθ
    rw [mul_pow, Real.sq_sqrt hθ.le, ← hfac θ]


/-- **The analytic branch.** There is `ψ`, real-analytic at `0` with `ψ 0 = θ_*`, such that near `(0, θ_*)` every solution
of `q(θ) = q(θ - γ)` with `γ > 0` is `θ = ψ γ` (implicit function theorem for `h(θ) + h(θ - γ) = 0`). -/
theorem analytic_branch (hq : 2 < q) {θs : ℝ} (hθs : IsThetaStar q θs) :
    ∃ ψ : ℝ → ℝ, AnalyticAt ℝ ψ 0 ∧ ψ 0 = θs ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ γ θ : ℝ, 0 < γ → γ < ε → |θ - θs| < ε → qang q θ = qang q (θ - γ) → ψ γ = θ := by
  obtain ⟨h, d, hd, hhC, hh0, hhd, hsq⟩ := morse_factor hq hθs
  have hhA : AnalyticAt ℝ h θs := hhC.analyticAt
  have hdθs : 0 < deriv h θs := hhd.deriv ▸ hd
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hhA.deriv.continuousAt.eventually (lt_mem_nhds hdθs)).and (hhA.eventually_analyticAt.and hsq))
  have hmono : StrictMonoOn h (Metric.ball θs ε₁) :=
    strictMonoOn_of_deriv_pos (convex_ball θs ε₁) (fun y hy => (hball hy).2.1.continuousAt.continuousWithinAt)
      (fun y hy => (hball (Metric.mem_ball.mp (interior_subset hy))).1)
  set F : ℝ × ℝ → ℝ := fun v => h v.2 + h (v.2 - v.1) with hFdef
  have hFC : ContDiffAt ℝ ω F ((0 : ℝ), θs) := by
    have h1 : ContDiffAt ℝ ω (fun v : ℝ × ℝ => h v.2) ((0 : ℝ), θs) := hhC.comp ((0 : ℝ), θs) contDiffAt_snd
    have h2 : ContDiffAt ℝ ω (fun v : ℝ × ℝ => h (v.2 - v.1)) ((0 : ℝ), θs) := by
      have hg : ContDiffAt ℝ ω h (((0 : ℝ), θs).2 - ((0 : ℝ), θs).1) := by simpa using hhC
      exact hg.comp ((0 : ℝ), θs) (contDiffAt_snd.sub contDiffAt_fst)
    exact h1.add h2
  have hpart : fderiv ℝ F ((0 : ℝ), θs) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ = (2 * d) • ContinuousLinearMap.id ℝ ℝ := by
    have hF' : HasFDerivAt F (fderiv ℝ F ((0 : ℝ), θs)) ((0 : ℝ), θs) := (hFC.differentiableAt (by simp)).hasFDerivAt
    have hcomp := hF'.comp θs (hasFDerivAt_prodMk_right (0 : ℝ) θs)
    have hdirect : HasDerivAt (F ∘ fun y => ((0 : ℝ), y)) (2 * d) θs := by
      have he : (F ∘ fun y => ((0 : ℝ), y)) = fun y => h y + h y := by
        funext y; simp [hFdef]
      rw [he]
      convert hhd.add hhd using 1
      ring
    rw [← hdirect.hasFDerivAt.unique hcomp]
    ext
    simp
  have hinv : (fderiv ℝ F ((0 : ℝ), θs) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hpart]
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := (2 * d)⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_ <;>
      ext <;> simp <;> field_simp
  have pn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hFC.implicitFunction pn hinv, (hFC.contDiffAt_implicitFunction pn hinv).analyticAt,
    hFC.implicitFunction_apply_self pn hinv, ?_⟩
  obtain ⟨ε₂, hε₂, hbox⟩ := Metric.eventually_nhds_iff.mp (hFC.eventually_apply_eq_iff_implicitFunction pn hinv)
  refine ⟨min (ε₁ / 2) ε₂, lt_min (by linarith) hε₂, fun γ θ hγ hγε hθ hqq => ?_⟩
  have hε₁' := min_le_left (ε₁ / 2) ε₂
  have hε₂' := min_le_right (ε₁ / 2) ε₂
  have hθb : dist θ θs < ε₁ := by rw [Real.dist_eq]; linarith
  have hθγb : dist (θ - γ) θs < ε₁ := by
    rw [Real.dist_eq]
    calc |θ - γ - θs| ≤ |θ - θs| + |γ| := by
          rw [show θ - γ - θs = (θ - θs) + (-γ) by ring, ← abs_neg γ]; exact abs_add_le _ _
      _ < ε₁ := by rw [abs_of_pos hγ]; linarith
  have e1 := (hball hθb).2.2
  have e2 := (hball hθγb).2.2
  have hsq_eq : h θ ^ 2 = h (θ - γ) ^ 2 := by rw [← e1, ← e2, hqq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq_eq with heq | heq
  · exfalso
    have := hmono.injOn hθb hθγb heq
    linarith
  · have hv : dist (γ, θ) ((0 : ℝ), θs) < ε₂ := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, sub_zero, abs_of_pos hγ]
      exact ⟨by linarith, by linarith⟩
    have hF : F (γ, θ) = F ((0 : ℝ), θs) := by
      simp only [hFdef, sub_zero, hh0, add_zero, heq]
      ring
    exact (hbox hv).mp hF


/-- `P_a(J) = r R_γ` in coordinates: `r cos γ = 1 + B`, `r sin γ = a` for `r = √((1+B)² + a²)`, `γ = arctan(a/(1+B))`. -/
lemma polar_Pa {B : ℝ} (hB : 0 < 1 + B) (a : ℝ) :
    √((1 + B) ^ 2 + a ^ 2) * Real.cos (arctan (a / (1 + B))) = 1 + B ∧
      √((1 + B) ^ 2 + a ^ 2) * Real.sin (arctan (a / (1 + B))) = a := by
  have hB0 : 1 + B ≠ 0 := hB.ne'
  have hs : 0 < √(1 + (a / (1 + B)) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsq : √((1 + B) ^ 2 + a ^ 2) = (1 + B) * √(1 + (a / (1 + B)) ^ 2) := by
    rw [show (1 + B) ^ 2 + a ^ 2 = (1 + B) ^ 2 * (1 + (a / (1 + B)) ^ 2) by field_simp,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB.le]
  rw [Real.cos_arctan, Real.sin_arctan, hsq]
  constructor <;> field_simp

/-- A zero of `Σ_a ≥ 0` is a critical point of `log N(θ - γ) - log N(θ)`: `q(θ) = q(θ - γ)`, `γ = arctan(a/(1+B))`. -/
lemma qang_eq_of_sigma_zero {a B C θ : ℝ} (hq : 1 < q) (hB : 0 < 1 + B)
    (hnn : ∀ θ', 0 ≤ SigmaAng q a B C θ') (h0 : SigmaAng q a B C θ = 0) :
    qang q θ = qang q (θ - arctan (a / (1 + B))) := by
  set r := √((1 + B) ^ 2 + a ^ 2) with hrdef
  set γ := arctan (a / (1 + B)) with hγdef
  obtain ⟨hrc, hrs⟩ := polar_Pa hB a
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hS : ∀ θ', SigmaAng q a B C θ' = 2 * (C ^ q * Nang q θ' - r ^ q * Nang q (θ' - γ)) := fun θ' => by
    rw [SJ.SigmaAng_eq, SJ.Mf_eq hr0.le hrc hrs]
  have hder : HasDerivAt (SigmaAng q a B C)
      (2 * (C ^ q * (-(q * qang q θ * Nang q θ)) - r ^ q * (-(q * qang q (θ - γ) * Nang q (θ - γ))))) θ := by
    have h1 := hasDerivAt_Nang q hq θ
    have h2 := (hasDerivAt_Nang q hq (θ - γ)).comp_sub_const θ γ
    have := ((h1.const_mul (C ^ q)).sub (h2.const_mul (r ^ q))).const_mul 2
    convert this using 1
    funext θ'
    exact hS θ'
  have hmin : IsLocalMin (SigmaAng q a B C) θ := Filter.Eventually.of_forall fun θ' => by rw [h0]; exact hnn θ'
  have hz := hmin.hasDerivAt_eq_zero hder
  have hX : C ^ q * Nang q θ = r ^ q * Nang q (θ - γ) := by rw [hS] at h0; linarith
  have hXpos : 0 < r ^ q * Nang q (θ - γ) := mul_pos (Real.rpow_pos_of_pos hr0 _) (Nang_pos q _ (by linarith))
  have hprod : (r ^ q * Nang q (θ - γ)) * (q * (qang q θ - qang q (θ - γ))) = 0 := by
    linear_combination (-1 / 2 : ℝ) * hz + (-q * qang q θ) * hX
  rcases mul_eq_zero.mp hprod with h | h
  · linarith
  · rcases mul_eq_zero.mp h with h' | h'
    · linarith
    · linarith

section Core

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- **Lemma 3.5 (iv), core.** With `θ_*` the maximum angle: there is `θ_f`, `θ_f(0) = θ_*`, real-analytic on `(-a₂, a₂)`,
such that for `0 < a < a₂` the angle `θ_f(a)` is a zero of `Σ_a` within `a` of `θ_*`, and `a ↦ C_a^p` is real-analytic
on `[0, a₂)`. -/
theorem core (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B) (θs : ℝ) (hθs : IsThetaStar p.toReal θs) :
    ∃ θf : ℝ → ℝ, θf 0 = θs ∧ ∃ a₂ : ℝ, 0 < a₂ ∧
      (∀ a : ℝ, 0 < a → a < a₂ → |θf a - θs| ≤ a ∧
        SigmaAng p.toReal a B (matNorm p (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) (θf a) = 0) ∧
      AnalyticOnNhd ℝ θf (Ioo (-a₂) a₂) ∧
      AnalyticOn ℝ (fun a => matNorm p (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) ^ p.toReal)
        (Ico 0 a₂) := by
  have hq2 : 2 < p.toReal := by simpa using (ENNReal.toReal_lt_toReal (by simp) hptop).2 hp
  have hq1 : 1 < p.toReal := by linarith
  have hp1 : 1 < p := lt_of_le_of_lt (by norm_num) hp
  have hB1 : 0 < 1 + B := by linarith
  set q := p.toReal with hqdef
  set C : ℝ → ℝ := fun a => matNorm p (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) with hCdef
  obtain ⟨ψ, hψA, hψ0, ε, hε, huniq⟩ := analytic_branch hq2 hθs
  set γ : ℝ → ℝ := fun a => arctan (a / (1 + B)) with hγdef
  set r : ℝ → ℝ := fun a => √((1 + B) ^ 2 + a ^ 2) with hrdef
  set θf : ℝ → ℝ := fun a => ψ (γ a) with hθfdef
  have hγC : ContDiff ℝ ω γ := contDiff_arctan.comp (contDiff_id.div_const (1 + B))
  have hγ0 : γ 0 = 0 := by simp [hγdef]
  have hθf0 : θf 0 = θs := by simp only [hθfdef, hγ0, hψ0]
  have hγt : Tendsto γ (𝓝 0) (𝓝 0) := by
    have := hγC.continuous.tendsto 0
    rwa [hγ0] at this
  have hθfc : ContinuousAt θf 0 := ContinuousAt.comp_of_eq hψA.continuousAt hγC.continuous.continuousAt hγ0
  have hE1 : ∀ᶠ a in 𝓝 (0 : ℝ), AnalyticAt ℝ ψ (γ a) := hγt.eventually hψA.eventually_analyticAt
  have hE2 : ∀ᶠ a in 𝓝 (0 : ℝ), dist (γ a) 0 < ε := (Metric.tendsto_nhds.mp hγt) ε hε
  have hE3 : ∀ᶠ a in 𝓝 (0 : ℝ), θf a ∈ Ioo 0 (π / 2) :=
    hθfc.eventually_mem (isOpen_Ioo.mem_nhds (hθf0 ▸ mem_Ioo_of_isThetaStar hθs))
  have hE4 : ∀ᶠ a in 𝓝 (0 : ℝ), θf a - γ a ∈ Ioo 0 (π / 2) := by
    have hc : ContinuousAt (fun a => θf a - γ a) 0 := hθfc.sub hγC.continuous.continuousAt
    refine hc.eventually_mem (isOpen_Ioo.mem_nhds ?_)
    simp only [hθf0, hγ0, sub_zero]
    exact mem_Ioo_of_isThetaStar hθs
  obtain ⟨δ₀, hδ₀, hall⟩ := Metric.eventually_nhds_iff.mp (hE1.and (hE2.and (hE3.and hE4)))
  obtain ⟨ρ₀, hρ₀, hSI⟩ := SJ.sigma_interface p hp hptop B hB θs hθs
  obtain ⟨a₁, η, ha₁, hη, hex⟩ := hSI ρ₀ hρ₀ le_rfl
  set a₂ := min δ₀ (min a₁ ε) with ha₂def
  have ha₂δ : a₂ ≤ δ₀ := min_le_left _ _
  have ha₂a₁ : a₂ ≤ a₁ := (min_le_right _ _).trans (min_le_left _ _)
  have ha₂ε : a₂ ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  have hin : ∀ a ∈ Ioo (-a₂) a₂, dist a 0 < δ₀ := fun a ha => by
    rw [Real.dist_eq, sub_zero, abs_lt]; exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hθfA : AnalyticOnNhd ℝ θf (Ioo (-a₂) a₂) := fun a ha =>
    (hall (hin a ha)).1.comp (hγC.contDiffAt.analyticAt)
  -- the zeros
  have hzero : ∀ a : ℝ, 0 < a → a < a₂ → |θf a - θs| ≤ a ∧ SigmaAng q a B (C a) (θf a) = 0 := by
    intro a ha ha'
    obtain ⟨θa, hθa, hz, -⟩ := hex a ha (lt_of_lt_of_le ha' ha₂a₁)
    have hcrit := qang_eq_of_sigma_zero hq1 hB1 (fun θ' => sigmaAng_nonneg p hp1 hptop a B θ') hz
    have hγpos : 0 < γ a := arctan_pos.mpr (div_pos ha hB1)
    have hγε : γ a < ε := by
      have := (hall (hin a ⟨by linarith, ha'⟩)).2.1
      rw [Real.dist_eq, sub_zero, abs_of_pos hγpos] at this
      exact this
    have heq : θf a = θa := huniq (γ a) θa hγpos hγε (by linarith) hcrit
    rw [heq]
    exact ⟨hθa, hz⟩
  have ha₂pos : 0 < a₂ := lt_min hδ₀ (lt_min ha₁ hε)
  refine ⟨θf, hθf0, a₂, ha₂pos, hzero, hθfA, ?_⟩
  -- `C_a^q = r^q N(θ_f - γ) / N(θ_f)` on `[0, a₂)`
  set K : ℝ → ℝ := fun a => r a ^ q * Nang q (θf a - γ a) / Nang q (θf a) with hKdef
  have hrpos : ∀ a, 0 < r a := fun a => Real.sqrt_pos.mpr (by positivity)
  have hpoly : ContDiff ℝ ω (fun a : ℝ => (1 + B) ^ 2 + a ^ 2) := contDiff_const.add (contDiff_id.pow 2)
  have hKA : AnalyticOnNhd ℝ K (Ioo (-a₂) a₂) := by
    intro a ha
    obtain ⟨-, -, hE3a, hE4a⟩ := hall (hin a ha)
    have hrC : ContDiffAt ℝ ω r a := (contDiffAt_sqrt (by positivity)).comp a hpoly.contDiffAt
    have hrq : ContDiffAt ℝ ω (fun a => r a ^ q) a := (contDiffAt_rpow_const_of_ne (hrpos a).ne').comp a hrC
    have hNg1 : ContDiffAt ℝ ω (Nang q) (θf a - γ a) := contDiffAt_Nang hE4a
    have hN1 : ContDiffAt ℝ ω (fun a => Nang q (θf a - γ a)) a := by
      have h := hNg1.comp a ((hθfA a ha).contDiffAt.sub hγC.contDiffAt)
      exact h
    have hN2 : ContDiffAt ℝ ω (fun a => Nang q (θf a)) a := (contDiffAt_Nang (q := q) hE3a).comp a (hθfA a ha).contDiffAt
    exact ((hrq.mul hN1).div hN2 (Nang_pos q _ (by linarith)).ne').analyticAt
  have hEq : EqOn (fun a => C a ^ q) K (Ico 0 a₂) := by
    intro a ha
    rcases eq_or_lt_of_le ha.1 with h0 | hpos
    · subst h0
      have hM0 : ∀ θ, SJ.Mf q 0 B θ = (1 + B) ^ q * Nang q θ := fun θ => by
        rw [SJ.Mf_eq hB1.le (β := 0) (by simp) (by simp) θ, sub_zero]
      obtain ⟨θ₀, h₀⟩ := SJ.exists_Mf_eq_matNorm p hptop 0 B
      rw [hM0] at h₀
      have hC0 : C 0 ^ q = (1 + B) ^ q :=
        mul_right_cancel₀ (Nang_pos q θ₀ (by linarith)).ne' h₀
      have hr0 : r 0 = 1 + B := by simp [hrdef, Real.sqrt_sq hB1.le]
      simp only [hKdef, hθf0, hγ0, sub_zero, hr0]
      rw [hC0, mul_div_assoc, div_self (Nang_pos q θs (by linarith)).ne', mul_one]
    · obtain ⟨-, hz⟩ := hzero a hpos ha.2
      obtain ⟨hrc, hrs⟩ := polar_Pa hB1 a
      rw [SJ.SigmaAng_eq, SJ.Mf_eq (hrpos a).le hrc hrs] at hz
      have hz' : 2 * (C a ^ q * Nang q (θf a) - r a ^ q * Nang q (θf a - γ a)) = 0 := hz
      have hN : 0 < Nang q (θf a) := Nang_pos q _ (by linarith)
      simp only [hKdef]
      rw [eq_div_iff hN.ne']
      linarith
  exact (hKA.analyticOn.mono fun x hx => ⟨by linarith [hx.1], hx.2⟩).congr hEq

end Core

end Matsaev.Lem35iv
