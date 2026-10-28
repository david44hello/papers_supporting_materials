/-
Matsaev/TK/Moving.lean — the angle form of `Q` and the moving-average localization used for the inequality of Lemma 4.1.
Paper: "Matsaev's (1971) conjecture is false for every p != 2", Dave Goel, short v2.00 (md5 a9b3c6be), Lemma 4.1 (`lem:TK`).

Notation: `e(φ) = (cos φ, sin φ)`, `nT q φ = ‖e(φ)‖_q^q`, `Th q φ = Q(e(φ))`.
(I)  `(log nT)' = -q Th`; `Th` has period `π/2`; on `[0, π/4]`, `Th = d ∘ tan` rises strictly up to `θ* = arctan t*`
     and falls strictly after it; `Th'(θ*) = 0`.
(II) `Lb q β φ = log nT(φ - β) - log nT(φ)` (the log of the ratio `‖R_β e(φ)‖^q / ‖e(φ)‖^q`). By the mean value
     theorem `Lb q β φ = q β Th(ξ)` for some `ξ ∈ (φ - β, φ)`. KEY (`key_localization`): at any maximum point `φw` of
     `Lb q β`, `D* - Th(φw - β) ≤ η β` once `β` is small. This replaces the paper's implicit-function argument.
-/
import Matsaev.Scalar.N1
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.ToIntervalMod

namespace Matsaev

namespace TK

open Real Set Filter Topology

/-! ### (I) The angle form -/

/-- `φ(t) = |t|^(q-2) t`, the form in which Mathlib states the derivative of `|t|^q`. -/
lemma phi_eq_abs_rpow (q t : ℝ) : phi q t = |t| ^ (q - 2) * t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [phi]
  · have hab : |t| ≠ 0 := abs_ne_zero.mpr ht
    have h1 : |t| ^ (q - 1) = |t| ^ (q - 2) * |t| := by
      rw [show q - 1 = (q - 2) + 1 by ring, Real.rpow_add_one hab]
    rw [phi, h1]
    linear_combination |t| ^ (q - 2) * sign_mul_abs t

/-- `nT q φ = |cos φ|^q + |sin φ|^q = ‖e(φ)‖_q^q`. -/
noncomputable def nT (q φ : ℝ) : ℝ := |cos φ| ^ q + |sin φ| ^ q

/-- `Th q φ = Q(cos φ, sin φ)`. -/
noncomputable def Th (q φ : ℝ) : ℝ := Qf q (cos φ) (sin φ)

lemma cos_sin_ne_zero (φ : ℝ) : (cos φ, sin φ) ≠ (0, 0) := by
  intro h
  simp only [Prod.mk.injEq] at h
  have := sin_sq_add_cos_sq φ
  rw [h.1, h.2] at this
  norm_num at this

lemma nT_pos {q : ℝ} (_hq : 0 < q) (φ : ℝ) : 0 < nT q φ := by
  unfold nT
  have h1 := rpow_nonneg (abs_nonneg (cos φ)) q
  have h2 := rpow_nonneg (abs_nonneg (sin φ)) q
  rcases eq_or_ne (cos φ) 0 with h | h
  · have hs : sin φ ≠ 0 := fun hs => cos_sin_ne_zero φ (by rw [h, hs])
    have := rpow_pos_of_pos (abs_pos.mpr hs) q
    linarith
  · have := rpow_pos_of_pos (abs_pos.mpr h) q
    linarith

lemma nT_mul_Th {q : ℝ} (hq : 0 < q) (φ : ℝ) :
    nT q φ * Th q φ = phi q (cos φ) * sin φ - phi q (sin φ) * cos φ := by
  have h := (nT_pos hq φ).ne'
  unfold nT at h ⊢
  unfold Th Qf
  field_simp

lemma hasDerivAt_nT {q : ℝ} (hq : 1 < q) (φ : ℝ) :
    HasDerivAt (nT q) (-q * (nT q φ * Th q φ)) φ := by
  have hc := (hasDerivAt_abs_rpow (cos φ) hq).comp φ (hasDerivAt_cos φ)
  have hs := (hasDerivAt_abs_rpow (sin φ) hq).comp φ (hasDerivAt_sin φ)
  refine (hc.add hs).congr_deriv ?_
  rw [nT_mul_Th (by linarith) φ, phi_eq_abs_rpow, phi_eq_abs_rpow]
  ring

lemma hasDerivAt_log_nT {q : ℝ} (hq : 1 < q) (φ : ℝ) :
    HasDerivAt (fun x => Real.log (nT q x)) (-q * Th q φ) φ := by
  have hn := (nT_pos (by linarith : (0 : ℝ) < q) φ).ne'
  refine ((hasDerivAt_nT hq φ).log hn).congr_deriv ?_
  field_simp

lemma Th_add_pi_div_two (q φ : ℝ) : Th q (φ + π / 2) = Th q φ := by
  unfold Th
  rw [cos_add_pi_div_two, sin_add_pi_div_two]
  have h1 := Qf_neg q (sin φ) (-cos φ)
  rw [neg_neg] at h1
  rw [h1, Qf_J]

lemma Th_periodic (q : ℝ) : Function.Periodic (Th q) (π / 2) := fun φ => Th_add_pi_div_two q φ

lemma Th_le_Dstar {q : ℝ} (hq : 2 < q) (φ : ℝ) : Th q φ ≤ Dstar q := by
  obtain ⟨t, -, -, -, -, hle, hD, -, -⟩ := lemma_3_3_proved q hq
  rw [hD]
  exact hle _ _ (cos_sin_ne_zero φ)

/-- The chart `(-π/2, π/2)`: `Th q φ = Q(1, tan φ)`. -/
lemma Th_eq_Qf_one_tan {q : ℝ} (hq : 1 < q) {φ : ℝ} (hφ : φ ∈ Ioo (-(π / 2)) (π / 2)) :
    Th q φ = Qf q 1 (tan φ) := by
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo hφ
  unfold Th
  rw [← Qf_homog q hq (cos φ) 1 (tan φ) hc.ne', mul_one, tan_eq_sin_div_cos, mul_div_cancel₀ _ hc.ne']

lemma dfun_zero {q : ℝ} (hq : 1 < q) : dfun q 0 = 0 := by
  unfold dfun
  rw [zero_rpow (by linarith : q - 1 ≠ 0)]
  ring

lemma Th_eq_dfun_tan {q : ℝ} (hq : 1 < q) {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ < π / 2) :
    Th q φ = dfun q (tan φ) := by
  rcases h0.lt_or_eq with h0 | rfl
  · rw [Th_eq_Qf_one_tan hq ⟨by linarith [pi_pos], h1⟩, Qf_one q _ (tan_pos_of_pos_of_lt_pi_div_two h0 h1)]
  · rw [tan_zero, dfun_zero hq]
    simp [Th, Qf, phi]

lemma Th_nonpos {q : ℝ} (hq : 2 < q) {φ : ℝ} (h0 : φ ≤ 0) (h1 : -(π / 4) ≤ φ) : Th q φ ≤ 0 := by
  have hpi := pi_pos
  rw [Th_eq_Qf_one_tan (by linarith) ⟨by linarith, by linarith⟩]
  apply Qf_one_nonpos_of_nonpos hq
  · have h := strictMonoOn_tan.monotoneOn (a := -(π / 4)) (b := φ) ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ h1
    rwa [tan_neg, tan_pi_div_four] at h
  · exact tan_nonpos_of_nonpos_of_neg_pi_div_two_le h0 (by linarith)

/-! ### The extremal angle `θ* = arctan t*` -/

section Tstar

variable {q t : ℝ} (hq : 2 < q) (ht : t ∈ Ioo (0 : ℝ) 1) (hgt : gN1 q t = 0)

include ht in
lemma arctan_mem : 0 < arctan t ∧ arctan t < π / 4 := by
  refine ⟨arctan_pos.mpr ht.1, ?_⟩
  rw [← arctan_one]
  exact arctan_strictMono ht.2

include hq ht in
lemma Th_arctan : Th q (arctan t) = dfun q t := by
  have h := arctan_mem ht
  rw [Th_eq_dfun_tan (by linarith) h.1.le (by linarith [pi_pos]), tan_arctan]

include hq ht in
/-- On `[0, θ*]` the tangent stays in `[0, t*]`, and `Th = d ∘ tan` there. -/
lemma tan_mem_of_mem_Icc_left {z : ℝ} (hz : z ∈ Icc 0 (arctan t)) :
    tan z ∈ Icc 0 t ∧ Th q z = dfun q (tan z) := by
  have h := arctan_mem ht
  have hpi := pi_pos
  have hmono := strictMonoOn_tan.monotoneOn
  refine ⟨⟨?_, ?_⟩, Th_eq_dfun_tan (by linarith) hz.1 (by linarith [hz.2])⟩
  · have := hmono (a := 0) (b := z) ⟨by linarith, by linarith⟩ ⟨by linarith [hz.1], by linarith [hz.2]⟩ hz.1
    rwa [tan_zero] at this
  · have := hmono (a := z) (b := arctan t) ⟨by linarith [hz.1], by linarith [hz.2]⟩
      ⟨by linarith, by linarith⟩ hz.2
    rwa [tan_arctan] at this

include hq ht in
/-- On `[θ*, π/4]` the tangent stays in `[t*, 1]`, and `Th = d ∘ tan` there. -/
lemma tan_mem_of_mem_Icc_right {z : ℝ} (hz : z ∈ Icc (arctan t) (π / 4)) :
    tan z ∈ Icc t 1 ∧ Th q z = dfun q (tan z) := by
  have h := arctan_mem ht
  have hpi := pi_pos
  have hmono := strictMonoOn_tan.monotoneOn
  refine ⟨⟨?_, ?_⟩, Th_eq_dfun_tan (by linarith) (by linarith [hz.1]) (by linarith [hz.2])⟩
  · have := hmono (a := arctan t) (b := z) ⟨by linarith, by linarith⟩
      ⟨by linarith [hz.1], by linarith [hz.2]⟩ hz.1
    rwa [tan_arctan] at this
  · have := hmono (a := z) (b := π / 4) ⟨by linarith [hz.1], by linarith [hz.2]⟩
      ⟨by linarith, by linarith⟩ hz.2
    rwa [tan_pi_div_four] at this

include hq ht hgt in
lemma Th_strictMonoOn : StrictMonoOn (Th q) (Icc 0 (arctan t)) := by
  intro x hx y hy hxy
  obtain ⟨hxI, hxe⟩ := tan_mem_of_mem_Icc_left hq ht hx
  obtain ⟨hyI, hye⟩ := tan_mem_of_mem_Icc_left hq ht hy
  have h := arctan_mem ht
  have hpi := pi_pos
  rw [hxe, hye]
  exact strictMonoOn_dfun hq ht hgt hxI hyI
    (strictMonoOn_tan ⟨by linarith [hx.1], by linarith [hx.2]⟩ ⟨by linarith [hy.1], by linarith [hy.2]⟩ hxy)

include hq ht hgt in
lemma Th_strictAntiOn : StrictAntiOn (Th q) (Icc (arctan t) (π / 4)) := by
  intro x hx y hy hxy
  obtain ⟨hxI, hxe⟩ := tan_mem_of_mem_Icc_right hq ht hx
  obtain ⟨hyI, hye⟩ := tan_mem_of_mem_Icc_right hq ht hy
  have h := arctan_mem ht
  have hpi := pi_pos
  rw [hxe, hye]
  exact strictAntiOn_dfun hq ht hgt hxI hyI
    (strictMonoOn_tan ⟨by linarith [hx.1], by linarith [hx.2]⟩ ⟨by linarith [hy.1], by linarith [hy.2]⟩ hxy)

include hq ht hgt in
/-- `Th'(θ*) = 0`. -/
lemma hasDerivAt_Th_arctan : HasDerivAt (Th q) 0 (arctan t) := by
  have h := arctan_mem ht
  have hpi := pi_pos
  have hcos : cos (arctan t) ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).ne'
  have h1 := (hasDerivAt_dfun (p := q) (s := tan (arctan t)) (by rw [tan_arctan]; exact ht.1)).comp (arctan t)
    (hasDerivAt_tan hcos)
  rw [tan_arctan, hgt, zero_div, zero_mul] at h1
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds h.1 (by linarith : arctan t < π / 2)] with x hx
  exact Th_eq_dfun_tan (by linarith) hx.1.le hx.2

include hq ht hgt in
/-- The window around `θ*`: `θlo = θ*/2`, `θhi = (θ* + π/4)/2`, and `m = max Th(θlo) Th(θhi)` satisfies
`0 < m < Th(θ*)`; every `φ` with `Th φ > m` is congruent mod `π/2` to a point of `(θlo, θhi)`. -/
lemma window :
    ∃ m : ℝ, 0 < m ∧ m < Th q (arctan t) ∧
      ∀ φ : ℝ, m < Th q φ → ∃ k : ℤ, φ - k * (π / 2) ∈ Ioo (arctan t / 2) ((arctan t + π / 4) / 2) := by
  have h := arctan_mem ht
  have hpi := pi_pos
  set θs := arctan t with hθs
  set θlo := θs / 2 with hθlo
  set θhi := (θs + π / 4) / 2 with hθhi
  have hloI : θlo ∈ Icc 0 θs := ⟨by linarith, by linarith⟩
  have hsI : θs ∈ Icc 0 θs := ⟨h.1.le, le_rfl⟩
  have hsI' : θs ∈ Icc θs (π / 4) := ⟨le_rfl, h.2.le⟩
  have hhiI : θhi ∈ Icc θs (π / 4) := ⟨by linarith, by linarith⟩
  have hlo_lt : Th q θlo < Th q θs := Th_strictMonoOn hq ht hgt hloI hsI (by linarith)
  have hhi_lt : Th q θhi < Th q θs := Th_strictAntiOn hq ht hgt hsI' hhiI (by linarith)
  have hlo_pos : 0 < Th q θlo := by
    obtain ⟨hI, he⟩ := tan_mem_of_mem_Icc_left hq ht hloI
    rw [he]
    refine dfun_pos hq ⟨tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith), ?_⟩
    exact lt_of_le_of_lt (by
      have := strictMonoOn_tan.monotoneOn (a := θlo) (b := θs) ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ (by linarith)
      rwa [hθs, tan_arctan] at this) ht.2
  refine ⟨max (Th q θlo) (Th q θhi), lt_max_of_lt_left hlo_pos, max_lt hlo_lt hhi_lt, ?_⟩
  intro φ hφ
  have hp2 : (0 : ℝ) < π / 2 := by positivity
  set k := toIcoDiv hp2 (-(π / 4)) φ
  have hmod := toIcoMod_add_toIcoDiv_zsmul hp2 (-(π / 4)) φ
  have hmem := toIcoMod_mem_Ico hp2 (-(π / 4)) φ
  set φ' := toIcoMod hp2 (-(π / 4)) φ
  have hφ' : φ' = φ - k * (π / 2) := by rw [zsmul_eq_mul] at hmod; linarith
  have hTh : Th q φ' = Th q φ := by
    rw [hφ', ← zsmul_eq_mul]
    exact (Th_periodic q).sub_zsmul_eq k
  refine ⟨k, ?_⟩
  rw [← hφ']
  rw [← hTh] at hφ
  have hφ'2 : φ' < π / 4 := by linarith [hmem.2]
  rcases le_or_gt φ' 0 with hneg | hpos
  · exfalso
    have := Th_nonpos hq hneg hmem.1
    linarith [le_max_left (Th q θlo) (Th q θhi)]
  · refine ⟨?_, ?_⟩
    · by_contra hle
      rw [not_lt] at hle
      have := Th_strictMonoOn hq ht hgt |>.monotoneOn ⟨hpos.le, by linarith⟩ hloI hle
      linarith [le_max_left (Th q θlo) (Th q θhi)]
    · by_contra hge
      rw [not_lt] at hge
      have := Th_strictAntiOn hq ht hgt |>.antitoneOn hhiI ⟨by linarith, hφ'2.le⟩ hge
      linarith [le_max_right (Th q θlo) (Th q θhi)]

end Tstar

/-! ### (II) The moving average -/

/-- `Lb q β φ = log ‖e(φ - β)‖_q^q - log ‖e(φ)‖_q^q`. -/
noncomputable def Lb (q β φ : ℝ) : ℝ := Real.log (nT q (φ - β)) - Real.log (nT q φ)

lemma hasDerivAt_Lb {q : ℝ} (hq : 1 < q) (β φ : ℝ) :
    HasDerivAt (Lb q β) (q * Th q φ - q * Th q (φ - β)) φ := by
  have h1 := (hasDerivAt_log_nT hq (φ - β)).comp φ ((hasDerivAt_id' φ).sub_const β)
  have h2 := hasDerivAt_log_nT hq φ
  exact (h1.sub h2).congr_deriv (by ring)

/-- Mean value theorem: `Lb q β φ = q β Th(ξ)` for some `ξ ∈ (φ - β, φ)`. -/
lemma Lb_eq_mvt {q : ℝ} (hq : 1 < q) {β : ℝ} (hβ : 0 < β) (φ : ℝ) :
    ∃ ξ ∈ Ioo (φ - β) φ, Lb q β φ = q * β * Th q ξ := by
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope (fun x => Real.log (nT q x)) (fun x => -q * Th q x)
    (by linarith : φ - β < φ)
    (fun x _ => (hasDerivAt_log_nT hq x).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_log_nT hq x)
  refine ⟨ξ, hξ, ?_⟩
  rw [show φ - (φ - β) = β by ring, eq_div_iff hβ.ne'] at h
  unfold Lb
  linear_combination h

/-- At a maximum point of `Lb q β`: `Th(φw - β) = Th(φw)`. -/
lemma Th_eq_of_isMax {q : ℝ} (hq : 1 < q) {β φw : ℝ} (hmax : ∀ φ, Lb q β φ ≤ Lb q β φw) :
    Th q (φw - β) = Th q φw := by
  have hloc : IsLocalMax (Lb q β) φw := Filter.Eventually.of_forall hmax
  have h := hloc.hasDerivAt_eq_zero (hasDerivAt_Lb hq β φw)
  have hq0 : q ≠ 0 := by linarith
  have : q * (Th q φw - Th q (φw - β)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hq0
  · linarith

/-- KEY: at any maximum point `φw` of `Lb q β`, `D* - Th(φw - β) ≤ η β`, once `β` is small. -/
theorem key_localization {q : ℝ} (hq : 2 < q) {η : ℝ} (hη : 0 < η) :
    ∃ β₁ : ℝ, 0 < β₁ ∧ ∀ β : ℝ, 0 < β → β < β₁ → ∀ φw : ℝ, (∀ φ, Lb q β φ ≤ Lb q β φw) →
      Dstar q - Th q (φw - β) ≤ η * β := by
  obtain ⟨t, ht, hcrit, -, -, -, hD, -, -⟩ := lemma_3_3_proved q hq
  have hgt : gN1 q t = 0 := by
    have h0 := (hcrit t ht).mpr rfl
    rw [(hasDerivAt_dfun ht.1).deriv, div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact h0
    · exfalso
      have : 0 < 1 + t ^ q := by have := rpow_nonneg ht.1.le q; linarith
      exact (pow_pos this 2).ne' h0
  have hq1 : 1 < q := by linarith
  have hpi := pi_pos
  have hθ := arctan_mem ht
  set θs := arctan t with hθs
  have hThs : Th q θs = Dstar q := by rw [hD]; exact Th_arctan hq ht
  obtain ⟨m, hm0, hmD, hwin⟩ := window hq ht hgt
  -- continuity of `Th` at `θ*`: `Th > m` within `δ₁`
  have hcont := (hasDerivAt_Th_arctan hq ht hgt).continuousAt
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually (lt_mem_nhds hmD))
  -- `Th'(θ*) = 0`: `|Th(θ* + h) - D*| ≤ η |h|` within `δ₂`
  have hlo := (hasDerivAt_iff_isLittleO_nhds_zero.mp (hasDerivAt_Th_arctan hq ht hgt)).def hη
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.eventually_nhds_iff.mp hlo
  refine ⟨min (min δ₁ δ₂) (min (θs / 2) (π / 4 - (θs + π / 4) / 2)), ?_, ?_⟩
  · refine lt_min (lt_min hδ₁ hδ₂) (lt_min (by linarith) (by linarith))
  intro β hβ hβ₁ φw hmax
  have hβδ₁ : β < δ₁ := lt_of_lt_of_le hβ₁ ((min_le_left _ _).trans (min_le_left _ _))
  have hβδ₂ : β < δ₂ := lt_of_lt_of_le hβ₁ ((min_le_left _ _).trans (min_le_right _ _))
  have hβlo : β < θs / 2 := lt_of_lt_of_le hβ₁ ((min_le_right _ _).trans (min_le_left _ _))
  have hβhi : β < π / 4 - (θs + π / 4) / 2 := lt_of_lt_of_le hβ₁ ((min_le_right _ _).trans (min_le_right _ _))
  -- the two mean-value points
  obtain ⟨ξs, hξs, hLs⟩ := Lb_eq_mvt hq1 hβ θs
  obtain ⟨ξw, hξw, hLw⟩ := Lb_eq_mvt hq1 hβ φw
  have hξs_m : m < Th q ξs := by
    apply hδ₁'
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hξs.1, hξs.2]
  have hξw_m : m < Th q ξw := by
    have hle := hmax θs
    rw [hLs, hLw] at hle
    have hqβ : 0 < q * β := by positivity
    have := le_of_mul_le_mul_left hle hqβ
    linarith
  -- shift everything by `k π/2` into the window
  obtain ⟨k, hk⟩ := hwin ξw hξw_m
  set s := (k : ℝ) * (π / 2)
  have hper : ∀ x, Th q (x - s) = Th q x := by
    intro x
    rw [show s = k • (π / 2) by rw [zsmul_eq_mul]]
    exact (Th_periodic q).sub_zsmul_eq k
  have hφ'_lo : 0 < φw - s - β := by linarith [hk.1, hξw.2]
  have hφ'_hi : φw - s < π / 4 := by linarith [hk.2, hξw.1]
  have heq : Th q (φw - s - β) = Th q (φw - s) := by
    rw [show φw - s - β = (φw - β) - s by ring, hper, hper]
    exact Th_eq_of_isMax hq1 hmax
  -- unimodality puts `θ*` strictly between `φ' - β` and `φ'`
  have hgt' : θs < φw - s := by
    by_contra hle
    rw [not_lt] at hle
    have := Th_strictMonoOn hq ht hgt ⟨by linarith, by linarith⟩ ⟨by linarith, hle⟩
      (by linarith : φw - s - β < φw - s)
    linarith
  have hlt' : φw - s - β < θs := by
    by_contra hle
    rw [not_lt] at hle
    have := Th_strictAntiOn hq ht hgt ⟨hle, by linarith⟩ ⟨by linarith, hφ'_hi.le⟩
      (by linarith : φw - s - β < φw - s)
    linarith
  -- the first-order estimate at `θ*`
  set h := φw - s - β - θs with hh
  have hh_abs : |h| < β := by rw [abs_lt]; constructor <;> linarith
  have hest := hδ₂' (y := h) (by rw [Real.dist_eq, sub_zero]; linarith)
  simp only [smul_zero, sub_zero, Real.norm_eq_abs] at hest
  rw [show θs + h = φw - s - β by rw [hh]; ring, hThs] at hest
  have hTw : Th q (φw - β) = Th q (φw - s - β) := by
    rw [show φw - s - β = (φw - β) - s by ring, hper]
  rw [hTw]
  have := (abs_le.mp hest).1
  nlinarith [abs_nonneg h]

end TK

end Matsaev
