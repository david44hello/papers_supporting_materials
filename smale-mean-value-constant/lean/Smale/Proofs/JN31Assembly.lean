/-
Smale/Proofs/JN31Assembly.lean — [JN, Prop. 3.1] as a theorem, at the exact type of the former citation. For `p ∈ 𝓟_d`,
`1 < R < m(p)`, `q = p/X`: the component `Ω` of `{|q| < R}` containing `0` has a Riemann map, whose inverse `φ` gives
`W = φ/φ'(0)` and `B = (q ∘ φ)/R`, a finite Blaschke product of degree at most `d - 1`.
-/
import Smale.Proofs.JN31Blaschke
import Smale.Proofs.JN31Domain
import Smale.Proofs.JN31Root
import Smale.Proofs.JN31Runge
import Smale.Proofs.Lemma53
import Smale.Proofs.UnivInverse

namespace Smale

open Polynomial Complex Metric Set Filter Topology

/-- A continuous function below `R` on a compact set stays below some `T < R`. -/
theorem exists_lt_forall_le_of_isCompact {K : Set ℂ} (hK : IsCompact K) {g : ℂ → ℝ} (hg : ContinuousOn g K) {R : ℝ}
    (h : ∀ z ∈ K, g z < R) : ∃ T < R, ∀ z ∈ K, g z ≤ T := by
  obtain ⟨a, ha, hle⟩ := hK.exists_forall_le' hg.neg (a := -R) fun z hz => neg_lt_neg (h z hz)
  exact ⟨-a, by linarith, fun z hz => by have := hle z hz; simp only [Pi.neg_apply] at this; linarith⟩

/-- **The lemniscate component has square roots.** -/
theorem lemComp_isRootDomain {q : ℂ[X]} (hq : 0 < q.natDegree) {R : ℝ} (h0 : ‖q.eval 0‖ < R) :
    IsRootDomain (lemComp q R) := by
  refine isRootDomain_of_primitive (lemComp_isOpen q R) (lemComp_isPreconnected q R) fun G hG => ?_
  set t : ℕ → ℝ := fun n => R - 1 / ((n : ℝ) + 1) with htdef
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have ht : ∀ n, t n < R := fun n => by
    have := hpos n
    simp only [htdef]
    linarith
  choose P hP using fun n : ℕ =>
    runge_poly (lemComp_sublevel_isCompact hq (ht n)) (lemComp_sublevel_compl_isPreconnected hq (ht n))
      (lemComp_isOpen q R) inter_subset_left hG (hpos n)
  refine exists_primitive_of_poly_approx (lemComp_isOpen q R) (lemComp_isPreconnected q R) (mem_lemComp_zero h0)
    (P := P) ?_
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (lemComp_isOpen q R)]
  intro K hKU hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hcont : ContinuousOn (fun z => ‖q.eval z‖) K := by fun_prop
  obtain ⟨T, hTR, hT⟩ := exists_lt_forall_le_of_isCompact hK hcont fun z hz => lemComp_lt (hKU hz)
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε := hlim.eventually (gt_mem_nhds hε)
  have h2 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < R - T := hlim.eventually (gt_mem_nhds (sub_pos.2 hTR))
  filter_upwards [h1, h2] with n hn1 hn2 z hz
  have hzK : z ∈ lemComp q R ∩ {z | ‖q.eval z‖ ≤ t n} := by
    refine ⟨hKU hz, ?_⟩
    have := hT z hz
    show ‖q.eval z‖ ≤ R - 1 / ((n : ℝ) + 1)
    linarith
  rw [dist_comm, dist_eq_norm]
  exact (hP n z hzK).trans hn1

/-- **The Riemann map of the lemniscate component.** -/
theorem lemComp_riemann {q : ℂ[X]} (hq : 0 < q.natDegree) {R : ℝ} (h0 : ‖q.eval 0‖ < R) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (lemComp q R) ∧ BijOn f (lemComp q R) (ball 0 1) ∧ f 0 = 0 :=
  exists_bijOn_unitBall_of_isRootDomain (lemComp_isOpen q R) (lemComp_isPreconnected q R) (lemComp_isBounded hq R)
    (lemComp_isRootDomain hq h0) (mem_lemComp_zero h0)

/-- **The collar**: near the unit circle, `|q ∘ φ|` is near `R`. -/
theorem lemComp_collar {q : ℂ[X]} (hq : 0 < q.natDegree) {R : ℝ} {f φ : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f (lemComp q R)) (hfm : MapsTo f (lemComp q R) (ball 0 1))
    (hφ : ∀ z ∈ disk, φ z ∈ lemComp q R) (hfφ : ∀ z ∈ disk, f (φ z) = z) {t : ℝ} (ht : t < R) :
    ∃ r, 0 ≤ r ∧ r < 1 ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ < 1 → t < ‖q.eval (φ z)‖ := by
  have hK := lemComp_sublevel_isCompact hq ht
  have hcont : ContinuousOn (fun z => ‖f z‖) (lemComp q R ∩ {z | ‖q.eval z‖ ≤ t}) :=
    (hfd.continuousOn.mono inter_subset_left).norm
  obtain ⟨a, ha1, ha⟩ := exists_lt_forall_le_of_isCompact hK hcont fun z hz => by simpa using hfm hz.1
  have hmax : max a 0 < 1 := max_lt ha1 one_pos
  refine ⟨(max a 0 + 1) / 2, by have := le_max_right a 0; linarith, by linarith, fun z hzr hz1 => ?_⟩
  by_contra hle
  have hzd : z ∈ disk := by simpa using hz1
  have h1 := ha (φ z) ⟨hφ z hzd, not_lt.1 hle⟩
  rw [hfφ z hzd] at h1
  have := le_max_left a 0
  linarith

set_option linter.unusedVariables false in
/-- **[JN, Prop. 3.1]** (A. Jatar and T. W. Ng, "Smale's mean value constant and admissible univalent Blaschke pairs",
arXiv:2610.21472v2, an unrefereed preprint; sketched in the paper's Remark 2.3, tex l.200-208), verbatim:
"Let $P\in\cP_d$ with $S(P)>1$. Suppose $1<R<S(P)$, then there is an admissible pair $(W,B)$ with $$
B(0)=\frac1R,\qquad 1\le\deg B\le d-1 . $$ Consequently for every $d\ge2$, $\Bee_{d-1}\ge S(P)$ for every $P\in\cP_d$ and
hence $\M_d\le\Bee_{d-1}$ and $\M\le\Bee$."
Lean form: the first sentence only (the unindexed form of the "Consequently", `M ≤ 𝓑`, is `rem_2_3_Kstar_le`; the indexed form
is not stated, and the paper does not use it); `B(0) = 1/R` (`B(0) > 0` is part of
admissible) as `1/(B 0).re = R`. JN's notation: 𝒫_d = polynomials of degree d ≥ 2 with P(0) = 0, P'(0) = 1; S(P) =
min_{P'(c)=0} |P(c)/c| (= our `IsPd`, `mval`). The route differs from the one in [JN]; see the headers of the modules imported
here. -/
theorem jatarNg_prop_3_1_proved (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (hm : 1 < mval p) (R : ℝ)
    (hR1 : 1 < R) (hRm : R < mval p) :
    ∃ (W B : ℂ → ℂ) (k : ℕ), 1 ≤ k ∧ k ≤ d - 1 ∧ IsAdmissible W B k ∧ 1 / (B 0).re = R := by
  have hR0 : 0 < R := by linarith
  set q : ℂ[X] := p.divX with hqdef
  have hpq : p = X * q := by
    have h := Polynomial.divX_mul_X_add p
    have hc : p.coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero]; exact hp.2.1
    rw [hc, C_0, add_zero] at h
    rw [mul_comm]
    exact h.symm
  have hq0 : q.eval 0 = 1 := by
    have h := hp.2.2
    rw [hpq, derivative_mul, derivative_X, eval_add, eval_mul, eval_mul, eval_one, one_mul, eval_X, zero_mul,
      add_zero] at h
    exact h
  have hqdeg : q.natDegree = d - 1 := by
    rw [hqdef, natDegree_divX_eq_natDegree_tsub_one, hp.1]
  have hqpos : 0 < q.natDegree := by omega
  have hqne : q ≠ 0 := fun h => by simp [h] at hqpos
  have h0 : ‖q.eval 0‖ < R := by rw [hq0, norm_one]; exact hR1
  set Ω := lemComp q R with hΩdef
  have hΩo : IsOpen Ω := lemComp_isOpen q R
  have h0Ω : (0 : ℂ) ∈ Ω := mem_lemComp_zero h0
  -- no critical point of `p` in the lemniscate domain
  have hcrit : ∀ w ∈ Ω, p.derivative.eval w ≠ 0 := by
    intro w hw hzero
    have hne := crit_ne_zero hp hzero
    have h1 := mval_le hzero
    have h2 : ‖p.eval w‖ / ‖w‖ = ‖q.eval w‖ := by
      rw [hpq, eval_mul, eval_X, norm_mul]
      field_simp
    rw [h2] at h1
    have h3 : ‖q.eval w‖ < R := lemComp_lt hw
    linarith
  -- the Riemann map and its inverse
  obtain ⟨f, hfd, hfb, hf0⟩ := lemComp_riemann hqpos h0
  have hfu : IsUnivalentOn f Ω := ⟨hfd, hfb.injOn⟩
  obtain ⟨-, hφu, hφimg, hφl, hφr, -⟩ := univalent_inverse hΩo hfu
  have himg : f '' Ω = disk := hfb.image_eq
  rw [himg] at hφu hφimg hφr
  set φ : ℂ → ℂ := Function.invFunOn f Ω with hφdef
  have hφΩ : ∀ z ∈ disk, φ z ∈ Ω := fun z hz => hφimg ▸ mem_image_of_mem φ hz
  have h0d : (0 : ℂ) ∈ disk := by simp
  have hφ0 : φ 0 = 0 := by
    have := hφl 0 h0Ω
    rwa [hf0] at this
  have hκ : deriv φ 0 ≠ 0 := injOn_deriv_ne_zero isOpen_ball hφu h0d
  set κ : ℂ := deriv φ 0 with hκdef
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
  -- the pair
  set W : ℂ → ℂ := fun z => φ z / κ with hWdef
  set B : ℂ → ℂ := fun z => q.eval (φ z) / R with hBdef
  have hB0 : B 0 = (1 / R : ℝ) := by
    simp only [hBdef, hφ0, hq0]
    push_cast
    rfl
  -- `B` is a finite Blaschke product
  obtain ⟨as, H, hlen, has, hHd, hH0, hHeq⟩ := exists_factor_of_univalent hφu hqne
  have hBlt : ∀ z ∈ disk, ‖B z‖ < 1 := fun z hz => by
    simp only [hBdef, norm_div, Complex.norm_real, Real.norm_of_nonneg hR0.le]
    rw [div_lt_one hR0]
    exact lemComp_lt (hφΩ z hz)
  have hBcollar : ∀ t < (1 : ℝ), ∃ r, 0 ≤ r ∧ r < 1 ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ < 1 → t < ‖B z‖ := by
    intro t ht
    have htR : t * R < R := by nlinarith
    obtain ⟨r, hr0, hr1, hr⟩ := lemComp_collar hqpos hfd hfb.mapsTo hφΩ hφr htR
    refine ⟨r, hr0, hr1, fun z hzr hz1 => ?_⟩
    simp only [hBdef, norm_div, Complex.norm_real, Real.norm_of_nonneg hR0.le]
    rw [lt_div_iff₀ hR0]
    exact hr z hzr hz1
  have hBbl : IsFiniteBlaschke B as.length := by
    refine isFiniteBlaschke_of_factor (H := fun z => H z / R) has (hHd.div_const _)
      (fun z hz => div_ne_zero (hH0 z hz) hRC) (fun z hz => ?_) hBlt hBcollar
    show q.eval (φ z) / R = H z / R * _
    rw [hHeq z hz]
    ring
  refine ⟨W, B, as.length, ?_, by omega, ⟨⟨⟨hφu.1.div_const κ, ?_⟩, ?_, ?_⟩, hBbl, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- `deg B ≥ 1`
    by_contra hk
    have hk0 : as.length = 0 := by omega
    obtain ⟨lam, as', hlam, hlen', -, hEq⟩ := hBbl
    have has' : as' = [] := List.length_eq_zero_iff.1 (hlen'.trans hk0)
    have h1 := hEq h0d
    rw [has', blaschkeProd, List.map_nil, List.prod_nil, mul_one, hB0] at h1
    have h2 := congrArg norm h1
    rw [hlam, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h2
    rw [div_eq_iff hR0.ne'] at h2
    linarith
  · -- `W` injective
    intro a ha b hb hab
    exact hφu.2 ha hb (div_left_inj' hκ |>.1 hab)
  · simp [hWdef, hφ0]
  · -- `W'(0) = 1`
    have h1 : HasDerivAt φ κ 0 := (hφu.1.differentiableAt (isOpen_ball.mem_nhds h0d)).hasDerivAt
    rw [(h1.div_const κ).deriv, div_self hκ]
  · rw [hB0, Complex.ofReal_im]
  · rw [hB0, Complex.ofReal_re]
    positivity
  · -- `(WB)' ≠ 0`
    intro w hw
    have hφw : HasDerivAt φ (deriv φ w) w := (hφu.1.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
    have hpev : ∀ z, W z * B z = p.eval (φ z) / (κ * R) := fun z => by
      simp only [hWdef, hBdef]
      rw [hpq, eval_mul, eval_X]
      field_simp
    have hder : HasDerivAt (fun z => W z * B z) (p.derivative.eval (φ w) * deriv φ w / (κ * R)) w := by
      have h1 := (p.hasDerivAt (φ w)).comp w hφw
      have h2 : (fun z => W z * B z) = (fun z => p.eval (φ z) / (κ * R)) := funext hpev
      rw [h2]
      exact h1.div_const _
    rw [hder.deriv]
    refine div_ne_zero (mul_ne_zero (hcrit _ (hφΩ w hw)) ?_) (mul_ne_zero hκ hRC)
    exact injOn_deriv_ne_zero isOpen_ball hφu hw
  · rw [hB0, Complex.ofReal_re]
    field_simp

end Smale
