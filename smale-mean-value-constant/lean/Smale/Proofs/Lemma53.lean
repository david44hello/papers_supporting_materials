/-
Smale/Proofs/Lemma53.lean — Lemma 5.3 of paper 009 (Crane, tex l.448-465): `K(d+1) ≥ K(d)`. For `p ∈ 𝓟_d` and
`ε ≠ 0`, `p_ε = p + εz^{d+1} ∈ 𝓟_{d+1}`; at a critical point `β` of `p_ε`, `p_ε(β)/β = p(β)/β - p'(β)/(d+1)`; the `d`
critical points of `p_ε` have product of modulus `1/((d+1)|ε|)`; and `m(p_ε) → m(p)` as `ε → 0`:
* upper bound: by Rouché on a small circle around the critical point of `p` where `m(p)` is attained, `p_ε` has a
  critical point close to it (the Hurwitz step of the paper);
* lower bound: on `|w| ≤ R` away from the critical points of `p`, `|p'|` has a positive minimum, so for small `ε` no
  critical point of `p_ε` lies there; for `|β| ≥ R`, `p_ε(β)/β = p(β)/β - p'(β)/(d+1)` is large (a polynomial of degree
  `d - 1 ≥ 1` in `β`).
Also `sec1_m_attained` (`m(p)` is the least of finitely many values).
-/
import Smale.Proofs.ArgPrinciple

namespace Smale

open Polynomial Complex Metric Filter Topology

/-! ### `m(p)` as a minimum (tex l.55) -/

theorem critRatios_bddBelow (q : ℂ[X]) : BddBelow (critRatios q) :=
  ⟨0, fun _ ⟨_, _, hr⟩ => hr ▸ div_nonneg (norm_nonneg _) (norm_nonneg _)⟩

theorem mval_le {q : ℂ[X]} {β : ℂ} (hβ : q.derivative.eval β = 0) : mval q ≤ ‖q.eval β‖ / ‖β‖ :=
  csInf_le (critRatios_bddBelow q) ⟨β, hβ, rfl⟩

theorem le_mval {q : ℂ[X]} {L : ℝ} (hne : ∃ β, q.derivative.eval β = 0)
    (h : ∀ β, q.derivative.eval β = 0 → L ≤ ‖q.eval β‖ / ‖β‖) : L ≤ mval q := by
  obtain ⟨β, hβ⟩ := hne
  exact le_csInf ⟨_, β, hβ, rfl⟩ fun r ⟨γ, hγ, hr⟩ => hr ▸ h γ hγ

theorem crit_ne_zero {d : ℕ} {p : ℂ[X]} (hp : IsPd d p) {β : ℂ} (hβ : p.derivative.eval β = 0) : β ≠ 0 := by
  rintro rfl
  rw [hp.2.2] at hβ
  exact one_ne_zero hβ

/-- tex l.55 ("min"), exactly the Statements type: `critRatios p` is finite and nonempty, and `m(p)` is its least
element. -/
theorem sec1_m_attained_proved (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) :
    (critRatios p).Finite ∧ mval p ∈ critRatios p ∧ ∀ r ∈ critRatios p, mval p ≤ r := by
  have hp' : p.derivative ≠ 0 := fun h => by
    have h1 := hp.2.2
    rw [h, eval_zero] at h1
    exact zero_ne_one h1
  have hfin : (critRatios p).Finite := by
    refine ((p.derivative.roots.toFinset.finite_toSet).image fun β => ‖p.eval β‖ / ‖β‖).subset ?_
    rintro r ⟨β, hβ, rfl⟩
    exact ⟨β, Multiset.mem_toFinset.2 ((mem_roots hp').2 hβ), rfl⟩
  have hdeg : 0 < p.derivative.degree := by
    rw [← natDegree_pos_iff_degree_pos, natDegree_derivative, hp.1]
    omega
  obtain ⟨β, hβ⟩ := Complex.exists_root hdeg
  have hne : (critRatios p).Nonempty := ⟨_, β, hβ.eq_zero, rfl⟩
  exact ⟨hfin, hfin.isClosed.csInf_mem hne (critRatios_bddBelow p), fun r hr => csInf_le (critRatios_bddBelow p) hr⟩

/-! ### `p_ε = p + ε z^{d+1}` -/

theorem eval_eps (p : ℂ[X]) (ε w : ℂ) (d : ℕ) : (p + C ε * X ^ (d + 1)).eval w = p.eval w + ε * w ^ (d + 1) := by
  rw [eval_add, eval_mul, eval_C, eval_pow, eval_X]

theorem derivative_eps (p : ℂ[X]) (ε : ℂ) (d : ℕ) :
    (p + C ε * X ^ (d + 1)).derivative = p.derivative + C (ε * ((d : ℂ) + 1)) * X ^ d := by
  rw [derivative_add, derivative_C_mul_X_pow, Nat.add_sub_cancel, Nat.cast_add_one]

theorem norm_natCast_add_one (d : ℕ) : ‖(d : ℂ) + 1‖ = (d : ℝ) + 1 := by
  rw [← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]

theorem eval_derivative_eps (p : ℂ[X]) (ε w : ℂ) (d : ℕ) :
    (p + C ε * X ^ (d + 1)).derivative.eval w = p.derivative.eval w + ε * ((d : ℂ) + 1) * w ^ d := by
  rw [derivative_eps, eval_add, eval_mul, eval_C, eval_pow, eval_X]

theorem isPd_eps {d : ℕ} (hd : 2 ≤ d) {p : ℂ[X]} (hp : IsPd d p) {ε : ℂ} (hε : ε ≠ 0) :
    IsPd (d + 1) (p + C ε * X ^ (d + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [natDegree_add_eq_right_of_natDegree_lt (by rw [natDegree_C_mul_X_pow _ _ hε, hp.1]; omega),
      natDegree_C_mul_X_pow _ _ hε]
  · rw [eval_eps, hp.2.1, zero_pow (by omega), mul_zero, add_zero]
  · rw [eval_derivative_eps, hp.2.2, zero_pow (by omega), mul_zero, add_zero]

/-- A critical point of `p_ε` is not `0`. -/
theorem crit_eps_ne_zero {d : ℕ} (hd : 2 ≤ d) {p : ℂ[X]} (hp : IsPd d p) {ε β : ℂ}
    (hβ : (p + C ε * X ^ (d + 1)).derivative.eval β = 0) : β ≠ 0 := by
  rintro rfl
  rw [eval_derivative_eps, hp.2.2, zero_pow (by omega), mul_zero, add_zero] at hβ
  exact one_ne_zero hβ

/-- Lemma 5.3, proof (tex l.457-461), exactly the Statements type: at a critical point `β` of `p_ε`,
`p_ε(β)/β = p(β)/β - p'(β)/(d+1)`. -/
theorem lem_5_3_identity_proved (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (ε β : ℂ) (_hε : ε ≠ 0)
    (hβ : (p + C ε * X ^ (d + 1)).derivative.eval β = 0) :
    (p + C ε * X ^ (d + 1)).eval β / β = p.eval β / β - p.derivative.eval β / ((d : ℂ) + 1) := by
  have hβ0 := crit_eps_ne_zero hd hp hβ
  rw [eval_derivative_eps] at hβ
  have hd1 : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  have h2 : p.derivative.eval β / ((d : ℂ) + 1) = -(ε * β ^ d) := by
    rw [div_eq_iff hd1]
    linear_combination hβ
  rw [h2, eval_eps, pow_succ, ← mul_assoc, add_div, mul_div_cancel_right₀ _ hβ0]
  ring

/-- Lemma 5.3, proof (tex l.456-457), exactly the Statements type: `p_ε'` has `d` roots, with product of modulus
`1/((d+1)|ε|)` (Vieta: `p_ε'(0) = 1` and the leading coefficient is `(d+1)ε`). -/
theorem lem_5_3_prod_proved (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (ε : ℂ) (hε : ε ≠ 0) :
    (p + C ε * X ^ (d + 1)).derivative.roots.card = d ∧
      ‖(p + C ε * X ^ (d + 1)).derivative.roots.prod‖ = 1 / ((d + 1) * ‖ε‖) := by
  have hd1 : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  have hlc0 : ε * ((d : ℂ) + 1) ≠ 0 := mul_ne_zero hε hd1
  have hlt : p.derivative.natDegree < (C (ε * ((d : ℂ) + 1)) * X ^ d).natDegree := by
    rw [natDegree_C_mul_X_pow _ _ hlc0, natDegree_derivative, hp.1]
    omega
  have hdeg : (p + C ε * X ^ (d + 1)).derivative.natDegree = d := by
    rw [derivative_eps, natDegree_add_eq_right_of_natDegree_lt hlt, natDegree_C_mul_X_pow _ _ hlc0]
  have hlc : (p + C ε * X ^ (d + 1)).derivative.leadingCoeff = ε * ((d : ℂ) + 1) := by
    rw [derivative_eps, leadingCoeff_add_of_degree_lt (degree_lt_degree hlt), leadingCoeff_C_mul_X_pow]
  have hc0 : (p + C ε * X ^ (d + 1)).derivative.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, eval_derivative_eps, hp.2.2, zero_pow (by omega), mul_zero, add_zero]
  refine ⟨IsAlgClosed.card_roots_eq_natDegree.trans hdeg, ?_⟩
  have hv := (IsAlgClosed.splits (p + C ε * X ^ (d + 1)).derivative).coeff_zero_eq_leadingCoeff_mul_prod_roots
  rw [hc0, hlc, hdeg] at hv
  have hn := congrArg (‖·‖) hv
  simp only [norm_one, norm_mul, norm_pow, norm_neg, one_pow, one_mul] at hn
  rw [norm_natCast_add_one] at hn
  have hpos : 0 < ((d : ℝ) + 1) * ‖ε‖ := mul_pos (by positivity) (norm_pos_iff.2 hε)
  rw [eq_div_iff hpos.ne']
  linear_combination -hn

/-! ### The limit `m(p_ε) → m(p)` -/

/-- `Q = p/z - p'/(d+1)`: at a critical point `β` of `p_ε`, `p_ε(β)/β = Q(β)`; `Q` has degree `d - 1 ≥ 1`. -/
noncomputable def farPoly (p : ℂ[X]) (d : ℕ) : ℂ[X] := divX p - C (((d : ℂ) + 1)⁻¹) * p.derivative

theorem eval_farPoly_of_crit {d : ℕ} (hd : 2 ≤ d) {p : ℂ[X]} (hp : IsPd d p) {ε β : ℂ} (hε : ε ≠ 0)
    (hβ : (p + C ε * X ^ (d + 1)).derivative.eval β = 0) :
    (p + C ε * X ^ (d + 1)).eval β / β = (farPoly p d).eval β := by
  have hβ0 := crit_eps_ne_zero hd hp hβ
  have hdiv : p.eval β / β = (divX p).eval β := by
    have h := congrArg (eval β) (divX_mul_X_add p)
    rw [eval_add, eval_mul, eval_X, eval_C, coeff_zero_eq_eval_zero, hp.2.1, add_zero] at h
    rw [← h, mul_div_cancel_right₀ _ hβ0]
  rw [lem_5_3_identity_proved d hd p hp ε β hε hβ, hdiv, farPoly, eval_sub, eval_mul, eval_C, div_eq_inv_mul]

theorem degree_farPoly_pos {d : ℕ} (hd : 2 ≤ d) {p : ℂ[X]} (hp : IsPd d p) : 0 < (farPoly p d).degree := by
  have hα : p.coeff d ≠ 0 := by
    rw [← hp.1]
    exact leadingCoeff_ne_zero.2 fun h => by
      have h1 := hp.2.2
      rw [h, derivative_zero, eval_zero] at h1
      exact zero_ne_one h1
  have hd1 : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  have hcoeff : (farPoly p d).coeff (d - 1) = p.coeff d * ((d : ℂ) + 1)⁻¹ := by
    rw [farPoly, coeff_sub, coeff_divX, coeff_C_mul, coeff_derivative, show d - 1 + 1 = d by omega]
    rw [show ((d - 1 : ℕ) : ℂ) + 1 = d by rw [← Nat.cast_add_one, Nat.sub_add_cancel (by omega : 1 ≤ d)]]
    field_simp
    ring
  have hne : (farPoly p d).coeff (d - 1) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero hα (inv_ne_zero hd1)
  have h1 := le_degree_of_ne_zero hne
  have h2 : (0 : WithBot ℕ) < ((d - 1 : ℕ) : WithBot ℕ) := by exact_mod_cast (show 0 < d - 1 by omega)
  exact h2.trans_le h1

/-- `|Q(z)| ≥ B` for all large `|z|`. -/
theorem farPoly_large {d : ℕ} (hd : 2 ≤ d) {p : ℂ[X]} (hp : IsPd d p) (B : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → B ≤ ‖(farPoly p d).eval z‖ := by
  have ht := (farPoly p d).tendsto_norm_atTop (degree_farPoly_pos hd hp) (l := comap norm atTop) (z := id)
    tendsto_comap
  obtain ⟨R0, hR0⟩ := eventually_atTop.1 (eventually_comap.1 (ht.eventually_ge_atTop B))
  exact ⟨max R0 1, lt_max_of_lt_right one_pos, fun z hz => hR0 ‖z‖ (le_of_max_le_left hz) z rfl⟩

/-- Lower bound: for small `ε`, every critical point `β` of `p_ε` has `|p_ε(β)|/|β| ≥ m(p) - δ`. -/
theorem lower_bound_eps {d : ℕ} (hd : 2 ≤ d) {p : ℂ[X]} (hp : IsPd d p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℂ, ε ≠ 0 → ‖ε‖ < η → ∀ β : ℂ, (p + C ε * X ^ (d + 1)).derivative.eval β = 0 →
      mval p - δ ≤ ‖(p + C ε * X ^ (d + 1)).eval β‖ / ‖β‖ := by
  obtain ⟨R, hR, hRbig⟩ := farPoly_large hd hp (mval p + 1)
  -- the compact set `A` where `|p(w)| ≤ (m(p) - δ/2)|w|`, `|w| ≤ R`: `p'` has no zero on it
  let A : Set ℂ := closedBall 0 R ∩ {w | ‖p.eval w‖ ≤ (mval p - δ / 2) * ‖w‖}
  have hA : IsCompact A := (isCompact_closedBall 0 R).inter_right
    (isClosed_le (continuous_norm.comp p.continuous) (continuous_const.mul continuous_norm))
  have hApos : ∀ w ∈ A, 0 < ‖p.derivative.eval w‖ := by
    intro w hw
    refine norm_pos_iff.2 fun h0 => ?_
    have hw0 := crit_ne_zero hp h0
    have h1 := mval_le h0
    have h2 : ‖p.eval w‖ / ‖w‖ ≤ mval p - δ / 2 := (div_le_iff₀ (norm_pos_iff.2 hw0)).2 hw.2
    linarith
  obtain ⟨τ, hτ, hτA⟩ := hA.exists_forall_le' (f := fun w => ‖p.derivative.eval w‖)
    (continuous_norm.comp p.derivative.continuous).continuousOn hApos
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ((d : ℝ) + 1) * R ^ d + 1 := ⟨_, rfl⟩
  have hRd : 0 < R ^ d := pow_pos hR d
  have hK : 0 < K := by
    rw [hKdef]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) hRd.le) one_pos
  have hRK : R ^ d ≤ K := by rw [hKdef]; nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hdRK : ((d : ℝ) + 1) * R ^ d ≤ K := by rw [hKdef]; linarith
  refine ⟨min τ (δ / 2) / K, div_pos (lt_min hτ (half_pos hδ)) hK, fun ε hε hεη β hβ => ?_⟩
  have hεK : ‖ε‖ * K < min τ (δ / 2) := (lt_div_iff₀ hK).1 hεη
  have hβ0 := crit_eps_ne_zero hd hp hβ
  have hβpos : 0 < ‖β‖ := norm_pos_iff.2 hβ0
  rcases le_or_gt R ‖β‖ with hRβ | hRβ
  · rw [← norm_div, eval_farPoly_of_crit hd hp hε hβ]
    linarith [hRbig β hRβ]
  · have hβd : ‖β‖ ^ d ≤ R ^ d := pow_le_pow_left₀ (norm_nonneg _) hRβ.le d
    have hεR : ‖ε‖ * ‖β‖ ^ d < δ / 2 := by
      have := mul_le_mul_of_nonneg_left (hβd.trans hRK) (norm_nonneg ε)
      linarith [min_le_right τ (δ / 2)]
    have hnotA : β ∉ A := by
      intro hβA
      have h1 : τ ≤ ‖p.derivative.eval β‖ := hτA β hβA
      rw [eval_derivative_eps] at hβ
      have h2 : p.derivative.eval β = -(ε * ((d : ℂ) + 1) * β ^ d) := by linear_combination hβ
      rw [h2, norm_neg, norm_mul, norm_mul, norm_pow, norm_natCast_add_one] at h1
      have h3 : ((d : ℝ) + 1) * ‖β‖ ^ d ≤ K :=
        le_trans (mul_le_mul_of_nonneg_left hβd (by positivity)) hdRK
      have h4 : ‖ε‖ * ((d : ℝ) + 1) * ‖β‖ ^ d ≤ ‖ε‖ * K := by
        calc ‖ε‖ * ((d : ℝ) + 1) * ‖β‖ ^ d = ‖ε‖ * (((d : ℝ) + 1) * ‖β‖ ^ d) := by ring
          _ ≤ ‖ε‖ * K := mul_le_mul_of_nonneg_left h3 (norm_nonneg ε)
      linarith [min_le_left τ (δ / 2)]
    have hbig : (mval p - δ / 2) * ‖β‖ < ‖p.eval β‖ := by
      by_contra h
      exact hnotA ⟨mem_closedBall_zero_iff.2 hRβ.le, not_lt.1 h⟩
    rw [le_div_iff₀ hβpos, eval_eps]
    have h4 : ‖ε * β ^ (d + 1)‖ = ‖ε‖ * ‖β‖ ^ d * ‖β‖ := by rw [norm_mul, norm_pow, pow_succ]; ring
    have h5 := norm_sub_norm_le (p.eval β) (-(ε * β ^ (d + 1)))
    rw [sub_neg_eq_add, norm_neg, h4] at h5
    nlinarith [mul_lt_mul_of_pos_right hεR hβpos]

/-- Upper bound: for small `ε`, `p_ε` has a critical point `β` with `|p_ε(β)|/|β| ≤ m(p) + δ` (Rouché on a small
circle around the critical point of `p` where `m(p)` is attained: the Hurwitz step). -/
theorem upper_bound_eps {d : ℕ} (hd : 2 ≤ d) {p : ℂ[X]} (hp : IsPd d p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℂ, ‖ε‖ < η → ∃ β : ℂ, (p + C ε * X ^ (d + 1)).derivative.eval β = 0 ∧
      ‖(p + C ε * X ^ (d + 1)).eval β‖ / ‖β‖ ≤ mval p + δ := by
  obtain ⟨-, ⟨β₀, hβ₀, hM⟩, -⟩ := sec1_m_attained_proved d hd p hp
  have hβ₀0 := crit_ne_zero hp hβ₀
  have hp' : p.derivative ≠ 0 := fun h => by
    have h1 := hp.2.2
    rw [h, eval_zero] at h1
    exact zero_ne_one h1
  -- continuity of `w ↦ |p(w)|/|w|` at `β₀`
  have hcont : ContinuousAt (fun w => ‖p.eval w‖ / ‖w‖) β₀ :=
    ((continuous_norm.comp p.continuous).continuousAt).div continuous_norm.continuousAt (norm_ne_zero_iff.2 hβ₀0)
  obtain ⟨ρ₀, hρ₀, hρ₀g⟩ := Metric.continuousAt_iff.1 hcont (δ / 2) (half_pos hδ)
  -- isolation of `β₀` among the critical points of `p`
  have hS : (p.derivative.roots.toFinset.erase β₀ : Set ℂ)ᶜ ∈ 𝓝 β₀ :=
    (Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨ρ₁, hρ₁, hρ₁S⟩ := Metric.mem_nhds_iff.1 hS
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min (ρ₀ / 2) (ρ₁ / 2) := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; exact lt_min (half_pos hρ₀) (half_pos hρ₁)
  have hρ₀' : ρ < ρ₀ := by rw [hρdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρ₁' : ρ < ρ₁ := by rw [hρdef]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- `p'` has no zero on the circle `|w - β₀| = ρ`
  have hsph : ∀ w ∈ sphere β₀ ρ, 0 < ‖p.derivative.eval w‖ := by
    intro w hw
    refine norm_pos_iff.2 fun h0 => ?_
    have hwd : ‖w - β₀‖ = ρ := mem_sphere_iff_norm.1 hw
    have hwne : w ≠ β₀ := fun h => by rw [h, sub_self, norm_zero] at hwd; exact hρ.ne hwd
    have hwball : w ∈ ball β₀ ρ₁ := mem_ball_iff_norm.2 (by rw [hwd]; exact hρ₁')
    exact hρ₁S hwball (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hwne, Multiset.mem_toFinset.2 ((mem_roots hp').2 h0)⟩))
  obtain ⟨τ, hτ, hτS⟩ := (isCompact_sphere β₀ ρ).exists_forall_le' (f := fun w => ‖p.derivative.eval w‖)
    (continuous_norm.comp p.derivative.continuous).continuousOn hsph
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ‖β₀‖ + ρ := ⟨_, rfl⟩
  have hB : 0 < B := by rw [hBdef]; exact add_pos_of_nonneg_of_pos (norm_nonneg _) hρ
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ((d : ℝ) + 1) * B ^ d + 1 := ⟨_, rfl⟩
  have hBd : 0 < B ^ d := pow_pos hB d
  have hK : 0 < K := by
    rw [hKdef]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) hBd.le) one_pos
  have hBK : B ^ d ≤ K := by rw [hKdef]; nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hdBK : ((d : ℝ) + 1) * B ^ d ≤ K := by rw [hKdef]; linarith
  refine ⟨min τ (δ / 2) / K, div_pos (lt_min hτ (half_pos hδ)) hK, fun ε hεη => ?_⟩
  have hεK : ‖ε‖ * K < min τ (δ / 2) := (lt_div_iff₀ hK).1 hεη
  -- Rouché on `|w - β₀| = ρ`
  have hrouche := zerosInBall_add_of_norm_lt p.derivative (C (ε * ((d : ℂ) + 1)) * X ^ d) β₀ hρ (fun w hw => by
    have hwB : ‖w‖ ≤ B := by
      have := norm_le_norm_add_norm_sub' w β₀
      rw [show ‖w - β₀‖ = ρ from hw] at this
      linarith [norm_sub_rev w β₀]
    have h1 : τ ≤ ‖p.derivative.eval w‖ := hτS w (mem_sphere_iff_norm.2 hw)
    rw [eval_mul, eval_C, eval_pow, eval_X, norm_mul, norm_mul, norm_pow, norm_natCast_add_one]
    have h3 : ((d : ℝ) + 1) * ‖w‖ ^ d ≤ K :=
      le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hwB d) (by positivity)) hdBK
    have h4 : ‖ε‖ * ((d : ℝ) + 1) * ‖w‖ ^ d ≤ ‖ε‖ * K := by
      calc ‖ε‖ * ((d : ℝ) + 1) * ‖w‖ ^ d = ‖ε‖ * (((d : ℝ) + 1) * ‖w‖ ^ d) := by ring
        _ ≤ ‖ε‖ * K := mul_le_mul_of_nonneg_left h3 (norm_nonneg ε)
    linarith [min_le_left τ (δ / 2)])
  rw [← derivative_eps] at hrouche
  have hcount : 0 < zerosInBall p.derivative β₀ ρ :=
    Multiset.card_pos_iff_exists_mem.2 ⟨β₀, Multiset.mem_filter.2 ⟨(mem_roots hp').2 hβ₀, by simpa using hρ⟩⟩
  rw [← hrouche] at hcount
  obtain ⟨β, hβmem⟩ := Multiset.card_pos_iff_exists_mem.1 hcount
  obtain ⟨hβroot, hβd⟩ := Multiset.mem_filter.1 hβmem
  replace hβd : ‖β - β₀‖ < ρ := hβd
  have hβ := (mem_roots'.1 hβroot).2.eq_zero
  refine ⟨β, hβ, ?_⟩
  have hβ0 := crit_eps_ne_zero hd hp hβ
  have hβpos : 0 < ‖β‖ := norm_pos_iff.2 hβ0
  have hβB : ‖β‖ ≤ B := by
    have := norm_le_norm_add_norm_sub' β β₀
    linarith [norm_sub_rev β β₀]
  have hg : ‖p.eval β‖ / ‖β‖ < mval p + δ / 2 := by
    have h1 := hρ₀g (show dist β β₀ < ρ₀ by rw [dist_eq_norm]; linarith)
    rw [Real.dist_eq, ← hM] at h1
    linarith [(abs_lt.1 h1).2]
  have hg' : ‖p.eval β‖ < (mval p + δ / 2) * ‖β‖ := (div_lt_iff₀ hβpos).1 hg
  have hεB : ‖ε‖ * ‖β‖ ^ d < δ / 2 := by
    have := mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) hβB d).trans hBK) (norm_nonneg ε)
    linarith [min_le_right τ (δ / 2)]
  rw [div_le_iff₀ hβpos, eval_eps]
  have h4 : ‖ε * β ^ (d + 1)‖ = ‖ε‖ * ‖β‖ ^ d * ‖β‖ := by rw [norm_mul, norm_pow, pow_succ]; ring
  have h5 := norm_add_le (p.eval β) (ε * β ^ (d + 1))
  rw [h4] at h5
  nlinarith [mul_lt_mul_of_pos_right hεB hβpos]

/-- Lemma 5.3, proof (tex l.453-465), exactly the Statements type: `p_ε ∈ 𝓟_{d+1}` and `m(p_ε) → m(p)`. -/
theorem lem_5_3_limit_proved (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) :
    (∀ ε : ℂ, ε ≠ 0 → IsPd (d + 1) (p + C ε * X ^ (d + 1))) ∧
      Tendsto (fun ε : ℂ => mval (p + C ε * X ^ (d + 1))) (𝓝[≠] 0) (𝓝 (mval p)) := by
  refine ⟨fun ε hε => isPd_eps hd hp hε, Metric.tendsto_nhdsWithin_nhds.2 fun δ hδ => ?_⟩
  obtain ⟨η₁, hη₁, hL⟩ := lower_bound_eps hd hp (half_pos hδ)
  obtain ⟨η₂, hη₂, hU⟩ := upper_bound_eps hd hp (half_pos hδ)
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun {ε} hε hdist => ?_⟩
  show dist (mval (p + C ε * X ^ (d + 1))) (mval p) < δ
  rw [dist_zero_right] at hdist
  have hε0 : ε ≠ 0 := hε
  obtain ⟨β, hβ, hβle⟩ := hU ε (lt_of_lt_of_le hdist (min_le_right _ _))
  have hup : mval (p + C ε * X ^ (d + 1)) ≤ mval p + δ / 2 := (mval_le hβ).trans hβle
  have hlow : mval p - δ / 2 ≤ mval (p + C ε * X ^ (d + 1)) :=
    le_mval ⟨β, hβ⟩ fun γ hγ => hL ε hε0 (lt_of_lt_of_le hdist (min_le_left _ _)) γ hγ
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Lemma 5.3 (Crane; tex l.448-450), exactly the Statements type: `K(d+1) ≥ K(d)` for every `d ≥ 2`. -/
theorem lem_5_3_proved (d : ℕ) (hd : 2 ≤ d) : Kd d ≤ Kd (d + 1) := by
  show (⨆ q : {q : ℂ[X] // IsPd d q}, ((mval q.1 : ℝ) : EReal)) ≤ Kd (d + 1)
  refine iSup_le fun q => ?_
  obtain ⟨hpd, hlim⟩ := lem_5_3_limit_proved d hd q.1 q.2
  have hlim' := (continuous_coe_real_ereal.tendsto _).comp hlim
  refine le_of_tendsto hlim' (eventually_mem_nhdsWithin.mono fun ε hε => ?_)
  exact le_iSup (fun r : {r : ℂ[X] // IsPd (d + 1) r} => ((mval r.1 : ℝ) : EReal)) ⟨_, hpd ε hε⟩

end Smale
