/-
Smale/Proofs/JNCrit.lean — the last two steps of the proof of [JN, Prop. 4.2].
First (`level_choice`): a level band free of critical values of `Q`.
Then (`perturb_crit`): for large `m`, every critical point `b` of `H_m = P + X q^{m+1}` has `|H_m(b)/b|` above `A`.
Write `P = X a`, so `H_m(b)/b = a(b) + q(b)^{m+1}`, and split by the size of `|q(b)|`, with `0 < ρ < 1`:
below `1 - ρ` there is no critical point at all; in the band `[1 - ρ, 1 + ρ]`, `|q(b)|^{m+1} = O(1/m)`; above `1 + ρ`,
`|q(b)|^{m+1}` beats `a(b)`, because `|a| ≤ C |q|^e` wherever `|q| ≥ 1`.
-/
import Smale.Proofs.Lemma53

namespace Smale

open Polynomial Complex Metric Filter Topology

/-! ### A level band free of critical values -/

/-- The moduli of the critical values of a nonconstant polynomial form a finite set. -/
theorem finite_critical_moduli {Q : ℂ[X]} (hQ : 1 ≤ Q.natDegree) :
    ((fun β => ‖Q.eval β‖) '' {β | Q.derivative.eval β = 0}).Finite := by
  have hne : Q.derivative ≠ 0 := fun h => by
    have := derivative_eq_zero.mp h
    omega
  exact Set.Finite.image _ (finite_setOfPred_isRoot hne)

set_option linter.unusedVariables false in
/-- A level band free of critical values, between `a` and `c`. -/
theorem level_choice {Q : ℂ[X]} (hQ : 1 ≤ Q.natDegree) {a c : ℝ} (ha : 0 < a) (hac : a < c) :
    ∃ s r : ℝ, 0 < r ∧ a < s - r ∧ s + r < c ∧
      ∀ β : ℂ, Q.derivative.eval β = 0 → ‖Q.eval β‖ ∉ Set.Icc (s - r) (s + r) := by
  have hfin := finite_critical_moduli hQ
  obtain ⟨s, hs, hsV⟩ := ((Set.Ioo_infinite hac).sdiff hfin).nonempty
  have hopen : IsOpen (Set.Ioo a c ∩ ((fun β => ‖Q.eval β‖) '' {β | Q.derivative.eval β = 0})ᶜ) :=
    isOpen_Ioo.inter hfin.isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen s ⟨hs, hsV⟩
  have hIcc : Set.Icc (s - ε / 2) (s + ε / 2) ⊆ ball s ε := by
    intro x hx
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine ⟨s, ε / 2, by linarith, ?_, ?_, fun β hβ hmem => ?_⟩
  · exact (hball (hIcc ⟨le_rfl, by linarith⟩)).1.1
  · exact (hball (hIcc ⟨by linarith, le_rfl⟩)).1.2
  · exact (hball (hIcc hmem)).2 ⟨β, hβ, rfl⟩

/-! ### The perturbation `H_m = P + X q^{m+1}` -/

namespace JNCrit

/-- The reverse triangle inequality, for a sum. -/
theorem norm_sub_norm_le_norm_add (x y : ℂ) : ‖x‖ - ‖y‖ ≤ ‖x + y‖ := by
  have h := norm_sub_norm_le x (-y)
  rwa [norm_neg, sub_neg_eq_add] at h

/-- `H_m = P + X q^{m+1}`. -/
noncomputable def pert (P q : ℂ[X]) (m : ℕ) : ℂ[X] := P + X * q ^ (m + 1)

/-- `H_m'(b) = P'(b) + q(b)^m (q(b) + (m+1) b q'(b))`. -/
theorem eval_pert_derivative (P q : ℂ[X]) (m : ℕ) (b : ℂ) :
    (pert P q m).derivative.eval b =
      P.derivative.eval b + q.eval b ^ m * (q.eval b + ((m : ℂ) + 1) * (b * q.derivative.eval b)) := by
  simp only [pert, derivative_add, derivative_mul, derivative_X, derivative_pow_succ, eval_add, eval_mul, eval_pow,
    eval_X, eval_C, one_mul]
  ring

/-- `P = X a`, with `a = divX P`, when `P(0) = 0`. -/
theorem eval_eq_mul_divX {P : ℂ[X]} (hP0 : P.eval 0 = 0) (b : ℂ) : P.eval b = b * P.divX.eval b := by
  have h := divX_mul_X_add P
  rw [coeff_zero_eq_eval_zero, hP0, C_0, add_zero] at h
  conv_lhs => rw [← h]
  rw [eval_mul, eval_X, mul_comm]

/-- `H_m(b) = b (a(b) + q(b)^{m+1})`. -/
theorem eval_pert {P : ℂ[X]} (hP0 : P.eval 0 = 0) (q : ℂ[X]) (m : ℕ) (b : ℂ) :
    (pert P q m).eval b = b * (P.divX.eval b + q.eval b ^ (m + 1)) := by
  simp only [pert, eval_add, eval_mul, eval_X, eval_pow]
  rw [eval_eq_mul_divX hP0 b]
  ring

/-! #### Growth: `|a| ≤ C |q|^e` where `|q| ≥ 1` -/

/-- `q(w) = rev q (1/w) w^N`. -/
theorem eval_reverse_mul_pow (q : ℂ[X]) {w : ℂ} (hw : w ≠ 0) :
    q.reverse.eval w⁻¹ * w ^ q.natDegree = q.eval w := by
  let : Invertible w := invertibleOfNonzero hw
  have h := eval₂_reverse_mul_pow (RingHom.id ℂ) w q
  rwa [eval₂_id, eval₂_id, invOf_eq_inv] at h

/-- A nonconstant polynomial grows at least linearly. -/
theorem exists_linear_lower (q : ℂ[X]) (hq : 1 ≤ q.natDegree) :
    ∃ c R : ℝ, 0 < c ∧ 1 ≤ R ∧ ∀ w : ℂ, R ≤ ‖w‖ → c * ‖w‖ ≤ ‖q.eval w‖ := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq
  have hlead : 0 < ‖q.leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hq0)
  have hrev : ‖q.reverse.eval 0‖ = ‖q.leadingCoeff‖ := by
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]
  have hev : ∀ᶠ u in 𝓝 (0 : ℂ), ‖q.leadingCoeff‖ / 2 < ‖q.reverse.eval u‖ := by
    have hc : Tendsto (fun u => ‖q.reverse.eval u‖) (𝓝 0) (𝓝 ‖q.reverse.eval 0‖) :=
      (q.reverse.continuous.norm).continuousAt.tendsto
    rw [hrev] at hc
    exact hc.eventually (lt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨‖q.leadingCoeff‖ / 2, max 1 (2 / δ), by linarith, le_max_left _ _, fun w hw => ?_⟩
  have hw1 : 1 ≤ ‖w‖ := (le_max_left _ _).trans hw
  have hwpos : 0 < ‖w‖ := by linarith
  have hw0 : w ≠ 0 := norm_pos_iff.mp hwpos
  have hinv : dist w⁻¹ 0 < δ := by
    rw [dist_zero_right, norm_inv, inv_lt_comm₀ hwpos hδ, inv_eq_one_div]
    exact lt_of_lt_of_le (div_lt_div_of_pos_right one_lt_two hδ) ((le_max_right _ _).trans hw)
  rw [← eval_reverse_mul_pow q hw0, norm_mul, norm_pow]
  calc ‖q.leadingCoeff‖ / 2 * ‖w‖ ≤ ‖q.reverse.eval w⁻¹‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right (hball hinv).le hwpos.le
    _ ≤ ‖q.reverse.eval w⁻¹‖ * ‖w‖ ^ q.natDegree :=
        mul_le_mul_of_nonneg_left (le_self_pow₀ hw1 (by omega)) (norm_nonneg _)

/-- A polynomial grows at most like the power of its degree. -/
theorem exists_eval_le_pow (a : ℂ[X]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖a.eval w‖ ≤ C * max 1 ‖w‖ ^ a.natDegree := by
  refine ⟨∑ i ∈ Finset.range (a.natDegree + 1), ‖a.coeff i‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun w => ?_⟩
  rw [eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖w‖ ^ i ≤ max 1 ‖w‖ ^ i := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
    _ ≤ max 1 ‖w‖ ^ a.natDegree :=
        pow_le_pow_right₀ (le_max_left _ _) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- `|a| ≤ C |q|^e` wherever `|q| ≥ 1`. -/
theorem exists_growth (a q : ℂ[X]) (hq : 1 ≤ q.natDegree) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 1 ≤ ‖q.eval w‖ → ‖a.eval w‖ ≤ C * ‖q.eval w‖ ^ a.natDegree := by
  obtain ⟨c, R, hc, hR, hlow⟩ := exists_linear_lower q hq
  obtain ⟨C, hC, hup⟩ := exists_eval_le_pow a
  have hL : 0 ≤ max (1 / c) R := le_max_of_le_right (by linarith)
  refine ⟨C * max (1 / c) R ^ a.natDegree, mul_nonneg hC (pow_nonneg hL _), fun w hw => ?_⟩
  have hmax : max 1 ‖w‖ ≤ max (1 / c) R * ‖q.eval w‖ := by
    rcases le_or_gt R ‖w‖ with h | h
    · rw [max_eq_right (hR.trans h)]
      calc ‖w‖ = (1 / c) * (c * ‖w‖) := by field_simp
        _ ≤ (1 / c) * ‖q.eval w‖ := mul_le_mul_of_nonneg_left (hlow w h) (by positivity)
        _ ≤ max (1 / c) R * ‖q.eval w‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    · calc max 1 ‖w‖ ≤ max (1 / c) R := (max_le hR h.le).trans (le_max_right _ _)
        _ ≤ max (1 / c) R * ‖q.eval w‖ := le_mul_of_one_le_right hL hw
  calc ‖a.eval w‖ ≤ C * max 1 ‖w‖ ^ a.natDegree := hup w
    _ ≤ C * (max (1 / c) R * ‖q.eval w‖) ^ a.natDegree :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmax _) hC
    _ = C * max (1 / c) R ^ a.natDegree * ‖q.eval w‖ ^ a.natDegree := by rw [mul_pow, mul_assoc]

/-! #### The three regions -/

/-- Region III, `|q(b)| > 1 + ρ`: `q(b)^{m+1}` dominates. The critical equation is not used. -/
theorem eventually_region_far (a : ℂ[X]) {q : ℂ[X]} (hq : 1 ≤ q.natDegree) {ρ : ℝ} (hρ0 : 0 < ρ) (L : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ b : ℂ, 1 + ρ < ‖q.eval b‖ → L ≤ ‖a.eval b + q.eval b ^ (m + 1)‖ := by
  obtain ⟨C, hC, hgrow⟩ := exists_growth a q hq
  have htend : Tendsto (fun n : ℕ => (1 + ρ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by linarith)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (htend.eventually_ge_atTop (C + max L 0))
  filter_upwards [eventually_ge_atTop (n₀ + a.natDegree)] with m hm b hb
  have hZ1 : 1 ≤ ‖q.eval b‖ := by linarith
  have hsplit : ‖q.eval b‖ ^ (m + 1) = ‖q.eval b‖ ^ a.natDegree * ‖q.eval b‖ ^ (m + 1 - a.natDegree) := by
    rw [← pow_add]
    congr 1
    omega
  have hbig : C + max L 0 ≤ ‖q.eval b‖ ^ (m + 1 - a.natDegree) :=
    (hn₀ _ (by omega)).trans (pow_le_pow_left₀ (by linarith) hb.le _)
  have hge1 : 1 ≤ ‖q.eval b‖ ^ a.natDegree := one_le_pow₀ hZ1
  have htri := norm_sub_norm_le_norm_add (q.eval b ^ (m + 1)) (a.eval b)
  rw [add_comm (q.eval b ^ (m + 1)) (a.eval b), norm_pow] at htri
  have hmaxL : L ≤ max L 0 := le_max_left _ _
  have hmax0 : 0 ≤ max L 0 := le_max_right _ _
  have hprod : ‖q.eval b‖ ^ (m + 1 - a.natDegree) - C ≤
      ‖q.eval b‖ ^ a.natDegree * (‖q.eval b‖ ^ (m + 1 - a.natDegree) - C) :=
    le_mul_of_one_le_left (by linarith) hge1
  have hgrowb := hgrow b hZ1
  nlinarith

/-- Region I, `|q(b)| < 1 - ρ`: no critical point, since `|P'| ≥ μ` there and the other term tends to `0`. -/
theorem eventually_region_near {P q : ℂ[X]} {K : Set ℂ} {ρ μ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hK : IsCompact K)
    (hμ : 0 < μ) (hKq : ∀ b, ‖q.eval b‖ ≤ 1 + ρ → b ∈ K) (hKP : ∀ b ∈ K, μ ≤ ‖P.derivative.eval b‖) :
    ∀ᶠ m : ℕ in atTop, ∀ b : ℂ, ‖q.eval b‖ < 1 - ρ → (pert P q m).derivative.eval b ≠ 0 := by
  have hcont : Continuous fun b : ℂ => b * q.derivative.eval b := continuous_id.mul q.derivative.continuous
  obtain ⟨X₀, hX₀⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hr0 : 0 ≤ 1 - ρ := by linarith
  have hr1 : 1 - ρ < 1 := by linarith
  have htend : Tendsto (fun m : ℕ => (1 - ρ) ^ m * (1 + ((m : ℝ) + 1) * X₀)) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const (1 + X₀)).add
      ((tendsto_self_mul_const_pow_of_lt_one hr0 hr1).const_mul X₀)
    have h0 : (0 : ℝ) * (1 + X₀) + X₀ * 0 = 0 := by ring
    rw [h0] at h
    exact h.congr fun m => by ring
  filter_upwards [htend.eventually (gt_mem_nhds hμ)] with m hm b hb hzero
  have hbK : b ∈ K := hKq b (by linarith)
  have hPb := hKP b hbK
  rw [eval_pert_derivative] at hzero
  have heq : ‖P.derivative.eval b‖ =
      ‖q.eval b ^ m * (q.eval b + ((m : ℂ) + 1) * (b * q.derivative.eval b))‖ := by
    rw [eq_neg_of_add_eq_zero_left hzero, norm_neg]
  have hmnorm : ‖((m : ℂ) + 1)‖ = (m : ℝ) + 1 := by
    have : ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_natCast]
    push_cast
    rfl
  have hinner : ‖q.eval b + ((m : ℂ) + 1) * (b * q.derivative.eval b)‖ ≤ 1 + ((m : ℝ) + 1) * X₀ := by
    refine (norm_add_le _ _).trans (add_le_add (by linarith) ?_)
    rw [norm_mul, hmnorm]
    exact mul_le_mul_of_nonneg_left (hX₀ b hbK) (by positivity)
  have hbound : ‖q.eval b ^ m * (q.eval b + ((m : ℂ) + 1) * (b * q.derivative.eval b))‖ ≤
      (1 - ρ) ^ m * (1 + ((m : ℝ) + 1) * X₀) := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hb.le _) hinner (norm_nonneg _) (pow_nonneg hr0 _)
  linarith

/-- The band `1 - ρ ≤ |q| ≤ 1 + ρ` inside `K` is compact, and `|b q'(b)|` is bounded below on it. -/
theorem exists_band_lower {P q : ℂ[X]} {K : Set ℂ} {A' ρ : ℝ} (hK : IsCompact K)
    (hKq : ∀ b, ‖q.eval b‖ ≤ 1 + ρ → b ∈ K)
    (hband : ∀ b, 1 - ρ ≤ ‖q.eval b‖ → ‖q.eval b‖ ≤ 1 + ρ →
      q.derivative.eval b ≠ 0 ∧ b ≠ 0 ∧ A' < ‖P.eval b‖ / ‖b‖) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ b, 1 - ρ ≤ ‖q.eval b‖ → ‖q.eval b‖ ≤ 1 + ρ → κ ≤ ‖b * q.derivative.eval b‖ := by
  have hqn : Continuous fun b : ℂ => ‖q.eval b‖ := q.continuous.norm
  have hS : IsCompact (K ∩ ({b | 1 - ρ ≤ ‖q.eval b‖} ∩ {b | ‖q.eval b‖ ≤ 1 + ρ})) :=
    hK.inter_right ((isClosed_le continuous_const hqn).inter (isClosed_le hqn continuous_const))
  have hg : ContinuousOn (fun b : ℂ => ‖b * q.derivative.eval b‖)
      (K ∩ ({b | 1 - ρ ≤ ‖q.eval b‖} ∩ {b | ‖q.eval b‖ ≤ 1 + ρ})) :=
    ((continuous_id.mul q.derivative.continuous).norm).continuousOn
  obtain ⟨κ, hκ, hlow⟩ := hS.exists_forall_le' hg (a := 0) fun b hb => by
    obtain ⟨hq', hb0, -⟩ := hband b hb.2.1 hb.2.2
    exact norm_pos_iff.mpr (mul_ne_zero hb0 hq')
  exact ⟨κ, hκ, fun b h1 h2 => hlow b ⟨hKq b h2, h1, h2⟩⟩

/-- Region II, the band: `|q(b)|^{m+1} = O(1/m)` at a critical point, so `|a(b) + q(b)^{m+1}|` stays above `L`. -/
theorem eventually_region_band {P q : ℂ[X]} {K : Set ℂ} {A' ρ L : ℝ} (hP0 : P.eval 0 = 0) (hL : L < A') (hρ0 : 0 < ρ)
    (hK : IsCompact K) (hKq : ∀ b, ‖q.eval b‖ ≤ 1 + ρ → b ∈ K)
    (hband : ∀ b, 1 - ρ ≤ ‖q.eval b‖ → ‖q.eval b‖ ≤ 1 + ρ →
      q.derivative.eval b ≠ 0 ∧ b ≠ 0 ∧ A' < ‖P.eval b‖ / ‖b‖) :
    ∀ᶠ m : ℕ in atTop, ∀ b : ℂ, 1 - ρ ≤ ‖q.eval b‖ → ‖q.eval b‖ ≤ 1 + ρ → (pert P q m).derivative.eval b = 0 →
      L ≤ ‖P.divX.eval b + q.eval b ^ (m + 1)‖ := by
  obtain ⟨κ, hκ, hlow⟩ := exists_band_lower hK hKq hband
  obtain ⟨Y, hY⟩ := hK.exists_bound_of_continuousOn (P.derivative.continuous.continuousOn)
  have htend : Tendsto (fun m : ℕ => (1 + ρ) * (2 * Y / κ) * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((1 + ρ) * (2 * Y / κ))
    rwa [mul_zero] at h
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge (2 * (1 + ρ) / κ)
  filter_upwards [htend.eventually (gt_mem_nhds (sub_pos.mpr hL)), eventually_ge_atTop n₁] with m hm hmn b h1 h2 hzero
  obtain ⟨-, hb0, hratio⟩ := hband b h1 h2
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hmκ : 2 * (1 + ρ) ≤ ((m : ℝ) + 1) * κ := by
    have hmn' : (n₁ : ℝ) ≤ m := by exact_mod_cast hmn
    have h3 : 2 * (1 + ρ) / κ ≤ (m : ℝ) + 1 := by linarith
    rwa [div_le_iff₀ hκ] at h3
  have hbK : b ∈ K := hKq b h2
  -- `|q + (m+1) b q'| ≥ (m+1) κ / 2`
  have hmnorm : ‖((m : ℂ) + 1)‖ = (m : ℝ) + 1 := by
    have : ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_natCast]
    push_cast
    rfl
  have hinner : ((m : ℝ) + 1) * κ / 2 ≤ ‖q.eval b + ((m : ℂ) + 1) * (b * q.derivative.eval b)‖ := by
    have htri := norm_sub_norm_le_norm_add (((m : ℂ) + 1) * (b * q.derivative.eval b)) (q.eval b)
    rw [add_comm (((m : ℂ) + 1) * (b * q.derivative.eval b)) (q.eval b), norm_mul, hmnorm] at htri
    have hmul := mul_le_mul_of_nonneg_left (hlow b h1 h2) hmpos.le
    linarith
  -- the critical equation
  rw [eval_pert_derivative] at hzero
  have heq : ‖P.derivative.eval b‖ =
      ‖q.eval b‖ ^ m * ‖q.eval b + ((m : ℂ) + 1) * (b * q.derivative.eval b)‖ := by
    rw [eq_neg_of_add_eq_zero_left hzero, norm_neg, norm_mul, norm_pow]
  have hpm : ‖q.eval b‖ ^ m * (((m : ℝ) + 1) * κ / 2) ≤ Y := by
    calc ‖q.eval b‖ ^ m * (((m : ℝ) + 1) * κ / 2)
        ≤ ‖q.eval b‖ ^ m * ‖q.eval b + ((m : ℂ) + 1) * (b * q.derivative.eval b)‖ :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = ‖P.derivative.eval b‖ := heq.symm
      _ ≤ Y := hY b hbK
  have hsmall : ‖q.eval b‖ ^ (m + 1) ≤ (1 + ρ) * (2 * Y / κ) * (1 / ((m : ℝ) + 1)) := by
    have hdiv : ‖q.eval b‖ ^ m ≤ (2 * Y / κ) * (1 / ((m : ℝ) + 1)) := by
      have hpos : 0 < ((m : ℝ) + 1) * κ / 2 := by positivity
      have hrw : (2 * Y / κ) * (1 / ((m : ℝ) + 1)) = Y / (((m : ℝ) + 1) * κ / 2) := by
        field_simp
      rw [hrw, le_div_iff₀ hpos]
      exact hpm
    calc ‖q.eval b‖ ^ (m + 1) = ‖q.eval b‖ * ‖q.eval b‖ ^ m := by rw [pow_succ, mul_comm]
      _ ≤ (1 + ρ) * ((2 * Y / κ) * (1 / ((m : ℝ) + 1))) :=
          mul_le_mul h2 hdiv (by positivity) (by linarith)
      _ = (1 + ρ) * (2 * Y / κ) * (1 / ((m : ℝ) + 1)) := by ring
  -- `|a(b)| = |P(b)/b| > A'`
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have ha : A' < ‖P.divX.eval b‖ := by
    rwa [eval_eq_mul_divX hP0 b, norm_mul, mul_div_cancel_left₀ _ hbpos.ne'] at hratio
  have htri := norm_sub_norm_le_norm_add (P.divX.eval b) (q.eval b ^ (m + 1))
  rw [norm_pow] at htri
  linarith

/-! #### The finish -/

/-- `κ_m = H_m'(0) = 1 + q(0)^{m+1}`. -/
theorem eval_pert_derivative_zero {P : ℂ[X]} (hP1 : P.derivative.eval 0 = 1) (q : ℂ[X]) (m : ℕ) :
    (pert P q m).derivative.eval 0 = 1 + q.eval 0 ^ (m + 1) := by
  rw [eval_pert_derivative, hP1]
  ring

/-- The degree of `H_m`, once `m` is large against `deg P`. -/
theorem natDegree_pert {P q : ℂ[X]} (hq : 1 ≤ q.natDegree) {m : ℕ} (hm : P.natDegree < m + 2) :
    (pert P q m).natDegree = (m + 1) * q.natDegree + 1 := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq
  have hX : (X * q ^ (m + 1)).natDegree = (m + 1) * q.natDegree + 1 := by
    rw [natDegree_X_mul (pow_ne_zero _ hq0), natDegree_pow]
  have hmul : m + 1 ≤ (m + 1) * q.natDegree := Nat.le_mul_of_pos_right _ (by omega)
  unfold pert
  rw [natDegree_add_eq_right_of_natDegree_lt (by omega), hX]

/-- `|κ_m| > 0`, and it is at most `1 + |q(0)|^{m+1}`. -/
theorem kappa_bounds {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    1 + z ^ (m + 1) ≠ 0 ∧ ‖1 + z ^ (m + 1)‖ ≤ 1 + ‖z‖ ^ (m + 1) := by
  refine ⟨fun h0 => ?_, ?_⟩
  · have h1 : ‖z ^ (m + 1)‖ = 1 := by
      rw [eq_neg_of_add_eq_zero_right h0, norm_neg, norm_one]
    rw [norm_pow] at h1
    exact absurd h1 (pow_lt_one₀ (norm_nonneg _) hz (by omega)).ne
  · refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_pow]

/-- The normalized `T = H_m / κ_m` is in `𝓟_d`, and any lower bound for `|a + q^{m+1}|` at the critical points gives
a lower bound for `mval T`. -/
theorem exists_of_index {P q : ℂ[X]} {A₁ L : ℝ} {m : ℕ} (hP0 : P.eval 0 = 0) (hP1 : P.derivative.eval 0 = 1)
    (hq : 1 ≤ q.natDegree) (hq01 : ‖q.eval 0‖ < 1) (hA₁ : 0 < A₁) (hdeg : P.natDegree < m + 2)
    (hκ : (1 + ‖q.eval 0‖ ^ (m + 1)) * A₁ < L)
    (hcrit : ∀ b, (pert P q m).derivative.eval b = 0 → L ≤ ‖P.divX.eval b + q.eval b ^ (m + 1)‖) :
    ∃ d : ℕ, 2 ≤ d ∧ ∃ T : ℂ[X], IsPd d T ∧ A₁ ≤ mval T := by
  obtain ⟨hκ0, hκle⟩ := kappa_bounds hq01 m
  have hH0 := eval_pert_derivative_zero hP1 q m
  have hdH := natDegree_pert (P := P) hq hdeg
  have hinv : (1 + q.eval 0 ^ (m + 1))⁻¹ ≠ 0 := inv_ne_zero hκ0
  set κ : ℂ := 1 + q.eval 0 ^ (m + 1) with hκdef
  set T : ℂ[X] := C κ⁻¹ * pert P q m with hT
  have hdT : T.natDegree = (m + 1) * q.natDegree + 1 := by rw [hT, natDegree_C_mul hinv, hdH]
  have hd2 : 2 ≤ (m + 1) * q.natDegree + 1 := by
    have : m + 1 ≤ (m + 1) * q.natDegree := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hT' : ∀ b, T.derivative.eval b = κ⁻¹ * (pert P q m).derivative.eval b := fun b => by
    rw [hT, derivative_C_mul, eval_mul, eval_C]
  have hTeval : ∀ b, T.eval b = κ⁻¹ * (pert P q m).eval b := fun b => by rw [hT, eval_mul, eval_C]
  have hpd : IsPd ((m + 1) * q.natDegree + 1) T := by
    refine ⟨hdT, ?_, ?_⟩
    · rw [hTeval, eval_pert hP0]
      simp
    · rw [hT', hH0]
      exact inv_mul_cancel₀ hκ0
  refine ⟨_, hd2, T, hpd, le_mval ?_ fun β hβ => ?_⟩
  · have hdeg' : 0 < T.derivative.degree := by
      rw [degree_derivative (by omega)]
      exact_mod_cast (by omega : 0 < T.natDegree - 1)
    exact Complex.exists_root hdeg'
  · have hβH : (pert P q m).derivative.eval β = 0 := by
      rw [hT'] at hβ
      exact (mul_eq_zero.mp hβ).resolve_left hinv
    have hβ0 : β ≠ 0 := by
      rintro rfl
      exact hκ0 (hH0.symm.trans hβH)
    have hβpos : 0 < ‖β‖ := norm_pos_iff.mpr hβ0
    have hκpos : 0 < ‖κ‖ := norm_pos_iff.mpr hκ0
    have hval : ‖T.eval β‖ / ‖β‖ = ‖P.divX.eval β + q.eval β ^ (m + 1)‖ / ‖κ‖ := by
      rw [hTeval, eval_pert hP0, norm_mul, norm_mul, norm_inv]
      field_simp
    rw [hval, le_div_iff₀ hκpos]
    have hstep : A₁ * ‖κ‖ ≤ (1 + ‖q.eval 0‖ ^ (m + 1)) * A₁ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hκle hA₁.le
    linarith [hcrit β hβH]

end JNCrit

open JNCrit

/-- The perturbation `P + X q^m`, normalized: all its critical points have ratio above `A`, for large `m`. -/
theorem perturb_crit {P q : ℂ[X]} {K : Set ℂ} {A A' ρ μ : ℝ} (hP0 : P.eval 0 = 0) (hP1 : P.derivative.eval 0 = 1)
    (hq : 1 ≤ q.natDegree) (hA0 : 0 < A) (hA : A < A') (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hq0 : ‖q.eval 0‖ < 1 - ρ)
    (hK : IsCompact K) (hμ : 0 < μ) (hKq : ∀ b, ‖q.eval b‖ ≤ 1 + ρ → b ∈ K)
    (hKP : ∀ b ∈ K, μ ≤ ‖P.derivative.eval b‖)
    (hband : ∀ b, 1 - ρ ≤ ‖q.eval b‖ → ‖q.eval b‖ ≤ 1 + ρ →
      q.derivative.eval b ≠ 0 ∧ b ≠ 0 ∧ A' < ‖P.eval b‖ / ‖b‖) :
    ∃ d : ℕ, 2 ≤ d ∧ ∃ T : ℂ[X], IsPd d T ∧ A < mval T := by
  -- the levels `A < A₁ < L < A'`
  obtain ⟨A₁, hAA₁, hA₁A'⟩ := exists_between hA
  obtain ⟨L, hA₁L, hLA'⟩ := exists_between hA₁A'
  have hA₁0 : 0 < A₁ := hA0.trans hAA₁
  have hq01 : ‖q.eval 0‖ < 1 := by linarith
  have hκ : ∀ᶠ m : ℕ in atTop, (1 + ‖q.eval 0‖ ^ (m + 1)) * A₁ < L := by
    have h := (((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq01).comp
      (tendsto_add_atTop_nat 1)).const_add 1).mul_const A₁
    have h1 : (1 + (0 : ℝ)) * A₁ < L := by linarith
    exact h.eventually (gt_mem_nhds h1)
  have hdeg : ∀ᶠ m : ℕ in atTop, P.natDegree < m + 2 := by
    filter_upwards [eventually_ge_atTop P.natDegree] with m hm
    omega
  obtain ⟨m, hfar, hnear, hbandm, hκm, hdegm⟩ :=
    ((eventually_region_far P.divX hq hρ0 L).and
      ((eventually_region_near hρ0 hρ1 hK hμ hKq hKP).and
        ((eventually_region_band hP0 hLA' hρ0 hK hKq hband).and (hκ.and hdeg)))).exists
  obtain ⟨d, hd, T, hT, hm⟩ := exists_of_index hP0 hP1 hq hq01 hA₁0 hdegm hκm fun b hb => by
    rcases lt_or_ge ‖q.eval b‖ (1 - ρ) with h1 | h1
    · exact absurd hb (hnear b h1)
    · rcases le_or_gt ‖q.eval b‖ (1 + ρ) with h2 | h2
      · exact hbandm b h1 h2 hb
      · exact hfar b h2
  exact ⟨d, hd, T, hT, hAA₁.trans_le hm⟩

end Smale
