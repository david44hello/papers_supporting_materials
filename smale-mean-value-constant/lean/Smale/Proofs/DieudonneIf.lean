/-
Smale/Proofs/DieudonneIf.lean — Dieudonné's criterion, the "if" direction, proved (the paper cites it): a polynomial `H` is
univalent on the open unit disk if no `P_c`, `c ∈ [-1,1]`, has a zero there.
Route. Suppose `H` is not injective on the disk. Among the pairs `u ≠ v` with `H u = H v`, take one minimizing
`max ‖u‖ ‖v‖` (compactness, through the divided difference of `H`, which is `H'` on the diagonal). If `‖u‖ < ‖v‖`,
move `v` slightly toward `0` and follow it with `u` by the inverse function theorem at `u`: a smaller pair, which is
impossible. So `‖u‖ = ‖v‖`, that is `u = w e^{iθ}`, `v = w e^{-iθ}`, and the identity
`H(we^{iθ}) - H(we^{-iθ}) = 2i sin θ · w · P_{cos θ}(w)` gives a zero of `P_{cos θ}` in the disk.
-/
import Smale.Proofs.Dieudonne

namespace Smale

open Polynomial Complex Metric Filter Topology

namespace DieudonneCriterion

/-- The divided difference of `H`: `D(x, y) = Σ_k h_k Σ_{i<k} x^i y^{k-1-i}`. -/
noncomputable def divDiff (H : ℂ[X]) (x y : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (H.natDegree + 1), H.coeff k * ∑ i ∈ Finset.range k, x ^ i * y ^ (k - 1 - i)

/-- `D(x, y) (x - y) = H(x) - H(y)`. -/
theorem divDiff_mul_sub (H : ℂ[X]) (x y : ℂ) : divDiff H x y * (x - y) = H.eval x - H.eval y := by
  rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib, divDiff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, geom_sum₂_mul, mul_sub]

/-- `D(u, u) = H'(u)`. -/
theorem divDiff_self (H : ℂ[X]) (u : ℂ) : divDiff H u u = H.derivative.eval u := by
  rw [derivative_eval, sum_over_range' _ (by simp) (H.natDegree + 1) (Nat.lt_succ_self _), divDiff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [geom_sum₂_self, mul_assoc]

/-- `D` is continuous. -/
theorem continuous_divDiff (H : ℂ[X]) : Continuous fun p : ℂ × ℂ => divDiff H p.1 p.2 := by
  unfold divDiff
  fun_prop

/-- Where `H' ≠ 0`, a zero of `D` is a pair of distinct points with equal values. -/
theorem pair_of_divDiff_eq_zero {H : ℂ[X]} {x y : ℂ} (h0 : divDiff H x y = 0) (hx : H.derivative.eval x ≠ 0) :
    x ≠ y ∧ H.eval x = H.eval y := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact hx (by rw [← divDiff_self, h0])
  · have h := divDiff_mul_sub H x y
    rw [h0, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)

/-- A pair of distinct points with equal values is a zero of `D`. -/
theorem divDiff_eq_zero_of_pair {H : ℂ[X]} {x y : ℂ} (hne : x ≠ y) (heq : H.eval x = H.eval y) :
    divDiff H x y = 0 := by
  have h := divDiff_mul_sub H x y
  rw [heq, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)

/-- Among the pairs `x ≠ y` with `H x = H y`, one minimizes `max ‖x‖ ‖y‖`, if `H' ≠ 0` on the disk and such a pair
exists in the disk. The minimizer lies in the disk. -/
theorem exists_min_pair {H : ℂ[X]} (hD : ∀ z ∈ disk, H.derivative.eval z ≠ 0) {z₁ z₂ : ℂ} (h₁ : z₁ ∈ disk)
    (h₂ : z₂ ∈ disk) (hne : z₁ ≠ z₂) (heq : H.eval z₁ = H.eval z₂) :
    ∃ u v, u ∈ disk ∧ v ∈ disk ∧ u ≠ v ∧ H.eval u = H.eval v ∧
      ∀ x y, x ≠ y → H.eval x = H.eval y → max ‖u‖ ‖v‖ ≤ max ‖x‖ ‖y‖ := by
  set ρ : ℝ := max ‖z₁‖ ‖z₂‖ with hρ
  have hρ1 : ρ < 1 := max_lt (by simpa using h₁) (by simpa using h₂)
  have hsub : ∀ z ∈ closedBall (0 : ℂ) ρ, z ∈ disk := fun z hz => by
    have : ‖z‖ ≤ ρ := by simpa using hz
    simpa using this.trans_lt hρ1
  set T : Set (ℂ × ℂ) := (closedBall (0 : ℂ) ρ ×ˢ closedBall (0 : ℂ) ρ) ∩ {p | divDiff H p.1 p.2 = 0} with hT
  have hTc : IsCompact T :=
    ((isCompact_closedBall (0 : ℂ) ρ).prod (isCompact_closedBall (0 : ℂ) ρ)).inter_right
      (isClosed_eq (continuous_divDiff H) continuous_const)
  have hTne : T.Nonempty := by
    refine ⟨(z₁, z₂), ⟨⟨?_, ?_⟩, divDiff_eq_zero_of_pair hne heq⟩⟩
    · exact mem_closedBall_zero_iff.mpr (le_max_left _ _)
    · exact mem_closedBall_zero_iff.mpr (le_max_right _ _)
  have hcont : ContinuousOn (fun p : ℂ × ℂ => max ‖p.1‖ ‖p.2‖) T := by
    apply Continuous.continuousOn
    fun_prop
  obtain ⟨⟨u, v⟩, ⟨⟨hu, hv⟩, hzero⟩, hmin⟩ := hTc.exists_isMinOn hTne hcont
  have hu' : u ∈ disk := hsub u hu
  have hv' : v ∈ disk := hsub v hv
  obtain ⟨huv, hval⟩ := pair_of_divDiff_eq_zero hzero (hD u hu')
  refine ⟨u, v, hu', hv', huv, hval, fun x y hxy hxyv => ?_⟩
  have hunorm : ‖u‖ ≤ ρ := by simpa using hu
  have hvnorm : ‖v‖ ≤ ρ := by simpa using hv
  by_cases hmem : max ‖x‖ ‖y‖ ≤ ρ
  · have hxT : (x, y) ∈ T := by
      refine ⟨⟨?_, ?_⟩, divDiff_eq_zero_of_pair hxy hxyv⟩
      · simpa using (le_max_left _ _).trans hmem
      · simpa using (le_max_right _ _).trans hmem
    exact hmin hxT
  · exact (max_le hunorm hvnorm).trans (not_le.mp hmem).le

/-- THE MOVE. If `u ≠ v`, `H u = H v`, `H'(u) ≠ 0` and `‖u‖ < ‖v‖`, there is a pair with the same property and both
norms below `‖v‖`: move `v` toward `0`, and follow it with `u`. -/
theorem exists_smaller_pair {H : ℂ[X]} {u v : ℂ} (huv : u ≠ v) (heq : H.eval u = H.eval v)
    (hD : H.derivative.eval u ≠ 0) (hlt : ‖u‖ < ‖v‖) :
    ∃ x y, x ≠ y ∧ H.eval x = H.eval y ∧ ‖x‖ < ‖v‖ ∧ ‖y‖ < ‖v‖ := by
  have hv0 : 0 < ‖v‖ := (norm_nonneg u).trans_lt hlt
  obtain ⟨U₁, V₁, hU₁, hV₁, hdisj⟩ := t2_separation_nhds huv
  set U : Set ℂ := U₁ ∩ ball (0 : ℂ) ‖v‖ with hU
  have hUn : U ∈ 𝓝 u := inter_mem hU₁ (isOpen_ball.mem_nhds (by simpa using hlt))
  -- The image of `U` is a neighbourhood of `H u`.
  have himage : (fun z => H.eval z) '' U ∈ 𝓝 (H.eval u) := by
    have hmap := (H.hasStrictDerivAt u).map_nhds_eq hD
    rw [← hmap]
    exact image_mem_map hUn
  -- The path `t ↦ t v`, which is `v` at `t = 1`.
  have hpath : Tendsto (fun t : ℝ => (t : ℂ) * v) (𝓝[<] 1) (𝓝 v) := by
    have hc : Continuous fun t : ℝ => (t : ℂ) * v := by fun_prop
    have ht := hc.tendsto 1
    simp only [Complex.ofReal_one, one_mul] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  have hvalues : Tendsto (fun t : ℝ => H.eval ((t : ℂ) * v)) (𝓝[<] 1) (𝓝 (H.eval u)) := by
    rw [heq]
    exact H.continuous.continuousAt.tendsto.comp hpath
  have hev₁ : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have hev₂ : ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), (t : ℂ) * v ∈ V₁ := hpath hV₁
  have hev₃ : ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), H.eval ((t : ℂ) * v) ∈ (fun z => H.eval z) '' U := hvalues himage
  obtain ⟨t, ⟨hti, hty⟩, ⟨x, hxU, hxval⟩⟩ := ((hev₁.and hev₂).and hev₃).exists
  refine ⟨x, (t : ℂ) * v, ?_, hxval, by simpa [U] using hxU.2, ?_⟩
  · intro hxy
    exact Set.disjoint_left.mp hdisj hxU.1 (hxy ▸ hty)
  · have ht0 : 0 ≤ t := (Set.mem_Ioo.mp hti).1.le
    have ht1 : t < 1 := (Set.mem_Ioo.mp hti).2
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    nlinarith

/-- `‖u‖ = ‖v‖`, `u ≠ v`, `H u = H v`: some `P_c`, `c ∈ [-1,1]`, has a zero `w` with `‖w‖ = ‖u‖`. -/
theorem exists_zero_of_equal_norms {H : ℂ[X]} {u v : ℂ} (huv : u ≠ v) (heq : H.eval u = H.eval v)
    (hnorm : ‖u‖ = ‖v‖) :
    ∃ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 ∧ ∃ w : ℂ, ‖w‖ = ‖u‖ ∧ (dieudonne H H.natDegree c).eval w = 0 := by
  set θ : ℝ := (arg u - arg v) / 2 with hθ
  set w : ℂ := (‖u‖ : ℂ) * exp (((arg u + arg v) / 2 : ℝ) * I) with hw
  have hwnorm : ‖w‖ = ‖u‖ := by
    rw [hw, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, norm_norm]
  have hwu : w * exp (θ * I) = u := by
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I u]
    rw [hw, mul_assoc, ← Complex.exp_add, hθ]
    congr 2
    push_cast
    ring
  have hwv : w * exp (-(θ * I)) = v := by
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I v, ← hnorm]
    rw [hw, mul_assoc, ← Complex.exp_add, hθ]
    congr 2
    push_cast
    ring
  have hid := sec4_dieudonne_identity_proved H H.natDegree le_rfl θ w
  rw [hwu, hwv, heq, sub_self] at hid
  have hsin : (Real.sin θ : ℂ) ≠ 0 := by
    intro h0
    have hexp := exp_sub_exp_neg 1 θ
    simp only [Nat.cast_one, one_mul] at hexp
    rw [show Complex.sin θ = (Real.sin θ : ℂ) by rw [Complex.ofReal_sin], h0, mul_zero] at hexp
    apply huv
    rw [← hwu, ← hwv, sub_eq_zero.mp hexp]
  have hw0 : w ≠ 0 := by
    intro h0
    have h1 : ‖u‖ = 0 := by rw [← hwnorm, h0, norm_zero]
    have h2 : ‖v‖ = 0 := by rw [← hnorm, h1]
    exact huv (by rw [norm_eq_zero.mp h1, norm_eq_zero.mp h2])
  refine ⟨Real.cos θ, ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩, w, hwnorm, ?_⟩
  have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have hne : (2 * I * (Real.sin θ : ℂ) * w) ≠ 0 := mul_ne_zero (mul_ne_zero h2I hsin) hw0
  exact (mul_eq_zero.mp hid.symm).resolve_left hne

end DieudonneCriterion

open DieudonneCriterion

/-- Dieudonné's criterion, the "if" direction, for every polynomial `H`: if no `P_c`, `c ∈ [-1,1]`, has a zero in the
disk, then `H` is injective on the disk. -/
theorem dieudonne_injOn (H : ℂ[X])
    (hP : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w ∈ disk, (dieudonne H H.natDegree c).eval w ≠ 0) :
    Set.InjOn (fun z => H.eval z) disk := by
  have hD : ∀ z ∈ disk, H.derivative.eval z ≠ 0 := fun z hz => by
    have h := hP 1 (by norm_num) z hz
    rwa [dieudonne_one H H.natDegree le_rfl] at h
  intro z₁ h₁ z₂ h₂ heq
  by_contra hne
  obtain ⟨u, v, hu, hv, huv, hval, hmin⟩ := exists_min_pair hD h₁ h₂ hne heq
  have hle : ‖u‖ = ‖v‖ := by
    refine le_antisymm (not_lt.mp fun hlt => ?_) (not_lt.mp fun hlt => ?_)
    · obtain ⟨x, y, hxy, hxyv, hx, hy⟩ := exists_smaller_pair huv.symm hval.symm (hD v hv) hlt
      have := hmin x y hxy hxyv
      have hmax : max ‖x‖ ‖y‖ < ‖u‖ := max_lt hx hy
      exact absurd ((le_max_left ‖u‖ ‖v‖).trans this) (not_le.mpr hmax)
    · obtain ⟨x, y, hxy, hxyv, hx, hy⟩ := exists_smaller_pair huv hval (hD u hu) hlt
      have := hmin x y hxy hxyv
      have hmax : max ‖x‖ ‖y‖ < ‖v‖ := max_lt hx hy
      exact absurd ((le_max_right ‖u‖ ‖v‖).trans this) (not_le.mpr hmax)
  obtain ⟨c, hc, w, hw, hzero⟩ := exists_zero_of_equal_norms huv hval hle
  refine hP c hc w ?_ hzero
  have hu1 : ‖u‖ < 1 := by simpa using hu
  simpa [hw] using hu1

set_option linter.unusedVariables false in
/-- Dieudonné's criterion (J. Dieudonné, Ann. Sci. École Norm. Sup. (3) 48 (1931), 247-358), as [JN, Lemma 6.3] states it
(the paper's Dieudonné criterion, tex l.280-283), verbatim:
"A polynomial $H(z)=\sum_{k=1}^n a_k z^k$ is univalent in $\D$ if and only if, for every $c\in[-1,1]$, its
Dieudonn\'e polynomial $$ P_c(w):=\sum_{k=1}^n a_k\,U_{k-1}(c)\,w^{k-1} $$ has no zero in $\D$. Here $U_n$ is the
Chebyshev polynomial of the second kind."
Lean form: the "if" direction only (the paper uses only it), for `H` with `H(0) = 0`; `P_c` = `dieudonne H H.natDegree c`
(the coefficients of index above `deg H` are `0`). The extension to every polynomial (tex l.281-283) is the claim
`sec4_dieudonne_any`, proved from this. The hypothesis `H(0) = 0` is not needed (`dieudonne_injOn`). -/
theorem dieudonne_criterion_proved (H : ℂ[X]) (h0 : H.coeff 0 = 0)
    (hP : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w ∈ disk, (dieudonne H H.natDegree c).eval w ≠ 0) :
    IsUnivalentOn (fun z => H.eval z) disk :=
  ⟨H.differentiable.differentiableOn, dieudonne_injOn H hP⟩

end Smale
