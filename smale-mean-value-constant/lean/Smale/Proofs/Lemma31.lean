/-
Smale/Proofs/Lemma31.lean — paper 009, Lemma 3.1 (tex l.193-217): from a polynomial `Q` with no critical point in `𝔻`
and `k + 1` distinct zeros `b, a₁, …, a_k` in `𝔻` such that `H = Q ∏ (1 - ā_j z)/(z - a_j)` is univalent in `𝔻`, the
pair `W = (H ∘ φ)/N`, `B = (|η|/η) ∏ B_{a_j} ∘ φ` is admissible with `deg B = k` and `1/B(0)² = ∏ J(a_j, b)`.
The paper's step "as `H` is univalent, `H'(b) ≠ 0`" is proved for polynomials from Rouché's theorem.
Helpers live in namespace `Smale.Lem31`.
-/
import Smale.Proofs.Disk
import Smale.Proofs.Hpoly
import Smale.Proofs.ArgPrinciple

namespace Smale

namespace Lem31

open Polynomial Complex Metric Filter Topology ComplexConjugate

/-! ### A polynomial injective on `𝔻` has no critical point in `𝔻` -/

/-- Two distinct elements of a multiset without repeated elements and with at least two elements. -/
theorem exists_ne_of_nodup {s : Multiset ℂ} (hs : s.Nodup) (h2 : 2 ≤ Multiset.card s) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card s)
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hx
  rw [Multiset.card_cons] at h2
  obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card t)
  have hxt : x ∉ t := (Multiset.nodup_cons.1 hs).1
  refine ⟨x, Multiset.mem_cons.2 (Or.inl rfl), y, Multiset.mem_cons_of_mem hy, fun h => hxt ?_⟩
  rw [h]
  exact hy

/-- A real number in `(0, c)` outside a given finite set. -/
theorem exists_mem_Ioo_notMem {c : ℝ} (hc : 0 < c) (S : Finset ℝ) : ∃ t, 0 < t ∧ t < c ∧ t ∉ S := by
  obtain ⟨t, ht, htS⟩ := (Set.Ioo_infinite hc).exists_notMem_finset S
  exact ⟨t, ht.1, ht.2, htS⟩

/-- A polynomial `H` that is injective on `𝔻` is not constant: `H' ≠ 0`. -/
theorem derivative_ne_zero_of_injOn (H : ℂ[X]) (hinj : Set.InjOn (fun z => H.eval z) disk) :
    H.derivative ≠ 0 := by
  intro h0
  have hc : H = C (H.coeff 0) := eq_C_of_natDegree_eq_zero (derivative_eq_zero.mp h0)
  have h12 : (2 : ℂ)⁻¹ ∈ disk := by
    rw [mem_ball_zero_iff, norm_inv, Complex.norm_two]
    norm_num
  have h00 : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  have := hinj h00 h12 (by simp only; rw [hc, eval_C, eval_C])
  norm_num at this

/-- The paper's "as `H` is univalent, `H'(b) ≠ 0`", for a polynomial `H` injective on `𝔻` and `b ∈ 𝔻`. If
`H'(b) = 0`, then `f = H - H(b)` has a zero of order at least `2` at `b`. On a circle `|w - b| = R` inside `𝔻` that
carries no zero of `f`, `|f|` has a positive minimum `μ`; for `0 < t < μ`, Rouché gives `f - t` at least `2` zeros in
`|w - b| < R`, and for `t` not a critical value of `f` these zeros are simple, hence two distinct points of `𝔻` with the
same value of `H`. -/
theorem derivative_eval_ne_zero_of_injOn (H : ℂ[X]) (hinj : Set.InjOn (fun z => H.eval z) disk) {b : ℂ}
    (hb : b ∈ disk) : H.derivative.eval b ≠ 0 := by
  classical
  intro hb'
  have hb1 : ‖b‖ < 1 := mem_ball_zero_iff.1 hb
  have hH' := derivative_ne_zero_of_injOn H hinj
  set f : ℂ[X] := H - C (H.eval b) with hf
  have hfd : f.derivative = H.derivative := by simp [hf]
  have hf0 : f ≠ 0 := by
    intro h0
    apply hH'
    rw [← hfd, h0, derivative_zero]
  have hfb : f.IsRoot b := by simp [hf]
  have hf'b : f.derivative.IsRoot b := by rw [hfd]; exact hb'
  have hmult : 1 < rootMultiplicity b f := (one_lt_rootMultiplicity_iff_isRoot hf0).2 ⟨hfb, hf'b⟩
  -- a radius `R < 1 - |b|` with no zero of `f` on the circle `|w - b| = R`
  obtain ⟨R, hR0, hR1, hRS⟩ := exists_mem_Ioo_notMem (by linarith : 0 < 1 - ‖b‖)
    (f.roots.toFinset.image fun z => ‖z - b‖)
  have hsph : ∀ w : ℂ, ‖w - b‖ = R → f.eval w ≠ 0 := by
    intro w hw h0
    apply hRS
    rw [Finset.mem_image]
    exact ⟨w, Multiset.mem_toFinset.2 ((mem_roots hf0).2 h0), hw⟩
  have hball : ∀ w : ℂ, ‖w - b‖ < R → w ∈ disk := by
    intro w hw
    rw [mem_ball_zero_iff]
    calc ‖w‖ = ‖(w - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - b‖ + ‖b‖ := norm_add_le _ _
      _ < 1 := by linarith
  -- the minimum `μ > 0` of `|f|` on the circle
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere b R).exists_isMinOn (NormedSpace.sphere_nonempty.2 hR0.le)
    f.continuous.norm.continuousOn
  have hw₀' : ‖w₀ - b‖ = R := by rw [← dist_eq_norm]; exact mem_sphere.1 hw₀
  have hμ : 0 < ‖f.eval w₀‖ := norm_pos_iff.2 (hsph w₀ hw₀')
  -- a value `t ∈ (0, μ)` that is not a critical value of `f`
  obtain ⟨t, ht0, htμ, htS⟩ := exists_mem_Ioo_notMem hμ
    (f.derivative.roots.toFinset.image fun z => (f.eval z).re)
  set g : ℂ[X] := f + -C (t : ℂ) with hg
  have hrouche : zerosInBall g b R = zerosInBall f b R :=
    zerosInBall_add_of_norm_lt f (-C (t : ℂ)) b hR0 fun w hw => by
      rw [eval_neg, eval_C, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact htμ.trans_le (isMinOn_iff.1 hmin w (by rw [mem_sphere, dist_eq_norm]; exact hw))
  have hcount : 2 ≤ zerosInBall f b R := by
    unfold zerosInBall
    calc 2 ≤ rootMultiplicity b f := hmult
      _ = (f.roots.filter fun w => ‖w - b‖ < R).count b := by
          rw [Multiset.count_filter_of_pos (by simpa using hR0), count_roots]
      _ ≤ _ := Multiset.count_le_card _ _
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 : g.eval b = 0 := by rw [h0, eval_zero]
    rw [hg, eval_add, hfb.eq_zero, eval_neg, eval_C, zero_add, neg_eq_zero] at h1
    exact ht0.ne' (Complex.ofReal_eq_zero.1 h1)
  -- the zeros of `g = f - t` are simple
  have hnodup : g.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro z
    rw [count_roots]
    by_contra hz
    obtain ⟨hgz, hg'z⟩ := (one_lt_rootMultiplicity_iff_isRoot hg0).1 (not_le.1 hz)
    have hgd : g.derivative = f.derivative := by simp [hg]
    have hfz : f.eval z = (t : ℂ) := by
      have h1 := hgz.eq_zero
      rw [hg, eval_add, eval_neg, eval_C] at h1
      linear_combination h1
    apply htS
    rw [Finset.mem_image]
    refine ⟨z, Multiset.mem_toFinset.2 ((mem_roots (by rw [hfd]; exact hH')).2 ?_), ?_⟩
    · rw [← hgd]; exact hg'z
    · rw [hfz, Complex.ofReal_re]
  -- two distinct zeros of `g` in `|w - b| < R`, both in `𝔻`, with the same value of `H`
  have h2 : 2 ≤ Multiset.card (g.roots.filter fun w => ‖w - b‖ < R) := by
    have h3 : 2 ≤ zerosInBall g b R := hrouche ▸ hcount
    unfold zerosInBall at h3
    exact h3
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_ne_of_nodup (hnodup.filter _) h2
  rw [Multiset.mem_filter] at hx hy
  apply hxy
  apply hinj (hball x hx.2) (hball y hy.2)
  have hgx := ((mem_roots hg0).1 hx.1).eq_zero
  have hgy := ((mem_roots hg0).1 hy.1).eq_zero
  simp only [hg, hf, eval_add, eval_neg, eval_C, eval_sub] at hgx hgy
  show H.eval x = H.eval y
  linear_combination hgx - hgy

/-! ### The algebra of the construction -/

theorem eval_zerosPoly (as : List ℂ) (u : ℂ) : (zerosPoly as).eval u = (as.map fun a => u - a).prod := by
  simp [zerosPoly, eval_list_prod, Function.comp_def]

theorem eval_reflPoly (as : List ℂ) (u : ℂ) :
    (reflPoly as).eval u = (as.map fun a => 1 - conj a * u).prod := by
  simp [reflPoly, eval_list_prod, Function.comp_def]

/-- `∏ B_{a_j}(u) · ∏ (1 - ā_j u) = ∏ (u - a_j)` when no `1 - ā_j u` vanishes. -/
theorem prod_blaschke_mul (u : ℂ) :
    ∀ as : List ℂ, (∀ a ∈ as, 1 - conj a * u ≠ 0) →
      (as.map fun a => blaschkeFactor a u).prod * (as.map fun a => 1 - conj a * u).prod =
        (as.map fun a => u - a).prod
  | [], _ => by simp
  | a :: as, hden => by
    have ha := hden a List.mem_cons_self
    have ih := prod_blaschke_mul u as fun a' ha' => hden a' (List.mem_cons_of_mem _ ha')
    simp only [List.map_cons, List.prod_cons]
    rw [← ih, blaschkeFactor, div_eq_mul_inv]
    linear_combination ((u - a) * (as.map fun a => blaschkeFactor a u).prod *
      (as.map fun a => 1 - conj a * u).prod) * inv_mul_cancel₀ ha

/-- `H(u) ∏ B_{a_j}(u) = Q(u)` on `𝔻` (the paper's `H ∏_j B_{a_j} = Q`). -/
theorem eval_Hpoly_mul_prod (Q : ℂ[X]) (as : List ℂ) (hnd : as.Nodup) (hz : ∀ a ∈ as, Q.eval a = 0)
    (hin : ∀ a ∈ as, a ∈ disk) {u : ℂ} (hu : u ∈ disk) :
    (Hpoly Q as).eval u * (as.map fun a => blaschkeFactor a u).prod = Q.eval u := by
  have hden : ∀ a ∈ as, 1 - conj a * u ≠ 0 := fun a ha =>
    one_sub_mul_ne_zero (by rw [Complex.norm_conj]; exact mem_ball_zero_iff.1 (hin a ha)) (mem_ball_zero_iff.1 hu).le
  have hR : (as.map fun a => 1 - conj a * u).prod ≠ 0 := List.prod_ne_zero fun h0 => by
    obtain ⟨a, ha, h⟩ := List.mem_map.1 h0
    exact hden a ha h
  have hH := congrArg (fun p => p.eval u) (lem_3_1_H_poly_proved Q as hnd hz)
  simp only [eval_mul] at hH
  rw [eval_zerosPoly, eval_reflPoly] at hH
  apply mul_right_cancel₀ hR
  rw [mul_assoc, prod_blaschke_mul u as hden, hH]

/-- `H(b) = 0`: `Q(b) = 0` and `b` is none of the `a_j`. -/
theorem eval_Hpoly_eq_zero (Q : ℂ[X]) (as : List ℂ) (hnd : as.Nodup) (hz : ∀ a ∈ as, Q.eval a = 0) {b : ℂ}
    (hba : b ∉ as) (hQb : Q.eval b = 0) : (Hpoly Q as).eval b = 0 := by
  have hZ : (zerosPoly as).eval b ≠ 0 := by
    rw [eval_zerosPoly]
    refine List.prod_ne_zero fun h0 => ?_
    obtain ⟨a, ha, h⟩ := List.mem_map.1 h0
    exact hba (by rw [sub_eq_zero.1 h]; exact ha)
  have hH := congrArg (fun p => p.eval b) (lem_3_1_H_poly_proved Q as hnd hz)
  simp only [eval_mul, hQb, zero_mul] at hH
  exact (mul_eq_zero.1 hH).resolve_right hZ

/-- `η = ∏ B_{a_j}(b) ≠ 0`. -/
theorem etaOf_ne_zero {as : List ℂ} {b : ℂ} (hb : b ∈ disk) (hin : ∀ a ∈ as, a ∈ disk) (hba : b ∉ as) :
    etaOf as b ≠ 0 := by
  unfold etaOf
  refine List.prod_ne_zero fun h0 => ?_
  obtain ⟨a, ha, h⟩ := List.mem_map.1 h0
  rw [blaschkeFactor, div_eq_zero_iff, sub_eq_zero] at h
  rcases h with h | h
  · exact hba (by rw [h]; exact ha)
  · exact one_sub_mul_ne_zero (by rw [Complex.norm_conj]; exact mem_ball_zero_iff.1 (hin a ha))
      (mem_ball_zero_iff.1 hb).le h

theorem etaOf_cons (a : ℂ) (as : List ℂ) (b : ℂ) : etaOf (a :: as) b = blaschkeFactor a b * etaOf as b := by
  simp [etaOf]

/-- `B(0) = |η|`. -/
theorem BOf_zero {as : List ℂ} {b : ℂ} (hη : etaOf as b ≠ 0) : BOf as b 0 = (‖etaOf as b‖ : ℂ) := by
  have h0 : diskAut b 0 = b := by simp [diskAut]
  rw [BOf, h0]
  change (‖etaOf as b‖ : ℂ) / etaOf as b * etaOf as b = _
  rw [div_mul_cancel₀ _ hη]

/-- `1/|η|² = ∏ J(a_j, b)`. -/
theorem one_div_norm_etaOf_sq (b : ℂ) (hb : b ∈ disk) :
    ∀ as : List ℂ, (∀ a ∈ as, a ∈ disk) → b ∉ as → 1 / ‖etaOf as b‖ ^ 2 = (as.map fun a => Jab a b).prod
  | [], _, _ => by simp [etaOf]
  | a :: as, hin, hba => by
    have ha := hin a List.mem_cons_self
    have hab : a ≠ b := fun h => hba (by rw [← h]; exact List.mem_cons_self)
    have ih := one_div_norm_etaOf_sq b hb as (fun a' ha' => hin a' (List.mem_cons_of_mem _ ha'))
      fun h => hba (List.mem_cons_of_mem _ h)
    rw [etaOf_cons, norm_mul, mul_pow, ← one_div_mul_one_div, ih, sec3_J_proved a b ha hb hab, List.map_cons,
      List.prod_cons]

/-- `WB = (|η|/(ηN)) Q ∘ φ` on `𝔻`. -/
theorem WOf_mul_BOf {Q : ℂ[X]} {as : List ℂ} {b : ℂ} (hnd : as.Nodup) (hz : ∀ a ∈ as, Q.eval a = 0)
    (hin : ∀ a ∈ as, a ∈ disk) (hb : b ∈ disk) {w : ℂ} (hw : w ∈ disk) :
    WOf Q as b w * BOf as b w = (‖etaOf as b‖ : ℂ) / (etaOf as b * NOf Q as b) * Q.eval (diskAut b w) := by
  have hφ : diskAut b w ∈ disk :=
    mem_ball_zero_iff.2 (norm_diskAut_lt_one (mem_ball_zero_iff.1 hb) (mem_ball_zero_iff.1 hw))
  rw [← eval_Hpoly_mul_prod Q as hnd hz hin hφ, WOf, BOf]
  ring

/-- The derivative of `φ_b` at a point where `1 + b̄w ≠ 0`. -/
theorem hasDerivAt_diskAut_of_ne (b w : ℂ) (hw : 1 + conj b * w ≠ 0) :
    HasDerivAt (diskAut b) ((1 - b * conj b) / (1 + conj b * w) ^ 2) w := by
  have h1 : HasDerivAt (fun w => w + b) 1 w := (hasDerivAt_id w).add_const b
  have h2 : HasDerivAt (fun w => 1 + conj b * w) (conj b) w := by
    simpa using ((hasDerivAt_id w).const_mul (conj b)).const_add 1
  have e : diskAut b = fun w => (w + b) / (1 + conj b * w) := rfl
  rw [e]
  convert h1.div h2 hw using 2
  ring

/-- `(WB)' = (|η|/(ηN)) Q'(φ) φ'` on `𝔻`. -/
theorem deriv_WOf_mul_BOf {Q : ℂ[X]} {as : List ℂ} {b : ℂ} (hnd : as.Nodup) (hz : ∀ a ∈ as, Q.eval a = 0)
    (hin : ∀ a ∈ as, a ∈ disk) (hb : b ∈ disk) {w : ℂ} (hw : w ∈ disk) :
    deriv (fun z => WOf Q as b z * BOf as b z) w =
      (‖etaOf as b‖ : ℂ) / (etaOf as b * NOf Q as b) * Q.derivative.eval (diskAut b w) * deriv (diskAut b) w := by
  set κ := (‖etaOf as b‖ : ℂ) / (etaOf as b * NOf Q as b) with hκ
  have hev : (fun z => WOf Q as b z * BOf as b z) =ᶠ[𝓝 w] fun z => κ * Q.eval (diskAut b z) :=
    eventually_of_mem (isOpen_ball.mem_nhds hw) fun z hz' => WOf_mul_BOf hnd hz hin hb hz'
  have hd : 1 + conj b * w ≠ 0 :=
    one_add_conj_mul_ne_zero (mem_ball_zero_iff.1 hb) (mem_ball_zero_iff.1 hw).le
  have hφ : HasDerivAt (diskAut b) (deriv (diskAut b) w) w :=
    (hasDerivAt_diskAut_of_ne b w hd).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun z => κ * Q.eval (diskAut b z))
      (κ * (Q.derivative.eval (diskAut b w) * deriv (diskAut b) w)) w :=
    ((Q.hasDerivAt (diskAut b w)).comp w hφ).const_mul κ
  rw [hev.deriv_eq, hcomp.deriv, mul_assoc]

/-- `lem_3_1_WB` (tex l.213-217): `B(0) = |η|`; `WB = (|η|/(ηN)) Q ∘ φ` on `𝔻`; `(WB)' = (|η|/(ηN)) Q'(φ) φ'` on `𝔻`. -/
theorem lem_3_1_WB_proved (k : ℕ) (_hk : 1 ≤ k) (Q : ℂ[X]) (b : ℂ) (as : List ℂ) (_hlen : as.length = k)
    (_hQ' : ∀ w ∈ disk, Q.derivative.eval w ≠ 0) (hnd : (b :: as).Nodup) (hin : ∀ a ∈ b :: as, a ∈ disk)
    (hzero : ∀ a ∈ b :: as, Q.eval a = 0) (_huniv : IsUnivalentOn (fun z => (Hpoly Q as).eval z) disk) :
    BOf as b 0 = (‖etaOf as b‖ : ℂ) ∧
      (∀ w ∈ disk, WOf Q as b w * BOf as b w =
        (‖etaOf as b‖ : ℂ) / (etaOf as b * NOf Q as b) * Q.eval (diskAut b w)) ∧
      ∀ w ∈ disk, deriv (fun z => WOf Q as b z * BOf as b z) w =
        (‖etaOf as b‖ : ℂ) / (etaOf as b * NOf Q as b) * Q.derivative.eval (diskAut b w) * deriv (diskAut b) w := by
  obtain ⟨hba, hnd'⟩ := List.nodup_cons.1 hnd
  have hb : b ∈ disk := hin b List.mem_cons_self
  have hin' : ∀ a ∈ as, a ∈ disk := fun a ha => hin a (List.mem_cons_of_mem _ ha)
  have hz' : ∀ a ∈ as, Q.eval a = 0 := fun a ha => hzero a (List.mem_cons_of_mem _ ha)
  exact ⟨BOf_zero (etaOf_ne_zero hb hin' hba), fun w hw => WOf_mul_BOf hnd' hz' hin' hb hw,
    fun w hw => deriv_WOf_mul_BOf hnd' hz' hin' hb hw⟩

/-! ### Lemma 3.1 -/

/-- `B_{a_j} ∘ φ = λ_j B_{γ_j}` for every `j` gives `∏_j B_{a_j} ∘ φ = λ ∏_j B_{γ_j}` with `|λ| = 1`, `γ_j ∈ 𝔻`. -/
theorem prod_blaschke_comp_aut (b : ℂ) (hb : b ∈ disk) :
    ∀ as : List ℂ, (∀ a ∈ as, a ∈ disk) → ∃ lam : ℂ, ∃ gs : List ℂ, ‖lam‖ = 1 ∧ gs.length = as.length ∧
      (∀ g ∈ gs, g ∈ disk) ∧ ∀ w ∈ disk,
        (as.map fun a => blaschkeFactor a (diskAut b w)).prod = lam * (gs.map fun g => blaschkeFactor g w).prod
  | [], _ => ⟨1, [], norm_one, rfl, by simp, fun w _ => by simp⟩
  | a :: as, hin => by
    obtain ⟨l, γ, hl, hγ, hfac⟩ := lem_3_1_aut_proved a b (hin a List.mem_cons_self) hb
    obtain ⟨lam, gs, hlam, hlen, hgs, hprod⟩ :=
      prod_blaschke_comp_aut b hb as fun a' ha' => hin a' (List.mem_cons_of_mem _ ha')
    refine ⟨l * lam, γ :: gs, by rw [norm_mul, hl, hlam, one_mul], by simp [hlen], fun g hg => ?_,
      fun w hw => ?_⟩
    · rcases List.mem_cons.1 hg with rfl | hg
      · exact hγ
      · exact hgs g hg
    · simp only [List.map_cons, List.prod_cons]
      rw [hfac w hw, hprod w hw]
      ring

/-- `lem_3_1` (tex l.193-217): `(W, B)` is an admissible pair, `deg B = k`, and `1/B(0)² = ∏_j J(a_j, b)`. -/
theorem lem_3_1_proved (k : ℕ) (_hk : 1 ≤ k) (Q : ℂ[X]) (b : ℂ) (as : List ℂ) (hlen : as.length = k)
    (hQ' : ∀ w ∈ disk, Q.derivative.eval w ≠ 0) (hnd : (b :: as).Nodup) (hin : ∀ a ∈ b :: as, a ∈ disk)
    (hzero : ∀ a ∈ b :: as, Q.eval a = 0) (huniv : IsUnivalentOn (fun z => (Hpoly Q as).eval z) disk) :
    IsAdmissible (WOf Q as b) (BOf as b) k ∧ 1 / (BOf as b 0).re ^ 2 = (as.map fun a => Jab a b).prod := by
  obtain ⟨hba, hnd'⟩ := List.nodup_cons.1 hnd
  have hb : b ∈ disk := hin b List.mem_cons_self
  have hb' : ‖b‖ < 1 := mem_ball_zero_iff.1 hb
  have hin' : ∀ a ∈ as, a ∈ disk := fun a ha => hin a (List.mem_cons_of_mem _ ha)
  have hz' : ∀ a ∈ as, Q.eval a = 0 := fun a ha => hzero a (List.mem_cons_of_mem _ ha)
  have hη := etaOf_ne_zero hb hin' hba
  have hB0 := BOf_zero hη
  have hφ0 : diskAut b 0 = b := by simp [diskAut]
  -- `H(b) = 0`, `H'(b) ≠ 0`, `N ≠ 0`
  have hHb := eval_Hpoly_eq_zero Q as hnd' hz' hba (hzero b List.mem_cons_self)
  have hH'b := derivative_eval_ne_zero_of_injOn (Hpoly Q as) huniv.2 hb
  have h1b : (1 : ℂ) - (‖b‖ : ℂ) ^ 2 ≠ 0 := by
    have h : (0 : ℝ) < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
    exact_mod_cast h.ne'
  have hN : NOf Q as b ≠ 0 := mul_ne_zero h1b hH'b
  have hφd : ∀ w ∈ disk, 1 + conj b * w ≠ 0 := fun w hw =>
    one_add_conj_mul_ne_zero hb' (mem_ball_zero_iff.1 hw).le
  have hφin : ∀ w ∈ disk, diskAut b w ∈ disk := fun w hw =>
    mem_ball_zero_iff.2 (norm_diskAut_lt_one hb' (mem_ball_zero_iff.1 hw))
  -- `W` has a derivative on `𝔻`
  have hWd : ∀ w ∈ disk, HasDerivAt (WOf Q as b)
      ((Hpoly Q as).derivative.eval (diskAut b w) * deriv (diskAut b) w / NOf Q as b) w := fun w hw =>
    (((Hpoly Q as).hasDerivAt (diskAut b w)).comp w
      (hasDerivAt_diskAut_of_ne b w (hφd w hw)).differentiableAt.hasDerivAt).div_const (NOf Q as b)
  -- `W ∈ 𝒮`
  have hS : InClassS (WOf Q as b) := by
    refine ⟨⟨fun w hw => (hWd w hw).differentiableAt.differentiableWithinAt, ?_⟩, ?_, ?_⟩
    · intro w₁ hw₁ w₂ hw₂ h
      have h' : (Hpoly Q as).eval (diskAut b w₁) = (Hpoly Q as).eval (diskAut b w₂) :=
        (div_left_inj' hN).1 h
      exact diskAut_injOn hb' hw₁ hw₂ (huniv.2 (hφin w₁ hw₁) (hφin w₂ hw₂) h')
    · rw [WOf, hφ0, hHb, zero_div]
    · have hNeq : (Hpoly Q as).derivative.eval b * (1 - (‖b‖ : ℂ) ^ 2) = NOf Q as b := by
        rw [NOf, mul_comm]
      rw [(hWd 0 (mem_ball_self one_pos)).deriv, hφ0, (hasDerivAt_diskAut b).deriv, hNeq, div_self hN]
  -- `B` is a finite Blaschke product of degree `k`
  have hBl : IsFiniteBlaschke (BOf as b) k := by
    obtain ⟨lam, gs, hlam, hlen', hgs, hprod⟩ := prod_blaschke_comp_aut b hb as hin'
    refine ⟨(‖etaOf as b‖ : ℂ) / etaOf as b * lam, gs, ?_, hlen'.trans hlen, hgs, fun w hw => ?_⟩
    · rw [norm_mul, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hη), hlam, one_mul]
    · show BOf as b w = blaschkeProd _ gs w
      rw [BOf, hprod w hw, blaschkeProd]
      ring
  -- `B(0) > 0`
  have hpos : PosAtZero (BOf as b) := by
    refine ⟨?_, ?_⟩ <;> rw [hB0]
    · exact Complex.ofReal_im _
    · rw [Complex.ofReal_re]
      exact norm_pos_iff.2 hη
  -- `(WB)'` has no zero in `𝔻`
  have hWB : ∀ w ∈ disk, deriv (fun z => WOf Q as b z * BOf as b z) w ≠ 0 := by
    intro w hw
    rw [deriv_WOf_mul_BOf hnd' hz' hin' hb hw, (hasDerivAt_diskAut_of_ne b w (hφd w hw)).deriv]
    have hκ : (‖etaOf as b‖ : ℂ) / (etaOf as b * NOf Q as b) ≠ 0 :=
      div_ne_zero (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hη)) (mul_ne_zero hη hN)
    have hbb : (1 : ℂ) - b * conj b ≠ 0 := by
      rw [mul_comm]
      exact one_sub_conj_mul_self_ne_zero hb'
    exact mul_ne_zero (mul_ne_zero hκ (hQ' _ (hφin w hw))) (div_ne_zero hbb (pow_ne_zero 2 (hφd w hw)))
  refine ⟨⟨hS, hBl, hpos, hWB⟩, ?_⟩
  rw [hB0, Complex.ofReal_re]
  exact one_div_norm_etaOf_sq b hb as hin' hba

end Lem31

end Smale
