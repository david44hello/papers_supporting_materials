/-
Smale/Proofs/JNFekete.lean — Fekete separation: for a compact infinite `E` with connected complement and a closed `F`
disjoint from `E`, one polynomial is small on `E` and larger on `F`. Fekete points on `E` make the Lagrange basis
bounded by `1` on `E`; a finite family of polynomials separating `F` from `E` then forces the node polynomial to be
large on `F`. This replaces Hilbert's lemniscate theorem.
-/
import Smale.Proofs.JNPole

namespace Smale

open Polynomial Complex Metric Filter Topology Set

/-! ### Separating polynomials -/

/-- One polynomial separating a point off `E` from `E`. -/
theorem exists_separator_at {E : Set ℂ} (hE : IsCompact E) (hc : IsPreconnected Eᶜ) {y : ℂ} (hy : y ∉ E) :
    ∃ p : ℂ[X], (∀ w ∈ E, ‖p.eval w‖ ≤ 1) ∧ ‖p.eval y‖ = 2 := by
  obtain ⟨M, hM⟩ := hE.isBounded.exists_norm_le
  set L : ℝ := |M| + ‖y‖ + 1 with hLdef
  have hL : 0 < L := by positivity
  obtain ⟨p₀, hp₀⟩ := exists_poly_near_inv hE hc hy (ε := 1 / (2 * L)) (by positivity)
  refine ⟨C 2 * (1 - (X - C y) * p₀), fun w hw => ?_, ?_⟩
  · have hwy : w - y ≠ 0 := fun h => hy (by rw [← sub_eq_zero.1 h]; exact hw)
    have hlen : ‖w - y‖ ≤ L := by
      have h1 := norm_sub_le w y
      have h2 := (hM w hw).trans (le_abs_self M)
      rw [hLdef]
      linarith
    have key : 1 - (w - y) * p₀.eval w = -((w - y) * (p₀.eval w - (w - y)⁻¹)) := by
      field_simp
      ring
    simp only [eval_mul, eval_C, eval_sub, eval_one, eval_X]
    rw [key, norm_mul, norm_neg, norm_mul, Complex.norm_ofNat]
    have h3 := (hp₀ w hw).le
    calc 2 * (‖w - y‖ * ‖p₀.eval w - (w - y)⁻¹‖) ≤ 2 * (L * (1 / (2 * L))) := by gcongr
      _ = 1 := by field_simp
  · simp

/-- A finite family of polynomials, at most `1` on `E`, one of them at least `3/2` at each point of `F`. -/
theorem exists_separators {E F : Set ℂ} (hE : IsCompact E) (hc : IsPreconnected Eᶜ) (hF : IsClosed F)
    (hd : Disjoint E F) :
    ∃ (ps : Finset ℂ[X]) (D : ℕ), 1 ≤ D ∧ (∀ p ∈ ps, p.natDegree ≤ D) ∧ (∀ p ∈ ps, ∀ w ∈ E, ‖p.eval w‖ ≤ 1) ∧
      ∀ y ∈ F, ∃ p ∈ ps, 3 / 2 ≤ ‖p.eval y‖ := by
  classical
  obtain ⟨M, hM⟩ := hE.isBounded.exists_norm_le
  set M' : ℝ := max M 1 with hM'def
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hK : IsCompact (F ∩ closedBall (0 : ℂ) (3 / 2 * M')) := (isCompact_closedBall _ _).inter_left hF
  have hsep : ∀ y, y ∈ F → ∃ p : ℂ[X], (∀ w ∈ E, ‖p.eval w‖ ≤ 1) ∧ ‖p.eval y‖ = 2 :=
    fun y hy => exists_separator_at hE hc (Set.disjoint_right.1 hd hy)
  choose! pf hpf1 hpf2 using hsep
  have hnhds : ∀ y ∈ F ∩ closedBall (0 : ℂ) (3 / 2 * M'), {x : ℂ | 3 / 2 < ‖(pf y).eval x‖} ∈ 𝓝 y := by
    intro y hy
    have hopen : IsOpen {x : ℂ | 3 / 2 < ‖(pf y).eval x‖} :=
      isOpen_lt continuous_const (pf y).continuous.norm
    refine hopen.mem_nhds ?_
    show 3 / 2 < ‖(pf y).eval y‖
    rw [hpf2 y hy.1]
    norm_num
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover _ hnhds
  set pinf : ℂ[X] := C (M' : ℂ)⁻¹ * X with hpinf
  have hpinfeval : ∀ w : ℂ, ‖pinf.eval w‖ = ‖w‖ / M' := by
    intro w
    rw [hpinf, eval_mul, eval_C, eval_X, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hM'pos.le,
      inv_mul_eq_div]
  set ps : Finset ℂ[X] := insert pinf (t.image pf) with hps
  refine ⟨ps, ps.sup natDegree + 1, by omega, fun p hp => ?_, fun p hp w hw => ?_, fun y hy => ?_⟩
  · have := Finset.le_sup (f := natDegree) hp
    omega
  · rw [hps, Finset.mem_insert, Finset.mem_image] at hp
    rcases hp with rfl | ⟨x, hx, rfl⟩
    · rw [hpinfeval, div_le_one hM'pos]
      exact (hM w hw).trans (le_max_left _ _)
    · exact hpf1 x (htK x hx).1 w hw
  · by_cases hyball : ‖y‖ ≤ 3 / 2 * M'
    · have hmem : y ∈ F ∩ closedBall (0 : ℂ) (3 / 2 * M') := ⟨hy, by simpa using hyball⟩
      obtain ⟨U, ⟨x, rfl⟩, ⟨U', ⟨hx, rfl⟩, hyU⟩⟩ := hcover hmem
      refine ⟨pf x, ?_, le_of_lt hyU⟩
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx)
    · refine ⟨pinf, Finset.mem_insert_self _ _, ?_⟩
      rw [hpinfeval, le_div_iff₀ hM'pos]
      exact (not_le.1 hyball).le

/-! ### Fekete points -/

/-- The product of `|ζ i - ζ i'|` over all ordered pairs of distinct indices. -/
noncomputable def fekVdm {N : ℕ} (ζ : Fin N → ℂ) : ℝ := ∏ i, ∏ i' ∈ Finset.univ.erase i, ‖ζ i - ζ i'‖

/-- The factors of `fekVdm` not involving the index `j`. -/
noncomputable def fekRest {N : ℕ} (j : Fin N) (ζ : Fin N → ℂ) : ℝ :=
  ∏ i ∈ Finset.univ.erase j, ∏ i' ∈ (Finset.univ.erase i).erase j, ‖ζ i - ζ i'‖

theorem fekVdm_split {N : ℕ} (ζ : Fin N → ℂ) (j : Fin N) :
    fekVdm ζ = (∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖) ^ 2 * fekRest j ζ := by
  unfold fekVdm fekRest
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  have h : ∀ i ∈ Finset.univ.erase j, ∏ i' ∈ Finset.univ.erase i, ‖ζ i - ζ i'‖ =
      ‖ζ j - ζ i‖ * ∏ i' ∈ (Finset.univ.erase i).erase j, ‖ζ i - ζ i'‖ := by
    intro i hi
    rw [← Finset.mul_prod_erase (Finset.univ.erase i) _
      (Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hi).symm, Finset.mem_univ j⟩), norm_sub_rev]
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, sq]
  ring

theorem fekRest_update {N : ℕ} (ζ : Fin N → ℂ) (j : Fin N) (z : ℂ) :
    fekRest j (Function.update ζ j z) = fekRest j ζ := by
  unfold fekRest
  refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun i' hi' => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), Function.update_of_ne (Finset.ne_of_mem_erase hi')]

theorem fekVdm_update_factor {N : ℕ} (ζ : Fin N → ℂ) (j : Fin N) (z : ℂ) :
    ∏ i ∈ Finset.univ.erase j, ‖Function.update ζ j z j - Function.update ζ j z i‖ =
      ∏ i ∈ Finset.univ.erase j, ‖z - ζ i‖ := by
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_self, Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem fekVdm_pos {N : ℕ} {ζ : Fin N → ℂ} (hinj : Function.Injective ζ) : 0 < fekVdm ζ :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hi' =>
    norm_pos_iff.2 (sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hi') (hinj h).symm)

theorem injective_of_fekVdm_pos {N : ℕ} {ζ : Fin N → ℂ} (h : 0 < fekVdm ζ) : Function.Injective ζ := by
  intro i i' hii'
  by_contra hne
  have h0 : fekVdm ζ = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (i := i')
      (Finset.mem_erase.2 ⟨fun h1 => hne h1.symm, Finset.mem_univ _⟩) ?_)
    rw [hii', sub_self, norm_zero]
  exact h.ne' h0

/-- **Fekete nodes**: `N` distinct points of `E` for which the Lagrange basis is at most `1` on `E`. -/
theorem fekete_nodes {E : Set ℂ} (hE : IsCompact E) (hinf : E.Infinite) (N : ℕ) :
    ∃ ζ : Fin N → ℂ, Function.Injective ζ ∧ (∀ i, ζ i ∈ E) ∧
      ∀ j, ∀ z ∈ E, ∏ i ∈ Finset.univ.erase j, ‖z - ζ i‖ ≤ ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖ := by
  set ζ₀ : Fin N → ℂ := fun i => (hinf.natEmbedding E i.val : ℂ) with hζ₀
  have hζ₀inj : Function.Injective ζ₀ := fun i i' h =>
    Fin.ext ((hinf.natEmbedding E).injective (Subtype.ext h))
  have hcomp : IsCompact (Set.pi Set.univ fun _ : Fin N => E) := isCompact_univ_pi fun _ => hE
  have hcont : Continuous (fekVdm (N := N)) := by
    unfold fekVdm
    fun_prop
  obtain ⟨ζ, hζ, hmax⟩ := hcomp.exists_isMaxOn ⟨ζ₀, fun i _ => (hinf.natEmbedding E i.val).2⟩ hcont.continuousOn
  have hζE : ∀ i, ζ i ∈ E := fun i => hζ i (Set.mem_univ i)
  have hpos : 0 < fekVdm ζ := lt_of_lt_of_le (fekVdm_pos hζ₀inj) (hmax fun i _ => (hinf.natEmbedding E i.val).2)
  refine ⟨ζ, injective_of_fekVdm_pos hpos, hζE, fun j z hz => ?_⟩
  have hupd : Function.update ζ j z ∈ Set.pi Set.univ fun _ : Fin N => E := by
    intro i _
    by_cases hij : i = j
    · rw [hij, Function.update_self]
      exact hz
    · rw [Function.update_of_ne hij]
      exact hζE i
  have hle : fekVdm (Function.update ζ j z) ≤ fekVdm ζ := hmax hupd
  rw [fekVdm_split (Function.update ζ j z) j, fekVdm_update_factor, fekRest_update, fekVdm_split ζ j] at hle
  have hRpos : 0 < fekRest j ζ := by
    rw [fekVdm_split ζ j] at hpos
    by_contra h
    have h2 : (∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖) ^ 2 * fekRest j ζ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 h)
    linarith
  have hsq := le_of_mul_le_mul_right hle hRpos
  exact (pow_le_pow_iff_left₀ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) two_ne_zero).1 hsq

/-! ### Lagrange interpolation -/

theorem norm_eval_lagrange_basis {N : ℕ} (ζ : Fin N → ℂ) (j : Fin N) (y : ℂ) :
    ‖(Lagrange.basis Finset.univ ζ j).eval y‖ =
      (∏ i ∈ Finset.univ.erase j, ‖y - ζ i‖) / ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖ := by
  rw [Lagrange.basis, eval_prod, norm_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Lagrange.basisDivisor, div_eq_inv_mul]

/-- Interpolation: a polynomial of low degree, at most `1` at the nodes, is bounded by the sum of the Lagrange basis. -/
theorem interpolation_bound {N : ℕ} {ζ : Fin N → ℂ} (hinj : Function.Injective ζ) {f : ℂ[X]}
    (hdeg : f.degree < N) (hf : ∀ i, ‖f.eval (ζ i)‖ ≤ 1) (y : ℂ) :
    ‖f.eval y‖ ≤ ∑ j, (∏ i ∈ Finset.univ.erase j, ‖y - ζ i‖) / ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖ := by
  have hrep := Lagrange.eq_interpolate (s := Finset.univ) (v := ζ) (f := f) hinj.injOn (by simpa using hdeg)
  rw [hrep, Lagrange.interpolate_apply, eval_finsetSum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [eval_mul, eval_C, norm_mul, norm_eval_lagrange_basis]
  have h0 : 0 ≤ (∏ i ∈ Finset.univ.erase j, ‖y - ζ i‖) / ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖ :=
    div_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  calc _ ≤ 1 * ((∏ i ∈ Finset.univ.erase j, ‖y - ζ i‖) / ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖) :=
        mul_le_mul_of_nonneg_right (hf j) h0
    _ = _ := one_mul _

/-! ### The separation -/

/-- `(3/2)^K` beats a linear function of `K`. -/
theorem exists_pow_ge_linear {c : ℝ} (hc : 0 < c) : ∃ K : ℕ, 1 ≤ K ∧ c * K ≤ (3 / 2 : ℝ) ^ K := by
  have h := tendsto_self_mul_const_pow_of_abs_lt_one (r := (2 / 3 : ℝ))
    (by rw [abs_of_pos (by norm_num)]; norm_num)
  have h2 := h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / c by positivity))
  obtain ⟨K, hK, hK1⟩ := (h2.and (eventually_ge_atTop 1)).exists
  refine ⟨K, hK1, ?_⟩
  have hpos : (0 : ℝ) < (2 / 3) ^ K := by positivity
  have hmul : (3 / 2 : ℝ) ^ K * (2 / 3) ^ K = 1 := by
    rw [← mul_pow]
    norm_num
  rw [lt_div_iff₀ hc] at hK
  nlinarith

/-- `‖Q(x)‖` splits off the node `j`. -/
theorem norm_eval_prod_X_sub_C {N : ℕ} (ζ : Fin N → ℂ) (x : ℂ) (j : Fin N) :
    ‖(∏ i, (X - C (ζ i)) : ℂ[X]).eval x‖ = ‖x - ζ j‖ * ∏ i ∈ Finset.univ.erase j, ‖x - ζ i‖ := by
  rw [eval_prod, norm_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp

/-- **Fekete separation.** -/
theorem fekete_separation {E F : Set ℂ} (hE : IsCompact E) (hinf : E.Infinite) (hc : IsPreconnected Eᶜ)
    (hF : IsClosed F) (hd : Disjoint E F) :
    ∃ (Q : ℂ[X]) (a c : ℝ), 1 ≤ Q.natDegree ∧ 0 < a ∧ a < c ∧ (∀ w ∈ E, ‖Q.eval w‖ ≤ a) ∧
      ∀ w ∈ F, c ≤ ‖Q.eval w‖ := by
  classical
  obtain ⟨ps, D, hD, hdeg, hE1, hF1⟩ := exists_separators hE hc hF hd
  -- the gap between `E` and `F`
  obtain ⟨δ, hδ, hthick⟩ := hE.exists_thickening_subset_open hF.isOpen_compl (Set.disjoint_left.1 hd)
  have hgap : ∀ w ∈ E, ∀ y ∈ F, δ ≤ ‖y - w‖ := by
    intro w hw y hy
    by_contra hlt
    have hmem : y ∈ thickening δ E := by
      rw [mem_thickening_iff]
      exact ⟨w, hw, by rw [dist_eq_norm]; exact not_le.1 hlt⟩
    exact hthick hmem hy
  obtain ⟨M₀, hM₀⟩ := hE.isBounded.exists_norm_le
  set M : ℝ := max M₀ 1 with hMdef
  have hM0 : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM : ∀ w ∈ E, ‖w‖ ≤ M := fun w hw => (hM₀ w hw).trans (le_max_left _ _)
  -- the number of nodes
  obtain ⟨K, hK1, hKbig⟩ := exists_pow_ge_linear (c := 2 * (2 * M) * ((D : ℝ) + 1) / δ) (by positivity)
  set N : ℕ := D * K + 1 with hNdef
  have hNpos : 0 < N := by omega
  obtain ⟨ζ, hinj, hζE, hmax⟩ := fekete_nodes hE hinf N
  set Q : ℂ[X] := ∏ i, (X - C (ζ i)) with hQdef
  have hQdeg : Q.natDegree = N := by
    rw [hQdef, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
  -- the maximum of `|Q|` on `E`
  obtain ⟨w₀, hw₀, hw₀max⟩ := hE.exists_isMaxOn hinf.nonempty (Q.continuous.norm.continuousOn)
  have hQne : Q ≠ 0 := fun h => by
    rw [h, natDegree_zero] at hQdeg
    omega
  have ha : 0 < ‖Q.eval w₀‖ := by
    obtain ⟨w₁, hw₁, hw₁r⟩ := hinf.exists_notMem_finset Q.roots.toFinset
    have h1 : Q.eval w₁ ≠ 0 := fun h =>
      hw₁r (Multiset.mem_toFinset.2 ((mem_roots hQne).2 h))
    exact lt_of_lt_of_le (norm_pos_iff.2 h1) (hw₀max hw₁)
  refine ⟨Q, ‖Q.eval w₀‖, 2 * ‖Q.eval w₀‖, by omega, ha, by linarith, fun w hw => hw₀max hw, fun y hy => ?_⟩
  obtain ⟨p, hp, hpy⟩ := hF1 y hy
  -- `p ^ K` has degree below `N`, and modulus at most `1` at the nodes
  have hdegK : (p ^ K).degree < N := by
    refine lt_of_le_of_lt degree_le_natDegree ?_
    have h1 : (p ^ K).natDegree ≤ K * p.natDegree := natDegree_pow_le
    have h2 : K * p.natDegree ≤ K * D := Nat.mul_le_mul_left _ (hdeg p hp)
    have h3 : (p ^ K).natDegree < N := by
      rw [hNdef, Nat.mul_comm D K]
      omega
    exact_mod_cast h3
  have hnodes : ∀ i, ‖(p ^ K).eval (ζ i)‖ ≤ 1 := fun i => by
    rw [eval_pow, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hE1 p hp _ (hζE i))
  have hint := interpolation_bound hinj hdegK hnodes y
  have hlow : (3 / 2 : ℝ) ^ K ≤ ‖(p ^ K).eval y‖ := by
    rw [eval_pow, norm_pow]
    exact pow_le_pow_left₀ (by norm_num) hpy K
  -- one Lagrange term is large
  obtain ⟨j, hj⟩ : ∃ j : Fin N, (3 / 2 : ℝ) ^ K / N ≤
      (∏ i ∈ Finset.univ.erase j, ‖y - ζ i‖) / ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖ := by
    by_contra hall
    push Not at hall
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hsum : ∑ j, (∏ i ∈ Finset.univ.erase j, ‖y - ζ i‖) / ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖ <
        ∑ _j : Fin N, (3 / 2 : ℝ) ^ K / N :=
      Finset.sum_lt_sum_of_nonempty ⟨⟨0, hNpos⟩, Finset.mem_univ _⟩ fun j _ => hall j
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hNreal.ne'] at hsum
    linarith
  -- the denominators are positive
  have hdj : 0 < ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖ :=
    Finset.prod_pos fun i hi => norm_pos_iff.2 (sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hi) (hinj h).symm)
  -- `a ≤ 2 M d_j`
  have haj : ‖Q.eval w₀‖ ≤ 2 * M * ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖ := by
    rw [hQdef, norm_eval_prod_X_sub_C ζ w₀ j]
    have h1 : ‖w₀ - ζ j‖ ≤ 2 * M := by
      have h2 := norm_sub_le w₀ (ζ j)
      have h3 := hM w₀ hw₀
      have h4 := hM _ (hζE j)
      linarith
    exact mul_le_mul h1 (hmax j w₀ hw₀) (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
  -- the bound at `y`
  have hyj : δ ≤ ‖y - ζ j‖ := hgap _ (hζE j) y hy
  have hprod : (3 / 2 : ℝ) ^ K / N * ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖ ≤ ∏ i ∈ Finset.univ.erase j, ‖y - ζ i‖ := by
    rwa [le_div_iff₀ hdj] at hj
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNle : (N : ℝ) ≤ ((D : ℝ) + 1) * K := by
    have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    rw [hNdef]
    push_cast
    nlinarith
  -- `2 · 2M · N / δ ≤ (3/2)^K`
  have hbig : 2 * (2 * M) * N / δ ≤ (3 / 2 : ℝ) ^ K := by
    refine le_trans ?_ hKbig
    rw [div_mul_eq_mul_div, mul_assoc (2 * (2 * M))]
    gcongr
  have hfinal : 2 * (2 * M) ≤ δ * ((3 / 2 : ℝ) ^ K / N) := by
    rw [div_le_iff₀ hδ] at hbig
    rw [← mul_div_assoc, le_div_iff₀ hNreal]
    linarith
  rw [hQdef, norm_eval_prod_X_sub_C ζ y j]
  calc 2 * ‖(∏ i, (X - C (ζ i)) : ℂ[X]).eval w₀‖
      ≤ 2 * (2 * M * ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖) := by gcongr
    _ = 2 * (2 * M) * ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖ := by ring
    _ ≤ (δ * ((3 / 2 : ℝ) ^ K / N)) * ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖ := by gcongr
    _ = δ * ((3 / 2 : ℝ) ^ K / N * ∏ i ∈ Finset.univ.erase j, ‖ζ j - ζ i‖) := by ring
    _ ≤ ‖y - ζ j‖ * ∏ i ∈ Finset.univ.erase j, ‖y - ζ i‖ := by
      apply mul_le_mul hyj hprod _ (norm_nonneg _)
      positivity

end Smale
