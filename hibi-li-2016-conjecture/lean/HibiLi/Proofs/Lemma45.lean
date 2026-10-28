/-
HibiLi/Proofs/Lemma45.lean — proof of paper Lemma 4.5 (local product structure of `B` near `u₀`).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Proofs.Lemma44

namespace HibiLi.Proofs

open Finset

namespace Lemma45

/-- The open box of radius `r` around `c` in the sup norm. -/
def box {ι : Type*} (c : ι → ℝ) (r : ℝ) : Set (ι → ℝ) := Set.pi Set.univ fun i => Metric.ball (c i) r

lemma isOpen_box {ι : Type*} [Finite ι] (c : ι → ℝ) (r : ℝ) : IsOpen (box c r) :=
  isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball

lemma center_mem_box {ι : Type*} (c : ι → ℝ) {r : ℝ} (hr : 0 < r) : c ∈ box c r :=
  fun _ _ => Metric.mem_ball_self hr

variable {P : Type*} [Fintype P] [PartialOrder P] (x : HibiLi.XSwitch P)

/-- The radius `ε = 1/(8(n+1))`, `n = |P'|`: any chain moves by at most `n ε ≤ 1/8` on the box. -/
noncomputable def eps : ℝ := 1 / (8 * (Fintype.card x.toSwitch.P' + 1))

lemma eps_pos : 0 < eps x := by unfold eps; positivity

lemma card_mul_eps (K : Finset x.toSwitch.P') : (K.card : ℝ) * eps x ≤ 1 / 8 := by
  have hK : (K.card : ℝ) ≤ Fintype.card x.toSwitch.P' := by exact_mod_cast K.card_le_univ
  have hn : (0 : ℝ) < Fintype.card x.toSwitch.P' + 1 := by positivity
  unfold eps
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma eps_le : eps x ≤ 1 / 8 := by
  unfold eps
  apply one_div_le_one_div_of_le (by norm_num)
  linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ Fintype.card x.toSwitch.P')]

/-- `u` is within `ε` of `u₀` in every coordinate. -/
def Close (u : x.toSwitch.P' → ℝ) : Prop := ∀ p, |u p - x.u0 p| < eps x

lemma distinct : x.pa ≠ x.pb ∧ x.pa ≠ x.pg ∧ x.pa ≠ x.ph ∧ x.pb ≠ x.pg ∧ x.pb ≠ x.ph ∧ x.pg ≠ x.ph :=
  Lemma44.distinct x (pa := x.pa) (pb := x.pb) (pg := x.pg) (ph := x.ph) rfl rfl rfl rfl

lemma not_special {p : x.toSwitch.P'} :
    p ∉ x.special ↔ p ≠ x.pa ∧ p ≠ x.pb ∧ p ≠ x.pg ∧ p ≠ x.ph := by
  simp [XSwitch.special]

lemma u0_pa : x.u0 x.pa = 1 / 4 := by simp [XSwitch.u0]
lemma u0_pb : x.u0 x.pb = 1 / 4 := by simp [XSwitch.u0]
lemma u0_pg : x.u0 x.pg = 3 / 4 := by
  obtain ⟨-, hag, -, hbg, -, -⟩ := distinct x
  simp [XSwitch.u0, hag.symm, hbg.symm]
lemma u0_ph : x.u0 x.ph = 3 / 4 := by
  obtain ⟨-, -, hah, -, hbh, -⟩ := distinct x
  simp [XSwitch.u0, hah.symm, hbh.symm]

lemma u0_I {p : x.toSwitch.P'} (hs : p ∉ x.special) (hp : p.1 ∈ x.toSwitch.I) : x.u0 p = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := (not_special x).mp hs
  simp [XSwitch.u0, h1, h2, h3, h4, hp]

lemma u0_J {p : x.toSwitch.P'} (hs : p ∉ x.special) (hp : p.1 ∉ x.toSwitch.I) : x.u0 p = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := (not_special x).mp hs
  simp [XSwitch.u0, h1, h2, h3, h4, hp]

/-- A coordinate of `I` other than `a, b` is not special (`g', h' ∉ I`). -/
lemma not_special_I {p : x.toSwitch.P'} (hp : p.1 ∈ x.toSwitch.I) (ha : p ≠ x.pa) (hb : p ≠ x.pb) :
    p ∉ x.special := by
  refine (not_special x).mpr ⟨ha, hb, fun e => ?_, fun e => ?_⟩
  · subst e; exact Lemma44.g'_notMem_I x hp
  · subst e; exact Lemma44.h'_notMem_I x hp

/-- A special coordinate outside `I` is `γ` or `η`. -/
lemma special_J {r : x.toSwitch.P'} (hs : r ∈ x.special) (hr : r.1 ∉ x.toSwitch.I) : r = x.pg ∨ r = x.ph := by
  simp only [XSwitch.special, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | h | h
  · exact absurd (Lemma44.a_mem_I x) hr
  · exact absurd (Lemma44.b_mem_I x) hr
  · exact Or.inl h
  · exact Or.inr h

section Close

variable {x} {u : x.toSwitch.P' → ℝ} (hu : Close x u)
include hu

lemma bounds (p : x.toSwitch.P') : x.u0 p - 1 / 8 < u p ∧ u p < x.u0 p + 1 / 8 := by
  have h := abs_lt.mp (hu p)
  have he := eps_le x
  constructor <;> linarith [h.1, h.2]

lemma special_bounds {p : x.toSwitch.P'} (hs : p ∈ x.special) : 1 / 8 < u p ∧ u p < 7 / 8 := by
  have h := bounds hu p
  simp only [XSwitch.special, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · rw [u0_pa] at h; constructor <;> linarith [h.1, h.2]
  · rw [u0_pb] at h; constructor <;> linarith [h.1, h.2]
  · rw [u0_pg] at h; constructor <;> linarith [h.1, h.2]
  · rw [u0_ph] at h; constructor <;> linarith [h.1, h.2]

lemma J_nonspecial {r : x.toSwitch.P'} (hr : r.1 ∉ x.toSwitch.I) (hs : r ∉ x.special) : 7 / 8 < u r := by
  have h := bounds hu r
  rw [u0_J x hs hr] at h
  linarith [h.1]

lemma J_bound {r : x.toSwitch.P'} (hr : r.1 ∉ x.toSwitch.I) : 5 / 8 < u r := by
  by_cases hs : r ∈ x.special
  · have h := bounds hu r
    rcases special_J x hs hr with rfl | rfl
    · rw [u0_pg] at h; linarith [h.1]
    · rw [u0_ph] at h; linarith [h.1]
  · linarith [J_nonspecial hu hr hs]

/-- A chain sum moves by at most `1/8` on the box. -/
lemma sum_le (K : Finset x.toSwitch.P') : ∑ p ∈ K, u p ≤ ∑ p ∈ K, x.u0 p + 1 / 8 := by
  have h1 : ∑ p ∈ K, u p ≤ ∑ p ∈ K, (x.u0 p + eps x) :=
    Finset.sum_le_sum fun p _ => by linarith [(abs_lt.mp (hu p)).2]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  linarith [card_mul_eps x K]

/-- On the box, every chain of `I` has sum at most `3/8` (at `u₀` a chain meets at most one of `a, b`). -/
lemma chain_bound {K : Finset x.toSwitch.P'} (hKI : ↑K ⊆ x.toSwitch.I') (hK : IsChainSet x.toSwitch.P' K) :
    ∑ p ∈ K, u p ≤ 3 / 8 := by
  have h0 := Lemma44.chainSum_le_max x (u := x.u0) (pa := x.pa) (pb := x.pb) rfl rfl
    (fun p hp ha hb => u0_I x (not_special_I x hp (fun e => ha (congrArg Subtype.val e))
      (fun e => hb (congrArg Subtype.val e))) hp) (by rw [u0_pa]; norm_num) hKI hK
  rw [u0_pa, u0_pb, max_self] at h0
  linarith [sum_le hu K]

end Close

/-- Points near `u₀` that agree with `u₀` off the special coordinates lie in `E₀` (Lemma 4.4's description). -/
lemma mem_E0 {w : x.toSwitch.P' → ℝ} (hw : ∀ p, |w p - x.u0 p| < 1 / 4)
    (hz : ∀ p, p ∉ x.special → w p = x.u0 p) : w ∈ x.E0 := by
  rw [(lemma_4_4_proved x x.pa x.pb x.pg x.ph rfl rfl rfl rfl).2.2]
  have ha := abs_lt.mp (hw x.pa)
  have hb := abs_lt.mp (hw x.pb)
  have hg := abs_lt.mp (hw x.pg)
  have hh := abs_lt.mp (hw x.ph)
  rw [u0_pa] at ha; rw [u0_pb] at hb; rw [u0_pg] at hg; rw [u0_ph] at hh
  refine ⟨fun p hp h1 h2 => ?_, fun r hr h1 h2 => ?_, by linarith [ha.1], by linarith [hb.1],
    max_le (le_min (by linarith [ha.2, hg.1]) (by linarith [ha.2, hh.1]))
      (le_min (by linarith [hb.2, hg.1]) (by linarith [hb.2, hh.1])), by linarith [hg.2], by linarith [hh.2]⟩
  · have hs := not_special_I x hp (fun e => h1 (congrArg Subtype.val e)) (fun e => h2 (congrArg Subtype.val e))
    rw [hz p hs, u0_I x hs hp]
  · have hs : r ∉ x.special := fun hs => by
      rcases special_J x hs hr with rfl | rfl
      exacts [h1 rfl, h2 rfl]
    rw [hz r hs, u0_J x hs hr]

lemma eq_of_zeta {u v : x.toSwitch.P' → ℝ} (hz : x.zeta u = x.zeta v) {p : x.toSwitch.P'} (hs : p ∉ x.special) :
    v p = u p :=
  (congrFun hz ⟨p, hs⟩).symm

/-- `r ≤ γ` (or `η`) with `r ∉ I` forces `r = γ` (or `η`): `g', h'` cover `q`. -/
lemma eq_of_le_special {r r' : x.toSwitch.P'} (hr : r.1 ∉ x.toSwitch.I) (hs : r' = x.pg ∨ r' = x.ph)
    (hle : r ≤ r') : r = r' := by
  rcases hle.eq_or_lt with h | h
  · exact h
  have hlt : r.1 < r'.1 := h
  have hq := Lemma44.q_lt_of_notMem x hr
  rcases hs with rfl | rfl
  · exact absurd hlt (x.q_covby_g'.2 hq)
  · exact absurd hlt (x.q_covby_h'.2 hq)

/-- (a), membership in `B`: on the box, every inequality of `B` involving `α, β, γ, η` is strict, so membership
depends only on `ζ`. -/
lemma mem_B_transfer {u v : x.toSwitch.P' → ℝ} (hv : Close x v) (hz : x.zeta u = x.zeta v)
    (huB : u ∈ x.toSwitch.B) : v ∈ x.toSwitch.B := by
  refine ⟨fun p hp => ?_, fun r hr => ?_, fun r r' hr hr' hle => ?_,
    fun r hr K hKI hK _ => ?_, fun K hKI hK => ?_⟩
  · by_cases hs : p ∈ x.special
    · linarith [(special_bounds hv hs).1]
    · rw [eq_of_zeta x hz hs]; exact huB.1 p hp
  · by_cases hs : r ∈ x.special
    · have h := special_bounds hv hs
      constructor <;> linarith [h.1, h.2]
    · rw [eq_of_zeta x hz hs]; exact huB.2.1 r hr
  · by_cases hs' : r' ∈ x.special
    · rw [eq_of_le_special x hr (special_J x hs' hr') hle]
    · by_cases hs : r ∈ x.special
      · linarith [(special_bounds hv hs).2, J_nonspecial hv hr' hs']
      · rw [eq_of_zeta x hz hs, eq_of_zeta x hz hs']; exact huB.2.2.1 r r' hr hr' hle
  · linarith [chain_bound hv hKI hK, J_bound hv hr]
  · linarith [chain_bound hv hKI hK]

/-- (a): a face `E ⊇ E₀` is exposed by `l`; `l` is constant on `E₀`, whose directions contain every small
perturbation of `α, β, γ, η`, so `l u = l v` when `ζ u = ζ v`. -/
lemma face_transfer {E : Set (x.toSwitch.P' → ℝ)} (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E)
    {u v : x.toSwitch.P' → ℝ} (hu : Close x u) (hv : Close x v) (hz : x.zeta u = x.zeta v) (huE : u ∈ E) :
    v ∈ E := by
  obtain ⟨l, hl⟩ := hE.2 hE.1
  have he := eps_le x
  have hd : x.u0 + (v - u) ∈ x.E0 := by
    refine mem_E0 x (fun p => ?_) (fun p hs => ?_)
    · have h1 := abs_lt.mp (hu p)
      have h2 := abs_lt.mp (hv p)
      simp only [Pi.add_apply, Pi.sub_apply, add_sub_cancel_left]
      exact abs_lt.mpr ⟨by linarith [h1.2, h2.1], by linarith [h1.1, h2.2]⟩
    · simp [eq_of_zeta x hz hs]
  have h0 : x.u0 ∈ x.E0 := mem_E0 x (fun p => by simp) (fun _ _ => rfl)
  have hd' := hE0 hd
  have h0' := hE0 h0
  rw [hl] at hd' h0' huE ⊢
  have heq : l (x.u0 + (v - u)) = l x.u0 := le_antisymm (h0'.2 _ hd'.1) (hd'.2 _ h0'.1)
  rw [map_add, map_sub] at heq
  refine ⟨mem_B_transfer x hv hz huE.1, fun y hy => ?_⟩
  linarith [huE.2 y hy]

/-- A chain avoiding `a, b` has sum at most `1/8` on the box, below `α > 1/8`. -/
lemma low_sum {u : x.toSwitch.P' → ℝ} (hu : Close x u) {K : Finset x.toSwitch.P'} (hKI : ↑K ⊆ x.toSwitch.I')
    (ha : x.pa ∉ K) (hb : x.pb ∉ K) : x.toSwitch.chainSum K u ≤ u x.pa := by
  have h0 : ∑ p ∈ K, x.u0 p = 0 := Finset.sum_eq_zero fun p hp =>
    u0_I x (not_special_I x (hKI hp) (fun e => ha (e ▸ hp)) (fun e => hb (e ▸ hp))) (hKI hp)
  have hpa := (special_bounds hu (show x.pa ∈ x.special by simp [XSwitch.special])).1
  have := sum_le hu K
  unfold Switch.chainSum
  linarith

/-- `α + λ_a(ζ)` is the maximum of the chain sums over chains containing `a`. -/
lemma add_lamA_le (u : x.toSwitch.P' → ℝ) : u x.pa + x.lamA u ≤ x.toSwitch.L u := by
  classical
  have : x.lamA u ≤ x.toSwitch.L u - u x.pa := by
    unfold XSwitch.lamA
    refine Finset.sup'_le _ _ fun K hK => ?_
    rw [Finset.mem_filter] at hK
    have h1 : x.toSwitch.chainSum K u ≤ x.toSwitch.L u :=
      Finset.le_sup' (fun K => x.toSwitch.chainSum K u) hK.1
    have h2 := Finset.add_sum_erase K u hK.2
    unfold Switch.chainSum at h1 ⊢
    linarith
  linarith

lemma add_lamB_le (u : x.toSwitch.P' → ℝ) : u x.pb + x.lamB u ≤ x.toSwitch.L u := by
  classical
  have : x.lamB u ≤ x.toSwitch.L u - u x.pb := by
    unfold XSwitch.lamB
    refine Finset.sup'_le _ _ fun K hK => ?_
    rw [Finset.mem_filter] at hK
    have h1 : x.toSwitch.chainSum K u ≤ x.toSwitch.L u :=
      Finset.le_sup' (fun K => x.toSwitch.chainSum K u) hK.1
    have h2 := Finset.add_sum_erase K u hK.2
    unfold Switch.chainSum at h1 ⊢
    linarith
  linarith

lemma chainSum_le_lamA (u : x.toSwitch.P' → ℝ) {K : Finset x.toSwitch.P'} (hK : K ∈ x.toSwitch.lowBranches)
    (ha : x.pa ∈ K) : x.toSwitch.chainSum K u ≤ u x.pa + x.lamA u := by
  classical
  have h1 : x.toSwitch.chainSum (K.erase x.pa) u ≤ x.lamA u := by
    unfold XSwitch.lamA
    refine Finset.le_sup' (fun K : Finset x.toSwitch.P' => x.toSwitch.chainSum (K.erase x.pa) u) ?_
    exact Finset.mem_filter.mpr ⟨hK, ha⟩
  have h2 := Finset.add_sum_erase K u ha
  unfold Switch.chainSum at h1 ⊢
  linarith

lemma chainSum_le_lamB (u : x.toSwitch.P' → ℝ) {K : Finset x.toSwitch.P'} (hK : K ∈ x.toSwitch.lowBranches)
    (hb : x.pb ∈ K) : x.toSwitch.chainSum K u ≤ u x.pb + x.lamB u := by
  classical
  have h1 : x.toSwitch.chainSum (K.erase x.pb) u ≤ x.lamB u := by
    unfold XSwitch.lamB
    refine Finset.le_sup' (fun K : Finset x.toSwitch.P' => x.toSwitch.chainSum (K.erase x.pb) u) ?_
    exact Finset.mem_filter.mpr ⟨hK, hb⟩
  have h2 := Finset.add_sum_erase K u hb
  unfold Switch.chainSum at h1 ⊢
  linarith

lemma lamA_nonneg (u : x.toSwitch.P' → ℝ) : 0 ≤ x.lamA u := by
  have h := chainSum_le_lamA x u x.singleton_pa_mem (Finset.mem_singleton_self _)
  simp only [Switch.chainSum, Finset.sum_singleton] at h
  linarith

/-- (b), first half: `L = max(α + λ_a, β + λ_b)` on the box. -/
lemma L_eq {u : x.toSwitch.P' → ℝ} (hu : Close x u) :
    x.toSwitch.L u = max (u x.pa + x.lamA u) (u x.pb + x.lamB u) := by
  refine le_antisymm (Finset.sup'_le _ _ fun K hK => ?_) (max_le (add_lamA_le x u) (add_lamB_le x u))
  by_cases ha : x.pa ∈ K
  · exact le_max_of_le_left (chainSum_le_lamA x u hK ha)
  by_cases hb : x.pb ∈ K
  · exact le_max_of_le_right (chainSum_le_lamB x u hK hb)
  have hKI : ↑K ⊆ x.toSwitch.I' := by
    simp only [Switch.lowBranches, Finset.mem_filter, Finset.mem_univ, true_and] at hK
    exact hK.1
  exact le_max_of_le_left ((low_sum x hu hKI ha hb).trans (le_add_of_nonneg_right (lamA_nonneg x u)))

/-- (b), second half: `U = min(γ, η)` on the box (the constant `1` and the other `y_r` exceed `7/8`). -/
lemma U_eq {u : x.toSwitch.P' → ℝ} (hu : Close x u) : x.toSwitch.U u = min (u x.pg) (u x.ph) := by
  classical
  have hg : some x.pg ∈ x.toSwitch.upBranches := by
    simp only [Switch.upBranches, Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Option.some.injEq, false_or]
    exact ⟨x.pg, x.q_covby_g'.lt, rfl⟩
  have hh : some x.ph ∈ x.toSwitch.upBranches := by
    simp only [Switch.upBranches, Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Option.some.injEq, false_or]
    exact ⟨x.ph, x.q_covby_h'.lt, rfl⟩
  have hpg := special_bounds hu (show x.pg ∈ x.special by simp [XSwitch.special])
  refine le_antisymm (le_min (Finset.inf'_le _ hg) (Finset.inf'_le _ hh)) (Finset.le_inf' _ _ fun j hj => ?_)
  cases j with
  | none =>
    show min (u x.pg) (u x.ph) ≤ 1
    linarith [min_le_left (u x.pg) (u x.ph), hpg.2]
  | some r =>
    show min (u x.pg) (u x.ph) ≤ u r
    simp only [Switch.upBranches, Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Option.some.injEq, false_or] at hj
    obtain ⟨r', hq, rfl⟩ := hj
    have hr : r'.1 ∉ x.toSwitch.I := fun h => h hq.le
    by_cases hs : r' ∈ x.special
    · rcases special_J x hs hr with rfl | rfl
      exacts [min_le_left _ _, min_le_right _ _]
    · linarith [min_le_left (u x.pg) (u x.ph), hpg.2, J_nonspecial hu hr hs]

lemma close_of_mem {u : x.toSwitch.P' → ℝ}
    (hu : u ∈ x.N0 (box (x.alphaPart x.u0) (eps x)) (box (x.zeta x.u0) (eps x))) : Close x u := by
  obtain ⟨h4, hz⟩ := hu
  simp only [box, Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_ball, Real.dist_eq] at h4 hz
  intro p
  by_cases hp : p ∈ x.special
  · simp only [XSwitch.special, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · simpa [XSwitch.alphaPart] using h4 0
    · simpa [XSwitch.alphaPart] using h4 1
    · simpa [XSwitch.alphaPart] using h4 2
    · simpa [XSwitch.alphaPart] using h4 3
  · simpa [XSwitch.zeta] using hz ⟨p, hp⟩

end Lemma45

/-- **Lemma 4.5** (paper lines 747–764): local product structure of `B` near `u₀`. -/
theorem lemma_4_5_proved {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∃ (V4 : Set (Fin 4 → ℝ)) (Vz : Set ({p // p ∉ x.special} → ℝ)), IsOpen V4 ∧ IsOpen Vz ∧
      x.alphaPart x.u0 ∈ V4 ∧ x.zeta x.u0 ∈ Vz ∧
      (∀ E, IsFace x.toSwitch.B E → x.E0 ⊆ E → ∀ u ∈ x.N0 V4 Vz, ∀ v ∈ x.N0 V4 Vz,
        x.zeta u = x.zeta v → (u ∈ E ↔ v ∈ E)) ∧
      (∀ u ∈ x.toSwitch.B, u ∈ x.N0 V4 Vz →
        x.toSwitch.L u = max (u x.pa + x.lamA u) (u x.pb + x.lamB u) ∧ x.toSwitch.U u = min (u x.pg) (u x.ph)) := by
  open Lemma45 in
  refine ⟨box (x.alphaPart x.u0) (eps x), box (x.zeta x.u0) (eps x), isOpen_box _ _, isOpen_box _ _,
    center_mem_box _ (eps_pos x), center_mem_box _ (eps_pos x), ?_, fun u _ hu => ?_⟩
  · intro E hE hE0 u hu v hv huv
    exact ⟨face_transfer x hE hE0 (close_of_mem x hu) (close_of_mem x hv) huv,
      face_transfer x hE hE0 (close_of_mem x hv) (close_of_mem x hu) huv.symm⟩
  · exact ⟨L_eq x (close_of_mem x hu), U_eq x (close_of_mem x hu)⟩

end HibiLi.Proofs
