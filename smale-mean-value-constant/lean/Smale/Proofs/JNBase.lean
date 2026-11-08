/-
Smale/Proofs/JNBase.lean — finite Blaschke products near the circle, and the base polynomial `P` of [JN, Prop. 4.2]:
`P(W z)` close to `G z` on a closed subdisk, and `P'(W z)` bounded away from `0` there.
-/
import Smale.Proofs.Disk
import Smale.Proofs.JNRunge

namespace Smale

open Polynomial Complex Metric Filter Topology Set ComplexConjugate

/-! ### Blaschke products -/

/-- One Blaschke factor has modulus close to `1` near the circle. -/
theorem blaschkeFactor_collar {a : ℂ} (ha : ‖a‖ < 1) {σ : ℝ} (hσ : σ < 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ < 1 → σ < ‖blaschkeFactor a z‖ := by
  set τ : ℝ := max σ 0 with hτdef
  have hτ0 : 0 ≤ τ := le_max_right _ _
  have hτ1 : τ < 1 := max_lt hσ one_pos
  set e : ℝ := 1 - τ ^ 2 with hedef
  have he : 0 < e := by
    rw [hedef]
    nlinarith
  set A : ℝ := ‖a‖ with hAdef
  have hA0 : 0 ≤ A := norm_nonneg _
  have hA1 : 0 < 1 - A := by linarith
  have hgap : 0 < e * (1 - A) / (4 * (1 + A)) := by positivity
  refine ⟨max 0 (1 - e * (1 - A) / (4 * (1 + A))), le_max_left _ _, max_lt one_pos (by linarith), fun z hzr hz1 => ?_⟩
  set Z : ℝ := ‖z‖ with hZdef
  have hZ0 : 0 ≤ Z := norm_nonneg _
  have hZgap : 1 - Z ≤ e * (1 - A) / (4 * (1 + A)) := by
    have := (le_max_right _ _).trans hzr
    linarith
  have hZ4 : (1 + A) * (1 - Z) * 4 ≤ e * (1 - A) := by
    rw [le_div_iff₀ (by positivity)] at hZgap
    linarith
  have hD : 1 - A ≤ ‖1 - conj a * z‖ := by
    have h1 : ‖conj a * z‖ ≤ A := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith
    have h2 := norm_sub_norm_le (1 : ℂ) (conj a * z)
    rw [norm_one] at h2
    linarith
  have hDpos : 0 < ‖1 - conj a * z‖ := by linarith
  have hid := normSq_one_sub_conj_mul a z
  set D : ℝ := ‖1 - conj a * z‖ with hDdef
  have hsq : τ ^ 2 * D ^ 2 < ‖a - z‖ ^ 2 := by
    have hlhs : (1 - A ^ 2) * (1 - Z ^ 2) = (1 - A) * ((1 + A) * (1 - Z)) * (1 + Z) := by ring
    have hX0 : 0 ≤ (1 + A) * (1 - Z) := mul_nonneg (by linarith) (by linarith)
    have h1 : (1 - A) * ((1 + A) * (1 - Z)) * (1 + Z) ≤ (1 - A) * ((1 + A) * (1 - Z)) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA1.le hX0)
    have h2 : (1 - A) * ((1 + A) * (1 - Z)) * 2 ≤ e * (1 - A) ^ 2 / 2 := by nlinarith
    have h3 : (1 - A) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hA1.le hD 2
    have h4 : e * (1 - A) ^ 2 / 2 < e * (1 - A) ^ 2 := by
      have : 0 < e * (1 - A) ^ 2 := by positivity
      linarith
    have h5 : e * (1 - A) ^ 2 ≤ e * D ^ 2 := mul_le_mul_of_nonneg_left h3 he.le
    have h6 : D ^ 2 - ‖a - z‖ ^ 2 < e * D ^ 2 := by
      rw [hid, hlhs]
      linarith
    rw [hedef] at h6
    linarith
  have hB : ‖blaschkeFactor a z‖ = ‖a - z‖ / D := by
    rw [blaschkeFactor, norm_div, norm_sub_rev z a]
  have hτB : τ < ‖blaschkeFactor a z‖ := by
    rw [hB, lt_div_iff₀ hDpos]
    have h7 : (τ * D) ^ 2 < ‖a - z‖ ^ 2 := by
      rw [mul_pow]
      exact hsq
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h7
  exact lt_of_le_of_lt (le_max_left _ _) hτB

/-- The product over a list of factors has modulus close to `1` near the circle. -/
theorem blaschke_list_collar (as : List ℂ) (has : ∀ a ∈ as, a ∈ disk) {t : ℝ} (ht : t < 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ < 1 → t < ‖(as.map fun a => blaschkeFactor a z).prod‖ := by
  induction as generalizing t with
  | nil =>
    refine ⟨0, le_rfl, one_pos, fun z _ _ => ?_⟩
    simpa using ht
  | cons a as ih =>
    set τ : ℝ := max t 0 with hτdef
    have hτ0 : 0 ≤ τ := le_max_right _ _
    have hτ1 : τ < 1 := max_lt ht one_pos
    set σ : ℝ := (1 + τ) / 2 with hσdef
    have hσ1 : σ < 1 := by
      rw [hσdef]
      linarith
    have hσ0 : 0 < σ := by
      rw [hσdef]
      positivity
    have hσsq : τ < σ * σ := by
      rw [hσdef]
      nlinarith [sq_pos_of_pos (show 0 < 1 - τ by linarith)]
    have haD : ‖a‖ < 1 := by simpa using has a (List.mem_cons_self ..)
    obtain ⟨r₁, h1r, h1r', h1⟩ := blaschkeFactor_collar haD hσ1
    obtain ⟨r₂, h2r, h2r', h2⟩ := ih (fun b hb => has b (List.mem_cons_of_mem _ hb)) hσ1
    refine ⟨max r₁ r₂, le_max_of_le_left h1r, max_lt h1r' h2r', fun z hzr hz1 => ?_⟩
    rw [List.map_cons, List.prod_cons, norm_mul]
    have h3 := h1 z ((le_max_left _ _).trans hzr) hz1
    have h4 := h2 z ((le_max_right _ _).trans hzr) hz1
    have h5 : σ * σ < ‖blaschkeFactor a z‖ * ‖(as.map fun a => blaschkeFactor a z).prod‖ :=
      mul_lt_mul'' h3 h4 hσ0.le hσ0.le
    have h6 : t ≤ τ := le_max_left _ _
    linarith

/-- A finite Blaschke product has modulus close to `1` near the circle. -/
theorem blaschke_collar {B : ℂ → ℂ} {k : ℕ} (hB : IsFiniteBlaschke B k) {t : ℝ} (ht : t < 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ < 1 → t < ‖B z‖ := by
  obtain ⟨lam, as, hlam, -, has, heq⟩ := hB
  obtain ⟨r, h0, h1, h⟩ := blaschke_list_collar as has ht
  refine ⟨r, h0, h1, fun z hzr hz1 => ?_⟩
  rw [heq (by simpa using hz1), blaschkeProd, norm_mul, hlam, one_mul]
  exact h z hzr hz1

/-- One factor is holomorphic on the disk. -/
theorem blaschkeFactor_differentiableOn {a : ℂ} (ha : ‖a‖ < 1) : DifferentiableOn ℂ (blaschkeFactor a) disk := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa using hw
  have hne : 1 - conj a * w ≠ 0 := one_sub_mul_ne_zero (by rwa [Complex.norm_conj]) hw'.le
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold blaschkeFactor
  exact ((differentiableAt_id.sub_const a).div ((differentiableAt_const _).sub
    ((differentiableAt_const _).mul differentiableAt_id)) hne)

/-- The product over a list of factors is holomorphic on the disk. -/
theorem blaschke_list_differentiableOn (as : List ℂ) (has : ∀ a ∈ as, a ∈ disk) :
    DifferentiableOn ℂ (fun z => (as.map fun a => blaschkeFactor a z).prod) disk := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (blaschkeFactor_differentiableOn (by simpa using has a (List.mem_cons_self ..))).mul
      (ih fun b hb => has b (List.mem_cons_of_mem _ hb))

/-- A finite Blaschke product is holomorphic on the disk. -/
theorem blaschke_differentiableOn {B : ℂ → ℂ} {k : ℕ} (hB : IsFiniteBlaschke B k) : DifferentiableOn ℂ B disk := by
  obtain ⟨lam, as, -, -, has, heq⟩ := hB
  refine DifferentiableOn.congr ?_ heq
  unfold blaschkeProd
  exact (blaschke_list_differentiableOn as has).const_mul lam

/-! ### The base polynomial -/

/-- The Cauchy estimate: closeness of `p ∘ W` to `G` passes to the derivatives on a smaller disk. -/
theorem deriv_comp_close {W G : ℂ → ℂ} (hWd : DifferentiableOn ℂ W disk) (hG : DifferentiableOn ℂ G disk) {p : ℂ[X]}
    {r r' η : ℝ} (hrr' : r < r') (hr' : r' < 1) (hclose : ∀ z ∈ closedBall (0 : ℂ) r', ‖p.eval (W z) - G z‖ ≤ η) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) r) : ‖p.derivative.eval (W z) * deriv W z - deriv G z‖ ≤ η / (r' - r) := by
  set g : ℂ → ℂ := fun x => p.eval (W x) - G x with hgdef
  have hgd : DifferentiableOn ℂ g disk := (p.differentiable.comp_differentiableOn hWd).sub hG
  have hzn : ‖z‖ ≤ r := by simpa using hz
  have hR : 0 < r' - r := by linarith
  have hsub : closedBall z (r' - r) ⊆ closedBall (0 : ℂ) r' := by
    intro x hx
    have h1 : ‖x - z‖ ≤ r' - r := by simpa [dist_eq_norm] using hx
    have h2 : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
      have := norm_add_le (x - z) z
      rwa [sub_add_cancel] at this
    simp only [mem_closedBall, dist_zero_right]
    linarith
  have hsub' : closedBall z (r' - r) ⊆ disk := hsub.trans (closedBall_subset_ball hr')
  have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR (hgd.diffContOnCl_ball hsub')
    (fun ζ hζ => hclose ζ (hsub (sphere_subset_closedBall hζ)))
  have hzd : z ∈ disk := hsub' (mem_closedBall_self hR.le)
  have hWat : HasDerivAt W (deriv W z) z := (hWd.differentiableAt (isOpen_ball.mem_nhds hzd)).hasDerivAt
  have hGat : HasDerivAt G (deriv G z) z := (hG.differentiableAt (isOpen_ball.mem_nhds hzd)).hasDerivAt
  have hgat : HasDerivAt g (p.derivative.eval (W z) * deriv W z - deriv G z) z :=
    ((p.hasDerivAt (W z)).comp z hWat).sub hGat
  rwa [hgat.deriv] at hbound

/-- **The base polynomial.** -/
theorem base_polynomial {W G : ℂ → ℂ} (hW : InClassS W) (hG : DifferentiableOn ℂ G disk) (hG0 : G 0 = 0)
    (hG1 : deriv G 0 = 1) (hG' : ∀ z ∈ disk, deriv G z ≠ 0) {r : ℝ} (h0 : 0 ≤ r) (hr : r < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℂ[X], P.eval 0 = 0 ∧ P.derivative.eval 0 = 1 ∧
      (∃ μ : ℝ, 0 < μ ∧ ∀ z ∈ closedBall (0 : ℂ) r, μ ≤ ‖P.derivative.eval (W z)‖) ∧
      ∀ z ∈ closedBall (0 : ℂ) r, ‖P.eval (W z) - G z‖ < ε := by
  obtain ⟨hUniv, hW0, hW1⟩ := hW
  obtain ⟨r', hrr', hr'1⟩ := exists_between hr
  have hρ : 0 < r' - r := by linarith
  have hsub : closedBall (0 : ℂ) r ⊆ disk := closedBall_subset_ball hr
  have hcomp : IsCompact (closedBall (0 : ℂ) r) := isCompact_closedBall _ _
  have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) r := mem_closedBall_self h0
  -- lower bound for `G'`, upper bounds for `W'` and `G`
  obtain ⟨δ, hδ, hGlow⟩ := hcomp.exists_forall_le' ((hG.deriv isOpen_ball).continuousOn.mono hsub).norm
    (fun z hz => norm_pos_iff.2 (hG' z (hsub hz)))
  obtain ⟨Mw₀, hMw₀⟩ := hcomp.exists_bound_of_continuousOn ((hUniv.1.deriv isOpen_ball).continuousOn.mono hsub)
  obtain ⟨MG₀, hMG₀⟩ := hcomp.exists_bound_of_continuousOn (hG.continuousOn.mono hsub)
  set Mw : ℝ := max Mw₀ 1 with hMwdef
  have hMw : 0 < Mw := lt_of_lt_of_le one_pos (le_max_right _ _)
  set MG : ℝ := max MG₀ 0 with hMGdef
  have hMG : 0 ≤ MG := le_max_right _ _
  -- the closeness to ask of `p`
  set η : ℝ := min (ε / (2 * (4 + 2 * MG / (r' - r)))) (min ((r' - r) * δ / 2) ((r' - r) / 2)) with hηdef
  have hc4 : 0 < 4 + 2 * MG / (r' - r) := by positivity
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hη1 : η ≤ ε / (2 * (4 + 2 * MG / (r' - r))) := min_le_left _ _
  have hη2 : η ≤ (r' - r) * δ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hη3 : η ≤ (r' - r) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hηδ : η / (r' - r) ≤ δ / 2 := by
    rw [div_le_iff₀ hρ]
    linarith
  have hηhalf : η / (r' - r) ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ]
    linarith
  obtain ⟨p, hp⟩ := exists_poly_near_comp hUniv hG (h0.trans hrr'.le) hr'1 hη
  have hdc := fun z (hz : z ∈ closedBall (0 : ℂ) r) =>
    deriv_comp_close hUniv.1 hG hrr' hr'1 (fun x hx => (hp x hx).le) hz
  -- at the origin
  set u : ℂ := p.derivative.eval 0 with hudef
  have hu1 : ‖u - 1‖ ≤ 1 / 2 := by
    have h1 := hdc 0 h0mem
    rw [hW0, hW1, hG1, mul_one] at h1
    exact h1.trans hηhalf
  have hu1' : ‖u - 1‖ ≤ η / (r' - r) := by
    have h1 := hdc 0 h0mem
    rwa [hW0, hW1, hG1, mul_one] at h1
  have hulow : 1 / 2 ≤ ‖u‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (1 - u)
    rw [norm_one, sub_sub_cancel, norm_sub_rev] at h1
    linarith
  have huhigh : ‖u‖ ≤ 3 / 2 := by
    have h1 := norm_add_le (u - 1) 1
    rw [sub_add_cancel, norm_one] at h1
    linarith
  have hupos : 0 < ‖u‖ := by linarith
  have hune : u ≠ 0 := norm_pos_iff.1 hupos
  have hp0 : ‖p.eval 0‖ ≤ η := by
    have h1 := hp 0 (mem_closedBall_self (h0.trans hrr'.le))
    rw [hW0, hG0, sub_zero] at h1
    exact h1.le
  set P : ℂ[X] := C u⁻¹ * (p - C (p.eval 0)) with hPdef
  have hPeval : ∀ w, P.eval w = u⁻¹ * (p.eval w - p.eval 0) := fun w => by
    simp [hPdef]
  have hPder : ∀ w, P.derivative.eval w = u⁻¹ * p.derivative.eval w := fun w => by
    simp [hPdef]
  refine ⟨P, by rw [hPeval, sub_self, mul_zero], by rw [hPder, ← hudef, inv_mul_cancel₀ hune], ?_, fun z hz => ?_⟩
  · -- `|P'(W z)|` from below
    refine ⟨δ / (3 * Mw), by positivity, fun z hz => ?_⟩
    have hznorm : ‖deriv W z‖ ≤ Mw := (hMw₀ z hz).trans (le_max_left _ _)
    have h1 := hdc z hz
    have h2 := hGlow z hz
    have h3 : δ / 2 ≤ ‖p.derivative.eval (W z) * deriv W z‖ := by
      have h4 := norm_sub_norm_le (deriv G z) (deriv G z - p.derivative.eval (W z) * deriv W z)
      rw [sub_sub_cancel, norm_sub_rev (deriv G z)] at h4
      linarith
    have h5 : δ / 2 ≤ ‖p.derivative.eval (W z)‖ * Mw := by
      rw [norm_mul] at h3
      exact h3.trans (mul_le_mul_of_nonneg_left hznorm (norm_nonneg _))
    rw [hPder, norm_mul, norm_inv, inv_mul_eq_div, div_le_div_iff₀ (by positivity) hupos]
    nlinarith [norm_nonneg (p.derivative.eval (W z))]
  · -- closeness of `P(W z)` to `G z`
    have hGn : ‖G z‖ ≤ MG := (hMG₀ z hz).trans (le_max_left _ _)
    have h1 : ‖p.eval (W z) - G z‖ < η :=
      hp z (closedBall_subset_closedBall hrr'.le hz)
    have hkey : P.eval (W z) - G z = u⁻¹ * ((p.eval (W z) - G z) - p.eval 0 + (1 - u) * G z) := by
      rw [hPeval]
      field_simp
      ring
    have hinv : ‖u⁻¹‖ ≤ 2 := by
      rw [norm_inv, inv_le_comm₀ hupos (by norm_num)]
      linarith
    have h2 : ‖(p.eval (W z) - G z) - p.eval 0 + (1 - u) * G z‖ ≤ η + η + η / (r' - r) * MG := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add h1.le hp0)) ?_)
      rw [norm_mul, norm_sub_rev]
      exact mul_le_mul hu1' hGn (norm_nonneg _) (by positivity)
    have h3 : 2 * (η + η + η / (r' - r) * MG) = η * (4 + 2 * MG / (r' - r)) := by
      field_simp
      ring
    have h4 : η * (4 + 2 * MG / (r' - r)) ≤ ε / 2 := by
      have h5 := mul_le_mul_of_nonneg_right hη1 hc4.le
      have h6 : ε / (2 * (4 + 2 * MG / (r' - r))) * (4 + 2 * MG / (r' - r)) = ε / 2 := by
        field_simp
      linarith
    rw [hkey, norm_mul]
    calc ‖u⁻¹‖ * ‖(p.eval (W z) - G z) - p.eval 0 + (1 - u) * G z‖
        ≤ 2 * (η + η + η / (r' - r) * MG) := mul_le_mul hinv h2 (norm_nonneg _) (by norm_num)
      _ ≤ ε / 2 := by rw [h3]; exact h4
      _ < ε := by linarith

end Smale
