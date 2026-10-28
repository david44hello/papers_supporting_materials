/-
Smale/Proofs/Disk.lean — the disk algebra of Section 3 of paper 009 (tex l.177-182, l.210-211): the identity
`|1 - āb|² - |a - b|² = (1 - |a|²)(1 - |b|²)`, `1/|B_a(b)|² = J(a, b)`, the automorphism `φ_b` of the unit disk, and
`B_a ∘ φ_b = λ B_γ`.
-/
import Smale.Defs.Basic

namespace Smale

open Polynomial Complex Metric ComplexConjugate

/-- `|1 - āb|² - |a - b|² = (1 - |a|²)(1 - |b|²)` (tex l.181). -/
theorem normSq_one_sub_conj_mul (a b : ℂ) :
    ‖1 - conj a * b‖ ^ 2 - ‖a - b‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- `|1 + b̄w|² - |w + b|² = (1 - |w|²)(1 - |b|²)`. -/
theorem normSq_one_add_conj_mul (b w : ℂ) :
    ‖1 + conj b * w‖ ^ 2 - ‖w + b‖ ^ 2 = (1 - ‖w‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- `(1 - |x|²)(1 - |y|²) > 0` for `x, y` in the open disk. -/
theorem one_sub_sq_mul_pos {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : 0 < (1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2) := by
  apply mul_pos <;> nlinarith [norm_nonneg x, norm_nonneg y]

theorem one_sub_mul_ne_zero {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ ≤ 1) : 1 - x * y ≠ 0 := by
  intro h
  have h1 : ‖x * y‖ = 1 := by rw [← sub_eq_zero.1 h, norm_one]
  rw [norm_mul] at h1
  nlinarith [norm_nonneg x, norm_nonneg y]

theorem one_add_mul_ne_zero {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ ≤ 1) : 1 + x * y ≠ 0 := by
  have := one_sub_mul_ne_zero (x := -x) (by rwa [norm_neg]) hy
  rwa [neg_mul, sub_neg_eq_add] at this

theorem one_add_conj_mul_ne_zero {b w : ℂ} (hb : ‖b‖ < 1) (hw : ‖w‖ ≤ 1) : 1 + conj b * w ≠ 0 :=
  one_add_mul_ne_zero (by rwa [Complex.norm_conj]) hw

/-- tex l.182, exactly the Statements type: `|1 - āb|² - |a - b|² = (1 - |a|²)(1 - |b|²)`. -/
theorem sec3_J_identity_proved (a b : ℂ) :
    ‖1 - conj a * b‖ ^ 2 - ‖a - b‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) :=
  normSq_one_sub_conj_mul a b

/-- tex l.182, exactly the Statements type: `1/|B_a(b)|² = J(a, b)` for `a ≠ b`. -/
theorem sec3_J_proved (a b : ℂ) (_ha : a ∈ disk) (_hb : b ∈ disk) (hab : a ≠ b) :
    1 / ‖blaschkeFactor a b‖ ^ 2 = Jab a b := by
  have hY : ‖a - b‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 hab))
  rw [blaschkeFactor, norm_div, div_pow, one_div_div, norm_sub_rev b a, Jab, ← normSq_one_sub_conj_mul a b,
    sub_div, div_self hY]
  ring

/-- `φ_b` maps the open disk into itself. -/
theorem norm_diskAut_lt_one {b w : ℂ} (hb : ‖b‖ < 1) (hw : ‖w‖ < 1) : ‖diskAut b w‖ < 1 := by
  have hpos : 0 < ‖1 + conj b * w‖ := norm_pos_iff.2 (one_add_conj_mul_ne_zero hb hw.le)
  rw [diskAut, norm_div, div_lt_one hpos]
  have h := normSq_one_add_conj_mul b w
  have h2 := one_sub_sq_mul_pos hw hb
  nlinarith [norm_nonneg (w + b), norm_nonneg (1 + conj b * w)]

theorem one_sub_conj_mul_self_ne_zero {b : ℂ} (hb : ‖b‖ < 1) : (1 : ℂ) - conj b * b ≠ 0 := by
  rw [Complex.conj_mul']
  have h : (0 : ℝ) < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  exact_mod_cast h.ne'

theorem diskAut_injOn {b : ℂ} (hb : ‖b‖ < 1) : Set.InjOn (diskAut b) disk := by
  intro w₁ hw₁ w₂ hw₂ h
  have h1 := one_add_conj_mul_ne_zero hb (mem_ball_zero_iff.1 hw₁).le
  have h2 := one_add_conj_mul_ne_zero hb (mem_ball_zero_iff.1 hw₂).le
  rw [diskAut, diskAut, div_eq_div_iff h1 h2] at h
  have h3 : (w₁ - w₂) * (1 - conj b * b) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact sub_eq_zero.1 h4
  · exact absurd h4 (one_sub_conj_mul_self_ne_zero hb)

theorem diskAut_surjOn {b : ℂ} (hb : ‖b‖ < 1) : Set.SurjOn (diskAut b) disk disk := by
  intro z hz
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hb' : ‖-b‖ < 1 := by rwa [norm_neg]
  have hw : ‖diskAut (-b) z‖ < 1 := norm_diskAut_lt_one hb' hz'
  refine ⟨diskAut (-b) z, mem_ball_zero_iff.2 hw, ?_⟩
  have h1 : 1 + conj (-b) * z ≠ 0 := one_add_conj_mul_ne_zero hb' hz'.le
  have hw' : diskAut (-b) z * (1 + conj (-b) * z) = z + -b := by rw [diskAut, div_mul_cancel₀ _ h1]
  have hden := one_add_conj_mul_ne_zero hb hw.le
  show (diskAut (-b) z + b) / (1 + conj b * diskAut (-b) z) = z
  rw [div_eq_iff hden]
  rw [map_neg] at hw'
  linear_combination hw'

theorem hasDerivAt_diskAut (b : ℂ) : HasDerivAt (diskAut b) (1 - (‖b‖ : ℂ) ^ 2) 0 := by
  have hn : HasDerivAt (fun w : ℂ => w + b) 1 0 := (hasDerivAt_id' 0).add_const b
  have hd : HasDerivAt (fun w : ℂ => 1 + conj b * w) (conj b) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℂ)).const_mul (conj b)).const_add 1
  have h0 : (1 : ℂ) + conj b * 0 ≠ 0 := by simp
  refine (hn.div hd h0).congr_deriv ?_
  simp [Complex.mul_conj']

/-- tex l.181-182: `φ(w) = (w + b)/(1 + b̄w)` maps `𝔻` onto `𝔻`, `φ(0) = b`, `φ'(0) = 1 - |b|²`. -/
theorem sec3_phi_proved (b : ℂ) (hb : b ∈ disk) :
    Set.BijOn (diskAut b) disk disk ∧ diskAut b 0 = b ∧ deriv (diskAut b) 0 = 1 - (‖b‖ : ℂ) ^ 2 := by
  have hb' : ‖b‖ < 1 := mem_ball_zero_iff.1 hb
  refine ⟨⟨fun w hw => mem_ball_zero_iff.2 (norm_diskAut_lt_one hb' (mem_ball_zero_iff.1 hw)),
    diskAut_injOn hb', diskAut_surjOn hb'⟩, by simp [diskAut], (hasDerivAt_diskAut b).deriv⟩

theorem cancel_div_div (N D u cu : ℂ) (hu : u ≠ 0) (hcu : cu ≠ 0) (hD : D ≠ 0) :
    cu / u * ((N / cu) / (D / u)) = N / D := by
  field_simp

/-- Lemma 3.1, proof (tex l.210-211): `B_a ∘ φ_b = λ B_γ` on `𝔻`, with `|λ| = 1` and `γ ∈ 𝔻`; here
`λ = (1 - a b̄)/(1 - ā b)` and `γ = (a - b)/(1 - a b̄)`. -/
theorem lem_3_1_aut_proved (a b : ℂ) (ha : a ∈ disk) (hb : b ∈ disk) :
    ∃ lam γ : ℂ, ‖lam‖ = 1 ∧ γ ∈ disk ∧ ∀ w ∈ disk, blaschkeFactor a (diskAut b w) = lam * blaschkeFactor γ w := by
  have ha' : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
  have hb' : ‖b‖ < 1 := mem_ball_zero_iff.1 hb
  have hu : 1 - conj a * b ≠ 0 := one_sub_mul_ne_zero (by rwa [Complex.norm_conj]) hb'.le
  have hcu : 1 - a * conj b ≠ 0 := one_sub_mul_ne_zero ha' (by rw [Complex.norm_conj]; exact hb'.le)
  have hcu_eq : conj (1 - conj a * b) = 1 - a * conj b := by simp
  have hnorm : ‖1 - a * conj b‖ = ‖1 - conj a * b‖ := by rw [← hcu_eq, Complex.norm_conj]
  refine ⟨(1 - a * conj b) / (1 - conj a * b), (a - b) / (1 - a * conj b), ?_, ?_, ?_⟩
  · rw [norm_div, hnorm, div_self (norm_ne_zero_iff.2 hu)]
  · rw [mem_ball_zero_iff, norm_div, hnorm, div_lt_one (norm_pos_iff.2 hu)]
    have h := normSq_one_sub_conj_mul a b
    have h2 := one_sub_sq_mul_pos ha' hb'
    nlinarith [norm_nonneg (a - b), norm_nonneg (1 - conj a * b)]
  · intro w hw
    have hw' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    have hd1 : 1 + conj b * w ≠ 0 := one_add_conj_mul_ne_zero hb' hw'.le
    have hφ : ‖diskAut b w‖ < 1 := norm_diskAut_lt_one hb' hw'
    have hd2 : 1 - conj a * diskAut b w ≠ 0 := one_sub_mul_ne_zero (by rwa [Complex.norm_conj]) hφ.le
    have hφeq : diskAut b w * (1 + conj b * w) = w + b := div_mul_cancel₀ _ hd1
    have hD : (1 - conj a * b) + (conj b - conj a) * w ≠ 0 := by
      have h5 : (1 - conj a * b) + (conj b - conj a) * w = (1 + conj b * w) * (1 - conj a * diskAut b w) := by
        linear_combination (conj a) * hφeq
      rw [h5]
      exact mul_ne_zero hd1 hd2
    have hL : blaschkeFactor a (diskAut b w) =
        ((1 - a * conj b) * w + (b - a)) / ((1 - conj a * b) + (conj b - conj a) * w) := by
      rw [blaschkeFactor, div_eq_div_iff hd2 hD]
      linear_combination (1 - a * conj a) * hφeq
    have hγ : conj ((a - b) / (1 - a * conj b)) = (conj a - conj b) / (1 - conj a * b) := by simp
    have hR1 : w - (a - b) / (1 - a * conj b) = ((1 - a * conj b) * w + (b - a)) / (1 - a * conj b) := by
      field_simp
      ring
    have hR2 : 1 - (conj a - conj b) / (1 - conj a * b) * w =
        ((1 - conj a * b) + (conj b - conj a) * w) / (1 - conj a * b) := by
      field_simp
      ring
    rw [hL, blaschkeFactor, hγ, hR1, hR2]
    exact (cancel_div_div _ _ _ _ hu hcu hD).symm

end Smale
