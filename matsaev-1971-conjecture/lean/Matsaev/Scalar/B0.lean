/-
Matsaev/Scalar/B0.lean — Lemma 3.2 (a = 0) and Lemma 3.3 (`lem:B0q`, growth of F₀) of the paper.
Paper short v2.00 (md5 a9b3c6be): Lemma 3.2 (`lem:B0`) and Lemma 3.3 (`lem:B0q`).

Route — one identity serves both lemmas. `breg p a y = |y|^p - |a|^p - p φ(a) (y - a)` is the gap of `|·|^p` above its
tangent line at `a`. With `z = (u - B w)/(1 + B)`:
    F0 = (1+B)^(p-1) (breg z u + B · breg z (-w))                                  (`F0_eq_breg`).
Bernoulli's inequality gives `breg ≥ 0`, and `breg > 0` off the diagonal when p > 1: this is Lemma 3.2. For p ≥ 2, a
midpoint split and a strong monotonicity bound for φ give `breg a y ≥ (p/8) ((|a| + |y - a|)/5)^(p-2) (y - a)^2`
(`breg_lower`); with `-w - z = -(u + w)/(1 + B)` this is Lemma 3.3, with an explicit constant (no compactness).
-/
import Matsaev.Defs.Scalar
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Matsaev

open Real

namespace B0

/-! ### The tangent-line gap of `|·|^p` -/

/-- The gap of `|·|^p` above its tangent line at `a`, evaluated at `y` (a helper for this file). -/
noncomputable def breg (p a y : ℝ) : ℝ := |y| ^ p - |a| ^ p - p * phi p a * (y - a)

lemma phi_zero (p : ℝ) : phi p 0 = 0 := by simp [phi]

lemma phi_neg (p x : ℝ) : phi p (-x) = -phi p x := by
  simp [phi, Left.sign_neg, abs_neg]

lemma phi_mul_self {p : ℝ} (hp : 0 < p) (x : ℝ) : phi p x * x = |x| ^ p := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [phi, Real.zero_rpow hp.ne']
  · have hax : |x| ≠ 0 := abs_ne_zero.mpr hx
    have h1 : phi p x * x = |x| ^ (p - 1) * ((SignType.sign x : ℝ) * x) := by unfold phi; ring
    rw [h1, sign_mul_self, Real.rpow_sub_one hax, div_mul_cancel₀ _ hax]

lemma phi_of_nonneg {p x : ℝ} (hp : 1 < p) (hx : 0 ≤ x) : phi p x = x ^ (p - 1) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [phi, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  · simp [phi, sign_pos hx, abs_of_pos hx]

/-- Bernoulli's inequality for `|t|^p`. -/
lemma bernoulli_abs {p : ℝ} (hp : 1 ≤ p) (t : ℝ) : 1 + p * (t - 1) ≤ |t| ^ p := by
  rcases le_or_gt 0 t with ht | ht
  · have h := one_add_mul_self_le_rpow_one_add (s := t - 1) (by linarith) hp
    rw [show 1 + (t - 1) = t by ring] at h
    rwa [abs_of_nonneg ht]
  · have h1 : 0 ≤ |t| ^ p := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (by linarith : (0 : ℝ) ≤ 1 - t)]

/-- Strict Bernoulli's inequality for `|t|^p`, `t ≠ 1`. -/
lemma bernoulli_abs_lt {p : ℝ} (hp : 1 < p) {t : ℝ} (ht1 : t ≠ 1) : 1 + p * (t - 1) < |t| ^ p := by
  rcases le_or_gt 0 t with ht | ht
  · have h := one_add_mul_self_lt_rpow_one_add (s := t - 1) (by linarith) (sub_ne_zero.mpr ht1) hp
    rw [show 1 + (t - 1) = t by ring] at h
    rwa [abs_of_nonneg ht]
  · have h1 : 0 ≤ |t| ^ p := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.le) (by linarith : (0 : ℝ) ≤ 1 - t)]

/-- The tangent gap at `x ≠ 0`, rescaled to Bernoulli's form with `t = y / x`. -/
lemma tangent_gap_eq {p : ℝ} (hp : 0 < p) {x : ℝ} (hx : x ≠ 0) (y : ℝ) :
    |y| ^ p - (|x| ^ p + p * phi p x * (y - x)) = |x| ^ p * (|y / x| ^ p - (1 + p * (y / x - 1))) := by
  have hy : |y| ^ p = |y / x| ^ p * |x| ^ p := by
    rw [← Real.mul_rpow (abs_nonneg _) (abs_nonneg _), ← abs_mul, div_mul_cancel₀ _ hx]
  have hyx : y - x = x * (y / x - 1) := by field_simp
  have hphi : phi p x * (y - x) = |x| ^ p * (y / x - 1) := by
    rw [hyx, ← mul_assoc, phi_mul_self hp x]
  rw [hy, mul_assoc p, hphi]
  ring

/-- `|·|^p` lies above its tangent lines (p ≥ 1). -/
lemma tangent_le {p : ℝ} (hp : 1 ≤ p) (x y : ℝ) : |x| ^ p + p * phi p x * (y - x) ≤ |y| ^ p := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : |(0 : ℝ)| ^ p = 0 := by simp [Real.zero_rpow (by linarith : p ≠ 0)]
    rw [h0, phi_zero]
    simp only [mul_zero, zero_mul, add_zero]
    positivity
  · have h := tangent_gap_eq (by linarith) hx y
    have hb := bernoulli_abs hp (y / x)
    have hxp : 0 ≤ |x| ^ p := by positivity
    nlinarith [mul_nonneg hxp (sub_nonneg.mpr hb)]

/-- `|·|^p` lies strictly above its tangent line at `x`, away from `x` (p > 1). -/
lemma tangent_lt {p : ℝ} (hp : 1 < p) {x y : ℝ} (hxy : x ≠ y) :
    |x| ^ p + p * phi p x * (y - x) < |y| ^ p := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : |(0 : ℝ)| ^ p = 0 := by simp [Real.zero_rpow (by linarith : p ≠ 0)]
    rw [h0, phi_zero]
    simp only [mul_zero, zero_mul, add_zero]
    exact Real.rpow_pos_of_pos (abs_pos.mpr (Ne.symm hxy)) p
  · have h := tangent_gap_eq (by linarith) hx y
    have ht1 : y / x ≠ 1 := by
      intro h1
      exact hxy ((div_eq_one_iff_eq hx).mp h1).symm
    have hb := bernoulli_abs_lt hp ht1
    have hxp : 0 < |x| ^ p := Real.rpow_pos_of_pos (abs_pos.mpr hx) p
    nlinarith [mul_pos hxp (sub_pos.mpr hb)]

lemma breg_nonneg {p : ℝ} (hp : 1 ≤ p) (a y : ℝ) : 0 ≤ breg p a y := by
  unfold breg; linarith [tangent_le hp a y]

lemma breg_pos {p : ℝ} (hp : 1 < p) {a y : ℝ} (hay : a ≠ y) : 0 < breg p a y := by
  unfold breg; linarith [tangent_lt hp hay]

lemma breg_self (p a : ℝ) : breg p a a = 0 := by
  simp [breg]

/-! ### Strong monotonicity of φ for p ≥ 2 -/

lemma rpow_sub_one_eq_mul {p x : ℝ} (hp : 2 ≤ p) (hx : 0 ≤ x) : x ^ (p - 1) = x ^ (p - 2) * x := by
  have h := Real.rpow_add' hx (show (p - 2) + 1 ≠ 0 by linarith)
  rw [Real.rpow_one] at h
  rw [show p - 1 = (p - 2) + 1 by ring]
  exact h

lemma phi_sub_ge_of_nonneg {p a b : ℝ} (hp : 2 ≤ p) (ha : 0 ≤ a) (hab : a ≤ b) :
    b ^ (p - 2) * (b - a) ≤ phi p b - phi p a := by
  have hb : 0 ≤ b := ha.trans hab
  rw [phi_of_nonneg (by linarith) ha, phi_of_nonneg (by linarith) hb, rpow_sub_one_eq_mul hp ha,
    rpow_sub_one_eq_mul hp hb]
  have hpow : a ^ (p - 2) ≤ b ^ (p - 2) := Real.rpow_le_rpow ha hab (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hpow ha]

lemma phi_sub_ge_of_opp {p a b : ℝ} (hp : 2 ≤ p) (ha : a ≤ 0) (hb : 0 ≤ b) :
    max |a| |b| ^ (p - 2) * (b - a) ≤ 2 * (phi p b - phi p a) := by
  have hna : 0 ≤ -a := by linarith
  have hphia : phi p a = -((-a) ^ (p - 1)) := by
    rw [← neg_neg a, phi_neg, phi_of_nonneg (by linarith) hna, neg_neg]
  rw [hphia, phi_of_nonneg (by linarith) hb, abs_of_nonpos ha, abs_of_nonneg hb]
  have hA : 0 ≤ (-a) ^ (p - 1) := Real.rpow_nonneg hna _
  have hB : 0 ≤ b ^ (p - 1) := Real.rpow_nonneg hb _
  rcases le_total (-a) b with h | h
  · rw [max_eq_right h]
    have hM := rpow_sub_one_eq_mul hp hb
    have hMp : 0 ≤ b ^ (p - 2) := Real.rpow_nonneg hb _
    nlinarith [mul_le_mul_of_nonneg_left (show b - a ≤ 2 * b by linarith) hMp]
  · rw [max_eq_left h]
    have hM := rpow_sub_one_eq_mul hp hna
    have hMp : 0 ≤ (-a) ^ (p - 2) := Real.rpow_nonneg hna _
    nlinarith [mul_le_mul_of_nonneg_left (show b - a ≤ 2 * (-a) by linarith) hMp]

/-- Strong monotonicity of φ: `max(|a|,|b|)^(p-2) (b - a) ≤ 2 (φ(b) - φ(a))` for `a ≤ b`, p ≥ 2. -/
lemma phi_sub_ge {p a b : ℝ} (hp : 2 ≤ p) (hab : a ≤ b) :
    max |a| |b| ^ (p - 2) * (b - a) ≤ 2 * (phi p b - phi p a) := by
  rcases le_total 0 a with ha | ha
  · have h := phi_sub_ge_of_nonneg hp ha hab
    have hb : 0 ≤ b := ha.trans hab
    rw [abs_of_nonneg ha, abs_of_nonneg hb, max_eq_right hab]
    nlinarith [mul_nonneg (Real.rpow_nonneg hb (p - 2)) (sub_nonneg.mpr hab)]
  · rcases le_total b 0 with hb | hb
    · have h := phi_sub_ge_of_nonneg hp (by linarith : 0 ≤ -b) (by linarith : -b ≤ -a)
      rw [phi_neg, phi_neg] at h
      rw [abs_of_nonpos ha, abs_of_nonpos hb, max_eq_left (by linarith : -b ≤ -a)]
      nlinarith [mul_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ -a) (p - 2)) (sub_nonneg.mpr hab)]
    · exact phi_sub_ge_of_opp hp ha hb

/-- The symmetric form: `max(|a|,|b|)^(p-2) (b - a)^2 ≤ 2 (b - a)(φ(b) - φ(a))` for all `a, b`, p ≥ 2. -/
lemma phi_sub_ge_sq {p : ℝ} (hp : 2 ≤ p) (a b : ℝ) :
    max |a| |b| ^ (p - 2) * (b - a) ^ 2 ≤ 2 * ((b - a) * (phi p b - phi p a)) := by
  rcases le_total a b with hab | hab
  · have h := phi_sub_ge hp hab
    nlinarith [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hab)]
  · have h := phi_sub_ge hp hab
    rw [max_comm] at h
    nlinarith [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hab)]

/-- The quantitative tangent gap for p ≥ 2. -/
lemma breg_lower {p : ℝ} (hp : 2 ≤ p) (a y : ℝ) :
    p / 8 * ((|a| + |y - a|) / 5) ^ (p - 2) * (y - a) ^ 2 ≤ breg p a y := by
  set b := (a + y) / 2 with hb_def
  have h1 := tangent_le (by linarith : (1 : ℝ) ≤ p) a b
  have h2 := tangent_le (by linarith : (1 : ℝ) ≤ p) b y
  have hsplit : p * ((b - a) * (phi p b - phi p a)) ≤ breg p a y := by
    unfold breg
    have hyb : y - b = b - a := by rw [hb_def]; ring
    have hya : y - a = 2 * (b - a) := by rw [hb_def]; ring
    rw [hyb] at h2
    rw [hya]
    linear_combination h1 + h2
  have h3 := phi_sub_ge_sq hp a b
  set M := max |a| |b| with hM_def
  have hMa : |a| ≤ M := le_max_left _ _
  have hMb : |b| ≤ M := le_max_right _ _
  have hya : y - a = 2 * (b - a) := by rw [hb_def]; ring
  have hX : (|a| + |y - a|) / 5 ≤ M := by
    have : |y - a| ≤ 2 * |b| + 2 * |a| := by
      rw [hya, abs_mul, abs_two]
      linarith [abs_sub (b) (a)]
    linarith
  have hX0 : 0 ≤ (|a| + |y - a|) / 5 := by positivity
  have hpow : ((|a| + |y - a|) / 5) ^ (p - 2) ≤ M ^ (p - 2) := Real.rpow_le_rpow hX0 hX (by linarith)
  have hp0 : 0 ≤ p := by linarith
  have hsq : 0 ≤ (y - a) ^ 2 := sq_nonneg _
  calc p / 8 * ((|a| + |y - a|) / 5) ^ (p - 2) * (y - a) ^ 2
      ≤ p / 8 * M ^ (p - 2) * (y - a) ^ 2 := by gcongr
    _ = p / 2 * (M ^ (p - 2) * (b - a) ^ 2) := by rw [hya]; ring
    _ ≤ p / 2 * (2 * ((b - a) * (phi p b - phi p a))) := by gcongr
    _ = p * ((b - a) * (phi p b - phi p a)) := by ring
    _ ≤ breg p a y := hsplit

/-! ### The identity for `F0` -/

lemma one_add_rpow_eq {p B : ℝ} (hB : 0 < B) : (1 + B) ^ p = (1 + B) ^ (p - 1) * (1 + B) := by
  have hne : (1 + B) ≠ 0 := by linarith
  rw [Real.rpow_sub_one hne, div_mul_cancel₀ _ hne]

/-- `F0 = (1+B)^(p-1) (breg z u + B · breg z (-w))` with `z = (u - B w)/(1 + B)`. -/
lemma F0_eq_breg {p B : ℝ} (hB : 0 < B) (u w : ℝ) :
    F0 p B u w = (1 + B) ^ (p - 1) *
      (breg p ((u - B * w) / (1 + B)) u + B * breg p ((u - B * w) / (1 + B)) (-w)) := by
  set z := (u - B * w) / (1 + B) with hz_def
  have hpos : 0 < 1 + B := by linarith
  have hz : (1 + B) * z = u - B * w := by rw [hz_def]; field_simp
  have hpow : |u - B * w| ^ p = (1 + B) ^ (p - 1) * (1 + B) * |z| ^ p := by
    rw [← hz, abs_mul, abs_of_pos hpos, Real.mul_rpow hpos.le (abs_nonneg z), one_add_rpow_eq hB]
  unfold F0 breg
  rw [abs_neg]
  linear_combination -hpow - (1 + B) ^ (p - 1) * p * phi p z * hz

end B0

open B0

/-! ### Lemma 3.2 and Lemma 3.3 -/

theorem lemma_3_2_proved (p : ℝ) (hp : 1 < p) (B : ℝ) (hB : 0 < B) (u v w : ℝ) :
    bellmanF p 0 B (1 + B) (G0 p B) u v w = F0 p B u w ∧ 0 ≤ F0 p B u w ∧ (F0 p B u w = 0 ↔ w = -u) := by
  have hc : 0 < (1 + B) ^ (p - 1) := Real.rpow_pos_of_pos (by linarith) _
  have hdec := F0_eq_breg (p := p) hB u w
  set z := (u - B * w) / (1 + B) with hz_def
  have hb1 := breg_nonneg hp.le z u
  have hb2 := breg_nonneg hp.le z (-w)
  refine ⟨?_, ?_, ?_⟩
  · unfold bellmanF G0 F0
    rw [one_add_rpow_eq hB, zero_mul, add_zero]
    ring
  · rw [hdec]; positivity
  · constructor
    · intro h0
      have hzw : z = -w := by
        by_contra hne
        have := breg_pos hp hne
        have : 0 < (1 + B) ^ (p - 1) * (breg p z u + B * breg p z (-w)) := by positivity
        linarith
      have hne : (1 + B) ≠ 0 := by linarith
      rw [hz_def, div_eq_iff hne] at hzw
      linarith
    · intro hw
      have hzu : z = u := by rw [hz_def, hw]; field_simp; ring
      rw [hdec, hzu, hw, neg_neg, breg_self]
      ring

theorem lemma_3_5_proved (p : ℝ) (hp : 2 < p) (B : ℝ) (hB : 0 < B) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ u w : ℝ, c₁ * (|u| + |u + w|) ^ (p - 2) * (u + w) ^ 2 ≤ F0 p B u w := by
  have hpos : 0 < 1 + B := by linarith
  set lam := (1 + B)⁻¹ with hlam_def
  have hlam0 : 0 < lam := inv_pos.mpr hpos
  have hlam1 : lam ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hBlam : B * lam ≤ 1 := by
    rw [hlam_def, ← div_eq_mul_inv, div_le_one hpos]; linarith
  have hBlam0 : 0 ≤ B * lam := by positivity
  have hc : 0 < (1 + B) ^ (p - 1) := Real.rpow_pos_of_pos hpos _
  refine ⟨(1 + B) ^ (p - 1) * B * (p / 8) * (lam / 10) ^ (p - 2) * lam ^ 2, by positivity, ?_⟩
  intro u w
  set ν := u + w with hν_def
  have hdec := F0_eq_breg (p := p) hB u w
  set z := (u - B * w) / (1 + B) with hz_def
  have hb1 := breg_nonneg (by linarith : (1 : ℝ) ≤ p) z u
  have hlow := breg_lower hp.le z (-w)
  -- the two increments
  have hwz : -w - z = -(lam * ν) := by
    rw [hz_def, hν_def, hlam_def]; field_simp; ring
  have huz : u = z + B * lam * ν := by
    rw [hz_def, hν_def, hlam_def]; field_simp; ring
  rw [hwz, abs_neg, abs_mul, abs_of_pos hlam0, neg_sq] at hlow
  -- compare the weights
  have hX : lam / 10 * (|u| + |ν|) ≤ (|z| + lam * |ν|) / 5 := by
    have h1 : |u| ≤ |z| + B * lam * |ν| := by
      rw [huz]
      calc |z + B * lam * ν| ≤ |z| + |B * lam * ν| := abs_add_le _ _
        _ = |z| + B * lam * |ν| := by rw [abs_mul, abs_of_nonneg hBlam0]
    have hzn : 0 ≤ |z| := abs_nonneg _
    have hνn : 0 ≤ |ν| := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 hlam0.le, mul_le_mul_of_nonneg_right hBlam (mul_nonneg hlam0.le hνn),
      mul_le_mul_of_nonneg_right hlam1 hzn]
  have hX0 : 0 ≤ lam / 10 * (|u| + |ν|) := by positivity
  have hpow : (lam / 10) ^ (p - 2) * (|u| + |ν|) ^ (p - 2) ≤ ((|z| + lam * |ν|) / 5) ^ (p - 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow hX0 hX (by linarith)
  have hF : (1 + B) ^ (p - 1) * (B * breg p z (-w)) ≤ F0 p B u w := by
    rw [hdec]
    have : 0 ≤ (1 + B) ^ (p - 1) * breg p z u := mul_nonneg hc.le hb1
    nlinarith
  have hp0 : 0 ≤ p := by linarith
  calc (1 + B) ^ (p - 1) * B * (p / 8) * (lam / 10) ^ (p - 2) * lam ^ 2 * (|u| + |ν|) ^ (p - 2) * ν ^ 2
      = (1 + B) ^ (p - 1) * B * (p / 8 * ((lam / 10) ^ (p - 2) * (|u| + |ν|) ^ (p - 2)) * (lam * ν) ^ 2) := by
        ring
    _ ≤ (1 + B) ^ (p - 1) * B * (p / 8 * ((|z| + lam * |ν|) / 5) ^ (p - 2) * (lam * ν) ^ 2) := by
        gcongr
    _ ≤ (1 + B) ^ (p - 1) * (B * breg p z (-w)) := by
        rw [mul_assoc]; gcongr
    _ ≤ F0 p B u w := hF

end Matsaev
