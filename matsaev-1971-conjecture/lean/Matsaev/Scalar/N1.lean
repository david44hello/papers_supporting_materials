/-
Matsaev/Scalar/N1.lean — Lemma 3.4 (`lem:N1`, "the maximum of Q") of the paper, and the symmetries of `Qf`.
Paper: "Matsaev's (1971) conjecture is false for every p != 2", Dave Goel, short v2.00 (md5 a9b3c6be), Lemma 3.4 (`lem:N1`).

Proof route (the paper's): `d'(t) = g(t) / (1 + t^p)^2` with `g(t) = 1 + t^(2p-2) - (p-1) t^(p-2) (1 + t^2)`;
`g' < 0` on `(0, 1)`, so `g` falls strictly from `g(0) = 1` to `g(1) = 4 - 2p < 0` and has exactly one zero `t*`.
Hence `d` rises on `[0, t*]` and falls on `[t*, 1]`. For the global maximum of `Q`, the symmetries
`Q(r w) = Q(w)`, `Q(J w) = Q(w)` reduce to `w = (1, s)` with `|s| ≤ 1`; `Q(1, s) = d(s)` for `s > 0` and
`Q(1, s) ≤ 0` for `s ≤ 0`.
For `h < 0` we use `t^p < t^2` on `(0, 1)` instead of the paper's `h(0) < 0, h' < 0`.
-/
import Matsaev.Defs.Scalar
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

namespace Matsaev

open Real Set Filter Topology

/-! ### Symmetries of `Qf` (exported for Theorem 3.6 and Lemma 4.1) -/

lemma phi_mul (p r u : ℝ) : phi p (r * u) = (SignType.sign r : ℝ) * |r| ^ (p - 1) * phi p u := by
  unfold phi
  rw [sign_mul, SignType.coe_mul, abs_mul, mul_rpow (abs_nonneg r) (abs_nonneg u)]
  ring

lemma phi_neg (p u : ℝ) : phi p (-u) = -phi p u := by
  unfold phi
  rw [Left.sign_neg, abs_neg, SignType.coe_neg]
  ring

lemma abs_mul_rpow (p r u : ℝ) : |r * u| ^ p = |r| ^ p * |u| ^ p := by
  rw [abs_mul, mul_rpow (abs_nonneg r) (abs_nonneg u)]

/-- `sign r · r · |r|^(p-1) = |r|^p` for `r ≠ 0`. -/
lemma sign_mul_self_mul_rpow (p r : ℝ) (hr : r ≠ 0) :
    (SignType.sign r : ℝ) * r * |r| ^ (p - 1) = |r| ^ p := by
  rw [sign_mul_self, mul_comm, ← rpow_add_one (abs_pos.mpr hr).ne', sub_add_cancel]

/-- `Q(r w) = Q(w)` for `r ≠ 0` (0-homogeneity). The hypothesis `1 < p` is not used. -/
theorem Qf_homog (p : ℝ) (_hp : 1 < p) (r u v : ℝ) (hr : r ≠ 0) : Qf p (r * u) (r * v) = Qf p u v := by
  unfold Qf
  rw [phi_mul, phi_mul, abs_mul_rpow, abs_mul_rpow]
  have hc := sign_mul_self_mul_rpow p r hr
  have hcpos : 0 < |r| ^ p := rpow_pos_of_pos (abs_pos.mpr hr) p
  calc (↑(SignType.sign r) * |r| ^ (p - 1) * phi p u * (r * v)
          - ↑(SignType.sign r) * |r| ^ (p - 1) * phi p v * (r * u)) / (|r| ^ p * |u| ^ p + |r| ^ p * |v| ^ p)
        = ((↑(SignType.sign r) * r * |r| ^ (p - 1)) * (phi p u * v - phi p v * u))
            / (|r| ^ p * (|u| ^ p + |v| ^ p)) := by congr 1 <;> ring
    _ = (|r| ^ p * (phi p u * v - phi p v * u)) / (|r| ^ p * (|u| ^ p + |v| ^ p)) := by rw [hc]
    _ = (phi p u * v - phi p v * u) / (|u| ^ p + |v| ^ p) := mul_div_mul_left _ _ hcpos.ne'

/-- `Q(J w) = Q(w)` with `J (u, v) = (v, -u)`. No hypotheses needed. -/
theorem Qf_J (p u v : ℝ) : Qf p v (-u) = Qf p u v := by
  unfold Qf
  rw [phi_neg, abs_neg, add_comm (|v| ^ p)]
  ring

/-- `Q(-w) = Q(w)`. No hypotheses needed. -/
theorem Qf_neg (p u v : ℝ) : Qf p (-u) (-v) = Qf p u v := by
  unfold Qf
  rw [phi_neg, phi_neg, abs_neg, abs_neg]
  ring

/-- `Q(1, t) = d(t)` for `t > 0`. -/
theorem Qf_one (p t : ℝ) (ht : 0 < t) : Qf p 1 t = dfun p t := by
  unfold Qf dfun phi
  rw [abs_one, one_rpow, one_rpow, abs_of_pos ht, sign_pos one_pos, sign_pos ht, SignType.coe_one]
  ring

/-! ### The functions `g` and `g'` -/

/-- The paper's `g(t) = 1 + t^(2p-2) - (p-1) t^(p-2) (1 + t^2)` (proof of Lemma 3.4). -/
noncomputable def gN1 (p t : ℝ) : ℝ := 1 + t ^ (2 * p - 2) - (p - 1) * t ^ (p - 2) * (1 + t ^ 2)

/-- `g'(t)` in the form `(p-1) t^(p-2) (2 t^p - (p-2) - p t^2) / t`, with `t^p` written as `t^(p-2) t^2`. -/
noncomputable def gdN1 (p t : ℝ) : ℝ :=
  (p - 1) * t ^ (p - 2) * (2 * t ^ (p - 2) * t ^ 2 - (p - 2) - p * t ^ 2) / t

/-- For `s > 0`, the powers of `s` that occur, written through `A = s^(p-2)`. -/
lemma rpow_split {s : ℝ} (hs : 0 < s) (p : ℝ) :
    s ^ (p - 1) = s ^ (p - 2) * s ∧ s ^ p = s ^ (p - 2) * s ^ 2 ∧
      s ^ (2 * p - 2) = (s ^ (p - 2)) ^ 2 * s ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show p - 1 = (p - 2) + 1 by ring, rpow_add_one hs.ne']
  · rw [show s ^ p = s ^ ((p - 2) + 2) by norm_num, rpow_add hs, rpow_two]
  · rw [show 2 * p - 2 = (p - 2) + (p - 2) + 2 by ring, rpow_add hs, rpow_add hs, rpow_two]
    ring

lemma hasDerivAt_dfun {p s : ℝ} (hs : 0 < s) :
    HasDerivAt (dfun p) (gN1 p s / (1 + s ^ p) ^ 2) s := by
  have hc : HasDerivAt (fun x : ℝ => x - x ^ (p - 1)) (1 - (p - 1) * s ^ (p - 1 - 1)) s :=
    (hasDerivAt_id' s).sub (hasDerivAt_rpow_const (Or.inl hs.ne'))
  have hd : HasDerivAt (fun x : ℝ => 1 + x ^ p) (p * s ^ (p - 1)) s :=
    (hasDerivAt_rpow_const (Or.inl hs.ne')).const_add 1
  have hden : (1 + s ^ p) ≠ 0 := by positivity
  refine (hc.div hd hden).congr_deriv ?_
  obtain ⟨h1, h2, h3⟩ := rpow_split hs p
  have h0 : s ^ (p - 1 - 1) = s ^ (p - 2) := by rw [show p - 1 - 1 = p - 2 by ring]
  unfold gN1
  rw [h0, h1, h2, h3]
  ring

lemma hasDerivAt_gN1 {p s : ℝ} (hs : 0 < s) : HasDerivAt (gN1 p) (gdN1 p s) s := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (2 * p - 2)) ((2 * p - 2) * s ^ (2 * p - 2 - 1)) s :=
    hasDerivAt_rpow_const (Or.inl hs.ne')
  have h2 : HasDerivAt (fun x : ℝ => (p - 1) * x ^ (p - 2)) ((p - 1) * ((p - 2) * s ^ (p - 2 - 1))) s :=
    (hasDerivAt_rpow_const (Or.inl hs.ne')).const_mul (p - 1)
  have h3 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (↑(2 : ℕ) * s ^ (2 - 1)) s :=
    (hasDerivAt_pow 2 s).const_add 1
  refine ((h1.const_add 1).sub (h2.mul h3)).congr_deriv ?_
  have e1 : s ^ (2 * p - 2 - 1) = (s ^ (p - 2)) ^ 2 * s := by
    rw [show 2 * p - 2 - 1 = (p - 2) + (p - 2) + 1 by ring, rpow_add_one hs.ne', rpow_add hs]
    ring
  have e2 : s ^ (p - 2 - 1) = s ^ (p - 2) / s := rpow_sub_one hs.ne' (p - 2)
  unfold gdN1
  rw [e1, e2]
  field_simp
  ring

lemma gdN1_neg {p s : ℝ} (hp : 2 < p) (hs0 : 0 < s) (hs1 : s < 1) : gdN1 p s < 0 := by
  unfold gdN1
  have hA0 : 0 < s ^ (p - 2) := rpow_pos_of_pos hs0 _
  have hA1 : s ^ (p - 2) < 1 := rpow_lt_one hs0.le hs1 (by linarith)
  have hs2 : 0 < s ^ 2 := by positivity
  have hbr : 2 * s ^ (p - 2) * s ^ 2 - (p - 2) - p * s ^ 2 < 0 := by
    nlinarith [mul_lt_mul_of_pos_right hA1 hs2]
  apply div_neg_of_neg_of_pos _ hs0
  exact mul_neg_of_pos_of_neg (mul_pos (by linarith) hA0) hbr

lemma continuousOn_gN1 {p : ℝ} (hp : 2 < p) : ContinuousOn (gN1 p) (Icc 0 1) := by
  have c1 : Continuous fun x : ℝ => x ^ (2 * p - 2) := continuous_rpow_const (by linarith)
  have c2 : Continuous fun x : ℝ => x ^ (p - 2) := continuous_rpow_const (by linarith)
  exact ((continuous_const.add c1).sub
    ((continuous_const.mul c2).mul (continuous_const.add (continuous_pow 2)))).continuousOn

lemma continuousOn_dfun {p : ℝ} (hp : 2 < p) : ContinuousOn (dfun p) (Ici 0) := by
  have c1 : Continuous fun x : ℝ => x ^ (p - 1) := continuous_rpow_const (by linarith)
  have c2 : Continuous fun x : ℝ => x ^ p := continuous_rpow_const (by linarith)
  refine ((continuous_id.sub c1).continuousOn).div ((continuous_const.add c2).continuousOn) ?_
  intro x hx
  have : 0 ≤ x ^ p := rpow_nonneg hx p
  positivity

lemma gN1_zero {p : ℝ} (hp : 2 < p) : gN1 p 0 = 1 := by
  unfold gN1
  rw [zero_rpow (by linarith), zero_rpow (by linarith)]
  ring

lemma gN1_one (p : ℝ) : gN1 p 1 = 4 - 2 * p := by
  unfold gN1
  rw [one_rpow, one_rpow]
  ring

lemma strictAntiOn_gN1 {p : ℝ} (hp : 2 < p) : StrictAntiOn (gN1 p) (Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1) (continuousOn_gN1 hp)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_gN1 hx.1).deriv]
  exact gdN1_neg hp hx.1 hx.2

/-- `g` has a zero in `(0, 1)`. -/
lemma exists_gN1_zero {p : ℝ} (hp : 2 < p) : ∃ t ∈ Ioo (0 : ℝ) 1, gN1 p t = 0 := by
  have hmem : (0 : ℝ) ∈ Icc (gN1 p 1) (gN1 p 0) := by
    rw [gN1_zero hp, gN1_one]
    constructor <;> linarith
  obtain ⟨t, ⟨ht0, ht1⟩, hgt⟩ := intermediate_value_Icc' zero_le_one (continuousOn_gN1 hp) hmem
  refine ⟨t, ⟨?_, ?_⟩, hgt⟩
  · rcases ht0.lt_or_eq with h | h
    · exact h
    · subst h; rw [gN1_zero hp] at hgt; norm_num at hgt
  · rcases ht1.lt_or_eq with h | h
    · exact h
    · subst h; rw [gN1_one] at hgt; linarith

/-! ### The extremal point `t*` and the shape of `d` -/

lemma dfun_pos {p t : ℝ} (hp : 2 < p) (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < dfun p t := by
  unfold dfun
  have h1 : t ^ (p - 1) < t ^ (1 : ℝ) := rpow_lt_rpow_of_exponent_gt ht.1 ht.2 (by linarith)
  rw [rpow_one] at h1
  have : 0 ≤ t ^ p := rpow_nonneg ht.1.le p
  apply div_pos <;> linarith

/-- `Q(1, s) ≤ 0` for `-1 ≤ s ≤ 0`. -/
lemma Qf_one_nonpos_of_nonpos {p s : ℝ} (hp : 2 < p) (hs1 : -1 ≤ s) (hs0 : s ≤ 0) : Qf p 1 s ≤ 0 := by
  unfold Qf phi
  rw [abs_one, one_rpow, one_rpow, sign_pos one_pos, SignType.coe_one]
  have hden : 0 < 1 + |s| ^ p := by have := rpow_nonneg (abs_nonneg s) p; linarith
  apply div_nonpos_iff.mpr
  right
  refine ⟨?_, hden.le⟩
  rcases hs0.lt_or_eq with hneg | hzero
  · rw [sign_neg hneg, SignType.coe_neg_one]
    have habs : |s| = -s := abs_of_neg hneg
    have hle : |s| ^ (p - 1) ≤ |s| :=
      rpow_le_self_of_le_one (abs_nonneg s) (by rw [habs]; linarith) (by linarith)
    linarith
  · rw [hzero, sign_zero, SignType.coe_zero]
    ring_nf
    rfl

section Shape

variable {p t : ℝ} (hp : 2 < p) (ht : t ∈ Ioo (0 : ℝ) 1) (hgt : gN1 p t = 0)
include hp ht hgt

lemma gN1_pos_of_lt {s : ℝ} (hs0 : 0 ≤ s) (hst : s < t) : 0 < gN1 p s := by
  have := strictAntiOn_gN1 hp ⟨hs0, by linarith [ht.2]⟩ ⟨ht.1.le, ht.2.le⟩ hst
  linarith

lemma gN1_neg_of_gt {s : ℝ} (hs1 : s ≤ 1) (hst : t < s) : gN1 p s < 0 := by
  have := strictAntiOn_gN1 hp ⟨ht.1.le, ht.2.le⟩ ⟨by linarith [ht.1], hs1⟩ hst
  linarith

lemma strictMonoOn_dfun : StrictMonoOn (dfun p) (Icc 0 t) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 t) ((continuousOn_dfun hp).mono fun x hx => hx.1)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_dfun hx.1).deriv]
  have : 0 < 1 + x ^ p := by have := rpow_nonneg hx.1.le p; linarith
  exact div_pos (gN1_pos_of_lt hp ht hgt hx.1.le hx.2) (by positivity)

lemma strictAntiOn_dfun : StrictAntiOn (dfun p) (Icc t 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc t 1)
    ((continuousOn_dfun hp).mono fun x hx => le_trans ht.1.le hx.1)
  intro x hx
  rw [interior_Icc] at hx
  have hx0 : 0 < x := lt_trans ht.1 hx.1
  rw [(hasDerivAt_dfun hx0).deriv]
  have : 0 < 1 + x ^ p := by have := rpow_nonneg hx0.le p; linarith
  exact div_neg_of_neg_of_pos (gN1_neg_of_gt hp ht hgt hx.2.le hx.1) (by positivity)

/-- `d(s) ≤ d(t*)` on `[0, 1]`, with equality only at `t*`. -/
lemma dfun_le (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : dfun p s ≤ dfun p t ∧ (dfun p s = dfun p t → s = t) := by
  rcases le_total s t with hst | hts
  · have hm := strictMonoOn_dfun hp ht hgt
    have hsI : s ∈ Icc 0 t := ⟨hs.1, hst⟩
    have htI : t ∈ Icc 0 t := ⟨ht.1.le, le_rfl⟩
    exact ⟨hm.monotoneOn hsI htI hst, fun h => hm.injOn hsI htI h⟩
  · have ha := strictAntiOn_dfun hp ht hgt
    have hsI : s ∈ Icc t 1 := ⟨hts, hs.2⟩
    have htI : t ∈ Icc t 1 := ⟨le_rfl, ht.2.le⟩
    exact ⟨ha.antitoneOn htI hsI hts, fun h => ha.injOn hsI htI h⟩

/-- The reduction step: for `u ≠ 0` and `|v| ≤ |u|`, `Q(u, v) ≤ d(t*)`, with equality iff `v = u t*`. -/
lemma Qf_le_of_abs_le (u v : ℝ) (hu : u ≠ 0) (hvu : |v| ≤ |u|) :
    Qf p u v ≤ dfun p t ∧ (Qf p u v = dfun p t ↔ v = u * t) := by
  have hQ : Qf p u v = Qf p 1 (v / u) := by
    rw [← Qf_homog p (by linarith) u 1 (v / u) hu, mul_one, mul_div_cancel₀ v hu]
  have hs : |v / u| ≤ 1 := by
    rw [abs_div]; exact (div_le_one (abs_pos.mpr hu)).mpr hvu
  have hiff : v = u * t ↔ v / u = t := by
    rw [div_eq_iff hu, mul_comm]
  rw [hQ, hiff]
  have hdpos := dfun_pos hp ht
  rcases lt_or_ge 0 (v / u) with hpos | hnp
  · rw [Qf_one p _ hpos]
    have hI : v / u ∈ Icc (0 : ℝ) 1 := ⟨hpos.le, le_trans (le_abs_self _) hs⟩
    obtain ⟨hle, heq⟩ := dfun_le hp ht hgt (v / u) hI
    exact ⟨hle, ⟨heq, fun h => by rw [h]⟩⟩
  · have hle := Qf_one_nonpos_of_nonpos hp (by linarith [neg_abs_le (v / u)]) hnp
    refine ⟨by linarith, ⟨fun h => by linarith, fun h => by linarith [ht.1]⟩⟩

end Shape

/-! ### Lemma 3.4 -/

theorem lemma_3_3_proved (p : ℝ) (hp : 2 < p) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      (∀ s ∈ Set.Ioo (0 : ℝ) 1, deriv (dfun p) s = 0 ↔ s = t) ∧
      deriv (deriv (dfun p)) t < 0 ∧
      0 < dfun p t ∧
      (∀ u v : ℝ, (u, v) ≠ (0, 0) → Qf p u v ≤ dfun p t) ∧
      Dstar p = dfun p t ∧
      (∀ u v : ℝ, (u, v) ≠ (0, 0) →
        (Qf p u v = dfun p t ↔ ∃ r : ℝ, r ≠ 0 ∧ ((u, v) = (r, r * t) ∨ (u, v) = (r * t, -r)))) ∧
      1 + t ^ (2 * p - 2) = (p - 1) * t ^ (p - 2) * (1 + t ^ 2) := by
  obtain ⟨t, ht, hgt⟩ := exists_gN1_zero hp
  -- the maximum of `Q`, and where it is attained
  have hmax : ∀ u v : ℝ, (u, v) ≠ (0, 0) →
      Qf p u v ≤ dfun p t ∧
        (Qf p u v = dfun p t ↔ ∃ r : ℝ, r ≠ 0 ∧ ((u, v) = (r, r * t) ∨ (u, v) = (r * t, -r))) := by
    intro u v huv
    rcases le_or_gt |v| |u| with hvu | huv'
    · have hu : u ≠ 0 := by
        rintro rfl
        have : v = 0 := abs_nonpos_iff.mp (by simpa using hvu)
        exact huv (by rw [this])
      obtain ⟨hle, hiff⟩ := Qf_le_of_abs_le hp ht hgt u v hu hvu
      refine ⟨hle, ?_⟩
      rw [hiff]
      constructor
      · intro h; exact ⟨u, hu, Or.inl (by rw [h])⟩
      · rintro ⟨r, hr, h | h⟩
        · simp only [Prod.mk.injEq] at h; rw [h.1, h.2]
        · exfalso
          simp only [Prod.mk.injEq] at h
          have hat : |r * t| < |r| := by
            rw [abs_mul, abs_of_pos ht.1]
            exact mul_lt_of_lt_one_right (abs_pos.mpr hr) ht.2
          rw [h.1, h.2, abs_neg] at hvu
          linarith
    · have hv : v ≠ 0 := by
        rintro rfl; rw [abs_zero] at huv'; linarith [abs_nonneg u]
      have hvu' : |-u| ≤ |v| := by rw [abs_neg]; exact huv'.le
      obtain ⟨hle, hiff⟩ := Qf_le_of_abs_le hp ht hgt v (-u) hv hvu'
      rw [Qf_J] at hle hiff
      refine ⟨hle, ?_⟩
      rw [hiff]
      constructor
      · intro h
        refine ⟨-v, neg_ne_zero.mpr hv, Or.inr ?_⟩
        simp only [Prod.mk.injEq]
        constructor <;> linarith
      · rintro ⟨r, hr, h | h⟩
        · exfalso
          simp only [Prod.mk.injEq] at h
          have hat : |r * t| < |r| := by
            rw [abs_mul, abs_of_pos ht.1]
            exact mul_lt_of_lt_one_right (abs_pos.mpr hr) ht.2
          rw [h.1, h.2] at huv'
          linarith
        · simp only [Prod.mk.injEq] at h
          rw [h.1, h.2]; ring
  have hdpos := dfun_pos hp ht
  refine ⟨t, ht, ?_, ?_, hdpos, fun u v huv => (hmax u v huv).1, ?_, fun u v huv => (hmax u v huv).2, ?_⟩
  · -- the critical points of `d` in `(0, 1)`
    intro s hs
    rw [(hasDerivAt_dfun hs.1).deriv]
    have hden : (1 + s ^ p) ^ 2 ≠ 0 := by
      have := rpow_nonneg hs.1.le p; positivity
    rw [div_eq_zero_iff, or_iff_left hden]
    constructor
    · intro h
      exact (strictAntiOn_gN1 hp).injOn ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩ (h.trans hgt.symm)
    · rintro rfl; exact hgt
  · -- `d''(t*) < 0`
    have heq : deriv (dfun p) =ᶠ[𝓝 t] fun s => gN1 p s / (1 + s ^ p) ^ 2 := by
      filter_upwards [Ioi_mem_nhds ht.1] with s hs
      exact (hasDerivAt_dfun hs).deriv
    rw [heq.deriv_eq]
    have hD : HasDerivAt (fun s : ℝ => (1 + s ^ p) ^ 2)
        (↑(2 : ℕ) * (1 + t ^ p) ^ (2 - 1) * (p * t ^ (p - 1))) t :=
      ((hasDerivAt_rpow_const (Or.inl ht.1.ne')).const_add 1).pow 2
    have hpos : 0 < 1 + t ^ p := by have := rpow_nonneg ht.1.le p; linarith
    have hq := (hasDerivAt_gN1 (p := p) ht.1).div hD (by positivity)
    rw [show (fun s => gN1 p s / (1 + s ^ p) ^ 2) = (gN1 p / fun s => (1 + s ^ p) ^ 2) from rfl,
      hq.deriv, hgt, zero_mul, sub_zero]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (gdN1_neg hp ht.1 ht.2) (by positivity))
      (by positivity)
  · -- `D* = d(t*)`
    apply IsGreatest.csSup_eq
    refine ⟨⟨1, t, by simp, Qf_one p t ht.1⟩, ?_⟩
    rintro q ⟨u, v, huv, rfl⟩
    exact (hmax u v huv).1
  · -- the identity (ST)
    unfold gN1 at hgt
    linarith

end Matsaev
