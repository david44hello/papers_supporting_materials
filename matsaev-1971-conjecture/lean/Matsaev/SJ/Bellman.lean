-- Matsaev/SJ/Bellman.lean — Steps F-I of the proof of Theorem 3.6 (`thm:SJ`): from SigmaInterface (Steps D/E), a Bellman function G_a exists.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.Defs.Spaces
import Matsaev.Bridge.Basic
import Matsaev.Angle.Defs
import Matsaev.Scalar.B0
import Matsaev.SJ.Interface
import Matsaev.SJ.BellmanDefs
import Matsaev.SJ.BellmanAlg
import Matsaev.SJ.BellmanTrig
import Matsaev.SJ.BellmanCases
import Matsaev.SJ.BellmanEst
import Matsaev.SJ.BellmanLam
import Matsaev.SJ.BellmanLip

/-!
# Steps F-I of the proof of Theorem 3.6

Order of constants (Theorem 3.6, "Order of the constants", our route): `κ = sin θ_*/2` (the extremal angles avoid the axis `u = 0`); `ε_d, d` (the λ-system
is uniquely solvable near `θ_*`); `K_R`, `Λ = 2K_R/d` (`|λ| ≤ Λa`); `c₁` (Lemma 3.3); `L` (the C¹ bound of `Δ`); `ν₃, a₃, K_T`
(Taylor in `ν`); `a₄, L'` (`n` is `O(a)`-Lipschitz); `ρ`, then `a₁, η` from `SigmaInterface`; `ν₂`; last `a₀` = the minimum of all
thresholds. For `0 < a < a₀`: take `θ_a` from `SigmaInterface`, `λ` from the 2×2 system at `e(θ_a)`, and `G = G_{a,λ}`.
-/

namespace Matsaev.SJ

open Real
open scoped ENNReal

/-- The exponent as a real number exceeds 2. -/
lemma toReal_gt_two {p : ℝ≥0∞} (hp : 2 < p) (hptop : p ≠ ⊤) : 2 < p.toReal := by
  have h := (ENNReal.toReal_lt_toReal (by simp) hptop).2 hp
  simpa using h

/-- A threshold: `a ≤ c/(k + 1)` gives `k a ≤ c` (`k, a ≥ 0`). -/
lemma mul_le_of_le_div_add_one {k a c : ℝ} (hk : 0 ≤ k) (ha : 0 ≤ a) (h : a ≤ c / (k + 1)) : k * a ≤ c := by
  have h1 := (le_div_iff₀ (by linarith : (0 : ℝ) < k + 1)).1 h
  have e : a * (k + 1) = k * a + a := by ring
  linarith

/-- `γ₀ = B(1+B)^(q-1) - B^q > 0`: the coefficient of `|w|^q` in the window at `s = 0` when `a = 0`. -/
lemma gamma0_pos {q B : ℝ} (hq : 1 < q) (hB : 0 < B) : 0 < B * (1 + B) ^ (q - 1) - B ^ q := by
  have h1 : B ^ (q - 1) < (1 + B) ^ (q - 1) := Real.rpow_lt_rpow hB.le (by linarith) (by linarith)
  have h2 : B ^ q = B * B ^ (q - 1) := by
    rw [← Real.rpow_one_add' hB.le (by linarith)]
    congr 1; ring
  rw [h2]
  nlinarith

/-- The case `a = 0` (proof of Theorem 3.6, first paragraph): `G = G₀` works, because `C_0 ≥ 1 + B` and Lemma 3.2. -/
lemma bellman_a_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (hq : 1 < p.toReal) (B : ℝ) (hB : 0 < B) :
    ∃ G : ℝ → ℝ → ℝ, Continuous (Function.uncurry G) ∧ G 0 0 = 0 ∧
      ∀ u v w : ℝ, 0 ≤ bellmanF p.toReal 0 B (Ca p 0 B) G u v w := by
  set q := p.toReal with hq_def
  have hq0 : 0 < q := by linarith
  refine ⟨G0 q B, ?_, ?_, fun u v w => ?_⟩
  · have h : Continuous fun x : ℝ => |x| ^ q := continuous_abs.rpow_const fun _ => Or.inr hq0.le
    change Continuous fun x : ℝ × ℝ => G0 q B x.1 x.2
    unfold G0
    exact continuous_const.mul ((h.comp continuous_fst).add (h.comp continuous_snd))
  · simp [G0, Real.zero_rpow hq0.ne']
  · have hC := one_add_le_Ca_zero p hptop B hB
    obtain ⟨h1, h2, -⟩ := lemma_3_2_proved q hq B hB u v w
    have hCq : (1 + B) ^ q ≤ (Ca p 0 B) ^ q := Real.rpow_le_rpow (by linarith) hC hq0.le
    have hsplit : bellmanF q 0 B (Ca p 0 B) (G0 q B) u v w =
        bellmanF q 0 B (1 + B) (G0 q B) u v w + ((Ca p 0 B) ^ q - (1 + B) ^ q) * |u| ^ q := by
      unfold bellmanF; ring
    rw [hsplit, h1]
    have : 0 ≤ ((Ca p 0 B) ^ q - (1 + B) ^ q) * |u| ^ q := mul_nonneg (by linarith) (by positivity)
    linarith

/-- The four points `θ_a + kπ/2` stay away from the axis `u = 0`: `|cos(θ_a + kπ/2)| ≥ κ = sin θ_*/2` when `|θ_a - θ_*| ≤ κ`. -/
lemma cos_bound_coset {θs θa : ℝ} (h0 : 0 < θs) (h1 : θs < π / 4) (hθa : |θa - θs| ≤ Real.sin θs / 2) (k : ℤ) :
    Real.sin θs / 2 ≤ |Real.cos (θa + k * (π / 2))| := by
  have h2 := sin_le_abs_cos_add_int_mul θs h0 h1 k
  have h3 := Real.abs_cos_sub_cos_le (θa + k * (π / 2)) (θs + k * (π / 2))
  rw [show θa + k * (π / 2) - (θs + k * (π / 2)) = θa - θs by ring] at h3
  have h4 := abs_sub_abs_le_abs_sub (Real.cos (θs + k * (π / 2))) (Real.cos (θa + k * (π / 2)))
  rw [abs_sub_comm (Real.cos (θs + k * (π / 2)))] at h4
  linarith

/-- **Step 6 on the unit circle** (Theorem 3.6, Step 6): the three cases, with every constant and estimate as a hypothesis. -/
lemma circle_nonneg {q a B C l1 l2 θa c₁ L KT L' η ρ ν₂ ν₃ κ : ℝ} (hq : 2 < q) (hB : 0 < B) (ha : 0 < a)
    (hc₁ : 0 < c₁) (hL : 0 ≤ L) (hη : 0 < η) (hρ : 0 < ρ) (hκ : 0 < κ) (hν₂ : 0 < ν₂) (hν₂1 : ν₂ ≤ 1) (hν₂3 : ν₂ ≤ ν₃)
    (hρκ : ρ ≤ κ / 2)
    (hF0 : ∀ u w : ℝ, c₁ * (|u| + |u + w|) ^ (q - 2) * (u + w) ^ 2 ≤ F0 q B u w)
    (hS : ∀ θ : ℝ, a * η * (min ρ (Angle.angDist θ θa)) ^ 2 ≤ Angle.SigmaAng q a B C θ)
    (hG2 : ∀ u v ν : ℝ, u ^ 2 + v ^ 2 = 1 → |DeltaUV q a B l1 l2 u v ν| ≤ L * a * (1 + |ν|) ^ (q - 1) * |ν|)
    (hTR : ∀ u v ν : ℝ, u ^ 2 + v ^ 2 = 1 → κ / 2 ≤ |u| → |ν| ≤ ν₃ →
      |DeltaUV q a B l1 l2 u v ν - q * ν * nUV q a B l1 l2 u v| ≤ KT * a * ν ^ 2)
    (hLip : ∀ θ θ₀ : ℝ, κ ≤ |Real.cos θ₀| → |θ - θ₀| ≤ κ / 2 →
      |nUV q a B l1 l2 (Real.cos θ) (Real.sin θ) - nUV q a B l1 l2 (Real.cos θ₀) (Real.sin θ₀)| ≤ L' * a * |θ - θ₀|)
    (hgz : ∀ k : ℤ, nUV q a B l1 l2 (Real.cos (θa + k * (π / 2))) (Real.sin (θa + k * (π / 2))) = 0)
    (hcos0 : ∀ k : ℤ, κ ≤ |Real.cos (θa + k * (π / 2))|)
    (hlarge : L * a * (1 / ν₂ + 1) ^ (q - 1) ≤ c₁) (hfar : L * 2 ^ (q - 1) * ν₂ ≤ η * ρ ^ 2 / 4)
    (hK : KT * a ≤ c₁ * (κ / 2) ^ (q - 2) / 2) (hL' : q ^ 2 * L' ^ 2 * a ≤ η * (c₁ * (κ / 2) ^ (q - 2) / 2)) :
    ∀ θ ν : ℝ, 0 ≤ fcirc q a B C l1 l2 θ ν := by
  intro θ ν
  rw [fcirc_eq q a B C l1 l2 θ ν hB]
  have hF : c₁ * (|Real.cos θ| + |ν|) ^ (q - 2) * ν ^ 2 ≤ F0 q B (Real.cos θ) (-Real.cos θ + ν) := by
    have h := hF0 (Real.cos θ) (-Real.cos θ + ν)
    rwa [show Real.cos θ + (-Real.cos θ + ν) = ν by ring] at h
  have hS0 : 0 ≤ Angle.SigmaAng q a B C θ := le_trans (by positivity) (hS θ)
  have hΔ1 := hG2 (Real.cos θ) (Real.sin θ) ν (Real.cos_sq_add_sin_sq θ)
  by_cases hνbig : ν₂ ≤ |ν|
  · -- Step 6, large |ν|
    exact case_large hq hc₁ hL ha hν₂ hν₂1 hνbig hF hS0 hΔ1 hlarge
  push_neg at hνbig
  by_cases hfarθ : ρ ≤ Angle.angDist θ θa
  · -- Step 6(a): far from the extremal angles
    have hSθ : a * η * ρ ^ 2 ≤ Angle.SigmaAng q a B C θ := by
      have h := hS θ; rwa [min_eq_left hfarθ] at h
    have hF0nn : 0 ≤ F0 q B (Real.cos θ) (-Real.cos θ + ν) :=
      (lemma_3_2_proved q (by linarith) B hB (Real.cos θ) 0 (-Real.cos θ + ν)).2.1
    exact case_far hq hL ha hη hρ hν₂1 hνbig.le hF0nn hSθ hΔ1 hfar
  -- Step 6(b): near the extremal angles
  push_neg at hfarθ
  obtain ⟨k, hk⟩ := exists_int_angDist θ θa
  have hr0 : 0 ≤ Angle.angDist θ θa := hk ▸ abs_nonneg _
  have hdist : |θ - (θa + k * (π / 2))| ≤ κ / 2 := hk ▸ (hfarθ.le.trans hρκ)
  have hcosθ : κ / 2 ≤ |Real.cos θ| := by
    have h1 := hcos0 k
    have h2 := Real.abs_cos_sub_cos_le θ (θa + k * (π / 2))
    have h3 := abs_sub_abs_le_abs_sub (Real.cos (θa + k * (π / 2))) (Real.cos θ)
    rw [abs_sub_comm (Real.cos (θa + k * (π / 2)))] at h3
    linarith
  have hn : |nUV q a B l1 l2 (Real.cos θ) (Real.sin θ)| ≤ L' * a * Angle.angDist θ θa := by
    have h := hLip θ (θa + k * (π / 2)) (hcos0 k) hdist
    rw [hgz k, sub_zero, hk] at h
    exact h
  have hTR' := hTR (Real.cos θ) (Real.sin θ) ν (Real.cos_sq_add_sin_sq θ) hcosθ (hνbig.le.trans hν₂3)
  have hSθ : a * η * (Angle.angDist θ θa) ^ 2 ≤ Angle.SigmaAng q a B C θ := by
    have h := hS θ; rwa [min_eq_right hfarθ.le] at h
  exact case_near hq hc₁ (by positivity) ha hη hr0 hcosθ hF hSθ hTR' hn hK hL'

/-- **Steps F-I of Theorem 3.6**: from Steps D/E (`SigmaInterface`) and Lemma 3.4 in angle form (`IsThetaStar`), for all small
`a ≥ 0` there is a Bellman function `G` (continuous, `G(0,0) = 0`) whose window function with `C = C_a` is `≥ 0` on `ℝ³`. -/
theorem bellman_of_sigma (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B)
    (θs : ℝ) (hθs : Angle.IsThetaStar p.toReal θs) (hSig : SigmaInterface p B θs) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 ≤ a → a < a₀ → ∃ G : ℝ → ℝ → ℝ, Continuous (Function.uncurry G) ∧ G 0 0 = 0 ∧
      ∀ u v w : ℝ, 0 ≤ bellmanF p.toReal a B (Ca p a B) G u v w := by
  have hq : 2 < p.toReal := toReal_gt_two hp hptop
  set q := p.toReal with hq_def
  have hq0 : 0 < q := by linarith
  have hq1 : 1 < q := by linarith
  obtain ⟨hθ0, hθ1⟩ := hθs.mem
  -- Step 0: κ (the four extremal angles θ_* + kπ/2 have |cos| ≥ sin θ_* = 2κ).
  have hsin : 0 < Real.sin θs := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  set κ := Real.sin θs / 2 with hκ_def
  have hκ : 0 < κ := by positivity
  -- Step 4: the λ-system is solvable near θ_*, with |λ| ≤ Λ a.
  obtain ⟨εd, d, hεd, hd, hdet⟩ := detL_bound_near q θs hq hθ0 hθ1
  obtain ⟨KR, hKR, hR⟩ := R_bound q B hq hB
  set Λ := 2 * KR / d with hΛ_def
  have hΛ : 0 ≤ Λ := by positivity
  -- Lemma 3.3, Step 5, Step 6 (Case 2).
  obtain ⟨c₁, hc₁, hF0⟩ := lemma_3_5_proved q hq B hB
  obtain ⟨L, hL, hG2⟩ := delta_first_order q B Λ hq hB hΛ
  obtain ⟨ν₃, a₃, KT, hν₃, ha₃, hKT, hTR⟩ := delta_second_order q B Λ (κ / 2) hq hB hΛ (by positivity)
  obtain ⟨a₄, L', ha₄, hL', hLip⟩ := nUV_lipschitz q B Λ κ hq hB hΛ hκ
  -- Step 3: ρ, then a₁ and η from Steps D/E.
  obtain ⟨ρ₀, hρ₀, hSρ⟩ := hSig
  set ρ := min ρ₀ (κ / 2) with hρ_def
  have hρ : 0 < ρ := lt_min hρ₀ (by positivity)
  obtain ⟨a₁, η, ha₁, hη, hSa⟩ := hSρ ρ hρ (min_le_left _ _)
  -- Step 6(a): the threshold ν₂ for |ν|.
  set ν₂ := min (min 1 ν₃) (η * ρ ^ 2 / 4 / (L * 2 ^ (q - 1) + 1)) with hν₂_def
  have hν₂ : 0 < ν₂ := lt_min (lt_min one_pos hν₃) (by positivity)
  have hν₂1 : ν₂ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hν₂3 : ν₂ ≤ ν₃ := (min_le_left _ _).trans (min_le_right _ _)
  have hν₂far : L * 2 ^ (q - 1) * ν₂ ≤ η * ρ ^ 2 / 4 :=
    mul_le_of_le_div_add_one (by positivity) hν₂.le (min_le_right _ _)
  -- The last thresholds for a.
  set γ₀ := B * (1 + B) ^ (q - 1) - B ^ q with hγ₀_def
  have hγ₀ : 0 < γ₀ := gamma0_pos hq1 hB
  set Q₀ := c₁ * (κ / 2) ^ (q - 2) / 2 with hQ₀_def
  have hQ₀ : 0 < Q₀ := by positivity
  set X := (1 / ν₂ + 1) ^ (q - 1) with hX_def
  have hX : 0 < X := by positivity
  set a₀ := min (min (min 1 a₁) (min εd κ)) (min (min a₃ a₄)
    (min (min (γ₀ / (1 / 2 + 2 * Λ + 1)) (c₁ / (L * X + 1))) (min (Q₀ / (KT + 1)) (η * Q₀ / (q ^ 2 * L' ^ 2 + 1)))))
    with ha₀_def
  have ha₀ : 0 < a₀ := by
    refine lt_min (lt_min (lt_min one_pos ha₁) (lt_min hεd hκ)) (lt_min (lt_min ha₃ ha₄) ?_)
    refine lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))
  refine ⟨a₀, ha₀, fun a ha0 ha => ?_⟩
  rcases ha0.eq_or_lt with rfl | hapos
  · exact bellman_a_zero p hptop hq1 B hB
  -- what a < a₀ gives
  have hA1 : a ≤ 1 := by
    have : a₀ ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    linarith
  have hAa₁ : a < a₁ := by
    have : a₀ ≤ a₁ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    linarith
  have hAεd : a ≤ εd := by
    have : a₀ ≤ εd := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hAκ : a ≤ κ := by
    have : a₀ ≤ κ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hAa₃ : a ≤ a₃ := by
    have : a₀ ≤ a₃ := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    linarith
  have hAa₄ : a ≤ a₄ := by
    have : a₀ ≤ a₄ := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    linarith
  have hAγ : a ≤ γ₀ / (1 / 2 + 2 * Λ + 1) := by
    have : a₀ ≤ γ₀ / (1 / 2 + 2 * Λ + 1) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
    linarith
  have hAlarge : a ≤ c₁ / (L * X + 1) := by
    have : a₀ ≤ c₁ / (L * X + 1) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
    linarith
  have hAK : a ≤ Q₀ / (KT + 1) := by
    have : a₀ ≤ Q₀ / (KT + 1) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hAL' : a ≤ η * Q₀ / (q ^ 2 * L' ^ 2 + 1) := by
    have : a₀ ≤ η * Q₀ / (q ^ 2 * L' ^ 2 + 1) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  -- θ_a (Steps D/E) and λ (Step 4).
  obtain ⟨θa, hθa, -, hSbound⟩ := hSa a hapos hAa₁
  set C := Ca p a B with hC_def
  set l1 := lam1 q a B (Real.cos θa) (Real.sin θa) with hl1_def
  set l2 := lam2 q a B (Real.cos θa) (Real.sin θa) with hl2_def
  have hdetθa : d ≤ |detL q (Real.cos θa) (Real.sin θa)| := hdet θa (hθa.trans hAεd)
  have hRθa := hR a (Real.cos θa) (Real.sin θa) hapos.le hA1 (Real.abs_cos_le_one θa) (Real.abs_sin_le_one θa)
  obtain ⟨hl1, hl2⟩ := lam_bound hq1 hd hdetθa (Real.abs_cos_le_one θa) (Real.abs_sin_le_one θa) hRθa.1 hRθa.2
  have hdet0 : detL q (Real.cos θa) (Real.sin θa) ≠ 0 := by
    intro h; rw [h, abs_zero] at hdetθa; linarith
  obtain ⟨hn0, hn1⟩ := nUV_lam q a B (Real.cos θa) (Real.sin θa) hdet0
  -- n vanishes on the coset θ_a + (π/2)ℤ.
  set g : ℝ → ℝ := fun θ => nUV q a B l1 l2 (Real.cos θ) (Real.sin θ) with hg_def
  have hg : ∀ θ, g (θ + π) = -g θ := by
    intro θ
    simp only [hg_def, Real.cos_add_pi, Real.sin_add_pi]
    exact nUV_neg q a B l1 l2 _ _
  have hgz : ∀ k : ℤ, g (θa + k * (π / 2)) = 0 := by
    refine zero_on_coset g hg θa hn0 ?_
    simp only [hg_def, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
    exact hn1
  -- The Bellman function.
  refine ⟨Gab q a B C l1 l2, continuous_Gab q a B C l1 l2 hq0, Gab_zero q a B C l1 l2 hq0, ?_⟩
  apply bellmanF_nonneg_of_circle hq0
  · -- s = 0 (Theorem 3.6, Step 6)
    intro w
    rw [bellmanF_zero_zero q a B C l1 l2 w hq0 hapos.le hB]
    refine mul_nonneg ?_ (by positivity)
    have haq : a ^ q ≤ a := Real.rpow_le_self_of_le_one hapos.le hA1 hq1.le
    have h1 := (abs_le.mp hl1).1
    have h2 := (abs_le.mp hl2).1
    have h3 := mul_le_of_le_div_add_one (by positivity : (0 : ℝ) ≤ 1 / 2 + 2 * Λ) hapos.le
      (show a ≤ γ₀ / (1 / 2 + 2 * Λ + 1) from hAγ)
    have e : (1 / 2 + 2 * Λ) * a = a / 2 + 2 * (Λ * a) := by ring
    linarith
  · -- the unit circle
    refine circle_nonneg (θa := θa) (c₁ := c₁) (L := L) (KT := KT) (L' := L') (η := η) (ρ := ρ) (ν₂ := ν₂) (ν₃ := ν₃)
      (κ := κ) hq hB hapos hc₁ hL hη hρ hκ hν₂ hν₂1 hν₂3 (min_le_right _ _) hF0 hSbound
      (fun u v ν huv => hG2 a l1 l2 u v ν hapos hA1 hl1 hl2 huv)
      (fun u v ν huv hu hν => hTR a l1 l2 u v ν hapos hAa₃ hl1 hl2 huv hu hν)
      (fun θ θ₀ h1 h2 => hLip a l1 l2 θ θ₀ hapos hAa₄ hl1 hl2 h1 h2) hgz
      (cos_bound_coset hθ0 hθ1 (hθa.trans hAκ)) ?_ hν₂far ?_ ?_
    · have h := mul_le_of_le_div_add_one (by positivity : (0 : ℝ) ≤ L * X) hapos.le hAlarge
      have e : L * X * a = L * a * X := by ring
      rw [hX_def] at e
      linarith
    · exact mul_le_of_le_div_add_one hKT hapos.le hAK
    · exact mul_le_of_le_div_add_one (by positivity) hapos.le hAL'

end Matsaev.SJ
