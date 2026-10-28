/-
Smale/Proofs/Hurwitz.lean — the Hurwitz step of the proof of Lemma 5.3 of paper 009 (posted v1.80, tex l.453-456):
as ε → 0, d - 1 of the d critical points of p_ε, counted with multiplicity, tend to those of p, and the other one
escapes. By Rouché's theorem (ArgPrinciple.lean) with f = p' and g = (d+1)εz^d: (i) in a disk |w| < R₀ that contains
all critical points of p, p_ε has exactly d - 1 critical points for small ε; (ii) in a small disk around a critical
point β of p of multiplicity μ, p_ε has exactly μ critical points for small ε.
-/
import Smale.Proofs.Lemma53

namespace Smale

open Polynomial Complex Metric Filter Topology

/-- Rouché for `p_ε'`: if `p'` has no zero on the circle `|w - c| = ρ`, then for small `ε` the derivative of
`p_ε = p + εz^{d+1}` has as many zeros in `|w - c| < ρ` as `p'`. -/
theorem zerosInBall_eps_eq {d : ℕ} (p : ℂ[X]) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hsph : ∀ w : ℂ, ‖w - c‖ = ρ → p.derivative.eval w ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℂ, ‖ε‖ < δ →
      zerosInBall (p + C ε * X ^ (d + 1)).derivative c ρ = zerosInBall p.derivative c ρ := by
  have hpos : ∀ w ∈ sphere c ρ, 0 < ‖p.derivative.eval w‖ :=
    fun w hw => norm_pos_iff.2 (hsph w (mem_sphere_iff_norm.1 hw))
  obtain ⟨τ, hτ, hτS⟩ := (isCompact_sphere c ρ).exists_forall_le' (f := fun w => ‖p.derivative.eval w‖)
    (continuous_norm.comp p.derivative.continuous).continuousOn hpos
  set B : ℝ := ‖c‖ + ρ with hBdef
  have hB : 0 < B := add_pos_of_nonneg_of_pos (norm_nonneg _) hρ
  set K : ℝ := ((d : ℝ) + 1) * B ^ d + 1 with hKdef
  have hK : 0 < K := add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) (pow_pos hB d).le) one_pos
  refine ⟨τ / K, div_pos hτ hK, fun ε hε => ?_⟩
  have hεK : ‖ε‖ * K < τ := (lt_div_iff₀ hK).1 hε
  have hrouche := zerosInBall_add_of_norm_lt p.derivative (C (ε * ((d : ℂ) + 1)) * X ^ d) c hρ (fun w hw => by
    have hwB : ‖w‖ ≤ B := by
      have := norm_le_norm_add_norm_sub' w c
      rw [hw] at this
      linarith
    have h1 : τ ≤ ‖p.derivative.eval w‖ := hτS w (mem_sphere_iff_norm.2 hw)
    rw [eval_mul, eval_C, eval_pow, eval_X, norm_mul, norm_mul, norm_pow, norm_natCast_add_one]
    have h3 : ((d : ℝ) + 1) * ‖w‖ ^ d ≤ K := by
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hwB d)
        (show (0 : ℝ) ≤ (d : ℝ) + 1 by positivity)
      linarith
    have h4 : ‖ε‖ * ((d : ℝ) + 1) * ‖w‖ ^ d ≤ ‖ε‖ * K := by
      calc ‖ε‖ * ((d : ℝ) + 1) * ‖w‖ ^ d = ‖ε‖ * (((d : ℝ) + 1) * ‖w‖ ^ d) := by ring
        _ ≤ ‖ε‖ * K := mul_le_mul_of_nonneg_left h3 (norm_nonneg ε)
    linarith)
  rwa [← derivative_eps] at hrouche

/-- tex l.453-456 (Hurwitz): (i) in a disk `|w| < R₀` that contains all critical points of `p`, `p_ε` has exactly
`d - 1` critical points (with multiplicity) for small `ε` (so the remaining one of its `d` lies outside); (ii) around
each critical point `β` of `p` there is `r₀ > 0` such that for every `0 < r ≤ r₀` and small `ε`, `p_ε` has exactly
`μ` critical points in `|w - β| < r`, `μ` the multiplicity of `β`. -/
theorem lem_5_3_hurwitz_proved (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) :
    (∀ R₀ : ℝ, (∀ β : ℂ, p.derivative.eval β = 0 → ‖β‖ < R₀) → ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℂ, ‖ε‖ < δ →
      zerosInBall (p + C ε * X ^ (d + 1)).derivative 0 R₀ = d - 1) ∧
    (∀ β : ℂ, p.derivative.eval β = 0 → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℂ, ‖ε‖ < δ → zerosInBall (p + C ε * X ^ (d + 1)).derivative β r = p.derivative.rootMultiplicity β) := by
  have hp' : p.derivative ≠ 0 := fun h => by
    have h1 := hp.2.2
    rw [h, eval_zero] at h1
    exact zero_ne_one h1
  have hdeg' : p.derivative.natDegree = d - 1 := by
    rw [natDegree_derivative, hp.1]
  constructor
  · intro R₀ hR₀
    -- a critical point exists (degree d - 1 ≥ 1), so R₀ > 0
    obtain ⟨β₁, hβ₁⟩ := IsAlgClosed.exists_root p.derivative (by
      rw [degree_eq_natDegree hp', hdeg']; exact_mod_cast (show d - 1 ≠ 0 by omega))
    have hR₀pos : 0 < R₀ := lt_of_le_of_lt (norm_nonneg _) (hR₀ β₁ hβ₁)
    obtain ⟨δ, hδ, hδε⟩ := zerosInBall_eps_eq (d := d) p 0 hR₀pos (fun w hw h0 => by
      have := hR₀ w h0
      rw [sub_zero] at hw
      linarith)
    refine ⟨δ, hδ, fun ε hε => ?_⟩
    rw [hδε ε hε]
    unfold zerosInBall
    rw [Multiset.filter_eq_self.2 (fun w hw => by
      rw [sub_zero]; exact hR₀ w ((mem_roots hp').1 hw)), IsAlgClosed.card_roots_eq_natDegree, hdeg']
  · intro β hβ
    -- isolate β among the critical points of p
    have hS : (p.derivative.roots.toFinset.erase β : Set ℂ)ᶜ ∈ 𝓝 β :=
      (Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds (by simp)
    obtain ⟨ρ₁, hρ₁, hρ₁S⟩ := Metric.mem_nhds_iff.1 hS
    have hiso : ∀ w : ℂ, ‖w - β‖ < ρ₁ → p.derivative.eval w = 0 → w = β := by
      intro w hw h0
      by_contra hne
      exact hρ₁S (mem_ball_iff_norm.2 hw)
        (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hne, Multiset.mem_toFinset.2 ((mem_roots hp').2 h0)⟩))
    refine ⟨ρ₁ / 2, half_pos hρ₁, fun r hr hrr => ?_⟩
    obtain ⟨δ, hδ, hδε⟩ := zerosInBall_eps_eq (d := d) p β hr (fun w hw h0 => by
      have hwβ := hiso w (by rw [hw]; linarith) h0
      rw [hwβ, sub_self, norm_zero] at hw
      exact hr.ne hw)
    refine ⟨δ, hδ, fun ε hε => ?_⟩
    rw [hδε ε hε]
    unfold zerosInBall
    rw [Multiset.filter_congr (q := fun w => w = β) (fun w hw => ⟨fun h => hiso w (by linarith)
      ((mem_roots hp').1 hw), fun h => by rw [h, sub_self, norm_zero]; exact hr⟩), Multiset.filter_eq',
      Multiset.card_replicate, count_roots]

end Smale
