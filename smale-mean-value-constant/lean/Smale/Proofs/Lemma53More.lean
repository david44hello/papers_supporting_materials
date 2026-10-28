/-
Smale/Proofs/Lemma53More.lean — two steps of the proof of Lemma 5.3 of paper 009 (posted v1.90, tex l.453-463): a
critical point of p_ε escapes to ∞ as ε → 0 (the d critical points have product of modulus 1/((d+1)|ε|)); and at a
critical point β of p_ε, p_ε(β)/β = Q(β) for one polynomial Q of degree d - 1 ≥ 1, so |p_ε(β)/β| → ∞ as |β| → ∞,
uniformly in ε.
-/
import Smale.Proofs.Lemma53

namespace Smale

open Polynomial Complex

theorem norm_multiset_prod_le_pow (s : Multiset ℂ) (M : ℝ) (hM : 0 ≤ M) (h : ∀ x ∈ s, ‖x‖ ≤ M) :
    ‖s.prod‖ ≤ M ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    exact mul_le_mul (h a (Multiset.mem_cons_self a s)) (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))
      (norm_nonneg _) hM

/-- tex l.453-456: as `ε → 0` a critical point of `p_ε` tends to `∞`: for every `M > 0` there is `δ > 0` such that for
`0 < |ε| < δ` some critical point `β` of `p_ε` has `|β| ≥ M`. -/
theorem lem_5_3_escape_proved (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (M : ℝ) (hM : 0 < M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℂ, ε ≠ 0 → ‖ε‖ < δ →
      ∃ β : ℂ, (p + C ε * X ^ (d + 1)).derivative.eval β = 0 ∧ M ≤ ‖β‖ := by
  have hMd : 0 < M ^ d := pow_pos hM d
  refine ⟨1 / (((d : ℝ) + 1) * M ^ d), by positivity, fun ε hε hεδ => ?_⟩
  by_contra hno
  simp only [not_exists, not_and, not_le] at hno
  obtain ⟨hcard, hprod⟩ := lem_5_3_prod_proved d hd p hp ε hε
  have hq0 : (p + C ε * X ^ (d + 1)).derivative ≠ 0 := by
    intro h; rw [h, roots_zero, Multiset.card_zero] at hcard; omega
  have hle := norm_multiset_prod_le_pow (p + C ε * X ^ (d + 1)).derivative.roots M hM.le
    fun x hx => (hno x ((mem_roots hq0).1 hx)).le
  rw [hcard, hprod] at hle
  have hεpos : 0 < ‖ε‖ := norm_pos_iff.2 hε
  have hden : 0 < ((d : ℝ) + 1) * M ^ d := by positivity
  have h1 : ‖ε‖ * (((d : ℝ) + 1) * M ^ d) < 1 := (lt_div_iff₀ hden).1 (by rw [one_div] at hεδ ⊢; exact hεδ)
  have h2 : 1 ≤ M ^ d * (((d : ℝ) + 1) * ‖ε‖) := (div_le_iff₀ (by positivity)).1 hle
  nlinarith

/-- tex l.456-463: at a critical point `β` of `p_ε`, `p_ε(β)/β = p(β)/β - p'(β)/(d+1)` is the value at `β` of one
polynomial of degree `d - 1 ≥ 1`, independent of `ε`, so it tends to `∞` in modulus as `|β| → ∞`, uniformly in `ε`. -/
theorem lem_5_3_far_ratio_proved (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (B : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ ε β : ℂ, ε ≠ 0 → (p + C ε * X ^ (d + 1)).derivative.eval β = 0 → R ≤ ‖β‖ →
      B ≤ ‖(p + C ε * X ^ (d + 1)).eval β / β‖ := by
  obtain ⟨R, hR, h⟩ := farPoly_large hd hp B
  exact ⟨R, hR, fun ε β hε hβ hRβ => by rw [eval_farPoly_of_crit hd hp hε hβ]; exact h β hRβ⟩

end Smale
