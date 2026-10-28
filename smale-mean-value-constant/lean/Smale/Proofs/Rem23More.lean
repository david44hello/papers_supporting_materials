/-
Smale/Proofs/Rem23More.lean — the steps of Remark 2.3 of paper 009 (posted v1.90, tex l.165-170) that need no Riemann
map, with the conformal map ψ as a parameter: the set {|q| < R} (so also its component Ω that contains 0) is bounded;
for R < m(p) every critical point of p lies outside it; and for every ψ with ψ(0) = 0 and ψ'(0) = κ, the pair
W = ψ/κ, B = (q∘ψ)/R has W(0) = 0, W'(0) = 1, B(0) = 1/R and (WB)' = p'(ψ)ψ'/(κR).
-/
import Smale.Proofs.Sec2

namespace Smale

open Polynomial Complex Metric Filter Topology

theorem degree_divX_pos (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) : 0 < (p /ₘ X).degree := by
  have h : (p /ₘ X).natDegree = d - 1 := by rw [natDegree_divByMonic _ monic_X, natDegree_X, hp.1]
  exact natDegree_pos_iff_degree_pos.1 (by omega)

/-- tex l.165-166: `{|q| < R}` is bounded (`q = p(w)/w` has degree `d - 1 ≥ 1`), so its component `Ω` is bounded. -/
theorem rem_2_3_bounded_proved (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (R : ℝ) :
    Bornology.IsBounded {w : ℂ | ‖(p /ₘ X).eval w‖ < R} := by
  have ht := (p /ₘ X).tendsto_norm_atTop (degree_divX_pos d hd p hp) (l := comap norm atTop) (z := id)
    tendsto_comap
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_comap.1 (ht.eventually_ge_atTop R))
  refine (isBounded_closedBall (x := (0 : ℂ)) (r := max M 0)).subset fun w hw => ?_
  rw [mem_closedBall_zero_iff]
  by_contra h
  have hge := hM ‖w‖ (le_of_max_le_left (not_le.1 h).le) w rfl
  exact absurd hw (not_lt.2 hge)

/-- tex l.169-170: for `R < m(p)` every critical point `β` of `p` lies outside `{|q| < R}` (as `|q(β)| ≥ m(p)`). -/
theorem rem_2_3_crit_outside_proved (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (R : ℝ) (hR : R < mval p)
    (β : ℂ) (hβ : p.derivative.eval β = 0) : β ∉ {w : ℂ | ‖(p /ₘ X).eval w‖ < R} := by
  have h := (rem_2_3_q_proved d hd p hp).2.2 β hβ
  intro hmem
  have hlt : ‖(p /ₘ X).eval β‖ < R := hmem
  linarith

/-- tex l.166-169, with `ψ` a parameter: for `ψ(0) = 0` and `ψ'(0) = κ ≠ 0`, `W = ψ/κ` and `B = (q∘ψ)/R` have
`W(0) = 0`, `W'(0) = 1`, `B(0) = 1/R`, and `(WB)' = p'(ψ)ψ'/(κR)` wherever `ψ` is differentiable. -/
theorem rem_2_3_formulas_proved (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (ψ : ℂ → ℂ) (κ R : ℝ)
    (hκ : κ ≠ 0) (hψ0 : ψ 0 = 0) (hψ' : HasDerivAt ψ κ 0) :
    (fun z => ψ z / κ) 0 = 0 ∧ deriv (fun z => ψ z / κ) 0 = 1 ∧ (fun z => (p /ₘ X).eval (ψ z) / R) 0 = 1 / R ∧
      ∀ w : ℂ, DifferentiableAt ℂ ψ w →
        deriv (fun z => ψ z / κ * ((p /ₘ X).eval (ψ z) / R)) w = p.derivative.eval (ψ w) * deriv ψ w / (κ * R) := by
  obtain ⟨hpq, hq0, -⟩ := rem_2_3_q_proved d hd p hp
  have hκC : (κ : ℂ) ≠ 0 := ofReal_ne_zero.2 hκ
  refine ⟨by simp [hψ0], ?_, by simp [hψ0, hq0], fun w hw => ?_⟩
  · rw [(hψ'.div_const (κ : ℂ)).deriv, div_self hκC]
  · have hfun : (fun z => ψ z / κ * ((p /ₘ X).eval (ψ z) / R)) = fun z => p.eval (ψ z) / (κ * R) := by
      funext z
      conv_rhs => rw [hpq]
      rw [eval_mul, eval_X]
      ring
    rw [hfun]
    exact (((p.hasDerivAt (ψ w)).comp w hw.hasDerivAt).div_const ((κ : ℂ) * R)).deriv

end Smale
