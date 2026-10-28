/-
Smale/Proofs/DataCrit.lean — three exact claims of Section 5 (paper v1.80): `GL` is monic of degree 17 (tex l.350);
the 17 critical points of `Q`, counted with multiplicity, are `z = 1` (order 5), the two zeros of `G` and the ten `ρ_j`:
ten lie within `0.0123` of `1`, the other seven have moduli between `1.017` and `1.238`, none lies in the open disk
(tex l.354-356, Figure 1 caption l.378-381); `J(a₁,b) = 1.30038…`, `J(a₂,b) = 1.02761…` (tex l.357). All bounds are
exact rational checks (the zeros of `G` are located as in Smale/Proofs/DataRoots.lean).
-/
import Smale.Proofs.DataRoots

namespace Smale.Exact

open Polynomial Complex ComplexConjugate

/-! ## `GL` is monic of degree 17 -/

theorem Gpoly_monic_deg : Gpoly.Monic ∧ Gpoly.natDegree = 2 := by
  have hdeg : Gpoly.natDegree = 2 := by
    rw [Gpoly_eq]; exact natDegree_toPoly rfl (by decide +kernel)
  refine ⟨?_, hdeg⟩
  rw [Monic, leadingCoeff, hdeg, Gpoly_eq, coeff_toPoly]
  have h : gGQ.getD 2 GQ.zero = one := rfl
  rw [h, toC_one]

theorem Lpoly_monic_deg : Lpoly.Monic ∧ Lpoly.natDegree = 15 := by
  have e1 : (X - 1 : ℂ[X]) = X - C 1 := by rw [map_one]
  have h1 : (X - C (1 : ℂ)).Monic := monic_X_sub_C 1
  have hP : (∏ j : Fin 10, (X - C (rho j))).Monic := monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
  rw [Lpoly, e1]
  refine ⟨(h1.pow 5).mul hP, ?_⟩
  rw [(h1.pow 5).natDegree_mul hP, h1.natDegree_pow, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _,
    natDegree_X_sub_C]
  simp

/-- `sec5_GL_monic`, proved. -/
theorem sec5_GL_monic_proved : (Gpoly * Lpoly).Monic ∧ (Gpoly * Lpoly).natDegree = 17 := by
  obtain ⟨hG, hGd⟩ := Gpoly_monic_deg
  obtain ⟨hL, hLd⟩ := Lpoly_monic_deg
  exact ⟨hG.mul hL, by rw [hG.natDegree_mul hL, hGd, hLd]⟩

/-! ## The critical points of `Q` -/

theorem lt_norm_iff_nsq (a : GQ) {c : ℚ} (hc : 0 ≤ c) : (c : ℝ) < ‖a.toC‖ ↔ c ^ 2 < nsq a := by
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  constructor
  · intro h
    have h2 : (c : ℝ) ^ 2 < ‖a.toC‖ ^ 2 := by nlinarith [norm_nonneg a.toC]
    rw [sq_norm_toC] at h2
    exact_mod_cast h2
  · intro h
    have h2 : (c : ℝ) ^ 2 < ‖a.toC‖ ^ 2 := by rw [sq_norm_toC]; exact_mod_cast h
    nlinarith [norm_nonneg a.toC]

theorem rho_near_iff (j : Fin 10) :
    ‖rho j - 1‖ < 0.0123 ↔ nsq (GQ.add (rhoGQ.getD j GQ.zero) (GQ.neg one)) < (0.0123 : ℚ) ^ 2 := by
  rw [← norm_lt_iff_nsq _ (by norm_num : (0 : ℚ) ≤ 0.0123), GQ.toC_add, GQ.toC_neg, toC_one, ← rho_eq,
    ← sub_eq_add_neg]
  norm_num

theorem rho_far_iff (j : Fin 10) :
    (1.017 < ‖rho j‖ ∧ ‖rho j‖ < 1.238) ↔
      ((1.017 : ℚ) ^ 2 < nsq (rhoGQ.getD j GQ.zero) ∧ nsq (rhoGQ.getD j GQ.zero) < (1.238 : ℚ) ^ 2) := by
  rw [← lt_norm_iff_nsq _ (by norm_num : (0 : ℚ) ≤ 1.017), ← norm_lt_iff_nsq _ (by norm_num : (0 : ℚ) ≤ 1.238),
    ← rho_eq]
  norm_num

/-- The exact checks: `ρ₁, ρ₂, ρ₉, ρ₁₀` (indices 0, 1, 8, 9) within `0.0123` of `1`, the other `ρ_j` with moduli in
`(1.017, 1.238)`, every `|ρ_j| ≥ 1`; `rG` within `0.0123 - 10⁻³⁰` of `1`; `|rG2|` in `(1.017 + 10⁻³⁰, 1.238 - 10⁻³⁰)`. -/
theorem check_crit :
    (∀ j : Fin 10, j ∈ ({0, 1, 8, 9} : Finset (Fin 10)) →
      nsq (GQ.add (rhoGQ.getD j GQ.zero) (GQ.neg one)) < (0.0123 : ℚ) ^ 2) ∧
    (∀ j : Fin 10, j ∉ ({0, 1, 8, 9} : Finset (Fin 10)) →
      (1.017 : ℚ) ^ 2 < nsq (rhoGQ.getD j GQ.zero) ∧ nsq (rhoGQ.getD j GQ.zero) < (1.238 : ℚ) ^ 2) ∧
    (∀ j : Fin 10, (1 : ℚ) ^ 2 ≤ nsq (rhoGQ.getD j GQ.zero)) ∧
    nsq (GQ.add rG (GQ.neg one)) < ((0.0123 : ℚ) - epsG) ^ 2 ∧
    ((1.017 : ℚ) + epsG) ^ 2 < nsq rG2 ∧ nsq rG2 < ((1.238 : ℚ) - epsG) ^ 2 := by
  decide +kernel

/-- The critical points of `Q`, counted with multiplicity. -/
theorem Qderiv_roots (z₁ z₂ : ℂ) (hG : Gpoly = (X - C z₁) * (X - C z₂)) :
    Qdata.derivative.roots = 5 • {1} + {z₁, z₂} + Finset.univ.val.map rho := by
  have e1 : (X - 1 : ℂ[X]) = X - C 1 := by rw [map_one]
  have h18 : (18 : ℂ[X]) = C 18 := (map_ofNat C 18).symm
  have hP : (∏ j : Fin 10, (X - C (rho j))) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => X_sub_C_ne_zero _
  have hA : C (18 : ℂ) * (X - C 1) ^ 5 ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr (by norm_num)) (pow_ne_zero _ (X_sub_C_ne_zero _))
  have hB : (X - C z₁) * (X - C z₂) ≠ 0 := mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  rw [Qdata_derivative, hG, e1, h18, roots_mul (mul_ne_zero (mul_ne_zero hA hB) hP), roots_mul (mul_ne_zero hA hB),
    roots_mul hA, roots_mul hB, roots_C, roots_pow, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C, roots_prod _ _ hP]
  simp [Multiset.bind_singleton, Multiset.singleton_add]

/-- `sec5_crit_points`, proved. -/
theorem sec5_crit_points_proved :
    ∃ z₁ z₂ : ℂ, Gpoly = (X - C z₁) * (X - C z₂) ∧
      Qdata.derivative.roots = 5 • {1} + {z₁, z₂} + Finset.univ.val.map rho ∧
      ‖z₁ - 1‖ < 0.0123 ∧ (∀ j : Fin 10, j ∈ ({0, 1, 8, 9} : Finset (Fin 10)) → ‖rho j - 1‖ < 0.0123) ∧
      (1.017 < ‖z₂‖ ∧ ‖z₂‖ < 1.238) ∧
      (∀ j : Fin 10, j ∉ ({0, 1, 8, 9} : Finset (Fin 10)) → 1.017 < ‖rho j‖ ∧ ‖rho j‖ < 1.238) ∧
      Multiset.card Qdata.derivative.roots = 17 ∧
      Multiset.card (Qdata.derivative.roots.filter fun z => ‖z - 1‖ < 0.0123) = 10 ∧
      ∀ z ∈ Qdata.derivative.roots, 1 ≤ ‖z‖ := by
  obtain ⟨z₁, z₂, hG, h1, h2⟩ := G_roots
  obtain ⟨cnear, cfar, cone, cr1, cr2lo, cr2hi⟩ := check_crit
  have hε : (0 : ℝ) < epsG := by norm_num [epsG]
  have hz1 : ‖z₁ - 1‖ < 0.0123 := by
    have hr := (norm_lt_iff_nsq (GQ.add rG (GQ.neg one)) (by norm_num [epsG])).mpr cr1
    rw [GQ.toC_add, GQ.toC_neg, toC_one, ← sub_eq_add_neg] at hr
    push_cast at hr
    calc ‖z₁ - 1‖ = ‖(z₁ - rG.toC) + (rG.toC - 1)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖z₁ - rG.toC‖ + ‖rG.toC - 1‖ := norm_add_le _ _
      _ < 0.0123 := by linarith
  have hz2lo : (1.017 : ℝ) < ‖z₂‖ := by
    have hr := (lt_norm_iff_nsq rG2 (by norm_num [epsG] : (0 : ℚ) ≤ 1.017 + epsG)).mpr cr2lo
    push_cast at hr
    have := norm_sub_norm_le rG2.toC z₂
    rw [norm_sub_rev] at this
    linarith
  have hz2hi : ‖z₂‖ < 1.238 := by
    have hr := (norm_lt_iff_nsq rG2 (by norm_num [epsG] : (0 : ℚ) ≤ 1.238 - epsG)).mpr cr2hi
    push_cast at hr
    have := norm_sub_norm_le z₂ rG2.toC
    linarith
  have hz1one : 1 ≤ ‖z₁‖ := by
    have hr := le_norm_of_nsq (by norm_num [epsG]) check_moduli.2.2.1
    push_cast at hr
    have := norm_sub_norm_le rG.toC z₁
    rw [norm_sub_rev] at this
    linarith
  have hnear : ∀ j : Fin 10, j ∈ ({0, 1, 8, 9} : Finset (Fin 10)) → ‖rho j - 1‖ < 0.0123 :=
    fun j hj => (rho_near_iff j).mpr (cnear j hj)
  have hfar : ∀ j : Fin 10, j ∉ ({0, 1, 8, 9} : Finset (Fin 10)) → 1.017 < ‖rho j‖ ∧ ‖rho j‖ < 1.238 :=
    fun j hj => (rho_far_iff j).mpr (cfar j hj)
  have hrho1 : ∀ j : Fin 10, 1 ≤ ‖rho j‖ := fun j => by
    have hr := le_norm_of_nsq (by norm_num) (cone j)
    push_cast at hr
    rw [rho_eq]; exact hr
  have hroots := Qderiv_roots z₁ z₂ hG
  refine ⟨z₁, z₂, hG, hroots, hz1, hnear, ⟨hz2lo, hz2hi⟩, hfar, ?_, ?_, ?_⟩
  · rw [hroots]; simp
  · have h0 : (0 : ℝ) < 0.0123 := by norm_num
    have hp2 : ¬ ‖z₂ - 1‖ < 0.0123 := by
      have := norm_sub_norm_le z₂ 1
      rw [norm_one] at this
      exact not_lt.mpr (by linarith)
    have hc : Multiset.card ((Finset.univ.val.map rho).filter fun z => ‖z - 1‖ < 0.0123) = 4 := by
      rw [Multiset.filter_map, Multiset.card_map, ← rho_near_one_card]; rfl
    rw [hroots, Multiset.filter_add, Multiset.filter_add, Multiset.card_add, Multiset.card_add, hc]
    simp [Multiset.filter_nsmul, Multiset.filter_singleton, h0, hz1, hp2]
  · intro z hz
    rw [hroots] at hz
    simp only [Multiset.mem_add, Multiset.mem_nsmul, Multiset.mem_singleton, Multiset.insert_eq_cons,
      Multiset.mem_cons, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hz
    rcases hz with ((⟨-, rfl⟩ | rfl | rfl) | ⟨j, rfl⟩)
    · simp
    · exact hz1one
    · linarith
    · exact hrho1 j

/-! ## The two factors of `Λ` -/

/-- `sec5_J_values`, proved. -/
theorem sec5_J_values_proved :
    1.30038 ≤ Jab a1D bD ∧ Jab a1D bD < 1.30039 ∧ 1.02761 ≤ Jab a2D bD ∧ Jab a2D bD < 1.02762 := by
  have h : (1.30038 : ℚ) ≤ jabQ a1GQ bGQ ∧ jabQ a1GQ bGQ < 1.30039 ∧ (1.02761 : ℚ) ≤ jabQ a2GQ bGQ ∧
      jabQ a2GQ bGQ < 1.02762 := by decide +kernel
  obtain ⟨c1, c2, c3, c4⟩ := h
  have q1 : ((1.30038 : ℚ) : ℝ) ≤ ((jabQ a1GQ bGQ : ℚ) : ℝ) := by exact_mod_cast c1
  have q2 : ((jabQ a1GQ bGQ : ℚ) : ℝ) < ((1.30039 : ℚ) : ℝ) := by exact_mod_cast c2
  have q3 : ((1.02761 : ℚ) : ℝ) ≤ ((jabQ a2GQ bGQ : ℚ) : ℝ) := by exact_mod_cast c3
  have q4 : ((jabQ a2GQ bGQ : ℚ) : ℝ) < ((1.02762 : ℚ) : ℝ) := by exact_mod_cast c4
  push_cast at q1 q2 q3 q4
  rw [a1D_eq, a2D_eq, bD_eq, Jab_toC, Jab_toC]
  exact ⟨q1, q2, q3, q4⟩

end Smale.Exact
