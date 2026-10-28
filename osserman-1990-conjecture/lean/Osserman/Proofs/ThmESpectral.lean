/-
ThmESpectral.lean — three-eigenspace decompositions for Theorem E, paper 013, lines 740–766.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.ThreeRoot
import Osserman.Proofs.Spectral

namespace Osserman.Proofs.ThmESpectral

open Osserman Matrix Osserman.Proofs.Spectral

lemma eig_dot_zero (R : CurvTensor 16) (x : Vec 16) (ℓ μ : ℝ) (hne : ℓ ≠ μ)
    (y z : Vec 16) (hy : y ∈ Esp R x ℓ) (hz : z ∈ Esp R x μ) : y ⬝ᵥ z = 0 := by
  have equal := jacobi_dot R x y z
  rw [(mem_Esp.mp hy).1, (mem_Esp.mp hz).1, smul_dotProduct, smul_dotProduct,
    dotProduct_comm z y, smul_eq_mul, smul_eq_mul] at equal
  have product : (ℓ - μ) * (y ⬝ᵥ z) = 0 := by nlinarith
  exact (mul_eq_zero.mp product).resolve_left (sub_ne_zero.mpr hne)

lemma three_dimensions (R : CurvTensor 16) (m : Fin 3 → ℕ) (hm : IsThmEPattern m)
    (ev : Fin 3 → ℝ) (hev : Function.Injective ev)
    (x : Vec 16) (hx : x ⬝ᵥ x = 1) (hpat : ∀ i, R.redMult x (ev i) = m i) :
    Esp R x (ev 1) ⊔ Esp R x (ev 2) ≤ perp x ∧
      Module.finrank ℝ ↥(Esp R x (ev 1) ⊔ Esp R x (ev 2)) = m 1 + m 2 ∧
      Esp R x (ev 0) ⊔ (Esp R x (ev 1) ⊔ Esp R x (ev 2)) = perp x := by
  have ne01 : ev 0 ≠ ev 1 := hev.ne (by decide)
  have ne02 : ev 0 ≠ ev 2 := hev.ne (by decide)
  have ne12 : ev 1 ≠ ev 2 := hev.ne (by decide)
  have disjoint012 : Esp R x (ev 0) ⊓ (Esp R x (ev 1) ⊔ Esp R x (ev 2)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro y hy
    obtain ⟨u, hu, v, hv, sum⟩ := Submodule.mem_sup.mp hy.2
    have first := eig_dot_zero R x _ _ ne01 y u hy.1 hu
    have second := eig_dot_zero R x _ _ ne02 y v hy.1 hv
    have zero : y ⬝ᵥ y = 0 := by
      calc
        y ⬝ᵥ y = y ⬝ᵥ (u + v) := congrArg (fun z => y ⬝ᵥ z) sum.symm
        _ = 0 := by rw [dotProduct_add, first, second, add_zero]
    exact dotProduct_self_eq_zero.mp zero
  have sumdim := Submodule.finrank_sup_add_finrank_inf_eq (Esp R x (ev 1)) (Esp R x (ev 2))
  rw [Esp_inf R x ne12, finrank_bot, add_zero] at sumdim
  have d0 : Module.finrank ℝ ↥(Esp R x (ev 0)) = m 0 := hpat 0
  have d1 : Module.finrank ℝ ↥(Esp R x (ev 1)) = m 1 := hpat 1
  have d2 : Module.finrank ℝ ↥(Esp R x (ev 2)) = m 2 := hpat 2
  have dim12 : Module.finrank ℝ ↥(Esp R x (ev 1) ⊔ Esp R x (ev 2)) = m 1 + m 2 := by omega
  have dim012 := Submodule.finrank_sup_add_finrank_inf_eq (Esp R x (ev 0))
    (Esp R x (ev 1) ⊔ Esp R x (ev 2))
  rw [disjoint012, finrank_bot, add_zero] at dim012
  have total : m 0 + m 1 + m 2 = 15 := by rcases hm with rfl | rfl | rfl | rfl <;> norm_num
  have perpdim := finrank_perp hx
  have inclusion : Esp R x (ev 0) ⊔ (Esp R x (ev 1) ⊔ Esp R x (ev 2)) ≤ perp x :=
    sup_le inf_le_right (sup_le inf_le_right inf_le_right)
  refine ⟨sup_le inf_le_right inf_le_right, dim12, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq inclusion
  omega

lemma three_decomp (R : CurvTensor 16) (m : Fin 3 → ℕ) (hm : IsThmEPattern m)
    (ev : Fin 3 → ℝ) (hev : Function.Injective ev)
    (x : Vec 16) (hx : x ⬝ᵥ x = 1) (hpat : ∀ i, R.redMult x (ev i) = m i)
    (y : Vec 16) (hy : y ∈ perp x) :
    ∃ y0 ∈ Esp R x (ev 0), ∃ y1 ∈ Esp R x (ev 1), ∃ y2 ∈ Esp R x (ev 2), y = y0 + y1 + y2 := by
  have span := (three_dimensions R m hm ev hev x hx hpat).2.2
  rw [← span, Submodule.mem_sup] at hy
  obtain ⟨y0, h0, rest, hr, sum⟩ := hy
  obtain ⟨y1, h1, y2, h2, sum2⟩ := Submodule.mem_sup.mp hr
  exact ⟨y0, h0, y1, h1, y2, h2, by rw [← sum, ← sum2, add_assoc]⟩

lemma pattern_osserman (R : CurvTensor 16) (m : Fin 3 → ℕ) (hm : IsThmEPattern m)
    (ev : Fin 3 → ℝ) (hev : Function.Injective ev)
    (hpat : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i, R.redMult x (ev i) = m i) : R.IsOsserman := by
  have other_zero (x : Vec 16) (hx : x ⬝ᵥ x = 1) (μ : ℝ) (hμ : ∀ i, μ ≠ ev i) : R.redMult x μ = 0 := by
    change Module.finrank ℝ ↥(Esp R x μ) = 0
    rw [Submodule.finrank_eq_zero, eq_bot_iff]
    intro y hy
    obtain ⟨y0, h0, y1, h1, y2, h2, sum⟩ := three_decomp R m hm ev hev x hx (hpat x hx) y hy.2
    have first := eig_dot_zero R x _ _ (hμ 0) y y0 hy h0
    have second := eig_dot_zero R x _ _ (hμ 1) y y1 hy h1
    have third := eig_dot_zero R x _ _ (hμ 2) y y2 hy h2
    apply dotProduct_self_eq_zero.mp
    calc
      y ⬝ᵥ y = y ⬝ᵥ (y0 + y1 + y2) := congrArg (fun z => y ⬝ᵥ z) sum
      _ = 0 := by rw [dotProduct_add, dotProduct_add, first, second, third]; ring
  intro x y hx hy μ
  by_cases zero : μ = ev 0
  · rw [zero, hpat x hx 0, hpat y hy 0]
  by_cases one : μ = ev 1
  · rw [one, hpat x hx 1, hpat y hy 1]
  by_cases two : μ = ev 2
  · rw [two, hpat x hx 2, hpat y hy 2]
  have different (i : Fin 3) : μ ≠ ev i := by fin_cases i <;> assumption
  rw [other_zero x hx μ different, other_zero y hy μ different]

end Osserman.Proofs.ThmESpectral

