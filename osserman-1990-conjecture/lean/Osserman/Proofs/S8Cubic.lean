/-
S8Cubic.lean — §8.2 of paper 013 (sec_small_roots.tex of the posting copy, lines 65-73): (eq:cubicidentities) for the simple
eigenfields of [Nik2006, Lemma 3.1(1)], from the unit sphere to every `x` by homogeneity (row `s8_cubic_identities`).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route: write `x = s u` with `s = |x| > 0` and `u` a unit vector. Then `E(x) = s^d E(u)` and `P(x) = q^k E(x)` with
`2k + d = 3`, so every identity at `x` is the identity at `u` times a power of `s`.
-/
import Osserman.Defs.SmallRoots
import Osserman.Proofs.Poly
import Osserman.Proofs.S8Tools

namespace Osserman.Proofs.S8Cubic

open Osserman Matrix MvPolynomial

lemma evalField_qpow (k : ℕ) (E : Fin 16 → MvPolynomial (Fin 16) ℝ) (x : Vec 16) :
    evalField (fun j => sqP 16 ^ k * E j) x = (x ⬝ᵥ x) ^ k • evalField E x := by
  funext j
  simp only [evalField, map_mul, map_pow, Osserman.Proofs.Poly.eval_sqP, Pi.smul_apply, smul_eq_mul]

lemma dot_self_nonneg (x : Vec 16) : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- The two cases of Section 8 (`d = 1`, `k = 1` and `d = 3`, `k = 0`; always `2k + d = 3`). -/
lemma cubic_core (k d : ℕ) (hkd : (k = 1 ∧ d = 1) ∨ (k = 0 ∧ d = 3)) (E : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (hE : ∀ j, (E j).IsHomogeneous d)
    (hunit : ∀ x : Vec 16, x ⬝ᵥ x = 1 → evalField E x ⬝ᵥ x = 0 ∧ evalField E x ⬝ᵥ evalField E x = 1 ∧
      evalField E (evalField E x) = -x) :
    (∀ j, (sqP 16 ^ k * E j).IsHomogeneous 3) ∧ CubicIdentities (fun j => sqP 16 ^ k * E j) := by
  have hdeg : 2 * k + d = 3 := by rcases hkd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hd0 : d ≠ 0 := by rcases hkd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  refine ⟨fun j => ?_, fun x => ?_⟩
  · have h := (Osserman.Proofs.Poly.sqP_isHomogeneous.pow k).mul (hE j)
    rwa [hdeg] at h
  simp only [evalField_qpow]
  by_cases hx : x = 0
  · subst hx
    simp [Osserman.Proofs.S8Tools.evalField_zero hE hd0]
  have hq : 0 < x ⬝ᵥ x := lt_of_le_of_ne (dot_self_nonneg x) (Ne.symm (mt dotProduct_self_eq_zero.mp hx))
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (x ⬝ᵥ x) := ⟨_, rfl⟩
  have hs : 0 < s := hsdef ▸ Real.sqrt_pos.mpr hq
  have hs2 : x ⬝ᵥ x = s ^ 2 := by rw [hsdef, Real.sq_sqrt hq.le]
  obtain ⟨u, hudef⟩ : ∃ u, u = s⁻¹ • x := ⟨_, rfl⟩
  have hxu : x = s • u := by rw [hudef, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hu : u ⬝ᵥ u = 1 := by
    rw [hudef, smul_dotProduct, dotProduct_smul, hs2, smul_eq_mul, smul_eq_mul]
    field_simp
  obtain ⟨h1, h2, h3⟩ := hunit u hu
  have hEx : evalField E x = s ^ d • evalField E u := by
    rw [hxu, Osserman.Proofs.S8Tools.evalField_smul hE]
  rw [hs2, hEx, smul_smul, Osserman.Proofs.S8Tools.evalField_smul hE ((s ^ 2) ^ k * s ^ d) (evalField E u), h3]
  conv_lhs => rw [hxu]
  conv_rhs => rw [hxu]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, h1, h2]
  rcases hkd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨by ring, by ring, ?_⟩
    module
  · refine ⟨by ring, by ring, ?_⟩
    module

/-- **§8.2** (lines 65-73), (eq:cubicidentities): the eigenfields of [Nik2006, Lemma 3.1(1)], multiplied by `q` if
linear, are homogeneous cubic and satisfy `⟨P(x),x⟩ = 0`, `|P(x)|² = q³`, `P(P(x)) = -q⁴x` at every `x`. -/
theorem s8_cubic_identities_proved (d : ℕ) (hd : d = 1 ∨ d = 3) (E : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (hE : ∀ j, (E j).IsHomogeneous d)
    (hunit : ∀ x : Vec 16, x ⬝ᵥ x = 1 → evalField E x ⬝ᵥ x = 0 ∧ evalField E x ⬝ᵥ evalField E x = 1 ∧
      evalField E (evalField E x) = -x) :
    let P : Fin 16 → MvPolynomial (Fin 16) ℝ := fun j => sqP 16 ^ ((3 - d) / 2) * E j
    (∀ j, (P j).IsHomogeneous 3) ∧ CubicIdentities P := by
  intro P
  rcases hd with rfl | rfl
  · exact cubic_core 1 1 (Or.inl ⟨rfl, rfl⟩) E hE hunit
  · exact cubic_core 0 3 (Or.inr ⟨rfl, rfl⟩) E hE hunit

end Osserman.Proofs.S8Cubic
