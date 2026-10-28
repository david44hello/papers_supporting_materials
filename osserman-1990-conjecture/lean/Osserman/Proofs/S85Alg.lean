/-
S85Alg.lean — §8.5 of paper 013 (sec_small_roots.tex of the posting copy, lines 252-294): the algebra rows `s8_5_char_eq`,
`s8_5_choose_z`, `s8_5_theta`, `s8_5_nik2005_arith` and the endpoint table `s8_5_endpoint_table`, cell by cell.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.SmallRoots

namespace Osserman.Proofs.S85

open Osserman Matrix

/-- **§8.5** (lines 265-268): "the characteristic equation of the block is $(\mu_1-z)(\mu_2-z)-C(d-z)=0$". -/
theorem s8_5_char_eq_proved (mu1 mu2 c1 c2 Cc z : ℝ) (hc : c1 ^ 2 + c2 ^ 2 = 1) :
    (!![mu1, 0; 0, mu2] - Cc • vecMulVec ![c1, c2] ![c1, c2] - z • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det =
      (mu1 - z) * (mu2 - z) - Cc * ((mu1 * c2 ^ 2 + mu2 * c1 ^ 2) - z) := by
  have entries : !![mu1, 0; 0, mu2] - Cc • vecMulVec ![c1, c2] ![c1, c2] - z • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      !![mu1 - Cc * (c1 * c1) - z, -(Cc * (c1 * c2)); -(Cc * (c2 * c1)), mu2 - Cc * (c2 * c2) - z] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vecHead, vecTail]
  rw [entries, Matrix.det_fin_two_of]
  linear_combination (Cc * z) * hc

/-- **§8.5** (lines 268-270): "Choose $z\in\{0,\lambda\}$ with $d\ne z$ (possible since $\lambda\ne0$) and
$C=(\mu_1-z)(\mu_2-z)/(d-z)$, which is nonzero". -/
theorem s8_5_choose_z_proved (lam mu1 mu2 d : ℝ) (hlam : lam ≠ 0) (h1 : mu1 ≠ 0 ∧ mu1 ≠ lam)
    (h2 : mu2 ≠ 0 ∧ mu2 ≠ lam) :
    ∃ z : ℝ, (z = 0 ∨ z = lam) ∧ d ≠ z ∧ (mu1 - z) * (mu2 - z) / (d - z) ≠ 0 := by
  by_cases hd : d = 0
  · refine ⟨lam, Or.inr rfl, by rw [hd]; exact hlam.symm, ?_⟩
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr h1.2) (sub_ne_zero.mpr h2.2))
      (sub_ne_zero.mpr (by rw [hd]; exact hlam.symm))
  · refine ⟨0, Or.inl rfl, hd, ?_⟩
    simpa using div_ne_zero (mul_ne_zero h1.1 h2.1) hd

/-- **§8.5** (lines 270-271): "The other eigenvalue is $\theta=\mu_1+\mu_2-C-z$". -/
theorem s8_5_theta_proved (mu1 mu2 d z : ℝ) (hdz : d ≠ z) :
    let Cc := (mu1 - z) * (mu2 - z) / (d - z)
    let θ := mu1 + mu2 - Cc - z
    ∀ t : ℝ, (mu1 - t) * (mu2 - t) - Cc * (d - t) = (t - z) * (t - θ) := by
  dsimp only
  intro t
  have key : (mu1 - z) * (mu2 - z) / (d - z) * (d - z) = (mu1 - z) * (mu2 - z) :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hdz)
  linear_combination (-1 : ℝ) * key

/-- **§8.5** (lines 289-291): "$m=10$ and $\nu=5$ satisfy $16\ge3\nu$ and $16>(\nu+1)^2/4$". -/
theorem s8_5_nik2005_arith_proved :
    (16 - 1 - 10 : ℕ) = 5 ∧ (16 : ℝ) ≥ 3 * ((5 : ℕ) : ℝ) ∧ (16 : ℝ) > (((5 : ℕ) : ℝ) + 1) ^ 2 / 4 := by
  norm_num

lemma inj3 {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Function.Injective ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

lemma inj4 {a b c d : ℝ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective ![a, b, c, d] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- **§8.5** (lines 275-287): the table of endpoints, cell by cell (`θ` new / `θ = μ₃` / `θ` other large / `θ = z`). -/
theorem s8_5_endpoint_table_proved (R' : CurvTensor 16) (M N : ℕ) (lam mu3 z θ : ℝ)
    (hdist : 0 ≠ lam ∧ 0 ≠ mu3 ∧ lam ≠ mu3) (_hz : z = 0 ∨ z = lam)
    (hmult : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ ν : ℝ, R'.redMult x ν =
      (if ν = 0 then M else 0) + (if ν = lam then N else 0) + (if ν = mu3 then 1 else 0) +
        (if ν = z then 1 else 0) + (if ν = θ then 1 else 0)) :
    (M = 7 ∧ N = 5 ∧ z = 0 →
        (θ ≠ 0 → θ ≠ lam → θ ≠ mu3 → HasPattern R' ![8, 5, 1, 1]) ∧
          (θ = mu3 → HasPattern R' ![8, 5, 2]) ∧
          (θ = lam → HasPattern R' ![8, 6, 1]) ∧
          (θ = 0 → HasPattern R' ![9, 5, 1])) ∧
      (M = 7 ∧ N = 5 ∧ z = lam →
        (θ ≠ 0 → θ ≠ lam → θ ≠ mu3 → HasPattern R' ![7, 6, 1, 1]) ∧
          (θ = mu3 → HasPattern R' ![7, 6, 2]) ∧
          (θ = 0 → HasPattern R' ![8, 6, 1]) ∧
          (θ = lam → HasPattern R' ![7, 7, 1])) ∧
      (M = 8 ∧ N = 4 ∧ z = 0 →
        (θ ≠ 0 → θ ≠ lam → θ ≠ mu3 → HasPattern R' ![9, 4, 1, 1]) ∧
          (θ = mu3 → HasPattern R' ![9, 4, 2]) ∧
          (θ = lam → HasPattern R' ![9, 5, 1]) ∧
          (θ = 0 → HasPattern R' ![10, 4, 1])) ∧
      (M = 8 ∧ N = 4 ∧ z = lam →
        (θ ≠ 0 → θ ≠ lam → θ ≠ mu3 → HasPattern R' ![8, 5, 1, 1]) ∧
          (θ = mu3 → HasPattern R' ![8, 5, 2]) ∧
          (θ = 0 → HasPattern R' ![9, 5, 1]) ∧
          (θ = lam → HasPattern R' ![8, 6, 1])) := by
  obtain ⟨h0l, h0m, hlm⟩ := hdist
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 hl hm
      exact ⟨![0, lam, mu3, θ], inj4 h0l h0m (Ne.symm h0) hlm (Ne.symm hl) (Ne.symm hm),
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm, h0, hl, hm, Ne.symm h0, Ne.symm hl, Ne.symm hm]⟩
    · intro hθ
      subst θ
      exact ⟨![0, lam, mu3], inj3 h0l h0m hlm,
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm]⟩
    · intro hθ
      subst θ
      exact ⟨![0, lam, mu3], inj3 h0l h0m hlm,
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm]⟩
    · intro hθ
      subst θ
      exact ⟨![0, lam, mu3], inj3 h0l h0m hlm,
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm]⟩
  · rintro ⟨rfl, rfl, hzl⟩
    subst z
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 hl hm
      exact ⟨![0, lam, mu3, θ], inj4 h0l h0m (Ne.symm h0) hlm (Ne.symm hl) (Ne.symm hm),
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm, h0, hl, hm, Ne.symm h0, Ne.symm hl, Ne.symm hm]⟩
    · intro hθ
      subst θ
      exact ⟨![0, lam, mu3], inj3 h0l h0m hlm,
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm]⟩
    · intro hθ
      subst θ
      exact ⟨![0, lam, mu3], inj3 h0l h0m hlm,
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm]⟩
    · intro hθ
      subst θ
      exact ⟨![0, lam, mu3], inj3 h0l h0m hlm,
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm]⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 hl hm
      exact ⟨![0, lam, mu3, θ], inj4 h0l h0m (Ne.symm h0) hlm (Ne.symm hl) (Ne.symm hm),
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm, h0, hl, hm, Ne.symm h0, Ne.symm hl, Ne.symm hm]⟩
    · intro hθ
      subst θ
      exact ⟨![0, lam, mu3], inj3 h0l h0m hlm,
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm]⟩
    · intro hθ
      subst θ
      exact ⟨![0, lam, mu3], inj3 h0l h0m hlm,
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm]⟩
    · intro hθ
      subst θ
      exact ⟨![0, lam, mu3], inj3 h0l h0m hlm,
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm]⟩
  · rintro ⟨rfl, rfl, hzl⟩
    subst z
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 hl hm
      exact ⟨![0, lam, mu3, θ], inj4 h0l h0m (Ne.symm h0) hlm (Ne.symm hl) (Ne.symm hm),
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm, h0, hl, hm, Ne.symm h0, Ne.symm hl, Ne.symm hm]⟩
    · intro hθ
      subst θ
      exact ⟨![0, lam, mu3], inj3 h0l h0m hlm,
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm]⟩
    · intro hθ
      subst θ
      exact ⟨![0, lam, mu3], inj3 h0l h0m hlm,
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm]⟩
    · intro hθ
      subst θ
      exact ⟨![0, lam, mu3], inj3 h0l h0m hlm,
        fun x hx i => by rw [hmult x hx]; fin_cases i <;> simp [h0l, h0m, hlm, h0l.symm, h0m.symm, hlm.symm]⟩

end Osserman.Proofs.S85
