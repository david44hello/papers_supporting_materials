/-
Osserman/Proofs/S83Ends.lean — §8.3 and §8.4 of paper 013: the endpoints with an eigenvalue of multiplicity nine, the
endpoint `(8,7)`, and the bound `ν ≤ 7` at the intermediate patterns and the §8.4 endpoints (rows s8_prop21_uses,
s8_3_endpoint_87, s8_3_intermediate_nu, s8_4_endpoints_nu; statements copied verbatim from
Osserman/Paper/Statements8.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof. (1) A pattern with a multiplicity `9` is Osserman (`hasPattern_osserman`), so [Nik2006, Proposition 2.1] gives a
Cliff(6) form. (2) At `(8,7)`, Theorem A (`thm_C`) leaves the Clifford forms and the Cayley form; the field `Jx` in the
multiplicity-8 eigenspace excludes the Cayley form (Theorem E, `thm_E_no_cayley`). (3) For a Clifford form with every
`η_α ≠ 0`, the base value `l0` has multiplicity `15 - ν` (`Rem72d.clifford_multiplicity`), and `ν ≤ 8` (Hurwitz-Radon).
If `ν = 8` this multiplicity is `7`; but in a pattern without a `7` every multiplicity is a pattern entry or `0`.
-/
import Osserman.Defs.SmallRoots
import Osserman.Proofs.CorD
import Osserman.Proofs.Rem72dCounts
import Osserman.Proofs.HurwitzRadon
import Osserman.Proofs.ThmC
import Osserman.Proofs.Sec5c
import Osserman.Proofs.ThmECayley
import Osserman.Cited.Nik2006

namespace Osserman.Proofs.S83

open Osserman Matrix

/-! ### Multiplicity nine: [Nik2006, Proposition 2.1] -/

lemma clifford_of_nine {k : ℕ} (R : CurvTensor 16) (m : Fin k → ℕ) (hsum : ∑ i, m i + 1 = 16) (i₀ : Fin k)
    (h9 : m i₀ = 9) (h : HasPattern R m) : R.IsClifford := by
  obtain ⟨hO, -⟩ := CorD.hasPattern_osserman_proved R m hsum h
  obtain ⟨ev, -, hm⟩ := h
  obtain ⟨J, hJ, l0, η, hjac⟩ :=
    Osserman.Cited.nik2006_prop_2_1 R hO ⟨ev i₀, fun x hx => (hm x hx i₀).trans h9⟩
  exact ⟨6, J, hJ, l0, η, hjac⟩

/-- Row `s8_prop21_uses`. -/
theorem s8_prop21_uses_proved (R : CurvTensor 16)
    (h : HasPattern R ![9, 6] ∨ HasPattern R ![9, 5, 1] ∨ HasPattern R ![9, 4, 2] ∨ HasPattern R ![9, 4, 1, 1]) :
    R.IsClifford := by
  rcases h with h | h | h | h
  · exact clifford_of_nine R _ (by simp [Fin.sum_univ_succ]) 0 rfl h
  · exact clifford_of_nine R _ (by simp [Fin.sum_univ_succ]) 0 rfl h
  · exact clifford_of_nine R _ (by simp [Fin.sum_univ_succ]) 0 rfl h
  · exact clifford_of_nine R _ (by simp [Fin.sum_univ_succ]) 0 rfl h

/-! ### The endpoint `(8,7)` -/

lemma ne_zero_of_orth {J : Matrix (Fin 16) (Fin 16) ℝ} (hJo : Jᵀ * J = 1) : J ≠ 0 := by
  intro h0
  rw [h0, transpose_zero, zero_mul] at hJo
  exact zero_ne_one hJo

/-- Row `s8_3_endpoint_87`. -/
theorem s8_3_endpoint_87_proved (Rt : CurvTensor 16) (lam : ℝ) (hpat : PatternEv Rt ![8, 7] ![0, lam])
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (hfield : ∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x ∈ Module.End.eigenspace (Rt.jacobiMap x) 0) :
    Rt.IsClifford := by
  obtain ⟨hinj, hm⟩ := hpat
  have hne : (0 : ℝ) ≠ lam := by
    intro h
    have := hinj (a₁ := 0) (a₂ := 1) (by simp [h])
    exact absurd this (by decide)
  have h8 (x : Vec 16) (hx : x ⬝ᵥ x = 1) : Rt.redMult x 0 = 8 := by simpa using hm x hx 0
  have h7 (x : Vec 16) (hx : x ⬝ᵥ x = 1) : Rt.redMult x lam = 7 := by simpa using hm x hx 1
  obtain ⟨μ, κ, -, -, A, -, hcases⟩ :=
    ThmC.thm_C_of_prop_5_2 Sec5c.prop_5_2_proved Rt ⟨0, lam, hne, fun x hx => ⟨h8 x hx, h7 x hx⟩⟩
  rcases hcases with ⟨-, hC⟩ | ⟨-, hC⟩ | ⟨-, T, hT, hop⟩
  · exact hC
  · exact hC
  · exact absurd ⟨μ - κ / 3, κ / 3, T, hT, hop⟩
      (ThmECayley.thm_E_no_cayley_proved Rt lam 0 hne.symm 7 8 (Or.inl ⟨rfl, rfl⟩)
        (fun x hx => ⟨h7 x hx, h8 x hx⟩) J hJs (ne_zero_of_orth hJo) hfield)

/-! ### `ν ≤ 7` in patterns without a multiplicity seven -/

lemma nu_le_7_of_pattern {k : ℕ} (R' : CurvTensor 16) (m : Fin k → ℕ) (hsum : ∑ i, m i + 1 = 16)
    (h7 : ∀ i, m i ≠ 7) (hpat : HasPattern R' m) {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : IsCliffordStr Jα) (l0 : ℝ) (η : Fin ν → ℝ) (hη : ∀ α, η α ≠ 0)
    (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, η α • jfam (Jα α) x) : ν ≤ 7 := by
  classical
  obtain ⟨ev, hev, hm⟩ := hpat
  let x : Vec 16 := Pi.single 0 1
  have hx : x ⬝ᵥ x = 1 := by simp [x, dotProduct, Pi.single_apply]
  have formula := Rem72d.clifford_multiplicity R' Jα hJ l0 η hjac x hx l0
  have empty : Fintype.card {a : Fin ν // l0 + η a = l0} = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun a => hη a.1 (by linarith [a.2])⟩
  simp only [empty, ite_true, zero_add] at formula
  have upper := HurwitzRadon.rem_7_2_nu_le_8_proved Jα hJ
  by_contra hgt
  by_cases hin : ∃ i, l0 = ev i
  · obtain ⟨i, rfl⟩ := hin
    have := hm x hx i
    have := h7 i
    omega
  · have := CorD.redMult_other R' hev hsum hx (hm x hx) (fun i h => hin ⟨i, h⟩)
    omega

/-- Row `s8_3_intermediate_nu`. -/
theorem s8_3_intermediate_nu_proved (R' : CurvTensor 16) (hpat : HasPattern R' ![8, 6, 1] ∨ HasPattern R' ![9, 5, 1])
    {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr Jα) (l0 : ℝ) (η : Fin ν → ℝ)
    (hη : ∀ α, η α ≠ 0) (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, η α • jfam (Jα α) x) : ν ≤ 7 := by
  rcases hpat with h | h
  · exact nu_le_7_of_pattern R' _ (by simp [Fin.sum_univ_succ]) (by decide) h Jα hJ l0 η hη hjac
  · exact nu_le_7_of_pattern R' _ (by simp [Fin.sum_univ_succ]) (by decide) h Jα hJ l0 η hη hjac

end Osserman.Proofs.S83

namespace Osserman.Proofs.S84

open Osserman Matrix

/-- Row `s8_4_endpoints_nu`. -/
theorem s8_4_endpoints_nu_proved (R' : CurvTensor 16)
    (hpat : HasPattern R' ![8, 5, 2] ∨ HasPattern R' ![8, 5, 1, 1] ∨ HasPattern R' ![9, 4, 2] ∨
      HasPattern R' ![9, 4, 1, 1])
    {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr Jα) (l0 : ℝ) (η : Fin ν → ℝ)
    (hη : ∀ α, η α ≠ 0) (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, η α • jfam (Jα α) x) : ν ≤ 7 := by
  rcases hpat with h | h | h | h
  · exact S83.nu_le_7_of_pattern R' _ (by simp [Fin.sum_univ_succ]) (by decide) h Jα hJ l0 η hη hjac
  · exact S83.nu_le_7_of_pattern R' _ (by simp [Fin.sum_univ_succ]) (by decide) h Jα hJ l0 η hη hjac
  · exact S83.nu_le_7_of_pattern R' _ (by simp [Fin.sum_univ_succ]) (by decide) h Jα hJ l0 η hη hjac
  · exact S83.nu_le_7_of_pattern R' _ (by simp [Fin.sum_univ_succ]) (by decide) h Jα hJ l0 η hη hjac

end Osserman.Proofs.S84
