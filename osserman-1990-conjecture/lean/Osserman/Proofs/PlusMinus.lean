/-
Osserman/Proofs/PlusMinus.lean — proof of `sec3_plus_or_minus` of paper 013 (§3 l. 473-482): F is the FKM quartic of
8 matrices (ε = 1, m = 7) or minus the FKM quartic of 9 matrices (ε = -1, m = 8), read off at z = (x, y).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

METHOD. Lemma 2.1 gives the hypotheses of the cited (A); (A) gives m, P, U, ε with F(z) = ε F_P(Uz). Absorbing U
(`sec3_absorb_U_proved`) gives F = ε F_{P'}; `sec3_eps_m_proved` gives (ε, m) = (1, 7) or (-1, 8). Evaluating at
z = Fin.append x y (`sec2_F_eval_proved`, `eval_quadP`) gives s² - 8b = ε (s² - 2∑⟨P'_iz,z⟩²), which is linear in
b and ∑⟨P'_iz,z⟩².
-/
import Osserman.Proofs.Lem21
import Osserman.Cited.Isoparametric

namespace Osserman.Proofs.PlusMinus

open Osserman Osserman.Cited Matrix MvPolynomial

/-- `F(x,y) = s² - 8b` against `ε F_P(x,y) = ε (s² - 2∑⟨P_iz,z⟩²)` at `z = (x, y)`. -/
lemma eval_split {k : ℕ} (R : CurvTensor 16) (μ κ ε : ℝ) (P : Fin k → Matrix (Fin 32) (Fin 32) ℝ)
    (hF : ∀ z, eval z (quarticP R μ κ) = ε * eval z (FKMP P)) (x y : Vec 16) :
    ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 - 8 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) =
      ε * (((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
        2 * ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) := by
  have h := hF (Fin.append x y)
  rw [Osserman.Proofs.Sec2.sec2_F_eval_proved] at h
  simpa only [FKMP, map_sub, map_mul, map_pow, map_sum, map_ofNat, Osserman.Proofs.Sec2.eval_sqP_append,
    Osserman.Proofs.Poly.eval_quadP] using h

theorem sec3_plus_or_minus_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    (∃ P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ, IsSymmCliffordSystem P ∧ ∀ x y : Vec 16,
        4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) ∨
      ∃ P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ, IsSymmCliffordSystem P ∧ ∀ x y : Vec 16,
        4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
          ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2 := by
  obtain ⟨hgrad, hlap, ⟨z, hz, hz1⟩, ⟨w, hw, hw1⟩⟩ := Osserman.Proofs.Lem21.lem_2_1_proved R μ κ h
  have hnc : ∃ z w : Vec 32, z ⬝ᵥ z = 1 ∧ w ⬝ᵥ w = 1 ∧ eval z (quarticP R μ κ) ≠ eval w (quarticP R μ κ) :=
    ⟨z, w, hz, hw, by rw [hz1, hw1]; norm_num⟩
  obtain ⟨m, P, hm, hP, U, hU, ε, hε, hF⟩ :=
    isoparametric_quartic_R32 _ (Osserman.Proofs.Sec2.sec2_F_homogeneous_proved R μ κ) hgrad hlap hnc
  obtain ⟨hP', hPU⟩ := Osserman.Proofs.Poly.sec3_absorb_U_proved P hP U hU
  generalize (fun i => Uᵀ * P i * U) = P' at hP' hPU
  have hF' : ∀ z, eval z (quarticP R μ κ) = ε * eval z (FKMP P') := fun z => by rw [hF, hPU]
  rcases Osserman.Proofs.Sec2.sec3_eps_m_proved m hm P' hP' ε hε _ hlap hF' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    refine ⟨P', hP', fun x y => ?_⟩
    have h1 : 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) =
        ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P' i *ᵥ (Fin.append x y : Vec 32))) ^ 2 := by
      have := eval_split R μ κ 1 P' hF' x y
      linarith
    exact h1
  · right
    refine ⟨P', hP', fun x y => ?_⟩
    have h1 : 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
        ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P' i *ᵥ (Fin.append x y : Vec 32))) ^ 2 := by
      have := eval_split R μ κ (-1) P' hF' x y
      linarith
    exact h1

end Osserman.Proofs.PlusMinus
