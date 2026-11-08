/-
Smale/Paper/Unconditional.lean — fact (R) and the main theorems of the paper, with no hypothesis left.
Route of fact (R): a common zero of P_c and P_c*, anywhere in the complex plane, would make the 17 x 17 Schur-Cohn matrix of P_c singular, so
it is enough that this matrix is invertible. For c in [0, 1] that is shown on 299 dyadic intervals that cover [0, 1]: on each one a fixed matrix
A makes A B(c) A* strictly row dominant, for every c of the interval, in exact integer arithmetic checked by the kernel (`decide +kernel`), with
the coefficients of H rounded at 2^-64 and the rounding error bounded. For c < 0 the symmetry P_(-c)(w) = P_c(-w) reduces to c > 0.
-/
import Smale.Paper.Statements
import Smale.R.Final

namespace Smale

open Polynomial

/-- Fact (R) of Lemma 4.3 for our data (tex l.332-335), proved here by a route of its own: the Schur-Cohn matrix is invertible on 299 intervals that
cover `[0, 1]`, each checked by the kernel. The computer check printed in the paper, `CheckR`, is a different route and stays as it is. -/
theorem condR_proved : CondRdata := RCheck.condR_proved

/-- Theorem 5.1 (tex l.430-434), with fact (R) proved. -/
theorem thm_5_1 :
    ((∀ a ∈ [bD, a1D, a2D], ‖a‖ < 1) ∧ [bD, a1D, a2D].Nodup ∧ ∀ a ∈ [bD, a1D, a2D], Qdata.eval a = 0) ∧
    (Qdata.derivative = (X - 1) ^ 5 * Vdata ∧ ∀ w ∈ closedDisk, Vdata.eval w ≠ 0) ∧
    (∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → resultant (dieudonne Hdata 18 c) (dieudonneStar Hdata 18 c) 17 17 ≠ 0) ∧
    (∀ w ∈ closedDisk, Hdata.derivative.eval w ≠ 0) ∧
    IsAdmissible (WOf Qdata [a1D, a2D] bD) (BOf [a1D, a2D] bD) 2 ∧
    1 / (BOf [a1D, a2D] bD 0).re ^ 2 = Jab a1D bD * Jab a2D bD ∧ Jab a1D bD * Jab a2D bD = (LambdaQ : ℝ) ∧
    ((Real.sqrt LambdaQ : ℝ) : EReal) ≤ Kstar ∧ (1.1559837 : ℝ) < Real.sqrt LambdaQ :=
  thm_5_1_of_R condR_proved

/-- Corollary 5.4 (tex l.510-512), with fact (R) proved. -/
theorem cor_5_4 : ∃ d₀ : ℕ, ∀ d ≥ d₀, ((1.1559837 : ℝ) : EReal) < Kd d := cor_5_4_of_R condR_proved

/-- Theorem 1.1 (tex l.122-129), with fact (R) proved. -/
theorem thm_1_1 :
    ((Real.sqrt LambdaQ : ℝ) : EReal) ≤ Kstar ∧
      (1.15598372919 : ℝ) ≤ Real.sqrt LambdaQ ∧ Real.sqrt LambdaQ < 1.1559837292 ∧
      ((1.1559837 : ℝ) : EReal) < Kstar ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀, ((1.1559837 : ℝ) : EReal) < Kd d :=
  thm_1_1_of_R condR_proved

/-- Remark 5.2 (tex l.467), with fact (R) proved: "The zeros of `V`, `H'` and the `P_c` lie outside `𝔻̄`". -/
theorem rem_5_2_zeros_outside_proved :
    (∀ w ∈ closedDisk, Vdata.eval w ≠ 0) ∧ (∀ w ∈ closedDisk, Hdata.derivative.eval w ≠ 0) ∧
      ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w ∈ closedDisk, (dieudonne Hdata 18 c).eval w ≠ 0 :=
  rem_5_2_zeros_outside condR_proved

end Smale
