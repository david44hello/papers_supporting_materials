/-
Smale/R/Tau.lean — Evaluation at real tau, perturbation and scaling of the Schur-Cohn matrix.
-/
import Smale.R.RowTest
import Smale.R.Gersh
import Smale.R.Link

namespace Smale.RCheck

open Polynomial Finset Smale.RK Matrix ComplexConjugate

noncomputable abbrev toC : GI →+* ℂ := GaussianInt.toComplex

theorem norm_toC_le (z : GI) : ‖toC z‖ ≤ (l1 z : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im (toC z)
  have hre : (toC z).re = (z.re : ℝ) := (GaussianInt.intCast_re z).symm
  have him : (toC z).im = (z.im : ℝ) := (GaussianInt.intCast_im z).symm
  rw [hre, him] at h
  unfold l1
  push_cast
  exact h

theorem re_toC (z : GI) : (toC z).re = (z.re : ℝ) := (GaussianInt.intCast_re z).symm

theorem l1N_castR (z : GI) : ((l1N z : ℕ) : ℝ) = (l1 z : ℝ) := by
  have := l1N_cast z
  exact_mod_cast this

theorem l1_nonnegR (z : GI) : (0 : ℝ) ≤ (l1 z : ℝ) := by
  exact_mod_cast l1_nonneg z

/-! ### Evaluating at real `tau` -/

noncomputable def psi (τ : ℝ) : GI[X] →+* ℂ := eval₂RingHom toC (τ : ℂ)

theorem psi_apply (τ : ℝ) (f : GI[X]) : psi τ f = f.eval₂ toC (τ : ℂ) := rfl

theorem psi_C (τ : ℝ) (z : GI) : psi τ (C z) = toC z := by
  simp [psi_apply]

theorem psi_sg (τ : ℝ) (f : GI[X]) : psi τ (sg f) = conj (psi τ f) := by
  simp only [psi_apply]
  have hcomp : (starRingEnd ℂ).comp toC = toC.comp (starRingEnd GI) := by
    refine RingHom.ext fun z => ?_
    exact (GaussianInt.toComplex_star z).symm
  calc (sg f).eval₂ toC (τ : ℂ) = f.eval₂ (toC.comp (starRingEnd GI)) (τ : ℂ) := by
        simp [sg, eval₂_map]
    _ = f.eval₂ ((starRingEnd ℂ).comp toC) ((starRingEnd ℂ) (τ : ℂ)) := by
        rw [hcomp, Complex.conj_ofReal]
    _ = (starRingEnd ℂ) (f.eval₂ toC (τ : ℂ)) := (hom_eval₂ f toC (starRingEnd ℂ) (τ : ℂ)).symm

theorem psi_expand (τ : ℝ) (f : GI[X]) (hf : f.natDegree < 35) :
    psi τ f = ∑ s ∈ range 35, toC (f.coeff s) * (τ : ℂ) ^ s :=
  eval₂_eq_sum_range' toC hf (τ : ℂ)

/-- The matrix `A`, over `ℂ`. -/
noncomputable def Ac (A : ℕ → ℕ → GI) : Matrix (Fin 17) (Fin 17) ℂ := Matrix.of fun j i => toC (A (j : ℕ) (i : ℕ))

section tau

variable (a D : ℤ) (h : ℕ → GI) (A : ℕ → ℕ → GI) (τ : ℝ)

theorem schurB_psi (i k : Fin 17) :
    schurB 17 (fun l => psi τ (qP a D h l)) i k = psi τ (bP a D h (i : ℕ) (k : ℕ)) := by
  rw [schurB_apply]
  unfold bP
  exact (bF_map sg 17 (qP a D h) (starRingEnd ℂ) (psi τ) (psi_sg τ) _ _).symm

theorem psi_hP (j k : ℕ) :
    ∑ i : Fin 17, toC (A j (i : ℕ)) * psi τ (bP a D h (i : ℕ) k) = psi τ (hP a D h A j k) := by
  unfold hP
  rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun i => psi τ (C (A j i) * bP a D h i k)) 17]
  refine sum_congr rfl fun i _ => ?_
  rw [map_mul, psi_C]

/-- `A M A*`, as a polynomial in `tau`, entry by entry. -/
theorem congr_entry (M : Matrix (Fin 17) (Fin 17) ℂ) (hM : ∀ i k : Fin 17, M i k = psi τ (bP a D h (i : ℕ) (k : ℕ)))
    (j t : Fin 17) :
    (Ac A * M * (Ac A)ᴴ) j t = ∑ s ∈ range 35, toC (gC a D h A s (j : ℕ) (t : ℕ)) * (τ : ℂ) ^ s := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Ac, Matrix.of_apply, hM]
  simp only [psi_hP]
  have h2 : ∀ k : Fin 17, psi τ (hP a D h A (j : ℕ) (k : ℕ)) * star (toC (A (t : ℕ) (k : ℕ))) =
      ∑ s ∈ range 35, toC (hC a D h A s (j : ℕ) (k : ℕ) * star (A (t : ℕ) (k : ℕ))) * (τ : ℂ) ^ s := by
    intro k
    have hdeg : (hP a D h A (j : ℕ) (k : ℕ)).natDegree < 35 := by
      have := hP_natDegree (a := a) (D := D) (h := h) (A := A) (j : ℕ) (k : ℕ) (by have := k.2; omega)
      omega
    rw [psi_expand τ _ hdeg, sum_mul]
    refine sum_congr rfl fun s _ => ?_
    rw [map_mul, GaussianInt.toComplex_star]
    unfold hC
    simp only [starRingEnd_apply]
    ring
  simp only [h2]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  unfold gC
  rw [map_sum, sum_mul]
  exact Fin.sum_univ_eq_sum_range
    (fun k => toC (hC a D h A s (j : ℕ) k * star (A (t : ℕ) k)) * (τ : ℂ) ^ s) 17

end tau

/-! ### Perturbation and scaling -/

theorem two_term (x y x' y' : ℂ) (e Q : ℝ) (hx : ‖x - x'‖ ≤ e) (hy : ‖y - y'‖ ≤ e) (hx' : ‖x'‖ ≤ Q) (hy' : ‖y'‖ ≤ Q) :
    ‖x * y - x' * y'‖ ≤ e * (2 * Q + e) := by
  have he : 0 ≤ e := (norm_nonneg _).trans hx
  have hQ : 0 ≤ Q := (norm_nonneg _).trans hx'
  have hsplit : x * y - x' * y' = (x - x') * y + x' * (y - y') := by ring
  have hyn : ‖y‖ ≤ e + Q := by
    have : y = (y - y') + y' := by ring
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add hy hy')
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 : ‖x - x'‖ * ‖y‖ ≤ e * (e + Q) := mul_le_mul hx hyn (norm_nonneg _) he
  have h2 : ‖x'‖ * ‖y - y'‖ ≤ Q * e := mul_le_mul hx' hy (norm_nonneg _) hQ
  nlinarith

theorem aT_perturb (p q : ℕ → ℂ) (e Q : ℝ) (hq : ∀ l, l ≤ 17 → ‖q l‖ ≤ Q) (he : ∀ l, l ≤ 17 → ‖p l - q l‖ ≤ e)
    (n m : ℕ) (hn : n ≤ 17) (hm : m ≤ 17) :
    ‖aT (starRingEnd ℂ) 17 p n m - aT (starRingEnd ℂ) 17 q n m‖ ≤ 2 * (e * (2 * Q + e)) := by
  unfold aT
  have hsplit : p n * conj (p m) - conj (p (17 - n)) * p (17 - m) - (q n * conj (q m) - conj (q (17 - n)) * q (17 - m)) =
      (p n * conj (p m) - q n * conj (q m)) - (conj (p (17 - n)) * p (17 - m) - conj (q (17 - n)) * q (17 - m)) := by
    ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  have hc : ∀ l, l ≤ 17 → ‖conj (p l) - conj (q l)‖ ≤ e := by
    intro l hl
    rw [← map_sub, Complex.norm_conj]
    exact he l hl
  have hcq : ∀ l, l ≤ 17 → ‖conj (q l)‖ ≤ Q := by
    intro l hl
    rw [Complex.norm_conj]
    exact hq l hl
  have h1 := two_term _ _ _ _ e Q (he n hn) (hc m hm) (hq n hn) (hcq m hm)
  have h2 := two_term _ _ _ _ e Q (hc (17 - n) (by omega)) (he (17 - m) (by omega)) (hcq (17 - n) (by omega))
    (hq (17 - m) (by omega))
  linarith

theorem schurB_perturb (p q : ℕ → ℂ) (e Q : ℝ) (hq : ∀ l, l ≤ 17 → ‖q l‖ ≤ Q) (he : ∀ l, l ≤ 17 → ‖p l - q l‖ ≤ e)
    (i k : Fin 17) : ‖schurB 17 p i k - schurB 17 q i k‖ ≤ 17 * (2 * (e * (2 * Q + e))) := by
  rw [schurB_apply, schurB_apply]
  unfold bF
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ range (min (i : ℕ) (k : ℕ) + 1),
      ‖aT (starRingEnd ℂ) 17 p ((i : ℕ) - n) ((k : ℕ) - n) - aT (starRingEnd ℂ) 17 q ((i : ℕ) - n) ((k : ℕ) - n)‖ ≤
        2 * (e * (2 * Q + e)) := by
    intro n _
    exact aT_perturb p q e Q hq he _ _ (by have := i.2; omega) (by have := k.2; omega)
  refine (sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [card_range, nsmul_eq_mul]
  have he0 : 0 ≤ e := (norm_nonneg _).trans (he 0 (by omega))
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hq 0 (by omega))
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have : min (i : ℕ) (k : ℕ) + 1 ≤ 17 := by have := i.2; omega
  exact_mod_cast this

theorem schurB_scale (r : ℝ) (p : ℕ → ℂ) :
    schurB 17 (fun l => (r : ℂ) * p l) = ((r : ℂ) ^ 2) • schurB 17 p := by
  ext i k
  simp only [schurB, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-! ### `V_l` at real `tau` -/

section wreal

variable (a D : ℤ)

/-- `wP` at real `tau`, in `ℂ`. -/
noncomputable def wC (τ : ℝ) (n : ℕ) : ℂ := (wP a D n).eval₂ (Int.castRingHom ℂ) (τ : ℂ)

theorem wC_step (τ : ℝ) (n : ℕ) :
    wC a D τ (n + 2) = (2 * (a : ℂ) + 2 * (τ : ℂ)) * wC a D τ (n + 1) - (D : ℂ) ^ 2 * wC a D τ n := by
  simp only [wC, wP, eval₂_sub, eval₂_mul, eval₂_add, eval₂_C, eval₂_X]
  simp only [eq_intCast]
  push_cast
  ring

theorem wC_U (_hD : (D : ℝ) ≠ 0) (τ c : ℝ) (hc : (D : ℝ) * c = a + τ) : ∀ l : ℕ,
    wC a D τ (l + 1) = (D : ℂ) ^ l * (((Chebyshev.U ℝ (l : ℤ)).eval c : ℝ) : ℂ) ∧
    wC a D τ (l + 2) = (D : ℂ) ^ (l + 1) * (((Chebyshev.U ℝ ((l + 1 : ℕ) : ℤ)).eval c : ℝ) : ℂ) := by
  have hcC : (D : ℂ) * (c : ℂ) = (a : ℂ) + (τ : ℂ) := by exact_mod_cast hc
  intro l
  induction l with
  | zero =>
    constructor
    · simp [wC, wP]
    · have h2 := wC_step a D τ 0
      have h1 : wC a D τ 1 = 1 := by simp [wC, wP]
      have h0 : wC a D τ 0 = 0 := by simp [wC, wP]
      rw [h2, h1, h0]
      simp only [Nat.zero_add, pow_one, mul_one, mul_zero, sub_zero]
      have hU1 : (Chebyshev.U ℝ ((0 + 1 : ℕ) : ℤ)).eval c = 2 * c := by simp [Chebyshev.U_one]
      rw [hU1]
      push_cast
      linear_combination (-2 : ℂ) * hcC
  | succ l ih =>
    refine ⟨ih.2, ?_⟩
    have hstep := wC_step a D τ (l + 1)
    rw [hstep, ih.2, ih.1]
    have hU : (Chebyshev.U ℝ ((l + 1 + 1 : ℕ) : ℤ)).eval c =
        2 * c * (Chebyshev.U ℝ ((l + 1 : ℕ) : ℤ)).eval c - (Chebyshev.U ℝ (l : ℤ)).eval c := by
      have := Chebyshev.U_add_two ℝ (l : ℤ)
      have hcast1 : ((l + 1 + 1 : ℕ) : ℤ) = (l : ℤ) + 2 := by push_cast; ring
      have hcast2 : ((l + 1 : ℕ) : ℤ) = (l : ℤ) + 1 := by push_cast; ring
      rw [hcast1, hcast2, this]
      simp
    rw [hU]
    generalize (Chebyshev.U ℝ ((l + 1 : ℕ) : ℤ)).eval c = u1
    generalize (Chebyshev.U ℝ (l : ℤ)).eval c = u0
    push_cast
    linear_combination (-2 : ℂ) * (D : ℂ) ^ (l + 1) * (u1 : ℂ) * hcC

end wreal

theorem psi_qP (a D : ℤ) (h : ℕ → GI) (τ : ℝ) (l : ℕ) :
    psi τ (qP a D h l) = toC (h l) * (D : ℂ) ^ (17 - l) * wC a D τ (l + 1) := by
  unfold qP wC
  rw [map_mul, psi_C, map_mul, psi_apply, eval₂_map]
  have hcast : toC.comp (Int.castRingHom GI) = Int.castRingHom ℂ := Subsingleton.elim _ _
  rw [hcast]
  congr 2
  simp [gI]

end Smale.RCheck
