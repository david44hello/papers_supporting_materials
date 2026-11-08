/-
Smale/R/Interval.lean — A passing check gives an invertible Schur-Cohn matrix on its whole interval, for the exact data.
-/
import Smale.R.Tau

namespace Smale.RCheck

open Polynomial Finset Smale.RK Matrix ComplexConjugate

noncomputable def colR (A : ℕ → ℕ → GI) (k' : ℕ) : ℝ := ∑ t ∈ range 17, (l1 (A t k') : ℝ)
noncomputable def rowR (A : ℕ → ℕ → GI) (j : ℕ) : ℝ := ∑ i ∈ range 17, (l1 (A j i) : ℝ)

theorem colR_nonneg (A : ℕ → ℕ → GI) (k' : ℕ) : 0 ≤ colR A k' := sum_nonneg fun _ _ => l1_nonnegR _
theorem rowR_nonneg (A : ℕ → ℕ → GI) (j : ℕ) : 0 ≤ rowR A j := sum_nonneg fun _ _ => l1_nonnegR _

/-- The rounding term of the test covers `A E A*`. -/
theorem sum_norm_AEA (A : ℕ → ℕ → GI) (E : Matrix (Fin 17) (Fin 17) ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hE : ∀ i k, ‖E i k‖ ≤ η) (j : Fin 17) :
    ∑ t : Fin 17, ‖(Ac A * E * (Ac A)ᴴ) j t‖ ≤ η * rowR A (j : ℕ) * ∑ k' ∈ range 17, colR A k' := by
  have hentry : ∀ t : Fin 17, ‖(Ac A * E * (Ac A)ᴴ) j t‖ ≤
      η * rowR A (j : ℕ) * ∑ k' ∈ range 17, (l1 (A (t : ℕ) k') : ℝ) := by
    intro t
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Ac, Matrix.of_apply]
    refine (norm_sum_le _ _).trans ?_
    have hk : ∀ k : Fin 17, ‖(∑ i : Fin 17, toC (A (j : ℕ) (i : ℕ)) * E i k) * star (toC (A (t : ℕ) (k : ℕ)))‖ ≤
        (η * rowR A (j : ℕ)) * (l1 (A (t : ℕ) (k : ℕ)) : ℝ) := by
      intro k
      rw [norm_mul, norm_star]
      refine mul_le_mul ?_ (norm_toC_le _) (norm_nonneg _) (mul_nonneg hη (rowR_nonneg _ _))
      refine (norm_sum_le _ _).trans ?_
      unfold rowR
      rw [mul_sum, ← Fin.sum_univ_eq_sum_range (fun i => η * (l1 (A (j : ℕ) i) : ℝ)) 17]
      refine sum_le_sum fun i _ => ?_
      rw [norm_mul, mul_comm η]
      exact mul_le_mul (norm_toC_le _) (hE i k) (norm_nonneg _) (l1_nonnegR _)
    refine (sum_le_sum fun k _ => hk k).trans (le_of_eq ?_)
    rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun k' => (l1 (A (t : ℕ) k') : ℝ)) 17]
  refine (sum_le_sum fun t _ => hentry t).trans (le_of_eq ?_)
  rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun t => ∑ k' ∈ range 17, (l1 (A t k') : ℝ)) 17, sum_comm]
  rfl

/-- The tail of the test covers the high orders of `G`. -/
theorem sum_norm_G_tail (a D : ℤ) (h : ℕ → GI) (A : ℕ → ℕ → GI) (s j : ℕ) :
    ∑ t ∈ range 17, ‖toC (gC a D h A s j t)‖ ≤ ∑ k' ∈ range 17, (l1 (hC a D h A s j k') : ℝ) * colR A k' := by
  have hentry : ∀ t ∈ range 17, ‖toC (gC a D h A s j t)‖ ≤
      ∑ k' ∈ range 17, (l1 (hC a D h A s j k') : ℝ) * (l1 (A t k') : ℝ) := by
    intro t _
    refine (norm_toC_le _).trans ?_
    have hint : l1 (gC a D h A s j t) ≤ ∑ k' ∈ range 17, l1 (hC a D h A s j k') * l1 (A t k') := by
      unfold gC
      refine (l1_sum_le _ _).trans (sum_le_sum fun k' _ => ?_)
      refine (l1_mul_le _ _).trans ?_
      rw [l1_star]
    exact_mod_cast hint
  refine (sum_le_sum hentry).trans (le_of_eq ?_)
  rw [sum_comm]
  refine sum_congr rfl fun k' _ => ?_
  unfold colR
  rw [mul_sum]

section final

variable {hb : List GS} {a k : ℕ} {amat : List (List GS)}

theorem colZ_cast (k' : ℕ) : ((colZ amat k' : ℕ) : ℝ) = colR (aE amat) k' := by
  unfold colZ colR
  push_cast
  exact sum_congr rfl fun t _ => l1N_castR _

theorem rowZ_cast (j : ℕ) : ((rowZ amat j : ℕ) : ℝ) = rowR (aE amat) j := by
  unfold rowZ rowR
  push_cast
  exact sum_congr rfl fun t _ => l1N_castR _

/-- The bound on the rest of the row. -/
theorem rest_bound (τ : ℝ) (hτ : |τ| ≤ 1) (E : Matrix (Fin 17) (Fin 17) ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hE : ∀ i k, ‖E i k‖ ≤ η) (X : Matrix (Fin 17) (Fin 17) ℂ)
    (hX : ∀ j t : Fin 17, X j t = ∑ s ∈ range 35, toC (gCI hb a k amat s (j : ℕ) (t : ℕ)) * (τ : ℂ) ^ s +
      (Ac (aE amat) * E * (Ac (aE amat))ᴴ) j t) (j : Fin 17) :
    ∑ t : Fin 17, ‖X j t - toC (gCI hb a k amat 0 (j : ℕ) (t : ℕ))‖ ≤
      ((∑ s ∈ range 5, ∑ t ∈ range 17, l1N (gCI hb a k amat (s + 1) (j : ℕ) t) : ℕ) : ℝ) +
      ((∑ s ∈ range 29, ∑ k' ∈ range 17, l1N (hCI hb a k amat (6 + s) (j : ℕ) k') * colZ amat k' : ℕ) : ℝ) +
      η * rowR (aE amat) (j : ℕ) * ∑ k' ∈ range 17, colR (aE amat) k' := by
  have hpow : ∀ s : ℕ, ‖(τ : ℂ) ^ s‖ ≤ 1 := by
    intro s
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_one₀ (abs_nonneg _) hτ
  have hentry : ∀ t : Fin 17, ‖X j t - toC (gCI hb a k amat 0 (j : ℕ) (t : ℕ))‖ ≤
      ∑ s ∈ range 34, ‖toC (gCI hb a k amat (s + 1) (j : ℕ) (t : ℕ))‖ +
        ‖(Ac (aE amat) * E * (Ac (aE amat))ᴴ) j t‖ := by
    intro t
    rw [hX, sum_range_succ' _ 34]
    have hrw : ∑ s ∈ range 34, toC (gCI hb a k amat (s + 1) (j : ℕ) (t : ℕ)) * (τ : ℂ) ^ (s + 1) +
          toC (gCI hb a k amat 0 (j : ℕ) (t : ℕ)) * (τ : ℂ) ^ 0 + (Ac (aE amat) * E * (Ac (aE amat))ᴴ) j t -
          toC (gCI hb a k amat 0 (j : ℕ) (t : ℕ)) =
        ∑ s ∈ range 34, toC (gCI hb a k amat (s + 1) (j : ℕ) (t : ℕ)) * (τ : ℂ) ^ (s + 1) +
          (Ac (aE amat) * E * (Ac (aE amat))ᴴ) j t := by
      rw [pow_zero, mul_one]
      ring
    rw [hrw]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sum_le _ _).trans (sum_le_sum fun s _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hpow _)
  refine (sum_le_sum fun t _ => hentry t).trans ?_
  rw [sum_add_distrib]
  refine add_le_add ?_ (sum_norm_AEA (aE amat) E η hη hE j)
  -- the orders of `tau`, split at 5
  have hswap : ∑ t : Fin 17, ∑ s ∈ range 34, ‖toC (gCI hb a k amat (s + 1) (j : ℕ) (t : ℕ))‖ =
      ∑ s ∈ range 34, ∑ t ∈ range 17, ‖toC (gCI hb a k amat (s + 1) (j : ℕ) t)‖ := by
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    exact Fin.sum_univ_eq_sum_range (fun t => ‖toC (gCI hb a k amat (s + 1) (j : ℕ) t)‖) 17
  rw [hswap, show (34 : ℕ) = 5 + 29 from rfl, sum_range_add]
  refine add_le_add ?_ ?_
  · push_cast
    refine sum_le_sum fun s _ => sum_le_sum fun t _ => ?_
    rw [l1N_castR]
    exact norm_toC_le _
  · push_cast
    refine sum_le_sum fun s _ => ?_
    have hidx : 5 + s + 1 = 6 + s := by omega
    rw [hidx]
    refine (sum_norm_G_tail _ _ _ _ _ _).trans (le_of_eq ?_)
    refine sum_congr rfl fun k' _ => ?_
    rw [l1N_castR, colZ_cast]

/-- **One interval.** -/
theorem interval_det_ne (hc : checkInterval hb a k 6 amat = true)
    (hh : ∀ l, l ≤ 17 → l1 (hE hb l) ≤ 2 ^ 75)
    (hround : ∀ l, l ≤ 17 → ‖(2 ^ 64 : ℂ) * Hdata.coeff (l + 1) - toC (hE hb l)‖ ≤ 2)
    (c : ℝ) (hc01 : c ∈ Set.Icc (-1 : ℝ) 1) (hc1 : (a : ℝ) - 1 ≤ 2 ^ k * c) (hc2 : (2 : ℝ) ^ k * c ≤ a + 1) :
    (schurB 17 (pData c)).det ≠ 0 := by
  obtain ⟨hG, hrows⟩ := check_good hc hh
  have hR0 : (0 : ℝ) < 2 ^ k := by positivity
  set R : ℝ := 2 ^ k with hR
  set τ : ℝ := R * c - a with hτdef
  have hτ : |τ| ≤ 1 := by
    rw [abs_le]
    constructor <;> rw [hτdef] <;> linarith
  have hDcast : ((dW k : ℤ) : ℝ) = R := by
    unfold dW
    rw [hR]
    push_cast
    rfl
  have hDC : ((dW k : ℤ) : ℂ) = (R : ℂ) := by
    have : ((dW k : ℤ) : ℂ) = (((dW k : ℤ) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, hDcast]
  have hcτ : ((dW k : ℤ) : ℝ) * c = ((a : ℤ) : ℝ) + τ := by
    rw [hDcast, hτdef]
    push_cast
    ring
  have hwC := wC_U (a : ℤ) (dW k) (by rw [hDcast]; exact hR0.ne') τ c hcτ
  -- the rounded and the exact coefficients
  let q : ℕ → ℂ := fun l => psi τ (qP (a : ℤ) (dW k) (hE hb) l)
  let r : ℝ := 2 ^ 64 * R ^ 17
  let p : ℕ → ℂ := fun l => (r : ℂ) * pData c l
  have hU : ∀ l : ℕ, l ≤ 17 → ‖(((Chebyshev.U ℝ (l : ℤ)).eval c : ℝ) : ℂ)‖ ≤ 18 := by
    intro l hl
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_U_le l c hc01
    have h2 : (l : ℝ) ≤ 17 := by exact_mod_cast hl
    linarith
  have hqeq : ∀ l : ℕ, l ≤ 17 → q l = toC (hE hb l) * (R : ℂ) ^ 17 * (((Chebyshev.U ℝ (l : ℤ)).eval c : ℝ) : ℂ) := by
    intro l hl
    simp only [q]
    rw [psi_qP, (hwC l).1, hDC]
    have hpow : (R : ℂ) ^ 17 = (R : ℂ) ^ (17 - l) * (R : ℂ) ^ l := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    ring
  have hR17 : ‖(R : ℂ) ^ 17‖ = R ^ 17 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
  have hRp : (0 : ℝ) ≤ R ^ 17 := by positivity
  have hq : ∀ l : ℕ, l ≤ 17 → ‖q l‖ ≤ 2 ^ 75 * 18 * R ^ 17 := by
    intro l hl
    rw [hqeq l hl, norm_mul, norm_mul, hR17]
    have h1 : ‖toC (hE hb l)‖ ≤ 2 ^ 75 := by
      refine (norm_toC_le _).trans ?_
      exact_mod_cast hh l hl
    calc ‖toC (hE hb l)‖ * R ^ 17 * ‖(((Chebyshev.U ℝ (l : ℤ)).eval c : ℝ) : ℂ)‖
        ≤ 2 ^ 75 * R ^ 17 * 18 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right h1 hRp) (hU l hl) (norm_nonneg _) (by positivity)
      _ = 2 ^ 75 * 18 * R ^ 17 := by ring
  have he : ∀ l : ℕ, l ≤ 17 → ‖p l - q l‖ ≤ 36 * R ^ 17 := by
    intro l hl
    have hdiff : p l - q l = ((2 ^ 64 : ℂ) * Hdata.coeff (l + 1) - toC (hE hb l)) * (R : ℂ) ^ 17 *
        (((Chebyshev.U ℝ (l : ℤ)).eval c : ℝ) : ℂ) := by
      rw [hqeq l hl]
      simp only [p, r, pData]
      push_cast
      ring
    rw [hdiff, norm_mul, norm_mul, hR17]
    calc ‖(2 ^ 64 : ℂ) * Hdata.coeff (l + 1) - toC (hE hb l)‖ * R ^ 17 * ‖(((Chebyshev.U ℝ (l : ℤ)).eval c : ℝ) : ℂ)‖
        ≤ 2 * R ^ 17 * 18 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (hround l hl) hRp) (hU l hl) (norm_nonneg _) (by positivity)
      _ = 36 * R ^ 17 := by ring
  -- the matrices
  let M : Matrix (Fin 17) (Fin 17) ℂ := schurB 17 q
  let N : Matrix (Fin 17) (Fin 17) ℂ := schurB 17 p
  let E : Matrix (Fin 17) (Fin 17) ℂ := N - M
  let η : ℝ := 2 ^ 93 * R ^ 34
  have hη : 0 ≤ η := by positivity
  have hEb : ∀ i k', ‖E i k'‖ ≤ η := by
    intro i k'
    have h1 := schurB_perturb p q (36 * R ^ 17) (2 ^ 75 * 18 * R ^ 17) hq he i k'
    have h2 : (17 : ℝ) * (2 * (36 * R ^ 17 * (2 * (2 ^ 75 * 18 * R ^ 17) + 36 * R ^ 17))) ≤ η := by
      have hsq : R ^ 34 = R ^ 17 * R ^ 17 := by rw [← pow_add]
      simp only [η]
      rw [hsq]
      have hnn : (0 : ℝ) ≤ R ^ 17 * R ^ 17 := by positivity
      nlinarith
    exact h1.trans h2
  have hNsplit : N = M + E := by
    simp only [E]
    abel
  let G0 : Matrix (Fin 17) (Fin 17) ℂ := Matrix.of fun j t => toC (gCI hb a k amat 0 (j : ℕ) (t : ℕ))
  let X : Matrix (Fin 17) (Fin 17) ℂ := Ac (aE amat) * N * (Ac (aE amat))ᴴ
  have hX : ∀ j t : Fin 17, X j t = ∑ s ∈ range 35, toC (gCI hb a k amat s (j : ℕ) (t : ℕ)) * (τ : ℂ) ^ s +
      (Ac (aE amat) * E * (Ac (aE amat))ᴴ) j t := by
    intro j t
    change (Ac (aE amat) * N * (Ac (aE amat))ᴴ) j t = _
    rw [hNsplit, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    congr 1
    exact congr_entry (a : ℤ) (dW k) (hE hb) (aE amat) τ M
      (fun i k' => schurB_psi (a : ℤ) (dW k) (hE hb) τ i k') j t
  have hdom : ∀ j, ∑ t ∈ univ.erase j, ‖G0 j t‖ + ∑ t, ‖(X - G0) j t‖ < (G0 j j).re := by
    intro j
    have hrow := hG.row_ineq (j : ℕ) j.2 (hrows (j : ℕ) j.2)
    have hrowR : (((∑ t ∈ range 17, (if t = (j : ℕ) then 0 else l1N (gCI hb a k amat 0 (j : ℕ) t))) : ℕ) : ℝ) +
        ((∑ s ∈ range 5, ∑ t ∈ range 17, l1N (gCI hb a k amat (s + 1) (j : ℕ) t) : ℕ) : ℝ) +
        ((∑ s ∈ range 29, ∑ k' ∈ range 17, l1N (hCI hb a k amat (6 + s) (j : ℕ) k') * colZ amat k' : ℕ) : ℝ) +
        ((((∑ k' ∈ range 17, colZ amat k') * (2 ^ 93 * (2 ^ k) ^ 34) * rowZ amat (j : ℕ) : ℕ)) : ℝ) + 1 ≤
        ((gCI hb a k amat 0 (j : ℕ) (j : ℕ)).re : ℝ) := by
      exact_mod_cast hrow
    have heta : ((((∑ k' ∈ range 17, colZ amat k') * (2 ^ 93 * (2 ^ k) ^ 34) * rowZ amat (j : ℕ) : ℕ)) : ℝ) =
        η * rowR (aE amat) (j : ℕ) * ∑ k' ∈ range 17, colR (aE amat) k' := by
      push_cast
      rw [rowZ_cast]
      simp only [colZ_cast, η, hR]
      rw [← pow_mul]
      ring
    have hfirst : ∑ t ∈ univ.erase j, ‖G0 j t‖ ≤
        (((∑ t ∈ range 17, (if t = (j : ℕ) then 0 else l1N (gCI hb a k amat 0 (j : ℕ) t))) : ℕ) : ℝ) := by
      rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range
        (fun t => (((if t = (j : ℕ) then 0 else l1N (gCI hb a k amat 0 (j : ℕ) t)) : ℕ) : ℝ)) 17]
      rw [← sum_erase_add _ _ (mem_univ j)]
      have hzero : (((if ((j : ℕ) = (j : ℕ)) then 0 else l1N (gCI hb a k amat 0 (j : ℕ) (j : ℕ))) : ℕ) : ℝ) = 0 := by simp
      rw [hzero, add_zero]
      refine sum_le_sum fun t ht => ?_
      have htj : (t : ℕ) ≠ (j : ℕ) := fun h => (mem_erase.1 ht).1 (Fin.ext h)
      rw [ite_eq_right htj, l1N_castR]
      exact norm_toC_le _
    have hrest := rest_bound (hb := hb) (a := a) (k := k) (amat := amat) τ hτ E η hη hEb X hX j
    have hG0 : (G0 j j).re = ((gCI hb a k amat 0 (j : ℕ) (j : ℕ)).re : ℝ) := re_toC _
    have hsum : ∑ t, ‖(X - G0) j t‖ = ∑ t : Fin 17, ‖X j t - toC (gCI hb a k amat 0 (j : ℕ) (t : ℕ))‖ := rfl
    rw [hG0, hsum]
    linarith
  have hfin := dominant_of_perturbation G0 (X - G0) hdom
  have hG0X : G0 + (X - G0) = X := by abel
  rw [hG0X] at hfin
  have hNdet : N.det ≠ 0 := det_ne_zero_of_congr_dominant (Ac (aE amat)) N hfin
  intro h0
  apply hNdet
  have hscale : N = ((r : ℂ) ^ 2) • schurB 17 (pData c) := schurB_scale r (pData c)
  rw [hscale, Matrix.det_smul, h0, mul_zero]

end final

end Smale.RCheck
