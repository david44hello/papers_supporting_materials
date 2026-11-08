/-
Smale/R/Poly.lean — The exact polynomials in tau behind the packed numbers, and a priori bounds on their coefficients.
-/
import Smale.R.Schur
import Smale.R.CheckerSpec

namespace Smale.RCheck

open Polynomial Finset Smale.RK

abbrev GI := GaussianInt

/-! ### Definitions -/

section defs

variable (a D : ℤ) (h : ℕ → GI) (A : ℕ → ℕ → GI)

/-- `wP (l + 1) = V_l`, `wP 0 = 0`. -/
noncomputable def wP : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => (C (2 * a) + C 2 * X) * wP (n + 1) - C (D ^ 2) * wP n

/-- `q_l(tau) = hbar_(l+1) D^(17-l) V_l(tau)`. -/
noncomputable def qP (l : ℕ) : GI[X] :=
  C (h l * gI (D ^ (17 - l))) * (wP a D (l + 1)).map (Int.castRingHom GI)

/-- Conjugation of the coefficients. -/
noncomputable def sg : GI[X] →+* GI[X] := Polynomial.mapRingHom (starRingEnd GI)

noncomputable def bP (j k : ℕ) : GI[X] := bF sg 17 (qP a D h) j k

noncomputable def hP (j k : ℕ) : GI[X] := ∑ i ∈ range 17, C (A j i) * bP a D h i k

/-- `(A B_s)_jk`. -/
noncomputable def hC (s j k : ℕ) : GI := (hP a D h A j k).coeff s

/-- `(A B_s A*)_jt`. -/
noncomputable def gC (s j t : ℕ) : GI := ∑ k ∈ range 17, hC a D h A s j k * star (A t k)

end defs

/-! ### The `ℓ¹` size of a Gaussian integer -/

def l1 (z : GI) : ℤ := |z.re| + |z.im|

theorem l1_nonneg (z : GI) : 0 ≤ l1 z := by
  unfold l1
  positivity

theorem abs_re_le_l1 (z : GI) : |z.re| ≤ l1 z := by
  unfold l1
  linarith [abs_nonneg z.im]

theorem abs_im_le_l1 (z : GI) : |z.im| ≤ l1 z := by
  unfold l1
  linarith [abs_nonneg z.re]

theorem l1_zero : l1 0 = 0 := by
  simp [l1]

theorem l1_add_le (z v : GI) : l1 (z + v) ≤ l1 z + l1 v := by
  unfold l1
  rw [Zsqrtd.re_add, Zsqrtd.im_add]
  linarith [abs_add_le z.re v.re, abs_add_le z.im v.im]

theorem l1_sub_le (z v : GI) : l1 (z - v) ≤ l1 z + l1 v := by
  unfold l1
  have h1 : (z - v).re = z.re - v.re := by
    rw [sub_eq_add_neg, Zsqrtd.re_add, Zsqrtd.re_neg]
    ring
  have h2 : (z - v).im = z.im - v.im := by
    rw [sub_eq_add_neg, Zsqrtd.im_add, Zsqrtd.im_neg]
    ring
  rw [h1, h2]
  linarith [abs_sub z.re v.re, abs_sub z.im v.im]

theorem l1_mul_le (z v : GI) : l1 (z * v) ≤ l1 z * l1 v := by
  unfold l1
  rw [Zsqrtd.re_mul, Zsqrtd.im_mul]
  have h1 : |z.re * v.re + (-1 : ℤ) * z.im * v.im| ≤ |z.re| * |v.re| + |z.im| * |v.im| := by
    calc |z.re * v.re + (-1 : ℤ) * z.im * v.im| ≤ |z.re * v.re| + |(-1 : ℤ) * z.im * v.im| := abs_add_le _ _
      _ = |z.re| * |v.re| + |z.im| * |v.im| := by simp [abs_mul]
  have h2 : |z.re * v.im + z.im * v.re| ≤ |z.re| * |v.im| + |z.im| * |v.re| := by
    calc |z.re * v.im + z.im * v.re| ≤ |z.re * v.im| + |z.im * v.re| := abs_add_le _ _
      _ = |z.re| * |v.im| + |z.im| * |v.re| := by simp [abs_mul]
  nlinarith [h1, h2]

theorem l1_star (z : GI) : l1 (star z) = l1 z := by
  simp [l1, Zsqrtd.re_star, Zsqrtd.im_star]

theorem l1_gI (n : ℤ) : l1 (gI n) = |n| := by
  simp [l1, gI]

theorem l1_sum_le {ι : Type*} (S : Finset ι) (f : ι → GI) : l1 (∑ i ∈ S, f i) ≤ ∑ i ∈ S, l1 (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [l1_zero]
  | insert x S hx ih =>
    rw [sum_insert hx, sum_insert hx]
    linarith [l1_add_le (f x) (∑ i ∈ S, f i)]

/-- Coefficients of a product. -/
theorem l1_coeff_mul (f g : GI[X]) (Mf Mg : ℤ) (hf : ∀ s, l1 (f.coeff s) ≤ Mf) (hg : ∀ s, l1 (g.coeff s) ≤ Mg)
    (s : ℕ) : l1 ((f * g).coeff s) ≤ (s + 1) * (Mf * Mg) := by
  have hMf : 0 ≤ Mf := (l1_nonneg _).trans (hf 0)
  have hMg : 0 ≤ Mg := (l1_nonneg _).trans (hg 0)
  rw [coeff_mul]
  refine (l1_sum_le _ _).trans ?_
  have hterm : ∀ x ∈ antidiagonal s, l1 (f.coeff x.1 * g.coeff x.2) ≤ Mf * Mg := by
    intro x _
    refine (l1_mul_le _ _).trans ?_
    exact mul_le_mul (hf _) (hg _) (l1_nonneg _) hMf
  have hsum := sum_le_card_nsmul _ _ _ hterm
  rw [Finset.Nat.card_antidiagonal] at hsum
  simpa [nsmul_eq_mul] using hsum

/-! ### Bounds on `V_l` -/

section bounds

variable {a D : ℤ}

theorem wP_coeff_bound (ha : 0 ≤ a) (hD : a + 1 ≤ D) : ∀ (n s : ℕ),
    |(wP a D (n + 1)).coeff s| ≤ (3 * D) ^ n ∧ |(wP a D n).coeff s| * (3 * D) ≤ (3 * D) ^ n := by
  have hD0 : 0 ≤ D := by linarith
  intro n
  induction n with
  | zero =>
    intro s
    constructor
    · simp only [wP, coeff_one, pow_zero]
      split_ifs <;> simp
    · simp [wP]
  | succ n ih =>
    intro s
    set B : ℤ := (3 * D) ^ n with hB
    have hB0 : 0 ≤ B := by positivity
    have hpow : (3 * D) ^ (n + 1) = B * (3 * D) := by rw [hB, pow_succ]
    refine ⟨?_, ?_⟩
    · have hf1 := (ih s).1
      have hg := (ih s).2
      have hprev : ∀ t : ℕ, |((X : ℤ[X]) * wP a D (n + 1)).coeff t| ≤ B := by
        intro t
        cases t with
        | zero => simp [hB0]
        | succ t =>
          rw [coeff_X_mul]
          exact (ih t).1
      have hcoeff : (wP a D (n + 1 + 1)).coeff s =
          2 * a * (wP a D (n + 1)).coeff s + 2 * ((X : ℤ[X]) * wP a D (n + 1)).coeff s - D ^ 2 * (wP a D n).coeff s := by
        have hexp : wP a D (n + 1 + 1) = C (2 * a) * wP a D (n + 1) + C 2 * ((X : ℤ[X]) * wP a D (n + 1)) -
            C (D ^ 2) * wP a D n := by
          rw [wP]
          ring
        rw [hexp, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul]
      rw [hcoeff, hpow]
      have h1 : |2 * a * (wP a D (n + 1)).coeff s + 2 * ((X : ℤ[X]) * wP a D (n + 1)).coeff s -
          D ^ 2 * (wP a D n).coeff s| ≤
          2 * a * |(wP a D (n + 1)).coeff s| + 2 * |((X : ℤ[X]) * wP a D (n + 1)).coeff s| +
            D ^ 2 * |(wP a D n).coeff s| := by
        have e1 : |2 * a * (wP a D (n + 1)).coeff s| = 2 * a * |(wP a D (n + 1)).coeff s| := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℤ) ≤ 2 * a)]
        have e2 : |2 * ((X : ℤ[X]) * wP a D (n + 1)).coeff s| = 2 * |((X : ℤ[X]) * wP a D (n + 1)).coeff s| := by
          rw [abs_mul]
          norm_num
        have e3 : |D ^ 2 * (wP a D n).coeff s| = D ^ 2 * |(wP a D n).coeff s| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ D ^ 2)]
        calc _ ≤ |2 * a * (wP a D (n + 1)).coeff s + 2 * ((X : ℤ[X]) * wP a D (n + 1)).coeff s| +
              |D ^ 2 * (wP a D n).coeff s| := abs_sub _ _
          _ ≤ |2 * a * (wP a D (n + 1)).coeff s| + |2 * ((X : ℤ[X]) * wP a D (n + 1)).coeff s| +
              |D ^ 2 * (wP a D n).coeff s| := by gcongr; exact abs_add_le _ _
          _ = _ := by rw [e1, e2, e3]
      have h2 : a * |(wP a D (n + 1)).coeff s| ≤ a * B := mul_le_mul_of_nonneg_left hf1 ha
      have h3 := hprev s
      have h4 : (a + 1) * B ≤ D * B := mul_le_mul_of_nonneg_right hD hB0
      have h5 : D * (|(wP a D n).coeff s| * (3 * D)) ≤ D * B := mul_le_mul_of_nonneg_left hg hD0
      nlinarith [h1, h2, h3, h4, h5, mul_nonneg hD0 hB0]
    · rw [hpow]
      exact mul_le_mul_of_nonneg_right (ih s).1 (by linarith)

theorem wP_natDegree : ∀ n : ℕ, (wP a D (n + 1)).natDegree ≤ n ∧ (wP a D n).natDegree ≤ n := by
  intro n
  induction n with
  | zero => simp [wP]
  | succ n ih =>
    have h1 : (wP a D (n + 1 + 1)).natDegree ≤ n + 1 := by
      rw [wP]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine natDegree_mul_le.trans ?_
        have hlin : (C (2 * a) + C 2 * X : ℤ[X]).natDegree ≤ 1 := by compute_degree
        have := ih.1
        omega
      · refine natDegree_mul_le.trans ?_
        have := ih.2
        simp only [natDegree_C]
        omega
    exact ⟨h1, ih.1.trans (Nat.le_succ n)⟩

end bounds

section qbounds

variable {a D : ℤ} {h : ℕ → GI}

theorem qP_natDegree (l : ℕ) : (qP a D h l).natDegree ≤ l := by
  unfold qP
  refine natDegree_C_mul_le _ _ |>.trans ?_
  exact natDegree_map_le.trans (wP_natDegree l).1

/-- The bound on the coefficients of `q_l`. -/
noncomputable def pB (D : ℤ) : ℤ := 2 ^ 75 * 3 ^ 17 * D ^ 17

theorem qP_coeff_bound (ha : 0 ≤ a) (hD : a + 1 ≤ D) (hh : ∀ l, l ≤ 17 → l1 (h l) ≤ 2 ^ 75) (l s : ℕ) (hl : l ≤ 17) :
    l1 ((qP a D h l).coeff s) ≤ pB D := by
  have hD0 : 0 ≤ D := by linarith
  have hD1 : 1 ≤ D := by linarith
  unfold qP pB
  rw [coeff_C_mul, coeff_map]
  have hw := (wP_coeff_bound ha hD l s).1
  have hstep : l1 (h l * gI (D ^ (17 - l)) * ((Int.castRingHom GI) ((wP a D (l + 1)).coeff s))) ≤
      l1 (h l) * |D ^ (17 - l)| * |(wP a D (l + 1)).coeff s| := by
    refine (l1_mul_le _ _).trans ?_
    have e : l1 ((Int.castRingHom GI) ((wP a D (l + 1)).coeff s)) = |(wP a D (l + 1)).coeff s| := by
      simpa [gI] using l1_gI ((wP a D (l + 1)).coeff s)
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    refine (l1_mul_le _ _).trans ?_
    rw [l1_gI]
  refine hstep.trans ?_
  have hDp : |D ^ (17 - l)| = D ^ (17 - l) := abs_of_nonneg (by positivity)
  rw [hDp]
  have h3 : (3 * D) ^ l * D ^ (17 - l) = 3 ^ l * D ^ 17 := by
    rw [mul_pow, mul_assoc, ← pow_add]
    congr 3
    omega
  have h4 : (3 : ℤ) ^ l ≤ 3 ^ 17 := pow_le_pow_right₀ (by norm_num) hl
  have hDl : (0 : ℤ) ≤ D ^ (17 - l) := by positivity
  calc l1 (h l) * D ^ (17 - l) * |(wP a D (l + 1)).coeff s|
      ≤ 2 ^ 75 * D ^ (17 - l) * (3 * D) ^ l := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (hh l hl) hDl) hw (abs_nonneg _) (by positivity)
    _ = 2 ^ 75 * (3 ^ l * D ^ 17) := by rw [← h3]; ring
    _ ≤ 2 ^ 75 * (3 ^ 17 * D ^ 17) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = 2 ^ 75 * 3 ^ 17 * D ^ 17 := by ring

theorem sg_coeff (f : GI[X]) (s : ℕ) : (sg f).coeff s = star (f.coeff s) := by
  simp [sg, coeff_map, starRingEnd_apply]

/-- The bound on the coefficients of `B_jk`, up to `tau^34`. -/
noncomputable def bB (D : ℤ) : ℤ := 18 * (2 * (35 * (pB D * pB D)))

theorem pB_nonneg (hD : 0 ≤ D) : 0 ≤ pB D := by
  unfold pB
  positivity

theorem bP_coeff_bound (ha : 0 ≤ a) (hD : a + 1 ≤ D) (hh : ∀ l, l ≤ 17 → l1 (h l) ≤ 2 ^ 75) (j k s : ℕ)
    (hj : j ≤ 17) (hk : k ≤ 17) (hs : s ≤ 34) : l1 ((bP a D h j k).coeff s) ≤ bB D := by
  have hD0 : 0 ≤ D := by linarith
  have hq : ∀ l, l ≤ 17 → ∀ s, l1 ((qP a D h l).coeff s) ≤ pB D := fun l hl s => qP_coeff_bound ha hD hh l s hl
  have hqs : ∀ l, l ≤ 17 → ∀ s, l1 ((sg (qP a D h l)).coeff s) ≤ pB D := by
    intro l hl s
    rw [sg_coeff, l1_star]
    exact hq l hl s
  have hP2 : 0 ≤ pB D * pB D := mul_nonneg (pB_nonneg hD0) (pB_nonneg hD0)
  have hs35 : ((s : ℤ) + 1) ≤ 35 := by
    have : (s : ℤ) ≤ 34 := by exact_mod_cast hs
    linarith
  have hprod : ∀ f g : GI[X], (∀ s, l1 (f.coeff s) ≤ pB D) → (∀ s, l1 (g.coeff s) ≤ pB D) →
      l1 ((f * g).coeff s) ≤ 35 * (pB D * pB D) := by
    intro f g hf hg
    refine (l1_coeff_mul f g _ _ hf hg s).trans ?_
    exact mul_le_mul_of_nonneg_right hs35 hP2
  unfold bP bF
  rw [finsetSum_coeff]
  refine (l1_sum_le _ _).trans ?_
  have hterm : ∀ i ∈ range (min j k + 1),
      l1 ((aT sg 17 (qP a D h) (j - i) (k - i)).coeff s) ≤ 2 * (35 * (pB D * pB D)) := by
    intro i _
    unfold aT
    rw [coeff_sub]
    refine (l1_sub_le _ _).trans ?_
    have h1 := hprod _ _ (hq (j - i) (by omega)) (hqs (k - i) (by omega))
    have h2 := hprod _ _ (hqs (17 - (j - i)) (by omega)) (hq (17 - (k - i)) (by omega))
    linarith
  have hsum := sum_le_card_nsmul _ _ _ hterm
  rw [card_range, nsmul_eq_mul] at hsum
  refine hsum.trans ?_
  unfold bB
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have : min j k + 1 ≤ 18 := by omega
  exact_mod_cast this

theorem bP_natDegree (j k : ℕ) (hj : j ≤ 17) (hk : k ≤ 17) : (bP a D h j k).natDegree ≤ 34 := by
  unfold bP bF
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  unfold aT
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    have h1 := qP_natDegree (a := a) (D := D) (h := h) (j - i)
    have h2 : (sg (qP a D h (k - i))).natDegree ≤ k - i :=
      natDegree_map_le.trans (qP_natDegree (k - i))
    omega
  · refine natDegree_mul_le.trans ?_
    have h1 : (sg (qP a D h (17 - (j - i)))).natDegree ≤ 17 - (j - i) :=
      natDegree_map_le.trans (qP_natDegree _)
    have h2 := qP_natDegree (a := a) (D := D) (h := h) (17 - (k - i))
    omega

variable {A : ℕ → ℕ → GI}

theorem hP_natDegree (j k : ℕ) (hk : k ≤ 17) : (hP a D h A j k).natDegree ≤ 34 := by
  unfold hP
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  exact bP_natDegree i k (by have := mem_range.1 hi; omega) hk

/-- The bound on `(A B_s)_jk`. -/
noncomputable def hB (D : ℤ) : ℤ := 17 * (2 ^ 49 * bB D)

/-- The bound on `(A B_s A*)_jt`. -/
noncomputable def gB (D : ℤ) : ℤ := 17 * (hB D * 2 ^ 49)

theorem bB_nonneg (hD : 0 ≤ D) : 0 ≤ bB D := by
  unfold bB
  have := pB_nonneg hD
  positivity

theorem hC_bound (ha : 0 ≤ a) (hD : a + 1 ≤ D) (hh : ∀ l, l ≤ 17 → l1 (h l) ≤ 2 ^ 75)
    (hA : ∀ j i, l1 (A j i) ≤ 2 ^ 49) (s j k : ℕ) (hk : k ≤ 17) (hs : s ≤ 34) :
    l1 (hC a D h A s j k) ≤ hB D := by
  have hD0 : 0 ≤ D := by linarith
  unfold hC hP hB
  rw [finsetSum_coeff]
  refine (l1_sum_le _ _).trans ?_
  have hterm : ∀ i ∈ range 17, l1 ((C (A j i) * bP a D h i k).coeff s) ≤ 2 ^ 49 * bB D := by
    intro i hi
    rw [coeff_C_mul]
    refine (l1_mul_le _ _).trans ?_
    refine mul_le_mul (hA j i) (bP_coeff_bound ha hD hh i k s (by have := mem_range.1 hi; omega) hk hs)
      (l1_nonneg _) (by norm_num)
  have hsum := sum_le_card_nsmul _ _ _ hterm
  rw [card_range, nsmul_eq_mul] at hsum
  simpa using hsum

theorem gC_bound (ha : 0 ≤ a) (hD : a + 1 ≤ D) (hh : ∀ l, l ≤ 17 → l1 (h l) ≤ 2 ^ 75)
    (hA : ∀ j i, l1 (A j i) ≤ 2 ^ 49) (s j t : ℕ) (hs : s ≤ 34) : l1 (gC a D h A s j t) ≤ gB D := by
  have hD0 : 0 ≤ D := by linarith
  unfold gC gB
  refine (l1_sum_le _ _).trans ?_
  have hH0 : 0 ≤ hB D := by
    unfold hB
    have := bB_nonneg hD0
    positivity
  have hterm : ∀ k ∈ range 17, l1 (hC a D h A s j k * star (A t k)) ≤ hB D * 2 ^ 49 := by
    intro k hk
    refine (l1_mul_le _ _).trans ?_
    rw [l1_star]
    refine mul_le_mul (hC_bound ha hD hh hA s j k (by have := mem_range.1 hk; omega) hs) (hA t k)
      (l1_nonneg _) hH0
  have hsum := sum_le_card_nsmul _ _ _ hterm
  rw [card_range, nsmul_eq_mul] at hsum
  simpa using hsum

set_option exponentiation.threshold 400 in
/-- The digit width is enough. -/
theorem gB_lt (k : ℕ) : gB (2 ^ k) < 2 ^ (324 + 34 * k - 1) := by
  have hexp : 324 + 34 * k - 1 = 323 + 34 * k := by omega
  rw [hexp]
  have hval : gB ((2 : ℤ) ^ k) = 17 * (17 * (2 ^ 49 * (18 * (2 * (35 * ((2 ^ 75 * 3 ^ 17) * (2 ^ 75 * 3 ^ 17)))))) * 2 ^ 49) *
      ((2 : ℤ) ^ (34 * k)) := by
    unfold gB hB bB pB
    have hpow : ((2 : ℤ) ^ k) ^ 17 * ((2 : ℤ) ^ k) ^ 17 = 2 ^ (34 * k) := by
      rw [← pow_add, ← pow_mul]
      congr 1
      ring
    calc _ = 17 * (17 * (2 ^ 49 * (18 * (2 * (35 * ((2 ^ 75 * 3 ^ 17) * (2 ^ 75 * 3 ^ 17)))))) * 2 ^ 49) *
          (((2 : ℤ) ^ k) ^ 17 * ((2 : ℤ) ^ k) ^ 17) := by ring
      _ = _ := by rw [hpow]
  rw [hval, pow_add]
  exact mul_lt_mul_of_pos_right (by norm_num) (by positivity)

theorem hB_le_gB (hD : 0 ≤ D) : hB D ≤ gB D := by
  unfold gB
  have h0 : 0 ≤ hB D := by
    unfold hB
    have := bB_nonneg hD
    positivity
  nlinarith

end qbounds

end Smale.RCheck
