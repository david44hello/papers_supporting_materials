/-
Lem82DivQ.lean — Lemma 8.2, the case "every component of P is divisible by q" (paper 013, sec_small_roots.tex
lines 79-90): "then $P(x)=qJx$ with $J$ linear, and (eq:cubicidentities) gives $\ip{Jx}x=0$ and $\norm{Jx}^2=q$, so
$J$ is skew and orthogonal."
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.SmallRoots

namespace Osserman.Proofs.Lem82DivQ

open Osserman Matrix MvPolynomial

/-! ### Polynomial facts -/

lemma sqP_isHomogeneous : (sqP 16).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i 2

lemma eval_sqP (x : Vec 16) : eval x (sqP 16) = x ⬝ᵥ x := by
  simp [sqP, dotProduct, sq]

lemma eval_linP (J : Matrix (Fin 16) (Fin 16) ℝ) (x : Vec 16) (j : Fin 16) :
    eval x (linP J j) = (J *ᵥ x) j := by
  simp [linP, mulVec, dotProduct]

/-- A homogeneous cubic divisible by `q` is `q` times a homogeneous linear polynomial (compare the homogeneous
components of degree 3 of both sides). -/
lemma dvd_cubic_eq {F : MvPolynomial (Fin 16) ℝ} (hF : F.IsHomogeneous 3) (hq : sqP 16 ∣ F) :
    ∃ g : MvPolynomial (Fin 16) ℝ, g.IsHomogeneous 1 ∧ F = sqP 16 * g := by
  obtain ⟨g, rfl⟩ := hq
  refine ⟨homogeneousComponent 1 g, homogeneousComponent_isHomogeneous 1 g, ?_⟩
  have comp (k : ℕ) : homogeneousComponent 3 (sqP 16 * homogeneousComponent k g) =
      if 3 = 2 + k then sqP 16 * homogeneousComponent k g else 0 :=
    homogeneousComponent_of_mem (sqP_isHomogeneous.mul (homogeneousComponent_isHomogeneous k g))
  have key : homogeneousComponent 3 (sqP 16 * g) = sqP 16 * homogeneousComponent 1 g := by
    conv_lhs => rw [← sum_homogeneousComponent g]
    rw [Finset.mul_sum, map_sum, Finset.sum_eq_single 1]
    · rw [comp]; simp
    · intro k _ hk1
      rw [comp, ite_eq_right (by omega)]
    · intro h1
      have hlt : g.totalDegree < 1 := by simpa [Finset.mem_range] using h1
      rw [homogeneousComponent_eq_zero 1 g hlt, mul_zero, map_zero]
  rw [← key, homogeneousComponent_of_mem hF, ite_eq_left rfl]

/-- A homogeneous linear polynomial is `∑_k c_k x_k`. -/
lemma linear_eq_sum {g : MvPolynomial (Fin 16) ℝ} (hg : g.IsHomogeneous 1) :
    ∃ c : Fin 16 → ℝ, ∑ k, C (c k) * X k = g := by
  have hmem : g ∈ Submodule.span ℝ (Set.range (X : Fin 16 → MvPolynomial (Fin 16) ℝ)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hg
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  exact ⟨c, by simpa [smul_eq_C_mul] using hc⟩

/-- "$P(x)=qJx$ with $J$ linear". -/
lemma linear_field {P : Fin 16 → MvPolynomial (Fin 16) ℝ} (hP3 : ∀ j, (P j).IsHomogeneous 3)
    (hq : ∀ j, sqP 16 ∣ P j) : ∃ J : Matrix (Fin 16) (Fin 16) ℝ, ∀ j, P j = sqP 16 * linP J j := by
  choose g hg hPg using fun j => dvd_cubic_eq (hP3 j) (hq j)
  choose c hc using fun j => linear_eq_sum (hg j)
  refine ⟨Matrix.of c, fun j => ?_⟩
  rw [hPg j, ← hc j]
  rfl

lemma evalField_eq {P : Fin 16 → MvPolynomial (Fin 16) ℝ} {J : Matrix (Fin 16) (Fin 16) ℝ}
    (hJ : ∀ j, P j = sqP 16 * linP J j) (x : Vec 16) : evalField P x = (x ⬝ᵥ x) • (J *ᵥ x) := by
  funext j
  simp only [evalField, hJ j, eval_mul, eval_sqP, eval_linP, Pi.smul_apply, smul_eq_mul]

/-! ### Pointwise identities and polarization -/

/-- Dividing (eq:cubicidentities) by powers of `q = |x|²`: `⟨Jx,x⟩ = 0` and `|Jx|² = |x|²`. -/
lemma pointwise {J : Matrix (Fin 16) (Fin 16) ℝ}
    (h : ∀ x : Vec 16, ((x ⬝ᵥ x) • (J *ᵥ x)) ⬝ᵥ x = 0 ∧
      ((x ⬝ᵥ x) • (J *ᵥ x)) ⬝ᵥ ((x ⬝ᵥ x) • (J *ᵥ x)) = (x ⬝ᵥ x) ^ 3) (x : Vec 16) :
    (J *ᵥ x) ⬝ᵥ x = 0 ∧ (J *ᵥ x) ⬝ᵥ (J *ᵥ x) = x ⬝ᵥ x := by
  by_cases hx : x = 0
  · subst hx; simp
  have hne : x ⬝ᵥ x ≠ 0 := fun h0 => hx (dotProduct_self_eq_zero.mp h0)
  obtain ⟨h1, h2⟩ := h x
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at h1 h2
  refine ⟨(mul_eq_zero.mp h1).resolve_left hne, ?_⟩
  have h3 : (x ⬝ᵥ x) ^ 2 * ((J *ᵥ x) ⬝ᵥ (J *ᵥ x)) = (x ⬝ᵥ x) ^ 2 * (x ⬝ᵥ x) := by
    linear_combination h2
  exact mul_left_cancel₀ (pow_ne_zero 2 hne) h3

/-- `⟨Jx,x⟩ = 0` for all `x` makes `J` skew. -/
lemma skew_of_forall {J : Matrix (Fin 16) (Fin 16) ℝ} (h : ∀ x : Vec 16, (J *ᵥ x) ⬝ᵥ x = 0) : Jᵀ = -J := by
  have pol (x y : Vec 16) : (J *ᵥ x) ⬝ᵥ y = -((J *ᵥ y) ⬝ᵥ x) := by
    have hxy := h (x + y)
    simp only [mulVec_add, add_dotProduct, dotProduct_add, h x, h y] at hxy
    linarith
  ext i j
  have e := pol (Pi.single j 1) (Pi.single i 1)
  simp only [mulVec_single_one, dotProduct_single_one] at e
  have e' : J i j = -J j i := e
  rw [transpose_apply, neg_apply]
  linarith

/-- `|Jx|² = |x|²` for all `x` makes `J` orthogonal. -/
lemma orth_of_forall {J : Matrix (Fin 16) (Fin 16) ℝ} (h : ∀ x : Vec 16, (J *ᵥ x) ⬝ᵥ (J *ᵥ x) = x ⬝ᵥ x) :
    Jᵀ * J = 1 := by
  have pol (x y : Vec 16) : (J *ᵥ x) ⬝ᵥ (J *ᵥ y) = x ⬝ᵥ y := by
    have hxy := h (x + y)
    simp only [mulVec_add, add_dotProduct, dotProduct_add, h x, h y] at hxy
    have c1 := dotProduct_comm (J *ᵥ y) (J *ᵥ x)
    have c2 := dotProduct_comm y x
    linarith
  ext i j
  have e := pol (Pi.single i 1) (Pi.single j 1)
  simp only [mulVec_single_one, dotProduct_single_one, Pi.single_apply] at e
  rw [mul_apply, one_apply]
  have e' : ∑ a, Jᵀ i a * J a j = if j = i then 1 else 0 := by
    rw [← e]; simp [dotProduct]
  rw [e']
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

/-! ### The row -/

theorem lem_8_2_div_q_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP3 : ∀ j, (P j).IsHomogeneous 3)
    (hP : CubicIdentities P) (hq : ∀ j, sqP 16 ∣ P j) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, (∀ j, P j = sqP 16 * linP J j) ∧
      (∀ x : Vec 16, (J *ᵥ x) ⬝ᵥ x = 0 ∧ (J *ᵥ x) ⬝ᵥ (J *ᵥ x) = x ⬝ᵥ x) ∧ Jᵀ = -J ∧ Jᵀ * J = 1 := by
  obtain ⟨J, hJ⟩ := linear_field hP3 hq
  have hpt : ∀ x : Vec 16, (J *ᵥ x) ⬝ᵥ x = 0 ∧ (J *ᵥ x) ⬝ᵥ (J *ᵥ x) = x ⬝ᵥ x := by
    refine pointwise fun x => ?_
    obtain ⟨h1, h2, -⟩ := hP x
    rw [evalField_eq hJ x] at h1 h2
    exact ⟨h1, h2⟩
  exact ⟨J, hJ, hpt, skew_of_forall fun x => (hpt x).1, orth_of_forall fun x => (hpt x).2⟩

end Osserman.Proofs.Lem82DivQ
