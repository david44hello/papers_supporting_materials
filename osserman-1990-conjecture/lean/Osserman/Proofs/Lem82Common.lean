/-
Lem82Common.lean — helpers shared by the Lemma 8.2 files of paper 013 (Lem82, Lem82R1aAlg, Lem82R1aLin, Lem82R1):
homogeneous components of a product, linear and quadratic forms, and the first identity of (eq:cubicidentities) as a
polynomial identity.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Lem82DivQ

namespace Osserman.Proofs.Lem82Common

open Osserman Matrix MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Homogeneous components of a product -/

lemma hc_eq (D : MvPolynomial (Fin 16) ℝ) (n : ℕ) :
    homogeneousComponent n D = (DirectSum.decompose (homogeneousSubmodule (Fin 16) ℝ) D n : MvPolynomial (Fin 16) ℝ) :=
  (decomposition.decompose'_apply D n).symm

lemma hc_mul_of_le {φ : MvPolynomial (Fin 16) ℝ} {r n : ℕ} (hφ : φ.IsHomogeneous r) (h : r ≤ n)
    (E : MvPolynomial (Fin 16) ℝ) : homogeneousComponent n (φ * E) = φ * homogeneousComponent (n - r) E := by
  have hmem : φ ∈ homogeneousSubmodule (Fin 16) ℝ r := hφ
  rw [hc_eq, hc_eq]
  exact DirectSum.coe_decompose_mul_of_left_mem_of_le _ hmem h

lemma hc_mul_of_lt {φ : MvPolynomial (Fin 16) ℝ} {r n : ℕ} (hφ : φ.IsHomogeneous r) (h : n < r)
    (E : MvPolynomial (Fin 16) ℝ) : homogeneousComponent n (φ * E) = 0 := by
  have hmem : φ ∈ homogeneousSubmodule (Fin 16) ℝ r := hφ
  rw [hc_eq]
  exact DirectSum.coe_decompose_mul_of_left_mem_of_not_le _ hmem (by omega)

/-- A homogeneous `F` of degree `n` that is `φ * g` with `φ` homogeneous of degree `m ≤ n` is `φ` times the degree
`n - m` component of `g`. -/
lemma eq_mul_homogeneousComponent {φ F g : MvPolynomial (Fin 16) ℝ} {m n : ℕ} (hφ : φ.IsHomogeneous m)
    (hF : F.IsHomogeneous n) (hmn : m ≤ n) (hFg : F = φ * g) : F = φ * homogeneousComponent (n - m) g := by
  subst hFg
  rw [← hc_mul_of_le hφ hmn, homogeneousComponent_eq_self hF]

/-! ### Linear and quadratic forms -/

lemma eval_formP (f x : Vec 16) : eval x (formP f) = f ⬝ᵥ x := by
  simp [formP, dotProduct]

lemma isHomogeneous_formP (f : Vec 16) : (formP f).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun k _ => isHomogeneous_C_mul_X (f k) k

lemma formP_ne_zero {f : Vec 16} (hf : f ≠ 0) : formP f ≠ 0 := by
  intro h
  have e := congrArg (eval f) h
  rw [eval_formP, map_zero] at e
  exact hf (dotProduct_self_eq_zero.mp e)

lemma quadP_eq (M : Matrix (Fin 16) (Fin 16) ℝ) : quadP M = ∑ j, linP M j * X j := by
  unfold quadP linP
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma eval_quadP (M : Matrix (Fin 16) (Fin 16) ℝ) (x : Vec 16) : eval x (quadP M) = (M *ᵥ x) ⬝ᵥ x := by
  simp [quadP_eq, Lem82DivQ.eval_linP, dotProduct]

/-! ### (eq:cubicidentities) as a polynomial identity -/

/-- `⟨P(x), x⟩ = 0` as a polynomial identity. -/
lemma tangency_poly {P : Fin 16 → MvPolynomial (Fin 16) ℝ} (hP : CubicIdentities P) : ∑ j, P j * X j = 0 := by
  refine MvPolynomial.funext fun x => ?_
  have e := (hP x).1
  simp only [evalField, dotProduct] at e
  simp [e]

end Osserman.Proofs.Lem82Common
