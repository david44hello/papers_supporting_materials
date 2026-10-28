/-
Osserman/Proofs/S8Tools.lean — tools for §8.3 and §8.4 of paper 013 (no rows): homogeneous evaluation, eigenfields at
every point, the polynomial entries of `J_x`, the spectral congruence modulo `q`, the sum-of-squares step, and cubic
fields divisible by `q`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.SmallRoots
import Osserman.Proofs.Spectral
import Osserman.Proofs.Poly
import Osserman.Proofs.ThmEFrames
import Osserman.Proofs.Rem72a
import Osserman.Cited.Nik2006

namespace Osserman.Proofs.S8Tools

open Osserman Matrix MvPolynomial

/-! ### Homogeneous evaluation -/

lemma eval_smul_of_homogeneous {p : MvPolynomial (Fin 16) ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (t : ℝ)
    (x : Vec 16) : eval (t • x) p = t ^ d * eval x p := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsum : ∑ i ∈ s.support, s i = d := (hp.degree_eq_sum_deg_support hs).symm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  ring

lemma evalField_smul {E : Fin 16 → MvPolynomial (Fin 16) ℝ} {d : ℕ} (hE : ∀ j, (E j).IsHomogeneous d) (t : ℝ)
    (x : Vec 16) : evalField E (t • x) = t ^ d • evalField E x := by
  funext j
  simp only [evalField, eval_smul_of_homogeneous (hE j), Pi.smul_apply, smul_eq_mul]

lemma evalField_zero {E : Fin 16 → MvPolynomial (Fin 16) ℝ} {d : ℕ} (hE : ∀ j, (E j).IsHomogeneous d)
    (hd : d ≠ 0) : evalField E 0 = 0 := by
  have h := evalField_smul hE 0 0
  rw [zero_smul, zero_pow hd, zero_smul] at h
  exact h

lemma evalField_linP (J : Matrix (Fin 16) (Fin 16) ℝ) (x : Vec 16) : evalField (linP J) x = J *ᵥ x := by
  funext j
  simp [evalField, linP, mulVec, dotProduct]

/-! ### Eigenfields -/

lemma mem_eig_iff (R : CurvTensor 16) (x v : Vec 16) (μ : ℝ) :
    v ∈ Module.End.eigenspace (R.jacobiMap x) μ ↔ R.jacobi x *ᵥ v = μ • v := by
  rw [Module.End.mem_eigenspace_iff, Rem72a.jacobiMap_eq_mulVec]

/-- A homogeneous field that is a reduced eigenvector of `μ` at unit `x`, times `q^k`, is an eigenfield of `μ`. -/
lemma eigenfield_of_unit {R : CurvTensor 16} {E : Fin 16 → MvPolynomial (Fin 16) ℝ} {d : ℕ}
    (hE : ∀ j, (E j).IsHomogeneous d) (μ : ℝ)
    (hunit : ∀ x : Vec 16, x ⬝ᵥ x = 1 → evalField E x ∈ Module.End.eigenspace (R.jacobiMap x) μ ⊓ perp x)
    (k : ℕ) : IsEigenfield R μ (fun j => sqP 16 ^ k * E j) := by
  intro x
  obtain ⟨s, u, hu, rfl⟩ := Spectral.exists_unit_scale x
  have hev : evalField (fun j => sqP 16 ^ k * E j) (s • u) = ((s * s) ^ k * s ^ d) • evalField E u := by
    funext j
    simp only [evalField, map_mul, map_pow, Poly.eval_sqP, eval_smul_of_homogeneous (hE j), Pi.smul_apply,
      smul_eq_mul, smul_dotProduct, dotProduct_smul, hu]
    ring
  obtain ⟨h1, h2⟩ := hunit u hu
  rw [hev]
  refine ⟨?_, ?_⟩
  · have h1' : evalField E u ∈ Module.End.eigenspace (R.jacobiMap u) μ := h1
    show _ ∈ Module.End.eigenspace (R.jacobiMap (s • u)) (μ * ((s • u) ⬝ᵥ (s • u)))
    rw [mem_eig_iff] at h1' ⊢
    rw [Spectral.jacobi_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, h1', smul_dotProduct, dotProduct_smul, hu]
    simp only [smul_smul, smul_eq_mul]
    congr 1
    ring
  · have h2' : u ⬝ᵥ evalField E u = 0 := h2
    show (s • u) ⬝ᵥ (((s * s) ^ k * s ^ d) • evalField E u) = 0
    rw [smul_dotProduct, dotProduct_smul, h2', smul_zero, smul_zero]

/-- Reduced eigenfields of distinct eigenvalues are orthogonal at every point (homogeneous of positive degree). -/
lemma eigenfield_orth {R : CurvTensor 16} {μ σ : ℝ} (hne : μ ≠ σ) {P Q : Fin 16 → MvPolynomial (Fin 16) ℝ}
    {d : ℕ} (hd : d ≠ 0) (hP3 : ∀ j, (P j).IsHomogeneous d) (hP : IsEigenfield R μ P) (hQ : IsEigenfield R σ Q)
    (x : Vec 16) : evalField P x ⬝ᵥ evalField Q x = 0 := by
  by_cases hx : x = 0
  · rw [hx, evalField_zero hP3 hd, zero_dotProduct]
  have hq : x ⬝ᵥ x ≠ 0 := fun h => hx (dotProduct_self_eq_zero.mp h)
  have e1 := (mem_eig_iff R x _ _).mp (hP x).1
  have e2 := (mem_eig_iff R x _ _).mp (hQ x).1
  have sym : (R.jacobi x *ᵥ evalField P x) ⬝ᵥ evalField Q x = evalField P x ⬝ᵥ (R.jacobi x *ᵥ evalField Q x) := by
    rw [← Matrix.vecMul_transpose, Spectral.jacobi_transpose, ← Matrix.dotProduct_mulVec]
  rw [e1, e2, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at sym
  have hne' : μ * (x ⬝ᵥ x) - σ * (x ⬝ᵥ x) ≠ 0 := by
    rw [← sub_mul]; exact mul_ne_zero (sub_ne_zero.mpr hne) hq
  have : (μ * (x ⬝ᵥ x) - σ * (x ⬝ᵥ x)) * (evalField P x ⬝ᵥ evalField Q x) = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left hne'

/-- If an eigenfield is `q` times a linear field, the linear field is an eigenfield. -/
lemma eigenfield_linP {R : CurvTensor 16} {μ : ℝ} {P : Fin 16 → MvPolynomial (Fin 16) ℝ}
    (hP : IsEigenfield R μ P) (J : Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : ∀ x : Vec 16, evalField P x = (x ⬝ᵥ x) • (J *ᵥ x)) : IsEigenfield R μ (linP J) := by
  intro x
  rw [evalField_linP]
  by_cases hx : x = 0
  · rw [hx, Matrix.mulVec_zero]; exact Submodule.zero_mem _
  have hq : x ⬝ᵥ x ≠ 0 := fun h => hx (dotProduct_self_eq_zero.mp h)
  have e : J *ᵥ x = (x ⬝ᵥ x)⁻¹ • evalField P x := by rw [hJ x, smul_smul, inv_mul_cancel₀ hq, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (hP x)

/-! ### The polynomial entries of `J_x` and the spectral congruence -/

/-- The entry `(i, j)` of `J_x`, as a polynomial in `x`. -/
noncomputable def jacP (R : CurvTensor 16) (i j : Fin 16) : MvPolynomial (Fin 16) ℝ :=
  ∑ a, ∑ b, C ((Classical.choose (Spectral.quad_jacobi R)) a b i j) * X a * X b

lemma eval_jacP (R : CurvTensor 16) (x : Vec 16) (i j : Fin 16) : eval x (jacP R i j) = R.jacobi x i j := by
  rw [Classical.choose_spec (Spectral.quad_jacobi R) x]
  simp only [jacP, map_sum, map_mul, eval_C, eval_X, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- (eq:twocolumn)-type identities at every `x` give the entrywise congruence modulo `q`. -/
lemma spectral_dvd (R : CurvTensor 16) {r : ℕ} (P : Fin r → Fin 16 → MvPolynomial (Fin 16) ℝ) (w : Fin r → ℝ)
    (lam : ℝ)
    (h : ∀ x : Vec 16, ∑ i, w i • vecMulVec (evalField (P i) x) (evalField (P i) x) =
      (x ⬝ᵥ x) • (R.jacobi x * (R.jacobi x - (lam * (x ⬝ᵥ x)) • (1 : Matrix (Fin 16) (Fin 16) ℝ))))
    (a b : Fin 16) : sqP 16 ∣ ∑ i, C (w i) * P i a * P i b := by
  classical
  refine ⟨∑ k, jacP R a k * jacP R k b - C lam * sqP 16 * jacP R a b, MvPolynomial.funext fun x => ?_⟩
  have e := congrFun (congrFun (h x) a) b
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Matrix.mul_apply, Matrix.sub_apply,
    Matrix.one_apply, smul_eq_mul, evalField, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at e
  simp only [map_sum, map_mul, eval_C, map_sub, eval_jacP, Poly.eval_sqP]
  have lhs : ∑ i, w i * eval x (P i a) * eval x (P i b) = ∑ i, w i * (eval x (P i a) * eval x (P i b)) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [lhs, e]
  ring

/-! ### Sums of squares (Lemma 3.11) and cubic fields divisible by `q` -/

lemma dvd_of_C_mul {c : ℝ} (hc : c ≠ 0) {p : MvPolynomial (Fin 16) ℝ} (h : sqP 16 ∣ C c * p) : sqP 16 ∣ p := by
  have e : p = C c⁻¹ * (C c * p) := by rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  rw [e]
  exact Dvd.dvd.mul_left h _

/-- "the sum-of-squares lemma": weights of one strict sign, at most eight terms. -/
lemma sos_dvd {k : ℕ} (hk : k ≤ 8) (p : Fin k → MvPolynomial (Fin 16) ℝ) (w : Fin k → ℝ)
    (hw : (∀ i, 0 < w i) ∨ ∀ i, w i < 0) (h : sqP 16 ∣ ∑ i, C (w i) * p i ^ 2) : ∀ i, sqP 16 ∣ p i := by
  have pos : ∀ v : Fin k → ℝ, (∀ i, 0 < v i) → sqP 16 ∣ ∑ i, C (v i) * p i ^ 2 → ∀ i, sqP 16 ∣ p i := by
    intro v hv hsum i
    have h' : sqP 16 ∣ ∑ i, (C (Real.sqrt (v i)) * p i) ^ 2 := by
      convert hsum using 2 with j
      rw [mul_pow, ← map_pow, Real.sq_sqrt (hv j).le]
    exact dvd_of_C_mul (Real.sqrt_pos.mpr (hv i)).ne' (Osserman.Cited.nik2006_lemma_3_11 k hk _ h' i)
  rcases hw with hw | hw
  · exact pos w hw h
  · refine pos (fun i => -w i) (fun i => neg_pos.mpr (hw i)) ?_
    have e : ∑ i, C (-w i) * p i ^ 2 = -∑ i, C (w i) * p i ^ 2 := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [map_neg, neg_mul]
    rw [e]
    exact (dvd_neg).mpr h

/-- A homogeneous cubic divisible by `q` is `q` times a homogeneous linear polynomial. -/
lemma dvd_cubic_eq {F : MvPolynomial (Fin 16) ℝ} (hF : F.IsHomogeneous 3) (hq : sqP 16 ∣ F) :
    ∃ g : MvPolynomial (Fin 16) ℝ, g.IsHomogeneous 1 ∧ F = sqP 16 * g := by
  obtain ⟨g, rfl⟩ := hq
  refine ⟨homogeneousComponent 1 g, homogeneousComponent_isHomogeneous 1 g, ?_⟩
  have comp (k : ℕ) : homogeneousComponent 3 (sqP 16 * homogeneousComponent k g) =
      if 3 = 2 + k then sqP 16 * homogeneousComponent k g else 0 :=
    homogeneousComponent_of_mem (Poly.sqP_isHomogeneous.mul (homogeneousComponent_isHomogeneous k g))
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

/-- A field of homogeneous cubics divisible by `q` is `q` times a linear field. -/
lemma dvd_cubic_field {F : Fin 16 → MvPolynomial (Fin 16) ℝ} (hF : ∀ j, (F j).IsHomogeneous 3)
    (hq : ∀ j, sqP 16 ∣ F j) : ∃ J : Matrix (Fin 16) (Fin 16) ℝ, ∀ x : Vec 16, evalField F x = (x ⬝ᵥ x) • (J *ᵥ x) := by
  choose g hg hFg using fun j => dvd_cubic_eq (hF j) (hq j)
  obtain ⟨J, hJ⟩ := ThmEFrames.thm_E_linear_fields_proved g 1 odd_one (by norm_num) hg
  refine ⟨J, fun x => ?_⟩
  funext j
  have e := congrFun (hJ x) j
  simp only [evalField] at e
  simp only [evalField, hFg j, map_mul, Poly.eval_sqP, e, Pi.smul_apply, smul_eq_mul]

end Osserman.Proofs.S8Tools
