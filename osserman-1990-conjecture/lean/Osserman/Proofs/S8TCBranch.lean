/-
Osserman/Proofs/S8TCBranch.lean — paper 013, Section 8: the Lean-only row s8_threeCol_branch_nonvacuous (review a3
SHOULD-1): the three-column hypotheses can hold with all three images `p_i` nonzero modulo `q`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Construction: `R = 0`, `μ = 0`; `K = Jcl₀Jcl₂`, `H = KᵀJcl₁` (symmetric, orthogonal, anticommutes with `Jcl₃`, so
`π(quadP H) ≠ 0`); the frame `D = ((Jcl₀+Jcl₁)/2 ± √½ Jcl₂, √½ (Jcl₀ - Jcl₁))` with `F`-components `(½, ½, -√½)`;
`P_i(x) = qD_ix - 2⟨Kx, D_ix⟩Kx` (a reflection of `D_ix`, so the Gram matrix is `q³δ`); weights `(1, 1, -1)` with
`Σ wᵢcᵢ² = 0`, so the weighted quadratic sum vanishes mod `q`; mod `q` each image is `-2cᵢ π(quadP H) π(Kx) ≠ 0`.
-/
import Osserman.Proofs.QPrime
import Osserman.Proofs.Rem72b
import Osserman.Proofs.S8TCFields
import Osserman.Proofs.S8TCWitness

/-! ### algebraic building blocks for the nonlinear three-column witness. -/

namespace Osserman.Proofs.S8TC

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Example Osserman.Proofs.CorDNonvacuous

lemma orth_product (A B : Matrix (Fin 16) (Fin 16) ℝ) (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) :
    (A * B)ᵀ * (A * B) = 1 := by
  calc
    _ = Bᵀ * (Aᵀ * A) * B := by rw [transpose_mul]; noncomm_ring
    _ = 1 := by rw [hA, mul_one, hB]

lemma double_commute (A B C : Matrix (Fin 16) (Fin 16) ℝ)
    (hAC : A * C = -(C * A)) (hBC : B * C = -(C * B)) : (A * B) * C = C * (A * B) := by
  calc
    _ = A * (B * C) := mul_assoc _ _ _
    _ = A * -(C * B) := by rw [hBC]
    _ = -(A * C) * B := by noncomm_ring
    _ = -(-(C * A)) * B := by rw [hAC]
    _ = _ := by noncomm_ring

lemma jcl_anti {a b : Fin 8} (different : a ≠ b) : Jcl a * Jcl b = -(Jcl b * Jcl a) := by
  have relation := jcl_clifford.1.2 a b
  rw [ite_eq_right different] at relation
  exact eq_neg_of_add_eq_zero_left relation

lemma matrix_ne_zero_of_orthogonal (A : Matrix (Fin 16) (Fin 16) ℝ) (hA : Aᵀ * A = 1) : A ≠ 0 := by
  intro zero
  have entry := congrArg (fun M : Matrix (Fin 16) (Fin 16) ℝ => M 0 0) hA
  simp [zero] at entry

lemma quad_image_ne_zero (H T : Matrix (Fin 16) (Fin 16) ℝ) (hHs : Hᵀ = H)
    (hHo : Hᵀ * H = 1) (hTo : Tᵀ * T = 1) (hanti : H * T + T * H = 0) : piO (quadP H) ≠ 0 := by
  intro zero
  have divides : sqP 16 ∣ quadP H := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp zero)
  obtain ⟨factor, equation⟩ := divides
  obtain ⟨d, hd⟩ := Osserman.Proofs.Rem72b.eval_eq_const_mul
    (Osserman.Proofs.Poly.quadP_isHomogeneous H) equation
  have scalar : H = d • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
    apply Osserman.Proofs.Threshold.symm_eq_of_quadratic H _ hHs ?_ ?_
    · simp [Matrix.IsSymm]
    · intro x
      rw [smul_mulVec, one_mulVec, dotProduct_smul]
      simpa only [Osserman.Proofs.Poly.eval_quadP, smul_eq_mul] using hd x
  have relation : (2 * d) • T = 0 := by
    rw [scalar, smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at hanti
    simpa only [← add_smul, two_mul] using hanti
  have d0 : d = 0 := by
    have coefficient : 2 * d = 0 := (smul_eq_zero.mp relation).resolve_right (matrix_ne_zero_of_orthogonal T hTo)
    linarith
  have H0 : H = 0 := by rw [scalar, d0, zero_smul]
  exact matrix_ne_zero_of_orthogonal H hHo H0

lemma linear_image_ne_zero (K : Matrix (Fin 16) (Fin 16) ℝ) (hKo : Kᵀ * K = 1) :
    ∃ a : Fin 16, piO (linP K a) ≠ 0 := by
  classical
  by_contra absent
  simp only [not_exists, not_not] at absent
  have all_zero (a : Fin 16) : linP K a = 0 := by
    by_contra nonzero
    have divides : sqP 16 ∣ linP K a :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (absent a))
    obtain ⟨z, hz⟩ := divides
    have qne := Osserman.Proofs.QPrime.s8_q_prime_proved.1.ne_zero
    have zne : z ≠ 0 := fun zero => nonzero (by rw [hz, zero, mul_zero])
    have degree := MvPolynomial.totalDegree_mul_of_isDomain qne zne
    rw [← hz, Osserman.Proofs.Poly.sqP_isHomogeneous.totalDegree qne] at degree
    have bound := (Osserman.Proofs.S83.linP_homogeneous K a).totalDegree_le
    omega
  have K0 : K = 0 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    rw [← Osserman.Proofs.S8Tools.evalField_linP, Matrix.zero_mulVec]
    ext a
    change eval x (linP K a) = 0
    rw [all_zero, map_zero]
  exact matrix_ne_zero_of_orthogonal K hKo K0

noncomputable def reflectedP (K D : Matrix (Fin 16) (Fin 16) ℝ) : Fin 16 → MvPolynomial (Fin 16) ℝ :=
  fun a => sqP 16 * linP D a - C 2 * quadP (Kᵀ * D) * linP K a

lemma reflectedP_eval (K D : Matrix (Fin 16) (Fin 16) ℝ) (x : Vec 16) :
    evalField (reflectedP K D) x = (x ⬝ᵥ x) • (D *ᵥ x) -
      (2 * ((K *ᵥ x) ⬝ᵥ (D *ᵥ x))) • (K *ᵥ x) := by
  ext a
  simp only [evalField, reflectedP, map_sub, map_mul, eval_C, Osserman.Proofs.Poly.eval_sqP,
    Osserman.Proofs.Poly.eval_quadP, Osserman.Proofs.Rem72b.dot_transpose_mul]
  have first := congrFun (Osserman.Proofs.S8Tools.evalField_linP D x) a
  have second := congrFun (Osserman.Proofs.S8Tools.evalField_linP K x) a
  change eval x (linP D a) = (D *ᵥ x) a at first
  change eval x (linP K a) = (K *ᵥ x) a at second
  rw [first, second]
  rfl

lemma reflectedP_homogeneous (K D : Matrix (Fin 16) (Fin 16) ℝ) (a : Fin 16) :
    (reflectedP K D a).IsHomogeneous 3 := by
  apply IsHomogeneous.sub
  · exact Osserman.Proofs.Poly.sqP_isHomogeneous.mul (Osserman.Proofs.S83.linP_homogeneous D a)
  · exact ((Osserman.Proofs.Poly.quadP_isHomogeneous _).C_mul 2).mul
      (Osserman.Proofs.S83.linP_homogeneous K a)

lemma reflection_dot (q : ℝ) (k v w : Vec 16) (hkk : k ⬝ᵥ k = q) :
    (q • v - (2 * (k ⬝ᵥ v)) • k) ⬝ᵥ (q • w - (2 * (k ⬝ᵥ w)) • k) = q ^ 2 * (v ⬝ᵥ w) := by
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm v k, hkk]
  ring

end Osserman.Proofs.S8TC

/-! ### a Clifford three-frame with a nonconstant central quadratic form. -/

namespace Osserman.Proofs.S8TC

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Example Osserman.Proofs.CorDNonvacuous

noncomputable def branchK : Matrix (Fin 16) (Fin 16) ℝ := Jcl 0 * Jcl 2
noncomputable def branchH : Matrix (Fin 16) (Fin 16) ℝ := branchKᵀ * Jcl 1
noncomputable def branchS : ℝ := Real.sqrt (1 / 2)
noncomputable def branchD : Fin 3 → Matrix (Fin 16) (Fin 16) ℝ :=
  ![(1 / 2 : ℝ) • (Jcl 0 + Jcl 1) + branchS • Jcl 2,
    (1 / 2 : ℝ) • (Jcl 0 + Jcl 1) - branchS • Jcl 2,
    branchS • (Jcl 0 - Jcl 1)]
noncomputable def branchCoeff : Fin 3 → ℝ := ![1 / 2, 1 / 2, -branchS]

lemma branchS_sq : branchS ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
lemma branchS_ne : branchS ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))

lemma branchK_skew : branchKᵀ = -branchK := by
  rw [branchK, transpose_mul, jcl_clifford.1.1, jcl_clifford.1.1, neg_mul_neg]
  exact jcl_anti (by decide : (2 : Fin 8) ≠ 0)

lemma branchK_orthogonal : branchKᵀ * branchK = 1 :=
  orth_product _ _ (jcl_clifford.2 0) (jcl_clifford.2 2)

lemma branchH_facts : branchHᵀ = branchH ∧ branchHᵀ * branchH = 1 ∧
    branchH * Jcl 3 + Jcl 3 * branchH = 0 := by
  have comm1 : branchK * Jcl 1 = Jcl 1 * branchK :=
    double_commute _ _ _ (jcl_anti (by decide : (0 : Fin 8) ≠ 1)) (jcl_anti (by decide : (2 : Fin 8) ≠ 1))
  have comm3 : branchK * Jcl 3 = Jcl 3 * branchK :=
    double_commute _ _ _ (jcl_anti (by decide : (0 : Fin 8) ≠ 3)) (jcl_anti (by decide : (2 : Fin 8) ≠ 3))
  refine ⟨?_, ?_, ?_⟩
  · rw [branchH, transpose_mul, transpose_transpose, jcl_clifford.1.1, branchK_skew]
    simp only [neg_mul]
    exact congrArg Neg.neg comm1.symm
  · apply orth_product _ _ _ (jcl_clifford.2 1)
    rw [transpose_transpose]
    have relation := branchK_orthogonal
    rw [branchK_skew, neg_mul] at relation
    rw [branchK_skew, mul_neg]
    exact relation
  · have anti13 : Jcl 1 * Jcl 3 + Jcl 3 * Jcl 1 = 0 := by
      simpa only [ite_eq_right (by decide : (1 : Fin 8) ≠ 3)] using jcl_clifford.1.2 1 3
    change (branchKᵀ * Jcl 1) * Jcl 3 + Jcl 3 * (branchKᵀ * Jcl 1) = 0
    rw [branchK_skew]
    calc
      _ = -(branchK * (Jcl 1 * Jcl 3 + Jcl 3 * Jcl 1)) := by
        simp only [neg_mul, mul_neg, ← mul_assoc]
        rw [comm3.symm]
        noncomm_ring
      _ = 0 := by rw [anti13, mul_zero, neg_zero]

lemma orth_dot (A : Matrix (Fin 16) (Fin 16) ℝ) (hA : Aᵀ * A = 1) (u v : Vec 16) :
    (A *ᵥ u) ⬝ᵥ (A *ᵥ v) = u ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, Matrix.mulVec_mulVec, hA, one_mulVec]

lemma branchK_dot0 (x : Vec 16) : (branchK *ᵥ x) ⬝ᵥ (Jcl 0 *ᵥ x) = 0 := by
  rw [branchK, ← Matrix.mulVec_mulVec, orth_dot _ (jcl_clifford.2 0), dotProduct_comm]
  exact Osserman.Proofs.Rem72a.skew_dot_self (jcl_clifford.1.1 2) x

lemma branchK_dot2 (x : Vec 16) : (branchK *ᵥ x) ⬝ᵥ (Jcl 2 *ᵥ x) = 0 := by
  rw [branchK, ← Matrix.mulVec_mulVec, dotProduct_comm]
  exact Osserman.Proofs.Rem72a.skew_dot_self (jcl_clifford.1.1 0) (Jcl 2 *ᵥ x)

lemma branchD_gram (x : Vec 16) (i j : Fin 3) :
    (branchD i *ᵥ x) ⬝ᵥ (branchD j *ᵥ x) = if i = j then x ⬝ᵥ x else 0 := by
  have square := branchS_sq
  have scaled : branchS ^ 2 * (x ⬝ᵥ x) = (1 / 2) * (x ⬝ᵥ x) := by rw [square]
  fin_cases i <;> fin_cases j <;>
    norm_num [branchD, add_mulVec, sub_mulVec, smul_mulVec, add_dotProduct, dotProduct_add,
      sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, frame_dot] <;>
    nlinarith [scaled]

lemma branchD_tangent (x : Vec 16) (i : Fin 3) : x ⬝ᵥ (branchD i *ᵥ x) = 0 := by
  have base (a : Fin 8) : x ⬝ᵥ (Jcl a *ᵥ x) = 0 := Osserman.Proofs.Rem72a.skew_dot_self (jcl_clifford.1.1 a) x
  fin_cases i <;> simp [branchD, add_mulVec, sub_mulVec, smul_mulVec, dotProduct_add,
    dotProduct_sub, dotProduct_smul, base]

lemma branchD_cross (x : Vec 16) (i : Fin 3) :
    (branchK *ᵥ x) ⬝ᵥ (branchD i *ᵥ x) = branchCoeff i * eval x (quadP branchH) := by
  have middle : (branchK *ᵥ x) ⬝ᵥ (Jcl 1 *ᵥ x) = eval x (quadP branchH) := by
    rw [Osserman.Proofs.Poly.eval_quadP, branchH, Osserman.Proofs.Rem72b.dot_transpose_mul]
  fin_cases i <;> simp [branchD, branchCoeff, add_mulVec, sub_mulVec, smul_mulVec,
    dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul, branchK_dot0, branchK_dot2, middle]

lemma branchD_quad (i : Fin 3) : quadP (branchKᵀ * branchD i) = C (branchCoeff i) * quadP branchH := by
  apply MvPolynomial.funext
  intro x
  rw [Osserman.Proofs.Poly.eval_quadP, Osserman.Proofs.Rem72b.dot_transpose_mul, branchD_cross,
    map_mul, eval_C]

end Osserman.Proofs.S8TC
/-! ### reflected Clifford-frame witness with three nonzero quotient images. -/

namespace Osserman.Proofs.S8TC

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Example Osserman.Proofs.CorDNonvacuous

lemma piO_C_ne_zero (r : ℝ) (hr : r ≠ 0) : piO (C r) ≠ 0 := by
  let _ := Osserman.Proofs.QPrime.s8_q_prime_proved.2.2
  have injective := (piO.comp (C : ℝ →+* MvPolynomial (Fin 16) ℝ)).injective
  intro zero
  apply hr
  apply injective
  simpa only [RingHom.comp_apply, map_zero, map_zero] using zero

theorem s8_threeCol_branch_nonvacuous_proved :
    ∃ (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (wt : Fin 3 → ℝ),
      ThreeColHyp R μ P wt ∧ ∀ i, tcImg wt P i ≠ 0 := by
  classical
  let _ := Osserman.Proofs.QPrime.s8_q_prime_proved.2.2
  obtain ⟨R, hR⟩ := exists_sum_RJ (fun a : Fin 0 => Fin.elim0 a) (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
  have jac_zero (x : Vec 16) : R.jacobi x = 0 := by simpa using hR x
  let P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ := fun i => reflectedP branchK (branchD i)
  let wt : Fin 3 → ℝ := ![1, 1, -1]
  have tangency (x : Vec 16) (i : Fin 3) : x ⬝ᵥ evalField (P i) x = 0 := by
    rw [reflectedP_eval, dotProduct_sub, dotProduct_smul, dotProduct_smul,
      branchD_tangent, Osserman.Proofs.Rem72a.skew_dot_self branchK_skew]
    simp
  have gram (x : Vec 16) (i j : Fin 3) :
      evalField (P i) x ⬝ᵥ evalField (P j) x = if i = j then (x ⬝ᵥ x) ^ 3 else 0 := by
    rw [reflectedP_eval, reflectedP_eval, reflection_dot _ _ _ _ (orth_dot _ branchK_orthogonal x x), branchD_gram]
    split_ifs <;> ring
  have coeffs : ∑ i, wt i * branchCoeff i ^ 2 = 0 := by
    norm_num [Fin.sum_univ_succ, wt, branchCoeff]
    nlinarith [branchS_sq]
  have coeffPoly : (∑ i, C (wt i) * (C (branchCoeff i) : MvPolynomial (Fin 16) ℝ) ^ 2) = 0 := by
    simpa only [map_sum, map_mul, map_pow, map_zero] using congrArg (C : ℝ →+* MvPolynomial (Fin 16) ℝ) coeffs
  have quadSum : (∑ i, piO (C (wt i)) * piO (quadP (branchKᵀ * branchD i)) ^ 2) = 0 := by
    have constants := congrArg piO coeffPoly
    simp only [map_sum, map_mul, map_pow, map_zero] at constants
    simp only [branchD_quad, map_mul]
    calc
      _ = (∑ i, piO (C (wt i)) * piO (C (branchCoeff i)) ^ 2) * piO (quadP branchH) ^ 2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [constants, zero_mul]
  have image (i : Fin 3) (a : Fin 16) :
      piO (P i a) = -(2 : Ocal) * piO (quadP (branchKᵀ * branchD i)) * piO (linP branchK a) := by
    change piO (sqP 16 * linP (branchD i) a - C 2 * quadP (branchKᵀ * branchD i) * linP branchK a) = _
    simp only [map_sub, map_mul, piO_q, zero_mul, zero_sub, map_ofNat]
    ring
  have congruence (a b : Fin 16) : sqP 16 ∣ ∑ i, C (wt i) * P i a * P i b := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change piO (∑ i, C (wt i) * P i a * P i b) = 0
    rw [map_sum]
    simp only [map_mul, image]
    calc
      _ = (4 * ∑ i, piO (C (wt i)) * piO (quadP (branchKᵀ * branchD i)) ^ 2) *
          piO (linP branchK a) * piO (linP branchK b) := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [quadSum]; ring
  refine ⟨R, fun _ => 0, P, wt, ?_, ?_⟩
  · refine ⟨fun i a => reflectedP_homogeneous _ _ _, ?_, ?_, ?_,
      by norm_num [wt], by norm_num [wt], by norm_num [wt], congruence⟩
    · intro i x
      refine Submodule.mem_inf.mpr ⟨?_, tangency x i⟩
      apply Module.End.mem_eigenspace_iff.mpr
      rw [Osserman.Proofs.Rem72a.jacobiMap_eq_mulVec, jac_zero, zero_mulVec, zero_mul, zero_smul]
    · intro x i j different
      simpa only [ite_eq_right different] using gram x i j
    · intro x i
      simpa only [ite_true] using gram x i i
  · have rho_ne : piO (quadP branchH) ≠ 0 :=
      quad_image_ne_zero branchH (Jcl 3) branchH_facts.1 branchH_facts.2.1 (jcl_clifford.2 3) branchH_facts.2.2
    obtain ⟨a, ha⟩ := linear_image_ne_zero branchK branchK_orthogonal
    intro i zero
    have ci : branchCoeff i ≠ 0 := by
      fin_cases i <;> simp [branchCoeff, branchS_ne]
    have factor_ne : piO (P i a) ≠ 0 := by
      rw [image, branchD_quad, map_mul]
      have two_ne : (2 : Ocal) ≠ 0 := by
        have h2 := piO_C_ne_zero 2 two_ne_zero
        rwa [map_ofNat, map_ofNat] at h2
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne) (mul_ne_zero (piO_C_ne_zero _ ci) rho_ne)) ha
    have scalar : Real.sqrt |wt i| = 1 := by fin_cases i <;> norm_num [wt]
    have entry := congrFun zero a
    change piO (C (Real.sqrt |wt i|) * P i a) = 0 at entry
    rw [scalar, map_one, one_mul] at entry
    exact factor_ne entry

end Osserman.Proofs.S8TC

