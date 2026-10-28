/-
Osserman/Proofs/S83Move.lean — §8.3 of paper 013, the linear case: rows s8_3_move_both, s8_3_restore_two,
s8_3_linear_case (statements copied verbatim from Osserman/Paper/Statements8.lean).
Premise rows (leading arguments with their exact types): lem_8_2_div_q, s8_move_eigenfield.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof. The linear eigenfields `J_0x` (of `μ`) and `J_1x` (of `σ`) are orthogonal. Moving `J_0` into `0` keeps `J_1x`
an eigenvector of `σ` (the rank-one term kills it), and moving `J_1` into `λ` gives the pattern `(M+1, N+1)`; at a unit
`x`, `J_0x` and `J_1x` land in the eigenspaces of `0` and `λ`. The endpoint is Clifford (`(8,7)`: Theorem A without
Cayley; `(9,6)`: Proposition 2.1), and [Nik2006, Lemma 3.2(1)] (`lem_nik_3_2_1`) restores both terms; Clifford
tensors are Osserman (`Rem72d.clifford_multiplicity`).
-/
import Osserman.Proofs.S83Fields
import Osserman.Proofs.S83Ends
import Osserman.Proofs.Rem72c

namespace Osserman.Proofs.S83

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Tools

/-- The type of row `s8_move_eigenfield`. -/
abbrev MoveHyp : Prop :=
  ∀ {k : ℕ} (R : CurvTensor 16) (m : Fin k → ℕ) (ev : Fin k → ℝ) (_hR : PatternEv R m ev)
    (_hsum : ∑ i, m i = 15) (J : Matrix (Fin 16) (Fin 16) ℝ) (_hJs : Jᵀ = -J) (_hJo : Jᵀ * J = 1) (i1 i2 : Fin k)
    (_h12 : i1 ≠ i2) (_hJ : IsEigenfield R (ev i1) (linP J)),
    ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - (ev i1 - ev i2) • RJfun J u v z) ∧
      (∀ x, R'.jacobi x = R.jacobi x - (ev i1 - ev i2) • jfam J x) ∧ R'.IsOsserman ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 → R'.redMult x (ev i1) = m i1 - 1 ∧ R'.redMult x (ev i2) = m i2 + 1 ∧
        ∀ i, i ≠ i1 → i ≠ i2 → R'.redMult x (ev i) = m i

/-! ### Linear eigenfields -/

lemma linP_homogeneous (J : Matrix (Fin 16) (Fin 16) ℝ) (j : Fin 16) : (linP J j).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

lemma orth_norm {J : Matrix (Fin 16) (Fin 16) ℝ} (hJo : Jᵀ * J = 1) (x : Vec 16) :
    (J *ᵥ x) ⬝ᵥ (J *ᵥ x) = x ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hJo, Matrix.one_mulVec]

lemma evalField_of_eq {P : Fin 16 → MvPolynomial (Fin 16) ℝ} {J : Matrix (Fin 16) (Fin 16) ℝ}
    (hP : ∀ j, P j = sqP 16 * linP J j) (x : Vec 16) : evalField P x = (x ⬝ᵥ x) • (J *ᵥ x) := by
  funext j
  have e := congrFun (evalField_linP J x) j
  simp only [evalField] at e ⊢
  rw [hP j, map_mul, Poly.eval_sqP, e, Pi.smul_apply, smul_eq_mul]

lemma lin_eig {R : CurvTensor 16} {μ : ℝ} {J : Matrix (Fin 16) (Fin 16) ℝ} (hJe : IsEigenfield R μ (linP J))
    (x : Vec 16) : R.jacobi x *ᵥ (J *ᵥ x) = (μ * (x ⬝ᵥ x)) • (J *ᵥ x) ∧ x ⬝ᵥ (J *ᵥ x) = 0 := by
  have h := hJe x
  rw [evalField_linP] at h
  exact ⟨(mem_eig_iff R x _ _).mp (Submodule.mem_inf.mp h).1, (Submodule.mem_inf.mp h).2⟩

lemma lin_orth {R : CurvTensor 16} {μ σ : ℝ} (hne : μ ≠ σ) {J K : Matrix (Fin 16) (Fin 16) ℝ}
    (hJ : IsEigenfield R μ (linP J)) (hK : IsEigenfield R σ (linP K)) (x : Vec 16) : (J *ᵥ x) ⬝ᵥ (K *ᵥ x) = 0 := by
  have h := eigenfield_orth hne one_ne_zero (linP_homogeneous J) hJ hK x
  rwa [evalField_linP, evalField_linP] at h

/-- After subtracting `c R_J`, a linear eigenfield of another eigenvalue stays an eigenfield. -/
lemma eigenfield_after_move {R R' : CurvTensor 16} {c μ σ : ℝ} {J K : Matrix (Fin 16) (Fin 16) ℝ}
    (hjac : ∀ x, R'.jacobi x = R.jacobi x - c • jfam J x) (hne : μ ≠ σ) (hJ : IsEigenfield R μ (linP J))
    (hK : IsEigenfield R σ (linP K)) : IsEigenfield R' σ (linP K) := by
  intro x
  rw [evalField_linP]
  obtain ⟨e1, p1⟩ := lin_eig hK x
  refine Submodule.mem_inf.mpr ⟨(mem_eig_iff R' x _ _).mpr ?_, p1⟩
  rw [hjac, Matrix.sub_mulVec, Matrix.smul_mulVec, Rem72a.jfam_mulVec, lin_orth hne hJ hK x, zero_smul, smul_zero,
    sub_zero, e1]

lemma clifford_osserman {R : CurvTensor 16} (hC : R.IsClifford) : R.IsOsserman := by
  obtain ⟨ν, J, hJ, l0, η, hjac⟩ := hC
  intro x y hx hy μ
  rw [Rem72d.clifford_multiplicity R J hJ l0 η hjac x hx μ, Rem72d.clifford_multiplicity R J hJ l0 η hjac y hy μ]

lemma inj_comp {k n : ℕ} {ev : Fin k → ℝ} (hev : Function.Injective ev) {g : Fin n → ℝ} (f : Fin n → Fin k)
    (hf : Function.Injective f) (hg : g = ev ∘ f) : Function.Injective g := hg ▸ hev.comp hf

/-! ### Moving both fields -/

lemma first_move (hMove : MoveHyp) {R : CurvTensor 16} {M N : ℕ} {ev : Fin 4 → ℝ}
    {P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ} (h : Sec83Data R M N ev P)
    (J : Fin 2 → Matrix (Fin 16) (Fin 16) ℝ) (hJ : ∀ i, (J i)ᵀ = -J i ∧ (J i)ᵀ * J i = 1)
    (hJe : IsEigenfield R (ev 2) (linP (J 0)) ∧ IsEigenfield R (ev 3) (linP (J 1))) :
    ∃ R1 : CurvTensor 16, (∀ u v z, R1.op u v z = R.op u v z - ev 2 • RJfun (J 0) u v z) ∧
      (∀ x, R1.jacobi x = R.jacobi x - ev 2 • jfam (J 0) x) ∧ R1.IsOsserman ∧
      PatternEv R1 ![M + 1, N, 0, 1] ev ∧ IsEigenfield R1 (ev 3) (linP (J 1)) := by
  obtain ⟨hMN, hR, h0, -, -, -, -⟩ := h
  obtain ⟨hsum, -⟩ := pattern_facts hMN
  have h23 : ev 2 ≠ ev 3 := fun e => absurd (hR.1 e) (by decide)
  obtain ⟨R1, hop, hjac, hO1, hm⟩ := hMove R _ ev hR hsum (J 0) (hJ 0).1 (hJ 0).2 2 0 (by decide) hJe.1
  simp only [h0, sub_zero] at hop hjac
  refine ⟨R1, hop, hjac, hO1, ⟨hR.1, fun x hx i => ?_⟩, eigenfield_after_move hjac h23 hJe.1 hJe.2⟩
  obtain ⟨a, b, c⟩ := hm x hx
  fin_cases i
  · simpa using b
  · simpa using c 1 (by decide) (by decide)
  · simpa using a
  · simpa using c 3 (by decide) (by decide)

/-- Row `s8_3_move_both`. -/
theorem s8_3_move_both_proved (hMove : MoveHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec83Data R M N ev P) (J : Fin 2 → Matrix (Fin 16) (Fin 16) ℝ) (hJ : ∀ i, (J i)ᵀ = -J i ∧ (J i)ᵀ * J i = 1)
    (hJe : IsEigenfield R (ev 2) (linP (J 0)) ∧ IsEigenfield R (ev 3) (linP (J 1))) :
    ∃ Rt : CurvTensor 16,
      (∀ u v z, Rt.op u v z = R.op u v z - ev 2 • RJfun (J 0) u v z - (ev 3 - ev 1) • RJfun (J 1) u v z) ∧
      PatternEv Rt ![M + 1, N + 1] ![0, ev 1] ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 → J 0 *ᵥ x ∈ Module.End.eigenspace (Rt.jacobiMap x) 0 ∧
        J 1 *ᵥ x ∈ Module.End.eigenspace (Rt.jacobiMap x) (ev 1) := by
  have h23 : ev 2 ≠ ev 3 := sec83_ne h
  obtain ⟨R1, hop1, hjac1, -, hpat1, hJ1⟩ := first_move hMove h J hJ hJe
  obtain ⟨hMN, hR, h0, -, -, -, -⟩ := h
  have hsum1 : ∑ i, (![M + 1, N, 0, 1] : Fin 4 → ℕ) i = 15 := by
    rcases hMN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Fin.sum_univ_succ]
  obtain ⟨Rt, hop, hjac, -, hm⟩ := hMove R1 _ ev hpat1 hsum1 (J 1) (hJ 1).1 (hJ 1).2 3 1 (by decide) hJ1
  refine ⟨Rt, fun u v z => by rw [hop, hop1],
    ⟨inj_comp hR.1 ![0, 1] (by decide) (by funext i; fin_cases i <;> simp [h0]), fun x hx i => ?_⟩,
    fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨-, b, c⟩ := hm x hx
    fin_cases i
    · simpa [h0] using c 0 (by decide) (by decide)
    · simpa using b
  · rw [mem_eig_iff, hjac, Matrix.sub_mulVec, hjac1, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Rem72a.jfam_mulVec, Rem72a.jfam_mulVec, (lin_eig hJe.1 x).1, orth_norm (hJ 0).2, lin_orth h23.symm hJe.2 hJe.1 x,
      hx]
    simp
  · rw [mem_eig_iff, hjac, Matrix.sub_mulVec, Matrix.smul_mulVec, Rem72a.jfam_mulVec, (lin_eig hJ1 x).1,
      orth_norm (hJ 1).2, hx]
    module

/-- Row `s8_3_restore_two`. -/
theorem s8_3_restore_two_proved (hMove : MoveHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P)
    (J : Fin 2 → Matrix (Fin 16) (Fin 16) ℝ) (hJ : ∀ i, (J i)ᵀ = -J i ∧ (J i)ᵀ * J i = 1)
    (hJe : IsEigenfield R (ev 2) (linP (J 0)) ∧ IsEigenfield R (ev 3) (linP (J 1))) (Rt : CurvTensor 16)
    (hRt : ∀ u v z, Rt.op u v z = R.op u v z - ev 2 • RJfun (J 0) u v z - (ev 3 - ev 1) • RJfun (J 1) u v z)
    (hC : Rt.IsClifford) :
    ∃ R1 : CurvTensor 16, (∀ u v z, R1.op u v z = R.op u v z - ev 2 • RJfun (J 0) u v z) ∧
      PatternEv R1 ![M + 1, N, 1] ![0, ev 1, ev 3] ∧ R1.IsClifford ∧ R.IsClifford := by
  obtain ⟨R1, hop1, -, hO1, hpat1, -⟩ := first_move hMove h J hJ hJe
  obtain ⟨hMN, hR, h0, -, -, -, -⟩ := h
  obtain ⟨hsum, -⟩ := pattern_facts hMN
  have hO : R.IsOsserman := (CorD.hasPattern_osserman_proved R ![M, N, 1, 1] (by rw [hsum]) ⟨ev, hR.1, hR.2⟩).1
  have h2 : ev 2 ≠ 0 := fun e => absurd (hR.1 (e.trans h0.symm)) (by decide)
  have h31 : ev 3 - ev 1 ≠ 0 := fun e => absurd (hR.1 (sub_eq_zero.mp e)) (by decide)
  have hC1 : R1.IsClifford :=
    Rem72c.lem_nik_3_2_1_proved R1 Rt (J 1) (hJ 1).1 (hJ 1).2 (ev 3 - ev 1) h31 (fun u v w => by rw [hRt, hop1])
      hO1 (clifford_osserman hC) hC
  refine ⟨R1, hop1, ⟨inj_comp hR.1 ![0, 1, 3] (by decide) (by funext i; fin_cases i <;> simp [h0]), fun x hx i => ?_⟩,
    hC1, Rem72c.lem_nik_3_2_1_proved R R1 (J 0) (hJ 0).1 (hJ 0).2 (ev 2) h2 hop1 hO hO1 hC1⟩
  fin_cases i
  · simpa [h0] using hpat1.2 x hx 0
  · simpa using hpat1.2 x hx 1
  · simpa using hpat1.2 x hx 3

/-- Row `s8_3_linear_case`. -/
theorem s8_3_linear_case_proved (hdiv : DivQHyp) (hMove : MoveHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P) (hq : ∀ i j, sqP 16 ∣ P i j) :
    R.IsClifford := by
  obtain ⟨J, hJ, -, hJe0, hJe1⟩ := s8_3_linear_fields_proved hdiv R M N ev P h hq
  obtain ⟨Rt, hRt, hpat, hfield⟩ := s8_3_move_both_proved hMove R M N ev P h J hJ ⟨hJe0, hJe1⟩
  have hC : Rt.IsClifford := by
    rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact s8_3_endpoint_87_proved Rt (ev 1) hpat (J 0) (hJ 0).1 (hJ 0).2 fun x hx => (hfield x hx).1
    · exact s8_prop21_uses_proved Rt (Or.inl ⟨_, hpat.1, hpat.2⟩)
  obtain ⟨-, -, -, -, hRC⟩ := s8_3_restore_two_proved hMove R M N ev P h J hJ ⟨hJe0, hJe1⟩ Rt hRt hC
  exact hRC

end Osserman.Proofs.S83
