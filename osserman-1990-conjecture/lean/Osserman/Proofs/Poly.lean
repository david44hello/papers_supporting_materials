/-
Osserman/Proofs/Poly.lean — proofs of the polynomial facts of paper 013 (Δs², homogeneity, |∇F_P|², Δ F_P,
U-absorption, traceless Clifford matrices).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.Poly

namespace Osserman.Proofs.Poly

open Osserman Matrix MvPolynomial

variable {N : ℕ}

/-! ### Basic derivatives -/

/-- `linP M a = (Mz)_a = ∑_b M_ab z_b` as a polynomial. -/
noncomputable def linP (M : Matrix (Fin N) (Fin N) ℝ) (a : Fin N) : MvPolynomial (Fin N) ℝ :=
  ∑ b, C (M a b) * X b

lemma pderiv_sqP (i : Fin N) : pderiv i (sqP N) = 2 * X i := by
  classical
  simp [sqP, map_sum, Pi.single_apply]

lemma pderiv_linP (M : Matrix (Fin N) (Fin N) ℝ) (i a : Fin N) : pderiv i (linP M a) = C (M a i) := by
  classical
  simp [linP, map_sum, Pi.single_apply]

lemma pderiv_quadP (M : Matrix (Fin N) (Fin N) ℝ) (hM : Mᵀ = M) (i : Fin N) :
    pderiv i (quadP M) = 2 * linP M i := by
  classical
  have hsym : ∀ a, M a i = M i a := fun a => by
    simpa using congrFun (congrFun hM i) a
  simp only [quadP, linP, map_sum, pderiv_mul, pderiv_X, pderiv_C, Pi.single_apply]
  simp only [zero_mul, zero_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [two_mul]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [eq_comm]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [hsym, mul_comm]

/-! ### Algebra of `quadP` and `linP` -/

lemma quadP_add (M M' : Matrix (Fin N) (Fin N) ℝ) : quadP (M + M') = quadP M + quadP M' := by
  simp only [quadP, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]

lemma quadP_neg (M : Matrix (Fin N) (Fin N) ℝ) : quadP (-M) = -quadP M := by
  simp only [quadP, Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

lemma quadP_zero : quadP (0 : Matrix (Fin N) (Fin N) ℝ) = 0 := by
  simp [quadP]

lemma quadP_one : quadP (1 : Matrix (Fin N) (Fin N) ℝ) = sqP N := by
  classical
  simp only [quadP, sqP, one_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [apply_ite C, ite_mul, Finset.sum_ite_eq, sq]

lemma quadP_transpose (M : Matrix (Fin N) (Fin N) ℝ) : quadP Mᵀ = quadP M := by
  simp only [quadP, transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma sum_X_mul_linP (M : Matrix (Fin N) (Fin N) ℝ) : ∑ a, X a * linP M a = quadP M := by
  simp only [linP, quadP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma sum_linP_mul_linP (M M' : Matrix (Fin N) (Fin N) ℝ) (hM : Mᵀ = M) :
    ∑ a, linP M a * linP M' a = quadP (M * M') := by
  have hsym : ∀ a b, M a b = M b a := fun a b => by
    simpa using congrFun (congrFun hM b) a
  calc ∑ a, linP M a * linP M' a = ∑ a, ∑ b, ∑ c, C (M b a * M' a c) * X b * X c := by
        simp only [linP, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => ?_
        rw [map_mul, hsym a b]
        ring
    _ = ∑ b, ∑ c, ∑ a, C (M b a * M' a c) * X b * X c := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = quadP (M * M') := by
        simp only [quadP, mul_apply, map_sum, Finset.sum_mul]

lemma pderiv_two_mul (i : Fin N) (f : MvPolynomial (Fin N) ℝ) : pderiv i (2 * f) = 2 * pderiv i f := by
  rw [two_mul, map_add, two_mul]

lemma pderiv_sq (i : Fin N) (f : MvPolynomial (Fin N) ℝ) : pderiv i (f ^ 2) = 2 * f * pderiv i f := by
  rw [sq, pderiv_mul]
  ring

/-! ### Symmetric Clifford systems -/

lemma quadP_mul_comm (A B : Matrix (Fin N) (Fin N) ℝ) (hA : Aᵀ = A) (hB : Bᵀ = B) :
    quadP (B * A) = quadP (A * B) := by
  rw [← quadP_transpose (A * B), transpose_mul, hA, hB]

lemma quadP_two : quadP (2 : Matrix (Fin N) (Fin N) ℝ) = 2 * sqP N := by
  rw [show (2 : Matrix (Fin N) (Fin N) ℝ) = 1 + 1 from one_add_one_eq_two.symm, quadP_add, quadP_one, two_mul]

/-- `⟨P_iP_jz, z⟩ = δ_ij |z|²` for a symmetric Clifford system. -/
lemma quadP_clifford {k : ℕ} (P : Fin k → Matrix (Fin N) (Fin N) ℝ) (hP : IsSymmCliffordSystem P) (i j : Fin k) :
    quadP (P i * P j) = if i = j then sqP N else 0 := by
  have h2 : 2 * quadP (P i * P j) = quadP (P i * P j + P j * P i) := by
    rw [quadP_add, quadP_mul_comm _ _ (hP.1 i) (hP.1 j), two_mul]
  rw [hP.2 i j] at h2
  have h20 : (2 : MvPolynomial (Fin N) ℝ) ≠ 0 := two_ne_zero
  split_ifs at h2 ⊢ with hij
  · rw [quadP_two] at h2
    exact mul_left_cancel₀ h20 h2
  · rw [quadP_zero] at h2
    exact (mul_eq_zero.mp h2).resolve_left h20

/-! ### Gradients and Laplacians -/

lemma gradSqP_sqP : gradSqP (sqP N) = 4 * sqP N := by
  simp only [gradSqP, pderiv_sqP]
  simp only [sqP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

lemma gradSqP_quadP (M : Matrix (Fin N) (Fin N) ℝ) (hM : Mᵀ = M) : gradSqP (quadP M) = 4 * quadP (M * M) := by
  rw [← sum_linP_mul_linP M M hM, gradSqP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pderiv_quadP M hM]
  ring

lemma lapP_sub (f g : MvPolynomial (Fin N) ℝ) : lapP (f - g) = lapP f - lapP g := by
  simp only [lapP, map_sub, Finset.sum_sub_distrib]

lemma lapP_two_mul (f : MvPolynomial (Fin N) ℝ) : lapP (2 * f) = 2 * lapP f := by
  simp only [lapP, pderiv_two_mul, Finset.mul_sum]

lemma lapP_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin N) ℝ) :
    lapP (∑ j ∈ s, f j) = ∑ j ∈ s, lapP (f j) := by
  simp only [lapP, map_sum]
  exact Finset.sum_comm

lemma pderiv_pderiv_sq (i : Fin N) (f : MvPolynomial (Fin N) ℝ) :
    pderiv i (pderiv i (f ^ 2)) = 2 * pderiv i f ^ 2 + 2 * f * pderiv i (pderiv i f) := by
  rw [pderiv_sq, mul_assoc, pderiv_two_mul, pderiv_mul]
  ring

/-- `Δ(f²) = 2fΔf + 2|∇f|²`. -/
lemma lapP_sq (f : MvPolynomial (Fin N) ℝ) : lapP (f ^ 2) = 2 * f * lapP f + 2 * gradSqP f := by
  simp only [lapP, gradSqP, pderiv_pderiv_sq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

lemma lapP_sqP : lapP (sqP N) = 2 * (N : MvPolynomial (Fin N) ℝ) := by
  simp only [lapP, pderiv_sqP, pderiv_two_mul, pderiv_X_self, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

lemma lapP_quadP (M : Matrix (Fin N) (Fin N) ℝ) (hM : Mᵀ = M) : lapP (quadP M) = 2 * C M.trace := by
  simp only [lapP, pderiv_quadP M hM, pderiv_two_mul, pderiv_linP, Matrix.trace, diag_apply, map_sum,
    Finset.mul_sum]

/-! ### (1) `Δ s² = 136 s` on `ℝ^32` -/

lemma lapP_sqP_sq : lapP (sqP N ^ 2) = 4 * ((N : MvPolynomial (Fin N) ℝ) + 2) * sqP N := by
  rw [lapP_sq, lapP_sqP, gradSqP_sqP]
  ring

theorem lem_2_1_lap_s2_proved : lapP (sqP 32 ^ 2) = 136 * sqP 32 := by
  rw [lapP_sqP_sq]
  norm_num

/-! ### (5) traceless -/

lemma sq_eq_one_of_clifford {k : ℕ} (P : Fin k → Matrix (Fin N) (Fin N) ℝ) (hP : IsSymmCliffordSystem P)
    (j : Fin k) : P j * P j = 1 := by
  have h := hP.2 j j
  rw [ite_eq_left rfl] at h
  have h' : (2 : ℝ) • (P j * P j) = (2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
    rw [two_smul, two_smul, h, one_add_one_eq_two]
  exact smul_right_injective _ two_ne_zero h'

lemma trace_eq_zero_of_ne {k : ℕ} (P : Fin k → Matrix (Fin N) (Fin N) ℝ) (hP : IsSymmCliffordSystem P)
    (i j : Fin k) (hij : i ≠ j) : (P i).trace = 0 := by
  have hanti : P j * P i = -(P i * P j) := by
    have h := hP.2 i j
    rw [ite_eq_right hij] at h
    exact eq_neg_of_add_eq_zero_right h
  have hjj := sq_eq_one_of_clifford P hP j
  have hcyc : (P j * P i * P j).trace = (P i).trace := by
    rw [Matrix.trace_mul_cycle, hjj, Matrix.one_mul]
  have hneg : P j * P i * P j = -P i := by
    rw [hanti, Matrix.neg_mul, Matrix.mul_assoc, hjj, Matrix.mul_one]
  rw [hneg, Matrix.trace_neg] at hcyc
  linarith

theorem trace_eq_zero_proved {N : ℕ} (m : ℕ) (hm : 1 ≤ m) (P : Fin (m + 1) → Matrix (Fin N) (Fin N) ℝ)
    (hP : IsSymmCliffordSystem P) : ∀ i, (P i).trace = 0 := by
  intro i
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨j, hj⟩ := exists_ne i
  exact trace_eq_zero_of_ne P hP i j hj.symm

/-! ### (6) `Δ F_P = (136 - 16(m+1)) s` on `ℝ^32` -/

lemma lapP_quadP_sq_clifford {k : ℕ} (P : Fin k → Matrix (Fin N) (Fin N) ℝ) (hP : IsSymmCliffordSystem P)
    (i : Fin k) (htr : (P i).trace = 0) : lapP (quadP (P i) ^ 2) = 8 * sqP N := by
  rw [lapP_sq, lapP_quadP _ (hP.1 i), htr, map_zero, gradSqP_quadP _ (hP.1 i), quadP_clifford P hP i i,
    ite_eq_left rfl]
  ring

theorem sec3_lap_FKM_proved (m : ℕ) (hm : 1 ≤ m) (P : Fin (m + 1) → Matrix (Fin 32) (Fin 32) ℝ)
    (hP : IsSymmCliffordSystem P) : lapP (FKMP P) = C (136 - 16 * ((m : ℝ) + 1)) * sqP 32 := by
  have htr := trace_eq_zero_proved m hm P hP
  rw [FKMP, lapP_sub, lapP_two_mul, lapP_sum, lem_2_1_lap_s2_proved]
  simp only [fun i => lapP_quadP_sq_clifford P hP i (htr i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, map_sub, map_mul, map_add, map_natCast, map_one, map_ofNat]
  push_cast
  ring

/-! ### (2) homogeneity -/

lemma sqP_isHomogeneous : (sqP N).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i 2

lemma quadP_isHomogeneous (M : Matrix (Fin N) (Fin N) ℝ) : (quadP M).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ =>
    (isHomogeneous_C_mul_X (M a b) a).mul (isHomogeneous_X ℝ b)

theorem FKMP_homogeneous_proved {N k : ℕ} (P : Fin k → Matrix (Fin N) (Fin N) ℝ) : (FKMP P).IsHomogeneous 4 := by
  have hsum : (∑ i, quadP (P i) ^ 2).IsHomogeneous 4 :=
    IsHomogeneous.sum _ _ _ fun i _ => (quadP_isHomogeneous (P i)).pow 2
  rw [FKMP, two_mul]
  exact (sqP_isHomogeneous.pow 2).sub (hsum.add hsum)

/-! ### (4) absorbing an orthogonal `U` -/

lemma eval_sqP (z : Fin N → ℝ) : eval z (sqP N) = z ⬝ᵥ z := by
  simp [sqP, dotProduct, sq]

lemma eval_quadP (M : Matrix (Fin N) (Fin N) ℝ) (z : Fin N → ℝ) : eval z (quadP M) = z ⬝ᵥ (M *ᵥ z) := by
  simp only [quadP, map_sum, map_mul, eval_C, eval_X, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma mulVec_dotProduct_eq (U : Matrix (Fin N) (Fin N) ℝ) (x y : Fin N → ℝ) :
    (U *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Uᵀ *ᵥ y) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

lemma eval_quadP_mulVec (M U : Matrix (Fin N) (Fin N) ℝ) (z : Fin N → ℝ) :
    eval (U *ᵥ z) (quadP M) = eval z (quadP (Uᵀ * M * U)) := by
  rw [eval_quadP, eval_quadP, mulVec_dotProduct_eq, mulVec_mulVec, mulVec_mulVec]

lemma eval_sqP_mulVec (U : Matrix (Fin N) (Fin N) ℝ) (hU : Uᵀ * U = 1) (z : Fin N → ℝ) :
    eval (U *ᵥ z) (sqP N) = eval z (sqP N) := by
  rw [← quadP_one, eval_quadP_mulVec, Matrix.mul_one, hU]

lemma conj_mul_conj (A B U : Matrix (Fin N) (Fin N) ℝ) (hU : U * Uᵀ = 1) :
    Uᵀ * A * U * (Uᵀ * B * U) = Uᵀ * (A * B) * U := by
  calc Uᵀ * A * U * (Uᵀ * B * U) = Uᵀ * A * (U * Uᵀ) * B * U := by simp only [Matrix.mul_assoc]
    _ = Uᵀ * (A * B) * U := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma conj_two (U : Matrix (Fin N) (Fin N) ℝ) (hU : Uᵀ * U = 1) : Uᵀ * (2 : Matrix (Fin N) (Fin N) ℝ) * U = 2 := by
  rw [show (2 : Matrix (Fin N) (Fin N) ℝ) = 1 + 1 from one_add_one_eq_two.symm, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, hU]

theorem sec3_absorb_U_proved {N k : ℕ} (P : Fin k → Matrix (Fin N) (Fin N) ℝ) (hP : IsSymmCliffordSystem P)
    (U : Matrix (Fin N) (Fin N) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin N) ℝ) :
    IsSymmCliffordSystem (fun i => Uᵀ * P i * U) ∧
      ∀ z, eval (U *ᵥ z) (FKMP P) = eval z (FKMP (fun i => Uᵀ * P i * U)) := by
  have hUU : U * Uᵀ = 1 := (mem_orthogonalGroup_iff (Fin N) ℝ).mp hU
  have hUU' : Uᵀ * U = 1 := (mem_orthogonalGroup_iff' (Fin N) ℝ).mp hU
  refine ⟨⟨fun i => ?_, fun i j => ?_⟩, fun z => ?_⟩
  · simp only [transpose_mul, transpose_transpose, hP.1 i, Matrix.mul_assoc]
  · simp only [conj_mul_conj _ _ U hUU, ← Matrix.add_mul, ← Matrix.mul_add, hP.2 i j]
    split_ifs
    · exact conj_two U hUU'
    · simp
  · simp only [FKMP, map_sub, map_mul, map_pow, map_sum, map_ofNat, eval_sqP_mulVec U hUU', eval_quadP_mulVec]

/-! ### (3) `|∇F_P|² = 16 s³` -/

/-- `∂_a F_P = 4 s z_a - 8 ∑_i ⟨P_iz,z⟩ (P_iz)_a`. -/
lemma pderiv_FKMP {k : ℕ} (P : Fin k → Matrix (Fin N) (Fin N) ℝ) (hP : IsSymmCliffordSystem P) (a : Fin N) :
    pderiv a (FKMP P) = 4 * sqP N * X a - 8 * ∑ i, quadP (P i) * linP (P i) a := by
  have hq : ∑ i, pderiv a (quadP (P i) ^ 2) = 4 * ∑ i, quadP (P i) * linP (P i) a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pderiv_sq, pderiv_quadP _ (hP.1 i)]
    ring
  rw [FKMP, map_sub, pderiv_two_mul, map_sum, hq, pderiv_sq, pderiv_sqP]
  ring

lemma gradSq_FKM_term1 : ∑ a : Fin N, (4 * sqP N * X a) ^ 2 = 16 * sqP N ^ 3 := by
  calc ∑ a : Fin N, (4 * sqP N * X a) ^ 2 = 16 * sqP N ^ 2 * ∑ a, X a ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = 16 * sqP N ^ 3 := by
        rw [show ∑ a : Fin N, (X a : MvPolynomial (Fin N) ℝ) ^ 2 = sqP N from rfl]
        ring

lemma gradSq_FKM_term2 {k : ℕ} (P : Fin k → Matrix (Fin N) (Fin N) ℝ) :
    ∑ a, 4 * sqP N * X a * (8 * ∑ i, quadP (P i) * linP (P i) a) =
      32 * sqP N * ∑ i, quadP (P i) ^ 2 := by
  calc ∑ a, 4 * sqP N * X a * (8 * ∑ i, quadP (P i) * linP (P i) a)
        = ∑ a, ∑ i, 32 * sqP N * quadP (P i) * (X a * linP (P i) a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, ∑ a, 32 * sqP N * quadP (P i) * (X a * linP (P i) a) := Finset.sum_comm
    _ = ∑ i, 32 * sqP N * quadP (P i) * quadP (P i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, sum_X_mul_linP]
    _ = 32 * sqP N * ∑ i, quadP (P i) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

lemma gradSq_FKM_term3 {k : ℕ} (P : Fin k → Matrix (Fin N) (Fin N) ℝ) (hP : IsSymmCliffordSystem P) :
    ∑ a, (8 * ∑ i, quadP (P i) * linP (P i) a) ^ 2 = 64 * sqP N * ∑ i, quadP (P i) ^ 2 := by
  calc ∑ a, (8 * ∑ i, quadP (P i) * linP (P i) a) ^ 2
        = ∑ a, ∑ i, ∑ j, 64 * (quadP (P i) * quadP (P j)) * (linP (P i) a * linP (P j) a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_pow, sq (∑ i, _), Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, ∑ j, 64 * (quadP (P i) * quadP (P j)) * ∑ a, linP (P i) a * linP (P j) a := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, 64 * (quadP (P i) * quadP (P j)) * (if i = j then sqP N else 0) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [sum_linP_mul_linP _ _ (hP.1 i), quadP_clifford P hP i j]
    _ = ∑ i, 64 * (quadP (P i) * quadP (P i)) * sqP N := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    _ = 64 * sqP N * ∑ i, quadP (P i) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

theorem gradSq_FKM_proved {N k : ℕ} (P : Fin k → Matrix (Fin N) (Fin N) ℝ) (hP : IsSymmCliffordSystem P) :
    gradSqP (FKMP P) = 16 * sqP N ^ 3 := by
  have hexp : gradSqP (FKMP P) = ∑ a, (4 * sqP N * X a) ^ 2 -
      2 * ∑ a, 4 * sqP N * X a * (8 * ∑ i, quadP (P i) * linP (P i) a) +
      ∑ a, (8 * ∑ i, quadP (P i) * linP (P i) a) ^ 2 := by
    rw [gradSqP, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pderiv_FKMP P hP a]
    ring
  rw [hexp, gradSq_FKM_term1, gradSq_FKM_term2, gradSq_FKM_term3 P hP]
  ring

end Osserman.Proofs.Poly
