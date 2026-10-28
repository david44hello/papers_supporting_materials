/-
Osserman/Proofs/Rem72c.lean — Remark 7.2 of paper 013, third part, and Nikolayevsky's Lemma 3.2(1): the residual
`J_{ν+1} = J - ∑ d_αJ_α`, the bound `c_0 = 0` for `ν = 8`, the extension to a `Cl(ν+1)`-structure, the
diagonalization, the normalized conclusion, the normalization and the lemma itself (rows rem_7_2_residual,
rem_7_2_nu8_c0, rem_7_2_extend, rem_7_2_diagonalize, rem_7_2_normalized, rem_7_2_normalize, lem_nik_3_2_1;
statements copied verbatim from Osserman/Paper/Statements7.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof. With `⟨J_αx, Jx⟩ = d_α|x|²` (row rem_7_2_inner_const), `K = J - ∑ d_αJ_α` has `Kx ⊥ J_αx`, so `KᵀJ_α` is
skew, i.e. `KJ_α + J_αK = 0`; and `|Kx|² = (1 - ∑ d_α²)|x|²`, so `KᵀK = c_0²I`. If `c_0 ≠ 0`, `c_0⁻¹K, J_1, …, J_ν`
is a `Cl(ν+1)`-structure (so `ν ≤ 7` by Hurwitz–Radon); if `c_0 = 0`, `K = 0`. In both cases `Jx = ∑_i γ_iJ'_ix` for
a Clifford structure `J'` and `J_x(R) = ∑_{i,j} S_ij(J'_ix)(J'_jx)ᵀ` with `S = diag(μ', 0) + cγγᵀ` symmetric. The
spectral theorem writes `S = Oᵀdiag(η)O` with `O` orthogonal, and `J''_a = ∑_i O_aiJ'_i` is again Clifford with
`J_x(R) = ∑ η_a(J''_ax)(J''_ax)ᵀ`. This needs no rotation inside the blocks (row rem_7_2_rotate is not used).
-/
import Osserman.Proofs.Rem72b

namespace Osserman.Proofs.Rem72c

open Osserman Matrix
open Osserman.Proofs.Rem72a Osserman.Proofs.Rem72b

variable {n : ℕ}

/-! ### Matrices from their quadratic forms -/

lemma transpose_eq_neg_of_dot {M : Matrix (Fin n) (Fin n) ℝ} (h : ∀ x : Vec n, x ⬝ᵥ (M *ᵥ x) = 0) : Mᵀ = -M := by
  have hb : ∀ x y : Vec n, x ⬝ᵥ (M *ᵥ y) + y ⬝ᵥ (M *ᵥ x) = 0 := fun x y => by
    have e := h (x + y)
    rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, h x, h y] at e
    linarith
  ext i j
  have e := hb (Pi.single j 1) (Pi.single i 1)
  simp only [mulVec_single, single_dotProduct, one_mul, op_smul_eq_smul, one_smul, col_apply] at e
  rw [transpose_apply, Matrix.neg_apply]
  linarith

lemma eq_of_dot_eq {A B : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : ∀ x : Vec n, x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (B *ᵥ x)) : A = B := by
  have hs := transpose_eq_neg_of_dot (M := A - B) fun x => by rw [sub_mulVec, dotProduct_sub, h, sub_self]
  rw [transpose_sub, hA, hB] at hs
  ext i j
  have e := congrFun (congrFun hs i) j
  simp only [Matrix.sub_apply, Matrix.neg_apply] at e
  linarith

lemma mat_eq_zero_of_dot {K : Matrix (Fin n) (Fin n) ℝ} (h : ∀ x : Vec n, (K *ᵥ x) ⬝ᵥ (K *ᵥ x) = 0) : K = 0 :=
  Matrix.ext_iff_mulVec.2 fun x => by
    rw [zero_mulVec]
    exact dotProduct_self_eq_zero.1 (h x)

/-! ### The residual `K = J - ∑ d_αJ_α` -/

section Resid

variable {J : Matrix (Fin 16) (Fin 16) ℝ} {ν : ℕ} {Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ} {d : Fin ν → ℝ}

lemma resid_mulVec (x : Vec 16) : resid J Jα d *ᵥ x = J *ᵥ x - ∑ α, d α • (Jα α *ᵥ x) := by
  rw [resid, sub_mulVec, comb_mulVec]

lemma resid_transpose (hJs : Jᵀ = -J) (hJ : IsCliffordStr Jα) : (resid J Jα d)ᵀ = -resid J Jα d := by
  rw [resid, transpose_sub, transpose_sum, hJs]
  simp only [transpose_smul, hJ.1, smul_neg, Finset.sum_neg_distrib]
  abel

lemma comb_dot (hJ : IsCliffordStr Jα) (x : Vec 16) (α : Fin ν) :
    (∑ β, d β • (Jα β *ᵥ x)) ⬝ᵥ (Jα α *ᵥ x) = d α * (x ⬝ᵥ x) := by
  rw [dotProduct_comm, dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul, cliff_dot hJ, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

lemma resid_dot (hJ : IsCliffordStr Jα) (hd : ∀ α x, (Jα α *ᵥ x) ⬝ᵥ (J *ᵥ x) = d α * (x ⬝ᵥ x)) (α : Fin ν)
    (x : Vec 16) : (resid J Jα d *ᵥ x) ⬝ᵥ (Jα α *ᵥ x) = 0 := by
  rw [resid_mulVec, sub_dotProduct, dotProduct_comm (J *ᵥ x), hd, comb_dot hJ, sub_self]

lemma resid_anticomm (hJs : Jᵀ = -J) (hJ : IsCliffordStr Jα)
    (hd : ∀ α x, (Jα α *ᵥ x) ⬝ᵥ (J *ᵥ x) = d α * (x ⬝ᵥ x)) (α : Fin ν) :
    resid J Jα d * Jα α + Jα α * resid J Jα d = 0 := by
  have h0 : ∀ x : Vec 16, x ⬝ᵥ (((resid J Jα d)ᵀ * Jα α) *ᵥ x) = 0 := fun x => by
    rw [dot_transpose_mul, resid_dot hJ hd α x]
  have hs := transpose_eq_neg_of_dot h0
  rw [transpose_mul, transpose_transpose, hJ.1 α, resid_transpose hJs hJ, neg_mul, neg_mul, neg_neg] at hs
  rw [← hs]
  abel

lemma resid_norm (hJo : Jᵀ * J = 1) (hJ : IsCliffordStr Jα)
    (hd : ∀ α x, (Jα α *ᵥ x) ⬝ᵥ (J *ᵥ x) = d α * (x ⬝ᵥ x)) (x : Vec 16) :
    (resid J Jα d *ᵥ x) ⬝ᵥ (resid J Jα d *ᵥ x) = (1 - ∑ α, d α ^ 2) * (x ⬝ᵥ x) := by
  have hJJ : (J *ᵥ x) ⬝ᵥ (J *ᵥ x) = x ⬝ᵥ x := by rw [← dot_transpose_mul, hJo, one_mulVec]
  have h1 : (resid J Jα d *ᵥ x) ⬝ᵥ (resid J Jα d *ᵥ x) = (resid J Jα d *ᵥ x) ⬝ᵥ (J *ᵥ x) := by
    conv_lhs => arg 2; rw [resid_mulVec]
    rw [dotProduct_sub, dotProduct_sum]
    simp only [dotProduct_smul, resid_dot hJ hd, smul_zero, Finset.sum_const_zero, sub_zero]
  have h2 : (∑ β, d β • (Jα β *ᵥ x)) ⬝ᵥ (J *ᵥ x) = (∑ β, d β ^ 2) * (x ⬝ᵥ x) := by
    rw [dotProduct_comm, dotProduct_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [dotProduct_smul, smul_eq_mul, dotProduct_comm, hd]
    ring
  rw [h1, resid_mulVec, sub_dotProduct, hJJ, h2]
  ring

lemma resid_coeff_nonneg (hJo : Jᵀ * J = 1) (hJ : IsCliffordStr Jα)
    (hd : ∀ α x, (Jα α *ᵥ x) ⬝ᵥ (J *ᵥ x) = d α * (x ⬝ᵥ x)) : 0 ≤ 1 - ∑ α, d α ^ 2 := by
  obtain ⟨-, e0, he0, -⟩ := Spectral.exists_unit_scale 0
  have h := resid_norm hJo hJ hd e0
  rw [he0, mul_one] at h
  rw [← h]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- `c_0⁻¹K, J_1, …, J_ν` is a `Cl(ν+1)`-structure when `c_0² = 1 - ∑ d_α² ≠ 0`. -/
lemma extend_clifford (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1) (hJ : IsCliffordStr Jα)
    (hd : ∀ α x, (Jα α *ᵥ x) ⬝ᵥ (J *ᵥ x) = d α * (x ⬝ᵥ x)) {c0 : ℝ} (hc0 : c0 ≠ 0)
    (hc0sq : c0 ^ 2 = 1 - ∑ α, d α ^ 2) : IsCliffordStr (vecCons (c0⁻¹ • resid J Jα d) Jα) := by
  have hKtK : (resid J Jα d)ᵀ * resid J Jα d = (1 - ∑ α, d α ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℝ) :=
    eq_of_dot_eq (by rw [transpose_mul, transpose_transpose]) (by rw [transpose_smul, transpose_one])
      fun x => by
        rw [dot_transpose_mul, resid_norm hJo hJ hd, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  have hKK : resid J Jα d * resid J Jα d = -((1 - ∑ α, d α ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℝ)) := by
    rw [resid_transpose hJs hJ, neg_mul] at hKtK
    rw [← hKtK, neg_neg]
  have hsq : (c0⁻¹ • resid J Jα d) * (c0⁻¹ • resid J Jα d) = -1 := by
    rw [smul_mul_smul_comm, hKK, smul_neg, smul_smul, ← hc0sq]
    have e : c0⁻¹ * c0⁻¹ * c0 ^ 2 = 1 := by field_simp
    rw [e, one_smul]
  have hac : ∀ α, (c0⁻¹ • resid J Jα d) * Jα α + Jα α * (c0⁻¹ • resid J Jα d) = 0 := fun α => by
    rw [smul_mul_assoc, mul_smul_comm, ← smul_add, resid_anticomm hJs hJ hd, smul_zero]
  have hT : (c0⁻¹ • resid J Jα d)ᵀ = -(c0⁻¹ • resid J Jα d) := by
    rw [transpose_smul, resid_transpose hJs hJ, smul_neg]
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [cons_val_zero] using hT
    · simpa only [cons_val_succ] using hJ.1 i
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rw [cons_val_zero, hsq, ite_eq_left rfl, ← neg_add, one_add_one_eq_two]
    · rw [cons_val_zero, cons_val_succ, ite_eq_right (Fin.succ_ne_zero j).symm]
      exact hac j
    · rw [cons_val_zero, cons_val_succ, ite_eq_right (Fin.succ_ne_zero i), add_comm]
      exact hac i
    · rw [cons_val_succ, cons_val_succ, hJ.2 i j]
      by_cases hij : i = j
      · rw [ite_eq_left hij, ite_eq_left (congrArg Fin.succ hij)]
      · rw [ite_eq_right hij, ite_eq_right fun e => hij (Fin.succ_injective _ e)]

lemma extend_core (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1) (hJ : IsCliffordStr Jα)
    (hd : ∀ α x, (Jα α *ᵥ x) ⬝ᵥ (J *ᵥ x) = d α * (x ⬝ᵥ x)) :
    J = ∑ α, d α • Jα α + Real.sqrt (1 - ∑ α, d α ^ 2) • ((Real.sqrt (1 - ∑ α, d α ^ 2))⁻¹ • resid J Jα d) ∧
      (Real.sqrt (1 - ∑ α, d α ^ 2) ≠ 0 →
        IsCliffordStr (vecCons ((Real.sqrt (1 - ∑ α, d α ^ 2))⁻¹ • resid J Jα d) Jα)) := by
  have hs0 := resid_coeff_nonneg hJo hJ hd
  have hc0sq : Real.sqrt (1 - ∑ α, d α ^ 2) ^ 2 = 1 - ∑ α, d α ^ 2 := Real.sq_sqrt hs0
  refine ⟨?_, fun hc0 => extend_clifford hJs hJo hJ hd hc0 hc0sq⟩
  by_cases hc0 : Real.sqrt (1 - ∑ α, d α ^ 2) = 0
  · have hs : 1 - ∑ α, d α ^ 2 = 0 := by
      rw [hc0, zero_pow two_ne_zero] at hc0sq
      exact hc0sq.symm
    have hK : resid J Jα d = 0 := mat_eq_zero_of_dot fun x => by rw [resid_norm hJo hJ hd, hs, zero_mul]
    rw [hc0, zero_smul, add_zero]
    rw [resid, sub_eq_zero] at hK
    exact hK
  · rw [smul_smul, mul_inv_cancel₀ hc0, one_smul, resid]
    abel

end Resid

variable {R R' : CurvTensor 16} {J : Matrix (Fin 16) (Fin 16) ℝ} {c : ℝ} {ν : ℕ}
  {Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ} {μ : Fin ν → ℝ} {d : Fin ν → ℝ}

/-- **Row rem_7_2_residual.** -/
theorem rem_7_2_residual_proved (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (d : Fin ν → ℝ) (h : Rem72Rot R R' J c Jα μ d) :
    let K := resid J Jα d
    Kᵀ = -K ∧ (∀ α, K * Jα α + Jα α * K = 0) ∧ (∀ α (x : Vec 16), (K *ᵥ x) ⬝ᵥ (Jα α *ᵥ x) = 0) ∧
      (∀ x : Vec 16, x ⬝ᵥ (K *ᵥ x) = 0) ∧ 0 ≤ 1 - ∑ α, d α ^ 2 ∧
      ∀ x : Vec 16, (K *ᵥ x) ⬝ᵥ (K *ᵥ x) = (1 - ∑ α, d α ^ 2) * (x ⬝ᵥ x) := by
  intro K
  obtain ⟨⟨hJs, hJo, -, -, -, -, hJ, -, -⟩, hd, -⟩ := h
  exact ⟨resid_transpose hJs hJ, resid_anticomm hJs hJ hd, resid_dot hJ hd,
    fun x => skew_dot_self (resid_transpose hJs hJ) x, resid_coeff_nonneg hJo hJ hd, resid_norm hJo hJ hd⟩

/-- **Row rem_7_2_nu8_c0.** -/
theorem rem_7_2_nu8_c0_proved (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (d : Fin ν → ℝ) (h : Rem72Rot R R' J c Jα μ d)
    (hν : ν = 8) : resid J Jα d = 0 := by
  obtain ⟨⟨hJs, hJo, -, -, -, -, hJ, -, -⟩, hd, -⟩ := h
  have hs0 := resid_coeff_nonneg hJo hJ hd
  by_cases hc0 : Real.sqrt (1 - ∑ α, d α ^ 2) = 0
  · have hs : 1 - ∑ α, d α ^ 2 = 0 := by
      have e := Real.sq_sqrt hs0
      rw [hc0, zero_pow two_ne_zero] at e
      exact e.symm
    exact mat_eq_zero_of_dot fun x => by rw [resid_norm hJo hJ hd, hs, zero_mul]
  · have hcl := extend_clifford hJs hJo hJ hd hc0 (Real.sq_sqrt hs0)
    have h9 := HurwitzRadon.rem_7_2_nu_le_8_proved _ hcl
    omega

/-- **Row rem_7_2_extend.** -/
theorem rem_7_2_extend_proved (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (d : Fin ν → ℝ) (h : Rem72Rot R R' J c Jα μ d) :
    let K := resid J Jα d
    let c0 := Real.sqrt (1 - ∑ α, d α ^ 2)
    J = ∑ α, d α • Jα α + c0 • (c0⁻¹ • K) ∧ (c0 ≠ 0 → IsCliffordStr (vecCons (c0⁻¹ • K) Jα)) := by
  intro K c0
  obtain ⟨⟨hJs, hJo, -, -, -, -, hJ, -, -⟩, hd, -⟩ := h
  exact extend_core hJs hJo hJ hd

/-! ### Diagonalization -/

/-- A symmetric real matrix is `∑_a η_a O_aᵀO_a` (entrywise) for an orthogonal `O`. -/
lemma symm_decomp {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} (hS : Sᵀ = S) :
    ∃ (O : Matrix (Fin m) (Fin m) ℝ) (η : Fin m → ℝ), O ∈ Matrix.orthogonalGroup (Fin m) ℝ ∧
      ∀ β γ, S β γ = ∑ a, η a * (O a β * O a γ) := by
  have hH : S.IsHermitian := by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hS]
  set U : Matrix (Fin m) (Fin m) ℝ := ↑hH.eigenvectorUnitary
  have hspec : S = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    have h := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hspec hUU
  refine ⟨Uᵀ, hH.eigenvalues, ?_, fun β γ => ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff, transpose_transpose]
    exact hUU
  · conv_lhs => rw [hspec]
    rw [mul_apply]
    simp only [mul_diagonal, transpose_apply, Function.comp_apply, RCLike.ofReal_real_eq_id, id]
    exact Finset.sum_congr rfl fun a _ => by ring

lemma diag_clifford {m : ℕ} {Je : Fin m → Matrix (Fin 16) (Fin 16) ℝ} (hJe : IsCliffordStr Je)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : Sᵀ = S) {R : CurvTensor 16}
    (hR : ∀ x, R.jacobi x = ∑ β, ∑ γ, S β γ • vecMulVec (Je β *ᵥ x) (Je γ *ᵥ x)) :
    ∃ (J'' : Fin m → Matrix (Fin 16) (Fin 16) ℝ) (η : Fin m → ℝ), IsCliffordStr J'' ∧
      ∀ x, R.jacobi x = ∑ a, η a • jfam (J'' a) x := by
  obtain ⟨O, η, hO, hSO⟩ := symm_decomp hS
  refine ⟨fun a => ∑ β, O a β • Je β, η, cliffordStr_orth_comb_proved Je hJe O hO, fun x => ?_⟩
  rw [hR x]
  simp only [jfam, comb_mulVec]
  refine Eq.symm ((sum_smul_vecMulVec_comb η (fun a β => O a β) (fun β => Je β *ᵥ x)).trans ?_)
  simp only [hSO]

lemma diag_form {m : ℕ} {Je : Fin m → Matrix (Fin 16) (Fin 16) ℝ} (hJe : IsCliffordStr Je) (μe de : Fin m → ℝ)
    (c : ℝ) {R : CurvTensor 16}
    (hR : ∀ x, R.jacobi x = ∑ i, μe i • jfam (Je i) x + c • jfam (∑ i, de i • Je i) x) :
    ∃ (J'' : Fin m → Matrix (Fin 16) (Fin 16) ℝ) (η : Fin m → ℝ), IsCliffordStr J'' ∧
      ∀ x, R.jacobi x = ∑ a, η a • jfam (J'' a) x := by
  refine diag_clifford hJe (S := diagonal μe + c • vecMulVec de de) ?_ fun x => ?_
  · rw [transpose_add, diagonal_transpose, transpose_smul, transpose_vecMulVec]
  · rw [hR x]
    have h1 := sum_smul_vecMulVec_comb (m := 1) (fun _ => c) (fun _ => de) (fun β => Je β *ᵥ x)
    simp only [Fin.sum_univ_one] at h1
    simp only [jfam, comb_mulVec, h1]
    simp only [Matrix.add_apply, diagonal_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, add_smul,
      Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

lemma diagonalize_core (h : Rem72Hyp R R' J c Jα μ) (hd : ∀ α x, (Jα α *ᵥ x) ⬝ᵥ (J *ᵥ x) = d α * (x ⬝ᵥ x)) :
    ∃ (ν' : ℕ) (J'' : Fin ν' → Matrix (Fin 16) (Fin 16) ℝ) (η : Fin ν' → ℝ), IsCliffordStr J'' ∧
      (ν' = ν ∨ ν' = ν + 1) ∧ ∀ x : Vec 16, R.jacobi x = ∑ a, η a • jfam (J'' a) x := by
  obtain ⟨hJs, hJo, -, hR', -, -, hJ, -, hjac⟩ := h
  have hRj : ∀ x, R.jacobi x = ∑ α, μ α • jfam (Jα α) x + c • jfam J x := fun x => by
    rw [(rem_7_2_jac_split_proved R R' J hJs c hR' x).1, hjac x]
  obtain ⟨hJeq, hcl⟩ := extend_core hJs hJo hJ hd
  by_cases hc0 : Real.sqrt (1 - ∑ α, d α ^ 2) = 0
  · rw [hc0, zero_smul, add_zero] at hJeq
    obtain ⟨J'', η, hJ'', hη⟩ := diag_form hJ μ d c (R := R) fun x => by rw [hRj x, ← hJeq]
    exact ⟨ν, J'', η, hJ'', Or.inl rfl, hη⟩
  · set c0 := Real.sqrt (1 - ∑ α, d α ^ 2)
    have hJsum : J = ∑ i, vecCons c0 d i • vecCons (c0⁻¹ • resid J Jα d) Jα i := by
      rw [Fin.sum_univ_succ]
      simp only [cons_val_zero, cons_val_succ]
      rw [add_comm]
      exact hJeq
    have hμsum : ∀ x, ∑ i, vecCons 0 μ i • jfam (vecCons (c0⁻¹ • resid J Jα d) Jα i) x =
        ∑ α, μ α • jfam (Jα α) x := fun x => by
      rw [Fin.sum_univ_succ]
      simp only [cons_val_zero, cons_val_succ, zero_smul, zero_add]
    obtain ⟨J'', η, hJ'', hη⟩ := diag_form (hcl hc0) (vecCons 0 μ) (vecCons c0 d) c (R := R) fun x => by
      rw [hRj x, hμsum x, ← hJsum]
    exact ⟨ν + 1, J'', η, hJ'', Or.inr rfl, hη⟩

/-- **Row rem_7_2_diagonalize.** -/
theorem rem_7_2_diagonalize_proved (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (d : Fin ν → ℝ) (h : Rem72Rot R R' J c Jα μ d) :
    ∃ (ν' : ℕ) (J'' : Fin ν' → Matrix (Fin 16) (Fin 16) ℝ) (η : Fin ν' → ℝ), IsCliffordStr J'' ∧
      (ν' = ν ∨ ν' = ν + 1) ∧ ∀ x : Vec 16, R.jacobi x = ∑ a, η a • jfam (J'' a) x :=
  diagonalize_core h.1 h.2.1

/-- **Row rem_7_2_normalized.** -/
theorem rem_7_2_normalized_proved (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) : R.IsClifford := by
  choose d hd using rem_7_2_inner_const_proved R R' J c Jα μ h
  obtain ⟨ν', J'', η, hJ'', -, hη⟩ := diagonalize_core h hd
  exact ⟨ν', J'', hJ'', 0, η, fun x => by rw [zero_smul, zero_add]; exact hη x⟩

/-! ### Normalization and Lemma 3.2(1) -/

/-- Dropping the zero coefficients of a Clifford form. -/
lemma drop_zero {ν0 : ℕ} {J0 : Fin ν0 → Matrix (Fin 16) (Fin 16) ℝ} (hJ0 : IsCliffordStr J0) (η : Fin ν0 → ℝ) :
    ∃ (k : ℕ) (Jα : Fin k → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin k → ℝ), IsCliffordStr Jα ∧ (∀ a, μ a ≠ 0) ∧
      ∀ x, ∑ α, μ α • jfam (Jα α) x = ∑ i, η i • jfam (J0 i) x := by
  set T := Finset.univ.filter fun i => η i ≠ 0
  let e : Fin T.card ≃ T := T.equivFin.symm
  refine ⟨T.card, fun a => J0 (e a).1, fun a => η (e a).1, ⟨fun a => hJ0.1 _, fun a b => ?_⟩,
    fun a => (Finset.mem_filter.1 (e a).2).2, fun x => ?_⟩
  · rw [hJ0.2]
    by_cases hab : a = b
    · subst hab
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right fun hh => hab (e.injective (Subtype.ext hh)), ite_eq_right hab]
  · rw [Equiv.sum_comp e (fun b : T => η b.1 • jfam (J0 b.1) x),
      Finset.sum_coe_sort T (fun i => η i • jfam (J0 i) x)]
    exact Finset.sum_filter_of_ne fun i _ hne h0 => hne (by simp [h0])

/-- **Row rem_7_2_normalize.** -/
theorem rem_7_2_normalize_proved (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J)
    (hJo : Jᵀ * J = 1) (c : ℝ) (hc : c ≠ 0) (hR' : ∀ u v w, R'.op u v w = R.op u v w - c • RJfun J u v w)
    (hO : R.IsOsserman) (hO' : R'.IsOsserman) (hC' : R'.IsClifford) :
    ∃ (l0 : ℝ) (R0 R0' : CurvTensor 16) (ν : ℕ) (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ),
      (∀ u v w, R0.op u v w = R.op u v w - l0 • R1fun u v w) ∧
      (∀ u v w, R0'.op u v w = R'.op u v w - l0 • R1fun u v w) ∧
      (∀ x, R'.jacobi x = l0 • Pi x + ∑ α, μ α • jfam (Jα α) x) ∧
      Rem72Hyp R0 R0' J c Jα μ ∧ (R0.IsClifford → R.IsClifford) := by
  obtain ⟨ν0, J0, hJ0, l0, η, hjac0⟩ := hC'
  obtain ⟨k, Jα, μ, hJα, hμ, hsum⟩ := drop_zero hJ0 η
  have hjac' : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, μ α • jfam (Jα α) x := fun x => by
    rw [hsum x]
    exact hjac0 x
  obtain ⟨R0, hR0op, -, hR0O, hR0C⟩ := shift_R1_proved R l0
  obtain ⟨R0', hR0'op, hR0'jac, hR0'O, -⟩ := shift_R1_proved R' l0
  refine ⟨l0, R0, R0', k, Jα, μ, hR0op, hR0'op, hjac',
    ⟨hJs, hJo, hc, fun u v w => ?_, hR0O.2 hO, hR0'O.2 hO', hJα, hμ, fun x => ?_⟩, hR0C.1⟩
  · rw [hR0'op, hR', hR0op]
    abel
  · rw [hR0'jac, hjac' x]
    abel

/-- **Row lem_nik_3_2_1** ([Nik2006, Lemma 3.2(1)], re-proved as Remark 7.2). -/
theorem lem_nik_3_2_1_proved (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J)
    (hJo : Jᵀ * J = 1) (c : ℝ) (hc : c ≠ 0) (hR' : ∀ u v w, R'.op u v w = R.op u v w - c • RJfun J u v w)
    (hO : R.IsOsserman) (hO' : R'.IsOsserman) (hC' : R'.IsClifford) : R.IsClifford := by
  obtain ⟨l0, R0, R0', ν, Jα, μ, -, -, -, hH, hback⟩ :=
    rem_7_2_normalize_proved R R' J hJs hJo c hc hR' hO hO' hC'
  exact hback (rem_7_2_normalized_proved R0 R0' J c Jα μ hH)

end Osserman.Proofs.Rem72c

