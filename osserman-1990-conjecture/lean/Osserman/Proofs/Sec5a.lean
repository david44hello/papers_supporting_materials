/-
Osserman/Proofs/Sec5a.lean — proofs of the nine rows of Proposition 5.1 of paper 013 (prop:plus, P013_short.tex
l. 539-563): prop_5_1_diag_zero, prop_5_1_offdiag_Q, prop_5_1_C_relations, prop_5_1_sum_sq, prop_5_1_const_w,
prop_5_1_C_w, prop_5_1_C_skew, prop_5_1_A_Cl7, prop_5_1 (statements copied verbatim from Osserman/Paper/Statements.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.Blocks
import Osserman.Proofs.Spectral
import Osserman.Proofs.Sec2
import Osserman.Proofs.Threshold
import Osserman.Proofs.CayleyProducts

namespace Osserman.Proofs.Sec5a

open Osserman Matrix

/-! ### Blocks: transposes and products -/

lemma blkXX_transpose (M : Matrix (Fin 32) (Fin 32) ℝ) : (blkXX M)ᵀ = blkXX Mᵀ := by
  simp only [blkXX, transpose_submatrix]

lemma blkYY_transpose (M : Matrix (Fin 32) (Fin 32) ℝ) : (blkYY M)ᵀ = blkYY Mᵀ := by
  simp only [blkYY, transpose_submatrix]

lemma blkXY_of_symm {M : Matrix (Fin 32) (Fin 32) ℝ} (hM : Mᵀ = M) : blkXY M = (blkYX M)ᵀ := by
  rw [blkXY, blkYX, transpose_submatrix, hM]

lemma blkXX_mul (A B : Matrix (Fin 32) (Fin 32) ℝ) :
    blkXX (A * B) = blkXX A * blkXX B + blkXY A * blkYX B := by
  ext r c
  simp only [blkXX, blkXY, blkYX, submatrix_apply, mul_apply, Matrix.add_apply]
  rw [Fin.sum_univ_add (a := 16) (b := 16)]

lemma blkYY_mul (A B : Matrix (Fin 32) (Fin 32) ℝ) :
    blkYY (A * B) = blkYX A * blkXY B + blkYY A * blkYY B := by
  ext r c
  simp only [blkYY, blkXY, blkYX, submatrix_apply, mul_apply, Matrix.add_apply]
  rw [Fin.sum_univ_add (a := 16) (b := 16)]

lemma blkXX_add (A B : Matrix (Fin 32) (Fin 32) ℝ) : blkXX (A + B) = blkXX A + blkXX B := by
  ext r c
  simp [blkXX]

lemma blkYY_add (A B : Matrix (Fin 32) (Fin 32) ℝ) : blkYY (A + B) = blkYY A + blkYY B := by
  ext r c
  simp [blkYY]

lemma blkXX_ite (i j : Fin 8) :
    blkXX (if i = j then (2 : Matrix (Fin 32) (Fin 32) ℝ) else 0) = if i = j then 2 else 0 := by
  split_ifs
  · exact submatrix_ofNat _ (fun a b hab => Fin.castAdd_inj.mp hab) 2
  · ext r c
    simp [blkXX]

lemma blkYY_ite (i j : Fin 8) :
    blkYY (if i = j then (2 : Matrix (Fin 32) (Fin 32) ℝ) else 0) = if i = j then 2 else 0 := by
  split_ifs
  · exact submatrix_ofNat _ (Fin.natAdd_injective 16 16) 2
  · ext r c
    simp [blkYY]

/-! ### Small linear-algebra facts -/

lemma dot_transpose (C : Matrix (Fin 16) (Fin 16) ℝ) (x y : Vec 16) : x ⬝ᵥ (Cᵀ *ᵥ y) = y ⬝ᵥ (C *ᵥ x) := by
  rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]

/-- A symmetric matrix with zero quadratic form is zero. -/
lemma eq_zero_of_quad {S : Matrix (Fin 16) (Fin 16) ℝ} (hS : Sᵀ = S) (h : ∀ x : Vec 16, x ⬝ᵥ (S *ᵥ x) = 0) :
    S = 0 :=
  Threshold.symm_eq_of_quadratic S 0 hS (isSymm_zero) (fun x => by rw [h, zero_mulVec, dotProduct_zero])

lemma sq_sum_zero {f : Fin 8 → ℝ} (h : ∑ i, f i ^ 2 = 0) (i : Fin 8) : f i = 0 := by
  have e := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (f k))).mp h i (Finset.mem_univ i)
  exact (pow_eq_zero_iff two_ne_zero).mp e

/-- The quadratic form of a symmetric `P` with zero diagonal blocks: `⟨Pz,z⟩ = 2⟨Cx,y⟩`. -/
lemma quad_offdiag {M : Matrix (Fin 32) (Fin 32) ℝ} (hM : Mᵀ = M) (hX : blkXX M = 0) (hY : blkYY M = 0)
    (x y : Vec 16) :
    (Fin.append x y : Vec 32) ⬝ᵥ (M *ᵥ (Fin.append x y : Vec 32)) = 2 * (y ⬝ᵥ (blkYX M *ᵥ x)) := by
  rw [quad_blocks, hX, hY, blkXY_of_symm hM, dot_transpose]
  simp only [zero_mulVec, dotProduct_zero]
  ring

/-- `∑_k (N_k)(N_k)ᵀ = NᵀN` (the `N_k` are the rows of `N`). -/
lemma sum_outer_eq {k n : ℕ} (N : Matrix (Fin k) (Fin n) ℝ) : ∑ a, vecMulVec (N a) (N a) = Nᵀ * N := by
  ext r c
  simp [Matrix.sum_apply, vecMulVec_apply, mul_apply]

/-- The polar form of `C_iᵀC_j + C_jᵀC_i = 2δ_ij I`: `C_uᵀC_v + C_vᵀC_u = 2⟨u,v⟩I`. -/
lemma comb_rel {C : Fin 8 → Matrix (Fin 16) (Fin 16) ℝ}
    (hrel : ∀ i j, (C i)ᵀ * C j + (C j)ᵀ * C i = if i = j then 2 else 0) (u v : Fin 8 → ℝ) :
    (∑ i, u i • C i)ᵀ * (∑ i, v i • C i) + (∑ i, v i • C i)ᵀ * (∑ i, u i • C i) =
      (2 * (u ⬝ᵥ v)) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  have expand : ∀ a b : Fin 8 → ℝ,
      (∑ i, a i • C i)ᵀ * (∑ j, b j • C j) = ∑ i, ∑ j, (a i * b j) • ((C i)ᵀ * C j) := by
    intro a b
    rw [transpose_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [transpose_smul, smul_mul_smul_comm]
  rw [expand, expand, Finset.sum_comm (f := fun i j => (v i * u j) • ((C i)ᵀ * C j)),
    ← Finset.sum_add_distrib]
  have inner : ∀ i, ∑ j, (u i * v j) • ((C i)ᵀ * C j) + ∑ j, (v j * u i) • ((C j)ᵀ * C i) =
      (u i * v i) • (2 : Matrix (Fin 16) (Fin 16) ℝ) := by
    intro i
    rw [← Finset.sum_add_distrib]
    simp_rw [mul_comm (v _) (u i), ← smul_add, hrel, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
  rw [Finset.sum_congr rfl fun i _ => inner i, ← Finset.sum_smul]
  ext r c
  by_cases hrc : r = c
  · subst hrc
    simp [dotProduct, ofNat_apply]
    ring
  · simp [hrc, ofNat_apply]

/-- With `(⟨C_ix,x⟩)_i = |x|²w`: `⟨C_ux,x⟩ = |x|²⟨u,w⟩`. -/
lemma comb_quad {C : Fin 8 → Matrix (Fin 16) (Fin 16) ℝ} {w : Fin 8 → ℝ}
    (hcw : ∀ x : Vec 16, (fun i => x ⬝ᵥ (C i *ᵥ x)) = (x ⬝ᵥ x) • w) (u : Fin 8 → ℝ) (x : Vec 16) :
    x ⬝ᵥ ((∑ i, u i • C i) *ᵥ x) = (x ⬝ᵥ x) * (u ⬝ᵥ w) := by
  have hi : ∀ i, x ⬝ᵥ (C i *ᵥ x) = (x ⬝ᵥ x) * w i := fun i => by
    simpa using congrFun (hcw x) i
  rw [sum_mulVec, dotProduct_sum]
  simp only [smul_mulVec, dotProduct_smul, smul_eq_mul, hi]
  rw [show u ⬝ᵥ w = ∑ i, u i * w i from rfl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### An orthonormal frame `w, u_1, …, u_7` of `ℝ^8` -/

/-- The `8 × 8` matrix with rows `w, u_1, …, u_7` is orthogonal. -/
lemma frame_orth (w : Fin 8 → ℝ) (u : Fin 7 → Fin 8 → ℝ) (hw : w ⬝ᵥ w = 1)
    (hu : ∀ j k, u j ⬝ᵥ u k = if j = k then 1 else 0) (huw : ∀ j, u j ⬝ᵥ w = 0) :
    (Matrix.of (vecCons w u))ᵀ * Matrix.of (vecCons w u) = 1 := by
  rw [mul_eq_one_comm]
  ext k l
  rw [mul_apply, one_apply]
  change vecCons w u k ⬝ᵥ vecCons w u l = _
  refine Fin.cases ?_ (fun k => ?_) k <;> refine Fin.cases ?_ (fun l => ?_) l
  · simp [hw]
  · rw [cons_val_zero, cons_val_succ, dotProduct_comm, huw, ite_eq_right (Fin.succ_ne_zero l).symm]
  · rw [cons_val_zero, cons_val_succ, huw, ite_eq_right (Fin.succ_ne_zero k)]
  · rw [cons_val_succ, cons_val_succ, hu]
    simp only [Fin.succ_inj]

/-- Parseval for the frame: `∑_i (C_ix)(C_ix)ᵀ = (C_wx)(C_wx)ᵀ + ∑_j (C_{u_j}x)(C_{u_j}x)ᵀ`. -/
lemma parseval_outer (C : Fin 8 → Matrix (Fin 16) (Fin 16) ℝ) (w : Fin 8 → ℝ) (u : Fin 7 → Fin 8 → ℝ)
    (hO : (Matrix.of (vecCons w u))ᵀ * Matrix.of (vecCons w u) = 1) (x : Vec 16) :
    ∑ i, vecMulVec (C i *ᵥ x) (C i *ᵥ x) =
      vecMulVec ((∑ i, w i • C i) *ᵥ x) ((∑ i, w i • C i) *ᵥ x) +
        ∑ j, vecMulVec ((∑ i, u j i • C i) *ᵥ x) ((∑ i, u j i • C i) *ᵥ x) := by
  have hrow : ∀ k, (Matrix.of (vecCons w u) * Matrix.of (fun a => C a *ᵥ x)) k =
      (∑ i, vecCons w u k i • C i) *ᵥ x := by
    intro k
    funext r
    simp [mul_apply, sum_mulVec, Finset.sum_apply, smul_mulVec]
  have h1 : ∑ i, vecMulVec (C i *ᵥ x) (C i *ᵥ x) =
      (Matrix.of (fun a => C a *ᵥ x))ᵀ * Matrix.of (fun a => C a *ᵥ x) :=
    sum_outer_eq (Matrix.of (fun a => C a *ᵥ x))
  have h2 : (Matrix.of (fun a => C a *ᵥ x))ᵀ * Matrix.of (fun a => C a *ᵥ x) =
      (Matrix.of (vecCons w u) * Matrix.of (fun a => C a *ᵥ x))ᵀ *
        (Matrix.of (vecCons w u) * Matrix.of (fun a => C a *ᵥ x)) := by
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of (vecCons w u))ᵀ, hO, Matrix.one_mul]
  rw [h1, h2, ← sum_outer_eq, Fin.sum_univ_succ]
  simp only [hrow, cons_val_zero, cons_val_succ]

/-- `w^⊥` has an orthonormal basis `u_1, …, u_7`. -/
lemma exists_orthonormal_perp (w : Fin 8 → ℝ) (hw : w ⬝ᵥ w = 1) :
    ∃ u : Fin 7 → Fin 8 → ℝ, (∀ j k, u j ⬝ᵥ u k = if j = k then 1 else 0) ∧ ∀ j, u j ⬝ᵥ w = 0 := by
  have hv : Orthonormal ℝ (({0} : Set (Fin 8)).domRestrict
      (fun _ => (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 8)))) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    rw [ite_eq_left rfl]
    change inner ℝ (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 w) = 1
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, hw]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b 0 = WithLp.toLp 2 w := hb 0 rfl
  have hon := orthonormal_iff_ite.mp b.orthonormal
  refine ⟨fun j => WithLp.ofLp (b j.succ), fun j k => ?_, fun j => ?_⟩
  · have e := hon k.succ j.succ
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at e
    rw [e]
    by_cases hjk : j = k
    · subst hjk
      simp
    · simp [hjk, Ne.symm hjk]
  · have e := hon 0 j.succ
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, hb0, ite_eq_right (Fin.succ_ne_zero j).symm] at e
    exact e

/-! ### The nine rows -/

theorem prop_5_1_diag_zero_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    ∀ i, blkXX (P i) = 0 ∧ blkYY (P i) = 0 := by
  have hb := Sec2.sec2_b_properties_proved R μ κ h
  intro i
  constructor
  · apply eq_zero_of_quad (by rw [blkXX_transpose, hP.1 i])
    intro x
    have e := hplus x 0
    rw [mulVec_zero, dotProduct_zero, mul_zero] at e
    simp only [quad_blocks, mulVec_zero, dotProduct_zero, zero_dotProduct, add_zero] at e
    exact sq_sum_zero (f := fun i => x ⬝ᵥ (blkXX (P i) *ᵥ x)) e.symm i
  · apply eq_zero_of_quad (by rw [blkYY_transpose, hP.1 i])
    intro y
    have e := hplus 0 y
    rw [hb.2.1 y, mul_zero] at e
    simp only [quad_blocks, mulVec_zero, dotProduct_zero, zero_dotProduct, zero_add] at e
    exact sq_sum_zero (f := fun i => y ⬝ᵥ (blkYY (P i) *ᵥ y)) e.symm i

/-- (eq:plus) with zero diagonal blocks: `⟨Q(x)y,y⟩ = ∑_i ⟨C_ix,y⟩²`. -/
lemma plus_reduced (R : CurvTensor 16) (μ κ : ℝ) (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ)
    (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hD : ∀ i, blkXX (P i) = 0 ∧ blkYY (P i) = 0) (x y : Vec 16) :
    (Qmat R μ κ x *ᵥ y) ⬝ᵥ y = ∑ i, (y ⬝ᵥ (blkYX (P i) *ᵥ x)) ^ 2 := by
  have e := hplus x y
  have hs : ∀ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2 =
      4 * (y ⬝ᵥ (blkYX (P i) *ᵥ x)) ^ 2 := fun i => by
    rw [quad_offdiag (hP.1 i) (hD i).1 (hD i).2 x y]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hs i), ← Finset.mul_sum] at e
  linarith

theorem prop_5_1_offdiag_Q_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    (∀ i, blkXY (P i) = (blkYX (P i))ᵀ) ∧
      ∀ x : Vec 16, Qmat R μ κ x = ∑ i, vecMulVec (blkYX (P i) *ᵥ x) (blkYX (P i) *ᵥ x) := by
  have hD := prop_5_1_diag_zero_proved R μ κ h P hP hplus
  refine ⟨fun i => blkXY_of_symm (hP.1 i), fun x => ?_⟩
  apply Threshold.symm_eq_of_quadratic
  · show (Qmat R μ κ x)ᵀ = Qmat R μ κ x
    rw [Qmat, transpose_add, Sec2.Amat_symm, transpose_vecMulVec]
  · show (∑ i, vecMulVec (blkYX (P i) *ᵥ x) (blkYX (P i) *ᵥ x))ᵀ = _
    rw [transpose_sum]
    exact Finset.sum_congr rfl fun i _ => transpose_vecMulVec _ _
  · intro y
    rw [dotProduct_comm, plus_reduced R μ κ P hP hplus hD x y, sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Threshold.quadratic_outer, dotProduct_comm]

theorem prop_5_1_C_relations_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    ∀ i j, (blkYX (P i))ᵀ * blkYX (P j) + (blkYX (P j))ᵀ * blkYX (P i) = (if i = j then 2 else 0) ∧
      blkYX (P i) * (blkYX (P j))ᵀ + blkYX (P j) * (blkYX (P i))ᵀ = (if i = j then 2 else 0) := by
  have hD := prop_5_1_diag_zero_proved R μ κ h P hP hplus
  have hXY := fun i => blkXY_of_symm (hP.1 i)
  intro i j
  have e := hP.2 i j
  constructor
  · have e1 := congrArg blkXX e
    rw [blkXX_add, blkXX_mul, blkXX_mul, (hD i).1, (hD j).1, hXY i, hXY j, blkXX_ite] at e1
    simpa only [zero_mul, zero_add] using e1
  · have e2 := congrArg blkYY e
    rw [blkYY_add, blkYY_mul, blkYY_mul, (hD i).2, (hD j).2, hXY i, hXY j, blkYY_ite] at e2
    simpa only [zero_mul, add_zero] using e2

theorem prop_5_1_sum_sq_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    ∀ x : Vec 16, ∑ i, (x ⬝ᵥ (blkYX (P i) *ᵥ x)) ^ 2 = (x ⬝ᵥ x) ^ 2 := by
  have hD := prop_5_1_diag_zero_proved R μ κ h P hP hplus
  intro x
  rw [← plus_reduced R μ κ P hP hplus hD x x]
  exact (Sec2.sec2_b_properties_proved R μ κ h).2.2.2 x

theorem prop_5_1_const_w_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    ∃ w : Fin 8 → ℝ, w ⬝ᵥ w = 1 ∧ ∀ x : Vec 16, (fun i => x ⬝ᵥ (blkYX (P i) *ᵥ x)) = (x ⬝ᵥ x) • w := by
  have hsq := prop_5_1_sum_sq_proved R μ κ h P hP hplus
  -- the symmetric parts `S_i = (C_i + C_iᵀ)/2` have the same quadratic forms
  let S : Fin (7 + 1) → Matrix (Fin 16) (Fin 16) ℝ := fun i => (1 / 2 : ℝ) • (blkYX (P i) + (blkYX (P i))ᵀ)
  have hS : ∀ i, (S i).IsSymm := fun i => by
    show ((1 / 2 : ℝ) • (blkYX (P i) + (blkYX (P i))ᵀ))ᵀ = _
    rw [transpose_smul, transpose_add, transpose_transpose, add_comm]
  have hhv : ∀ x : Vec 16, hvec S x = fun i => x ⬝ᵥ (blkYX (P i) *ᵥ x) := by
    intro x
    funext i
    simp only [hvec, S, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, dot_transpose, smul_eq_mul]
    ring
  have hnorm : ∀ x : Vec 16, ∑ i, hvec S x i ^ 2 = (x ⬝ᵥ x) ^ 2 := fun x => by
    rw [hhv]
    exact hsq x
  have he : (Pi.single 0 1 : Vec 16) ⬝ᵥ Pi.single 0 1 = 1 := by simp
  refine ⟨hvec S (Pi.single 0 1), Threshold.hvec_unit S hnorm _ he, fun x => ?_⟩
  obtain ⟨s, u, hu, rfl⟩ := Spectral.exists_unit_scale x
  rw [← hhv, Threshold.hvec_smul, Threshold.threshold_b S hS hnorm (by norm_num) u _ hu he, smul_dotProduct,
    dotProduct_smul, hu, smul_eq_mul, smul_eq_mul, mul_one, sq]

theorem prop_5_1_C_w_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 8 → ℝ) (hw : w ⬝ᵥ w = 1) (hcw : ∀ x : Vec 16, (fun i => x ⬝ᵥ (blkYX (P i) *ᵥ x)) = (x ⬝ᵥ x) • w) :
    (∑ i, w i • blkYX (P i))ᵀ * (∑ i, w i • blkYX (P i)) = 1 ∧
      (∀ x : Vec 16, x ⬝ᵥ ((∑ i, w i • blkYX (P i)) *ᵥ x) = x ⬝ᵥ x) ∧ ∑ i, w i • blkYX (P i) = 1 := by
  have hrel := fun i j => (prop_5_1_C_relations_proved R μ κ h P hP hplus i j).1
  have hT : (∑ i, w i • blkYX (P i))ᵀ * (∑ i, w i • blkYX (P i)) = 1 := by
    have e := comb_rel hrel w w
    rw [hw, mul_one, ← two_smul ℝ] at e
    exact smul_right_injective _ two_ne_zero e
  have hq : ∀ x : Vec 16, x ⬝ᵥ ((∑ i, w i • blkYX (P i)) *ᵥ x) = x ⬝ᵥ x := fun x => by
    rw [comb_quad hcw w x, hw, mul_one]
  refine ⟨hT, hq, ?_⟩
  rw [ext_iff_mulVec]
  intro x
  rw [one_mulVec]
  have h1 : ((∑ i, w i • blkYX (P i)) *ᵥ x) ⬝ᵥ ((∑ i, w i • blkYX (P i)) *ᵥ x) = x ⬝ᵥ x := by
    rw [← dot_transpose (∑ i, w i • blkYX (P i)) x, mulVec_mulVec, hT, one_mulVec]
  have hn : ((∑ i, w i • blkYX (P i)) *ᵥ x - x) ⬝ᵥ ((∑ i, w i • blkYX (P i)) *ᵥ x - x) = 0 := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, h1, dotProduct_comm ((∑ i, w i • blkYX (P i)) *ᵥ x) x,
      hq x]
    ring
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hn)

theorem prop_5_1_C_skew_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 8 → ℝ) (hw : w ⬝ᵥ w = 1) (hcw : ∀ x : Vec 16, (fun i => x ⬝ᵥ (blkYX (P i) *ᵥ x)) = (x ⬝ᵥ x) • w) :
    ∀ u v : Fin 8 → ℝ, u ⬝ᵥ w = 0 → v ⬝ᵥ w = 0 →
      (∑ i, u i • blkYX (P i))ᵀ = -(∑ i, u i • blkYX (P i)) ∧
      (∑ i, u i • blkYX (P i)) * (∑ i, v i • blkYX (P i)) + (∑ i, v i • blkYX (P i)) * (∑ i, u i • blkYX (P i)) =
        (-2 * (u ⬝ᵥ v)) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  have hrel := fun i j => (prop_5_1_C_relations_proved R μ κ h P hP hplus i j).1
  have skew : ∀ a : Fin 8 → ℝ, a ⬝ᵥ w = 0 → (∑ i, a i • blkYX (P i))ᵀ = -(∑ i, a i • blkYX (P i)) := by
    intro a ha
    have hz : (∑ i, a i • blkYX (P i)) + (∑ i, a i • blkYX (P i))ᵀ = 0 := by
      apply eq_zero_of_quad
      · rw [transpose_add, transpose_transpose, add_comm]
      · intro x
        rw [add_mulVec, dotProduct_add, dot_transpose, comb_quad hcw a x, ha, mul_zero, add_zero]
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact hz
  intro u v hu hv
  refine ⟨skew u hu, ?_⟩
  have e := comb_rel hrel u v
  rw [skew u hu, skew v hv, neg_mul, neg_mul, ← neg_add] at e
  rw [neg_mul, neg_smul, ← e, neg_neg]

theorem prop_5_1_A_Cl7_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 8 → ℝ) (hw : w ⬝ᵥ w = 1) (hcw : ∀ x : Vec 16, (fun i => x ⬝ᵥ (blkYX (P i) *ᵥ x)) = (x ⬝ᵥ x) • w)
    (u : Fin 7 → Fin 8 → ℝ) (hu : ∀ j k, u j ⬝ᵥ u k = if j = k then 1 else 0) (huw : ∀ j, u j ⬝ᵥ w = 0) :
    IsCliffordStr (fun j => ∑ i, u j i • blkYX (P i)) ∧
      ∀ x : Vec 16, Amat R μ κ x =
        ∑ j, vecMulVec ((∑ i, u j i • blkYX (P i)) *ᵥ x) ((∑ i, u j i • blkYX (P i)) *ᵥ x) := by
  have hCw1 := (prop_5_1_C_w_proved R μ κ h P hP hplus w hw hcw).2.2
  have hsk := prop_5_1_C_skew_proved R μ κ h P hP hplus w hw hcw
  have hQ := (prop_5_1_offdiag_Q_proved R μ κ h P hP hplus).2
  refine ⟨⟨fun j => (hsk (u j) (u j) (huw j) (huw j)).1, fun j k => ?_⟩, fun x => ?_⟩
  · dsimp only
    rw [(hsk (u j) (u k) (huw j) (huw k)).2, hu j k]
    split_ifs
    · ext r c
      by_cases hrc : r = c
      · subst hrc
        simp [ofNat_apply]
      · simp [hrc, ofNat_apply]
    · simp
  · have hA : Amat R μ κ x = Qmat R μ κ x - vecMulVec x x := by
      rw [Qmat, add_sub_cancel_right]
    rw [hA, hQ x, parseval_outer _ w u (frame_orth w u hw hu huw) x, hCw1, one_mulVec, add_sub_cancel_left]

theorem prop_5_1_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ)
    (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    IsFormCl7 (Amat R μ κ) := by
  obtain ⟨w, hw, hcw⟩ := prop_5_1_const_w_proved R μ κ h P hP hplus
  obtain ⟨u, hu, huw⟩ := exists_orthonormal_perp w hw
  obtain ⟨hcl, hA⟩ := prop_5_1_A_Cl7_proved R μ κ h P hP hplus w hw hcw u hu huw
  exact ⟨_, hcl, hA⟩

end Osserman.Proofs.Sec5a
