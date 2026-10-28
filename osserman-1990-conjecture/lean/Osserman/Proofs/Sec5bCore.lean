/-
Osserman/Proofs/Sec5bCore.lean — shared tools for Proposition 5.2 of paper 013 (prop:minus, P013_short.tex
l. 566-606), used by both halves of its proof (h constant: Sec5b.lean; h not constant: Sec5c.lean): blocks of the
combinations `P_v = ∑ v_i P_i`, the Clifford relations of the combinations and of their blocks, an orthonormal frame
`w, u_1, …, u_k` (Parseval), and the two rows prop_5_2_blocks and prop_5_2_trace (statements copied verbatim from
Osserman/Paper/Statements.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.Blocks
import Osserman.Proofs.Spectral
import Osserman.Proofs.Sec2
import Osserman.Proofs.Threshold
import Osserman.Proofs.Poly
import Osserman.Proofs.CayleyProducts
import Osserman.Proofs.Sec5a

namespace Osserman.Proofs.Sec5bCore

open Osserman Matrix

variable {k : ℕ}

/-! ### Blocks of combinations -/

lemma blkXX_comb (M : Fin k → Matrix (Fin 32) (Fin 32) ℝ) (v : Fin k → ℝ) :
    blkXX (∑ i, v i • M i) = ∑ i, v i • blkXX (M i) := by
  ext r c
  simp [blkXX, Matrix.sum_apply]

lemma blkXY_comb (M : Fin k → Matrix (Fin 32) (Fin 32) ℝ) (v : Fin k → ℝ) :
    blkXY (∑ i, v i • M i) = ∑ i, v i • blkXY (M i) := by
  ext r c
  simp [blkXY, Matrix.sum_apply]

lemma blkYX_comb (M : Fin k → Matrix (Fin 32) (Fin 32) ℝ) (v : Fin k → ℝ) :
    blkYX (∑ i, v i • M i) = ∑ i, v i • blkYX (M i) := by
  ext r c
  simp [blkYX, Matrix.sum_apply]

lemma blkYY_comb (M : Fin k → Matrix (Fin 32) (Fin 32) ℝ) (v : Fin k → ℝ) :
    blkYY (∑ i, v i • M i) = ∑ i, v i • blkYY (M i) := by
  ext r c
  simp [blkYY, Matrix.sum_apply]

lemma blkXX_smul (c : ℝ) (M : Matrix (Fin 32) (Fin 32) ℝ) : blkXX (c • M) = c • blkXX M := by
  ext r s
  simp [blkXX]

lemma blkYY_smul (c : ℝ) (M : Matrix (Fin 32) (Fin 32) ℝ) : blkYY (c • M) = c • blkYY M := by
  ext r s
  simp [blkYY]

lemma blkXX_one : blkXX (1 : Matrix (Fin 32) (Fin 32) ℝ) = 1 := by
  unfold blkXX
  exact submatrix_one _ (fun a b hab => Fin.castAdd_inj.mp hab)

lemma blkYY_one : blkYY (1 : Matrix (Fin 32) (Fin 32) ℝ) = 1 := by
  unfold blkYY
  exact submatrix_one _ (Fin.natAdd_injective 16 16)

/-- `tr M = tr H + tr D`. -/
lemma trace_blocks (M : Matrix (Fin 32) (Fin 32) ℝ) : M.trace = (blkXX M).trace + (blkYY M).trace := by
  simp only [Matrix.trace, Matrix.diag, blkXX, blkYY, submatrix_apply]
  rw [Fin.sum_univ_add (a := 16) (b := 16)]

/-- `⟨Pz,z⟩ = ⟨Hx,x⟩ + 2⟨Bx,y⟩ + ⟨Dy,y⟩` for a symmetric `P` and `z = (x, y)`. -/
lemma quad_symm {M : Matrix (Fin 32) (Fin 32) ℝ} (hM : Mᵀ = M) (x y : Vec 16) :
    (Fin.append x y : Vec 32) ⬝ᵥ (M *ᵥ (Fin.append x y : Vec 32)) =
      x ⬝ᵥ (blkXX M *ᵥ x) + 2 * (y ⬝ᵥ (blkYX M *ᵥ x)) + y ⬝ᵥ (blkYY M *ᵥ y) := by
  rw [quad_blocks, Sec5a.blkXY_of_symm hM, Sec5a.dot_transpose]
  ring

/-! ### Combinations of a Clifford system -/

/-- `∑_j (e_i)_j M_j = M_i`. -/
lemma sum_single {n : ℕ} (M : Fin k → Matrix (Fin n) (Fin n) ℝ) (i : Fin k) :
    ∑ j, (Pi.single i 1 : Fin k → ℝ) j • M j = M i := by
  simp [Pi.single_apply]

/-- A combination of symmetric matrices is symmetric. -/
lemma comb_transpose {n : ℕ} {S : Fin k → Matrix (Fin n) (Fin n) ℝ} (hS : ∀ i, (S i)ᵀ = S i) (v : Fin k → ℝ) :
    (∑ i, v i • S i)ᵀ = ∑ i, v i • S i := by
  rw [transpose_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [transpose_smul, hS i]

/-- The polar form of `S_iS_j + S_jS_i = 2δ_ij I`: `S_uS_v + S_vS_u = 2⟨u,v⟩I`. -/
lemma clifford_comb {n : ℕ} {S : Fin k → Matrix (Fin n) (Fin n) ℝ}
    (hS : ∀ i j, S i * S j + S j * S i = if i = j then 2 else 0) (u v : Fin k → ℝ) :
    (∑ i, u i • S i) * (∑ i, v i • S i) + (∑ i, v i • S i) * (∑ i, u i • S i) =
      (2 * (u ⬝ᵥ v)) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have expand : ∀ a b : Fin k → ℝ,
      (∑ i, a i • S i) * (∑ j, b j • S j) = ∑ i, ∑ j, (a i * b j) • (S i * S j) := by
    intro a b
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  rw [expand, expand, Finset.sum_comm (f := fun i j => (v i * u j) • (S i * S j)), ← Finset.sum_add_distrib]
  have inner : ∀ i, ∑ j, (u i * v j) • (S i * S j) + ∑ j, (v j * u i) • (S j * S i) =
      (u i * v i) • (2 : Matrix (Fin n) (Fin n) ℝ) := by
    intro i
    rw [← Finset.sum_add_distrib]
    simp_rw [mul_comm (v _) (u i), ← smul_add, hS, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
  rw [Finset.sum_congr rfl fun i _ => inner i, ← Finset.sum_smul]
  ext r c
  by_cases hrc : r = c
  · subst hrc
    simp [dotProduct, ofNat_apply]
    ring
  · simp [hrc, ofNat_apply]

/-- With `(⟨C_ix,x⟩)_i = |x|²w`: `⟨C_ux,x⟩ = |x|²⟨u,w⟩`. -/
lemma comb_quad {n : ℕ} {C : Fin k → Matrix (Fin n) (Fin n) ℝ} {w : Fin k → ℝ}
    (hcw : ∀ x : Vec n, (fun i => x ⬝ᵥ (C i *ᵥ x)) = (x ⬝ᵥ x) • w) (u : Fin k → ℝ) (x : Vec n) :
    x ⬝ᵥ ((∑ i, u i • C i) *ᵥ x) = (x ⬝ᵥ x) * (u ⬝ᵥ w) := by
  have hi : ∀ i, x ⬝ᵥ (C i *ᵥ x) = (x ⬝ᵥ x) * w i := fun i => by
    simpa using congrFun (hcw x) i
  rw [sum_mulVec, dotProduct_sum]
  simp only [smul_mulVec, dotProduct_smul, smul_eq_mul, hi]
  rw [show u ⬝ᵥ w = ∑ i, u i * w i from rfl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `v = ⟨v,w⟩w + (v - ⟨v,w⟩w)` in the combinations. -/
lemma comb_split {n : ℕ} (M : Fin k → Matrix (Fin n) (Fin n) ℝ) (v w : Fin k → ℝ) :
    ∑ i, v i • M i = (v ⬝ᵥ w) • ∑ i, w i • M i + ∑ i, (v - (v ⬝ᵥ w) • w) i • M i := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum,
    smul_smul]
  abel

/-- `(v - ⟨v,w⟩w) ⊥ w` for a unit `w`. -/
lemma perp_part {w : Fin k → ℝ} (hw : w ⬝ᵥ w = 1) (v : Fin k → ℝ) : (v - (v ⬝ᵥ w) • w) ⬝ᵥ w = 0 := by
  rw [sub_dotProduct, smul_dotProduct, hw, smul_eq_mul, mul_one, sub_self]

lemma sq_sum_zero {f : Fin k → ℝ} (h : ∑ i, f i ^ 2 = 0) (i : Fin k) : f i = 0 := by
  have e := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (f j))).mp h i (Finset.mem_univ i)
  exact (pow_eq_zero_iff two_ne_zero).mp e

/-! ### Blocks of the Clifford relations -/

/-- The upper-left block of `P_uP_v + P_vP_u = 2⟨u,v⟩I`: `H_uH_v + B_uᵀB_v + H_vH_u + B_vᵀB_u = 2⟨u,v⟩I`. -/
lemma comb_rel_XX {P : Fin k → Matrix (Fin 32) (Fin 32) ℝ} (hP : IsSymmCliffordSystem P) (u v : Fin k → ℝ) :
    (∑ i, u i • blkXX (P i)) * (∑ i, v i • blkXX (P i)) +
        (∑ i, u i • blkYX (P i))ᵀ * (∑ i, v i • blkYX (P i)) +
      ((∑ i, v i • blkXX (P i)) * (∑ i, u i • blkXX (P i)) +
        (∑ i, v i • blkYX (P i))ᵀ * (∑ i, u i • blkYX (P i))) =
      (2 * (u ⬝ᵥ v)) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  have e := congrArg blkXX (clifford_comb hP.2 u v)
  rw [Sec5a.blkXX_add, Sec5a.blkXX_mul, Sec5a.blkXX_mul, blkXX_smul, blkXX_one,
    Sec5a.blkXY_of_symm (comb_transpose hP.1 u), Sec5a.blkXY_of_symm (comb_transpose hP.1 v)] at e
  simpa only [blkXX_comb, blkYX_comb] using e

/-- The lower-right block of `P_uP_v + P_vP_u = 2⟨u,v⟩I`: `B_uB_vᵀ + D_uD_v + B_vB_uᵀ + D_vD_u = 2⟨u,v⟩I`. -/
lemma comb_rel_YY {P : Fin k → Matrix (Fin 32) (Fin 32) ℝ} (hP : IsSymmCliffordSystem P) (u v : Fin k → ℝ) :
    (∑ i, u i • blkYX (P i)) * (∑ i, v i • blkYX (P i))ᵀ +
        (∑ i, u i • blkYY (P i)) * (∑ i, v i • blkYY (P i)) +
      ((∑ i, v i • blkYX (P i)) * (∑ i, u i • blkYX (P i))ᵀ +
        (∑ i, v i • blkYY (P i)) * (∑ i, u i • blkYY (P i))) =
      (2 * (u ⬝ᵥ v)) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  have e := congrArg blkYY (clifford_comb hP.2 u v)
  rw [Sec5a.blkYY_add, Sec5a.blkYY_mul, Sec5a.blkYY_mul, blkYY_smul, blkYY_one,
    Sec5a.blkXY_of_symm (comb_transpose hP.1 u), Sec5a.blkXY_of_symm (comb_transpose hP.1 v)] at e
  simpa only [blkYY_comb, blkYX_comb] using e

/-- The upper-left block of `P_i² = I`: `H_i² + B_iᵀB_i = I`. -/
lemma sq_XX {P : Fin k → Matrix (Fin 32) (Fin 32) ℝ} (hP : IsSymmCliffordSystem P) (i : Fin k) :
    blkXX (P i) * blkXX (P i) + (blkYX (P i))ᵀ * blkYX (P i) = 1 := by
  have e := congrArg blkXX (CayleyProducts.system_square P hP i)
  rwa [Sec5a.blkXX_mul, Sec5a.blkXY_of_symm (hP.1 i), blkXX_one] at e

/-- The lower-right block of `P_i² = I`: `B_iB_iᵀ + D_i² = I`. -/
lemma sq_YY {P : Fin k → Matrix (Fin 32) (Fin 32) ℝ} (hP : IsSymmCliffordSystem P) (i : Fin k) :
    blkYX (P i) * (blkYX (P i))ᵀ + blkYY (P i) * blkYY (P i) = 1 := by
  have e := congrArg blkYY (CayleyProducts.system_square P hP i)
  rwa [Sec5a.blkYY_mul, Sec5a.blkXY_of_symm (hP.1 i), blkYY_one] at e

/-! ### An orthonormal frame `w, u_1, …, u_k` of `ℝ^(k+1)` -/

/-- The matrix with rows `w, u_1, …, u_k` is orthogonal. -/
lemma frame_orth (w : Fin (k + 1) → ℝ) (u : Fin k → Fin (k + 1) → ℝ) (hw : w ⬝ᵥ w = 1)
    (hu : ∀ j l, u j ⬝ᵥ u l = if j = l then 1 else 0) (huw : ∀ j, u j ⬝ᵥ w = 0) :
    (Matrix.of (vecCons w u))ᵀ * Matrix.of (vecCons w u) = 1 := by
  rw [mul_eq_one_comm]
  ext a b
  rw [mul_apply, one_apply]
  change vecCons w u a ⬝ᵥ vecCons w u b = _
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
  · simp [hw]
  · rw [cons_val_zero, cons_val_succ, dotProduct_comm, huw, ite_eq_right (Fin.succ_ne_zero b).symm]
  · rw [cons_val_zero, cons_val_succ, huw, ite_eq_right (Fin.succ_ne_zero a)]
  · rw [cons_val_succ, cons_val_succ, hu]
    simp only [Fin.succ_inj]

/-- Parseval for the frame: `∑_i (C_ix)(C_ix)ᵀ = (C_wx)(C_wx)ᵀ + ∑_j (C_{u_j}x)(C_{u_j}x)ᵀ`. -/
lemma parseval_outer {n : ℕ} (C : Fin (k + 1) → Matrix (Fin n) (Fin n) ℝ) (w : Fin (k + 1) → ℝ)
    (u : Fin k → Fin (k + 1) → ℝ) (hO : (Matrix.of (vecCons w u))ᵀ * Matrix.of (vecCons w u) = 1) (x : Vec n) :
    ∑ i, vecMulVec (C i *ᵥ x) (C i *ᵥ x) =
      vecMulVec ((∑ i, w i • C i) *ᵥ x) ((∑ i, w i • C i) *ᵥ x) +
        ∑ j, vecMulVec ((∑ i, u j i • C i) *ᵥ x) ((∑ i, u j i • C i) *ᵥ x) := by
  have hrow : ∀ a, (Matrix.of (vecCons w u) * Matrix.of (fun i => C i *ᵥ x)) a =
      (∑ i, vecCons w u a i • C i) *ᵥ x := by
    intro a
    funext r
    simp [mul_apply, sum_mulVec, Finset.sum_apply, smul_mulVec]
  have h1 : ∑ i, vecMulVec (C i *ᵥ x) (C i *ᵥ x) =
      (Matrix.of (fun i => C i *ᵥ x))ᵀ * Matrix.of (fun i => C i *ᵥ x) :=
    Sec5a.sum_outer_eq (Matrix.of (fun i => C i *ᵥ x))
  have h2 : (Matrix.of (fun i => C i *ᵥ x))ᵀ * Matrix.of (fun i => C i *ᵥ x) =
      (Matrix.of (vecCons w u) * Matrix.of (fun i => C i *ᵥ x))ᵀ *
        (Matrix.of (vecCons w u) * Matrix.of (fun i => C i *ᵥ x)) := by
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of (vecCons w u))ᵀ, hO, Matrix.one_mul]
  rw [h1, h2, ← Sec5a.sum_outer_eq, Fin.sum_univ_succ]
  simp only [hrow, cons_val_zero, cons_val_succ]

/-- `w^⊥` has an orthonormal basis `u_1, …, u_k`. -/
lemma exists_orthonormal_perp (w : Fin (k + 1) → ℝ) (hw : w ⬝ᵥ w = 1) :
    ∃ u : Fin k → Fin (k + 1) → ℝ, (∀ j l, u j ⬝ᵥ u l = if j = l then 1 else 0) ∧ ∀ j, u j ⬝ᵥ w = 0 := by
  have hv : Orthonormal ℝ (({0} : Set (Fin (k + 1))).domRestrict
      (fun _ => (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin (k + 1))))) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    rw [ite_eq_left rfl]
    change inner ℝ (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin (k + 1))) (WithLp.toLp 2 w) = 1
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, hw]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b 0 = WithLp.toLp 2 w := hb 0 rfl
  have hon := orthonormal_iff_ite.mp b.orthonormal
  refine ⟨fun j => WithLp.ofLp (b j.succ), fun j l => ?_, fun j => ?_⟩
  · have e := hon l.succ j.succ
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at e
    rw [e]
    by_cases hjl : j = l
    · subst hjl
      simp
    · simp [hjl, Ne.symm hjl]
  · have e := hon 0 j.succ
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, hb0, ite_eq_right (Fin.succ_ne_zero j).symm] at e
    exact e

/-! ### The two shared rows -/

theorem prop_5_2_blocks_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    (∀ i, blkXY (P i) = (blkYX (P i))ᵀ ∧ (blkXX (P i))ᵀ = blkXX (P i) ∧ (blkYY (P i))ᵀ = blkYY (P i)) ∧
      (∀ x : Vec 16, ∑ i, hvec (fun i => blkXX (P i)) x i ^ 2 = (x ⬝ᵥ x) ^ 2) ∧
      ∀ y : Vec 16, ∑ i, hvec (fun i => blkYY (P i)) y i ^ 2 = (y ⬝ᵥ y) ^ 2 := by
  have hb := Sec2.sec2_b_properties_proved R μ κ h
  refine ⟨fun i => ⟨Sec5a.blkXY_of_symm (hP.1 i), by rw [Sec5a.blkXX_transpose, hP.1 i],
    by rw [Sec5a.blkYY_transpose, hP.1 i]⟩, fun x => ?_, fun y => ?_⟩
  · have e := hminus x 0
    rw [mulVec_zero, dotProduct_zero, mul_zero] at e
    simp only [quad_blocks, mulVec_zero, dotProduct_zero, zero_dotProduct, add_zero] at e
    simp only [hvec]
    linarith
  · have e := hminus 0 y
    rw [hb.2.1 y, mul_zero] at e
    simp only [quad_blocks, mulVec_zero, dotProduct_zero, zero_dotProduct, zero_add] at e
    simp only [hvec]
    linarith

theorem prop_5_2_trace_proved (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P) :
    (∀ i j, i ≠ j → P i = -(P j * P i * P j)) ∧ ∀ v : Fin 9 → ℝ, (∑ i, v i • P i).trace = 0 := by
  refine ⟨fun i j hij => ?_, fun v => ?_⟩
  · have hanti : P j * P i = -(P i * P j) := by
      have e := hP.2 i j
      rw [ite_eq_right hij] at e
      exact eq_neg_of_add_eq_zero_right e
    rw [hanti, Matrix.neg_mul, Matrix.mul_assoc, CayleyProducts.system_square P hP j, Matrix.mul_one, neg_neg]
  · rw [trace_sum]
    simp only [trace_smul, Poly.trace_eq_zero_proved 8 (by norm_num) P hP, smul_zero, Finset.sum_const_zero]

end Osserman.Proofs.Sec5bCore
