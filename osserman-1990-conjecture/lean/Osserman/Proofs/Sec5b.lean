/-
Osserman/Proofs/Sec5b.lean — Proposition 5.2 of paper 013 (prop:minus, P013_short.tex l. 566-606), the case
`h` constant (l. 578-592): prop_5_2_const_rotate, prop_5_2_B_w, prop_5_2_D_w, prop_5_2_offdiag, prop_5_2_Q_Cl8,
prop_5_2_B_skew, prop_5_2_A_Cl8 (statements copied verbatim from Osserman/Paper/Statements.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Without coordinates (the rotation of the index takes `w` to `e_0`): with `h(x) = |x|²w`, every combination
`H_v = ∑ v_iH_i` has the quadratic form `|x|²⟨v,w⟩`, so `H_v = ⟨v,w⟩I` (`H_comb`). The upper-left block of
`P_w² = I` gives `B_w = 0`; its lower-right block gives `D_w² = I`, and `tr P_w = 0` gives `tr D_w = -16`; then
`E = D_w + I` has `EᵀE = 2E` with trace `0`, so `E = 0`. The lower-right block of `P_uP_w + P_wP_u = 0` gives
`D_u = 0` for `u ⊥ w`, hence `D_v = -⟨v,w⟩I` (`D_comb`).
-/
import Osserman.Proofs.Sec5bCore

namespace Osserman.Proofs.Sec5b

open Osserman Matrix

/-! ### The combinations `H_v` and `D_v` -/

/-- `⟨H_vx,x⟩ = |x|²⟨v,w⟩`. -/
lemma H_quad {P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ} {w : Fin 9 → ℝ}
    (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) (v : Fin 9 → ℝ) (x : Vec 16) :
    x ⬝ᵥ ((∑ i, v i • blkXX (P i)) *ᵥ x) = (x ⬝ᵥ x) * (v ⬝ᵥ w) :=
  Sec5bCore.comb_quad (C := fun i => blkXX (P i)) hhw v x

/-- `H_v = ⟨v,w⟩I`. -/
lemma H_comb {P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ} (hP : IsSymmCliffordSystem P) {w : Fin 9 → ℝ}
    (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) (v : Fin 9 → ℝ) :
    ∑ i, v i • blkXX (P i) = (v ⬝ᵥ w) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  apply Threshold.symm_eq_of_quadratic
  · exact Sec5bCore.comb_transpose (fun i => by rw [Sec5a.blkXX_transpose, hP.1 i]) v
  · show ((v ⬝ᵥ w) • (1 : Matrix (Fin 16) (Fin 16) ℝ))ᵀ = _
    rw [transpose_smul, transpose_one]
  · intro x
    rw [H_quad hhw v x, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, mul_comm]

lemma D_symm {P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ} (hP : IsSymmCliffordSystem P) (v : Fin 9 → ℝ) :
    (∑ i, v i • blkYY (P i))ᵀ = ∑ i, v i • blkYY (P i) :=
  Sec5bCore.comb_transpose (fun i => by rw [Sec5a.blkYY_transpose, hP.1 i]) v

/-! ### The rows -/

theorem prop_5_2_const_rotate_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hconst : ∀ x y : Vec 16, x ⬝ᵥ x = 1 → y ⬝ᵥ y = 1 →
      hvec (fun i => blkXX (P i)) x = hvec (fun i => blkXX (P i)) y) :
    ∃ w : Fin 9 → ℝ, w ⬝ᵥ w = 1 ∧ (∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) ∧
      Hcomb (fun i => blkXX (P i)) w = 1 ∧ ∀ u : Fin 9 → ℝ, u ⬝ᵥ w = 0 → Hcomb (fun i => blkXX (P i)) u = 0 := by
  have hnorm := (Sec5bCore.prop_5_2_blocks_proved R μ κ h P hP hminus).2.1
  have he : (Pi.single 0 1 : Vec 16) ⬝ᵥ Pi.single 0 1 = 1 := by simp
  have hw := Threshold.hvec_unit (fun i => blkXX (P i)) hnorm _ he
  have hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x =
      (x ⬝ᵥ x) • hvec (fun i => blkXX (P i)) (Pi.single 0 1) := by
    intro x
    obtain ⟨s, u, hu, rfl⟩ := Spectral.exists_unit_scale x
    rw [Threshold.hvec_smul, hconst u _ hu he, smul_dotProduct, dotProduct_smul, hu, smul_eq_mul, smul_eq_mul,
      mul_one, sq]
  refine ⟨_, hw, hhw, ?_, fun u hu => ?_⟩
  · simp only [Hcomb]
    rw [H_comb hP hhw, hw, one_smul]
  · simp only [Hcomb]
    rw [H_comb hP hhw, hu, zero_smul]

theorem prop_5_2_B_w_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) :
    (∑ i, w i • blkXX (P i)) * (∑ i, w i • blkXX (P i)) + (∑ i, w i • blkYX (P i))ᵀ * (∑ i, w i • blkYX (P i)) = 1 ∧
      ∑ i, w i • blkYX (P i) = 0 := by
  have e := Sec5bCore.comb_rel_XX hP w w
  rw [hw, mul_one, ← two_smul ℝ] at e
  have hsq : (∑ i, w i • blkXX (P i)) * (∑ i, w i • blkXX (P i)) +
      (∑ i, w i • blkYX (P i))ᵀ * (∑ i, w i • blkYX (P i)) = 1 := smul_right_injective _ two_ne_zero e
  refine ⟨hsq, ?_⟩
  have hH : ∑ i, w i • blkXX (P i) = 1 := by rw [H_comb hP hhw w, hw, one_smul]
  rw [hH, Matrix.one_mul] at hsq
  have h0 : (∑ i, w i • blkYX (P i))ᵀ * (∑ i, w i • blkYX (P i)) = 0 :=
    add_left_cancel (hsq.trans (add_zero 1).symm)
  rw [← conjTranspose_eq_transpose_of_trivial] at h0
  exact Matrix.conjTranspose_mul_self_eq_zero.mp h0

theorem prop_5_2_D_w_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) :
    (∑ i, w i • blkYY (P i)) * (∑ i, w i • blkYY (P i)) = 1 ∧ (∑ i, w i • blkYY (P i)).trace = -16 ∧
      ∑ i, w i • blkYY (P i) = -1 := by
  have hBw := (prop_5_2_B_w_proved R μ κ h P hP hminus w hw hhw).2
  have hH : ∑ i, w i • blkXX (P i) = 1 := by rw [H_comb hP hhw w, hw, one_smul]
  have e := Sec5bCore.comb_rel_YY hP w w
  rw [hBw, Matrix.zero_mul, zero_add, hw, mul_one, ← two_smul ℝ] at e
  have hsq : (∑ i, w i • blkYY (P i)) * (∑ i, w i • blkYY (P i)) = 1 := smul_right_injective _ two_ne_zero e
  have htr : (∑ i, w i • blkYY (P i)).trace = -16 := by
    have t := (Sec5bCore.prop_5_2_trace_proved P hP).2 w
    rw [Sec5bCore.trace_blocks, Sec5bCore.blkXX_comb, Sec5bCore.blkYY_comb, hH, trace_one, Fintype.card_fin,
      Nat.cast_ofNat] at t
    linarith
  refine ⟨hsq, htr, ?_⟩
  have hDs := D_symm hP w
  set D := ∑ i, w i • blkYY (P i) with hD
  have hE : (D + 1)ᴴ * (D + 1) = (2 : ℝ) • (D + 1) := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_add, hDs, transpose_one, add_mul, mul_add, mul_add, hsq]
    simp only [Matrix.mul_one, Matrix.one_mul]
    rw [two_smul]
    abel
  have htr0 : ((D + 1)ᴴ * (D + 1)).trace = 0 := by
    rw [hE, trace_smul, trace_add, htr, trace_one, Fintype.card_fin]
    norm_num
  exact eq_neg_of_add_eq_zero_left (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr0)

theorem prop_5_2_offdiag_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) :
    ∀ u : Fin 9 → ℝ, u ⬝ᵥ w = 0 → ∑ i, u i • blkXX (P i) = 0 ∧ ∑ i, u i • blkYY (P i) = 0 := by
  have hBw := (prop_5_2_B_w_proved R μ κ h P hP hminus w hw hhw).2
  have hDw := (prop_5_2_D_w_proved R μ κ h P hP hminus w hw hhw).2.2
  intro u hu
  refine ⟨by rw [H_comb hP hhw u, hu, zero_smul], ?_⟩
  have e := Sec5bCore.comb_rel_YY hP u w
  rw [hBw, hDw, hu] at e
  simp only [transpose_zero, Matrix.zero_mul, zero_add, Matrix.mul_neg, Matrix.mul_one,
    Matrix.neg_mul, Matrix.one_mul, mul_zero, zero_smul] at e
  have h2 : (2 : ℝ) • ∑ i, u i • blkYY (P i) = 0 := by
    rw [two_smul, ← neg_eq_zero, neg_add]
    exact e
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- `D_v = -⟨v,w⟩I`. -/
lemma D_comb (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w)
    (v : Fin 9 → ℝ) : ∑ i, v i • blkYY (P i) = -(v ⬝ᵥ w) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  rw [Sec5bCore.comb_split _ v w, (prop_5_2_D_w_proved R μ κ h P hP hminus w hw hhw).2.2,
    (prop_5_2_offdiag_proved R μ κ h P hP hminus w hw hhw _ (Sec5bCore.perp_part hw v)).2, add_zero, smul_neg,
    neg_smul]

/-- (eq:minus) in the case `h` constant: `⟨Q(x)y,y⟩ = |x|²|y|² - ∑_i ⟨B_ix,y⟩²`. -/
lemma minus_reduced (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w)
    (x y : Vec 16) :
    (Qmat R μ κ x *ᵥ y) ⬝ᵥ y = (x ⬝ᵥ x) * (y ⬝ᵥ y) - ∑ i, (y ⬝ᵥ (blkYX (P i) *ᵥ x)) ^ 2 := by
  have hBw := (prop_5_2_B_w_proved R μ κ h P hP hminus w hw hhw).2
  have hHi : ∀ i, x ⬝ᵥ (blkXX (P i) *ᵥ x) = (x ⬝ᵥ x) * w i := fun i => by
    simpa [hvec] using congrFun (hhw x) i
  have hDi : ∀ i, y ⬝ᵥ (blkYY (P i) *ᵥ y) = -(w i) * (y ⬝ᵥ y) := fun i => by
    have e := D_comb R μ κ h P hP hminus w hw hhw (Pi.single i 1)
    rw [Sec5bCore.sum_single, single_one_dotProduct] at e
    rw [e, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  have hc : ∑ i, w i * (y ⬝ᵥ (blkYX (P i) *ᵥ x)) = 0 := by
    have e : y ⬝ᵥ ((∑ i, w i • blkYX (P i)) *ᵥ x) = ∑ i, w i * (y ⬝ᵥ (blkYX (P i) *ᵥ x)) := by
      rw [sum_mulVec, dotProduct_sum]
      simp only [smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [← e, hBw, zero_mulVec, dotProduct_zero]
  have hww : ∑ i, w i ^ 2 = 1 := by
    rw [← hw]
    simp [dotProduct, sq]
  have hterm : ∀ i, (Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32)) =
      (x ⬝ᵥ x - y ⬝ᵥ y) * w i + 2 * (y ⬝ᵥ (blkYX (P i) *ᵥ x)) := fun i => by
    rw [Sec5bCore.quad_symm (hP.1 i), hHi i, hDi i]
    ring
  have hsq : ∀ i, ((x ⬝ᵥ x - y ⬝ᵥ y) * w i + 2 * (y ⬝ᵥ (blkYX (P i) *ᵥ x))) ^ 2 =
      (x ⬝ᵥ x - y ⬝ᵥ y) ^ 2 * w i ^ 2 + 4 * (x ⬝ᵥ x - y ⬝ᵥ y) * (w i * (y ⬝ᵥ (blkYX (P i) *ᵥ x))) +
        4 * (y ⬝ᵥ (blkYX (P i) *ᵥ x)) ^ 2 := fun i => by ring
  have hsum : ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2 =
      (x ⬝ᵥ x - y ⬝ᵥ y) ^ 2 + 4 * ∑ i, (y ⬝ᵥ (blkYX (P i) *ᵥ x)) ^ 2 := by
    simp only [hterm, hsq, Finset.sum_add_distrib, ← Finset.mul_sum, hww, hc]
    ring
  have e := hminus x y
  rw [hsum] at e
  linear_combination e / 4

theorem prop_5_2_Q_Cl8_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) :
    ∀ x : Vec 16, Qmat R μ κ x =
      (x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - ∑ i, vecMulVec (blkYX (P i) *ᵥ x) (blkYX (P i) *ᵥ x) := by
  intro x
  apply Threshold.symm_eq_of_quadratic
  · show (Qmat R μ κ x)ᵀ = Qmat R μ κ x
    rw [Qmat, transpose_add, Sec2.Amat_symm, transpose_vecMulVec]
  · show ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) -
      ∑ i, vecMulVec (blkYX (P i) *ᵥ x) (blkYX (P i) *ᵥ x))ᵀ = _
    rw [transpose_sub, transpose_smul, transpose_one, transpose_sum]
    simp only [transpose_vecMulVec]
  · intro y
    rw [dotProduct_comm, minus_reduced R μ κ h P hP hminus w hw hhw x y, sub_mulVec, smul_mulVec, one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, sum_mulVec, dotProduct_sum]
    simp only [Threshold.quadratic_outer, dotProduct_comm (blkYX (P _) *ᵥ x) y]

theorem prop_5_2_B_skew_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) :
    (∀ x : Vec 16, ∑ i, (x ⬝ᵥ (blkYX (P i) *ᵥ x)) ^ 2 = 0) ∧ (∀ i, (blkYX (P i))ᵀ = -blkYX (P i)) ∧
      ∀ u v : Fin 9 → ℝ, u ⬝ᵥ w = 0 → v ⬝ᵥ w = 0 →
        (∑ i, u i • blkYX (P i)) * (∑ i, v i • blkYX (P i)) + (∑ i, v i • blkYX (P i)) * (∑ i, u i • blkYX (P i)) =
          (-2 * (u ⬝ᵥ v)) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  have hzero : ∀ x : Vec 16, ∑ i, (x ⬝ᵥ (blkYX (P i) *ᵥ x)) ^ 2 = 0 := by
    intro x
    have e := minus_reduced R μ κ h P hP hminus w hw hhw x x
    rw [(Sec2.sec2_b_properties_proved R μ κ h).2.2.2 x] at e
    linarith
  have hskew : ∀ i, (blkYX (P i))ᵀ = -blkYX (P i) := by
    intro i
    have hz : blkYX (P i) + (blkYX (P i))ᵀ = 0 := by
      apply Sec5a.eq_zero_of_quad
      · rw [transpose_add, transpose_transpose, add_comm]
      · intro x
        rw [add_mulVec, dotProduct_add, Sec5a.dot_transpose,
          Sec5bCore.sq_sum_zero (f := fun i => x ⬝ᵥ (blkYX (P i) *ᵥ x)) (hzero x) i, add_zero]
    exact eq_neg_of_add_eq_zero_right hz
  refine ⟨hzero, hskew, fun u v hu hv => ?_⟩
  have hsk : ∀ a : Fin 9 → ℝ, (∑ i, a i • blkYX (P i))ᵀ = -∑ i, a i • blkYX (P i) := fun a => by
    rw [transpose_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [transpose_smul, hskew i, smul_neg]
  have e := Sec5bCore.comb_rel_XX hP u v
  rw [H_comb hP hhw u, H_comb hP hhw v, hu, hv, zero_smul, hsk u, hsk v] at e
  simp only [Matrix.zero_mul, zero_add, Matrix.neg_mul] at e
  rw [neg_mul, neg_smul, ← e, neg_add, neg_neg, neg_neg]

theorem prop_5_2_A_Cl8_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w)
    (u : Fin 8 → Fin 9 → ℝ) (hu : ∀ j k, u j ⬝ᵥ u k = if j = k then 1 else 0) (huw : ∀ j, u j ⬝ᵥ w = 0) :
    IsCliffordStr (fun j => ∑ i, u j i • blkYX (P i)) ∧
      ∀ x : Vec 16, Amat R μ κ x =
        Pi x - ∑ j, vecMulVec ((∑ i, u j i • blkYX (P i)) *ᵥ x) ((∑ i, u j i • blkYX (P i)) *ᵥ x) := by
  obtain ⟨-, hskew, hrel⟩ := prop_5_2_B_skew_proved R μ κ h P hP hminus w hw hhw
  have hBw := (prop_5_2_B_w_proved R μ κ h P hP hminus w hw hhw).2
  have hQ := prop_5_2_Q_Cl8_proved R μ κ h P hP hminus w hw hhw
  refine ⟨⟨fun j => ?_, fun j k => ?_⟩, fun x => ?_⟩
  · dsimp only
    rw [transpose_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [transpose_smul, hskew i, smul_neg]
  · dsimp only
    rw [hrel (u j) (u k) (huw j) (huw k), hu j k]
    split_ifs
    · ext r c
      by_cases hrc : r = c
      · subst hrc
        simp [ofNat_apply]
      · simp [hrc, ofNat_apply]
    · simp
  · have hA : Amat R μ κ x = Qmat R μ κ x - vecMulVec x x := by
      rw [Qmat, add_sub_cancel_right]
    rw [hA, hQ x, Sec5bCore.parseval_outer _ w u (Sec5bCore.frame_orth w u hw hu huw) x, hBw, zero_mulVec,
      vecMulVec_zero, zero_add, Osserman.Pi, sub_right_comm]

end Osserman.Proofs.Sec5b
