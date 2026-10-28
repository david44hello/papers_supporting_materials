/-
Osserman/Proofs/Sec5c.lean — Proposition 5.2 of paper 013 (prop:minus, P013_short.tex l. 566-606), the case
`h` not constant (l. 594-606): prop_5_2_H_clifford, prop_5_2_B_zero, prop_5_2_b_formula, prop_5_2_d_eq,
prop_5_2_D_eq, prop_5_2_Q_cayley, prop_5_2_A_cayley; and the closing rows prop_5_2_cases and prop_5_2 (statements
copied verbatim from Osserman/Paper/Statements.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Lemma 4.1(c) makes the `H_i` a symmetric Clifford system, so `H_i² = I` and `H_i² + B_iᵀB_i = I` give `B_i = 0`.
Then `⟨P_iz,z⟩ = h_i(x) + d_i(y)`, and (eq:minus) becomes `b(x,y) = ½(|x|²|y|² - ⟨h(x),d(y)⟩)`. With `b(x,x) = |x|⁴`
this gives `⟨h(x),d(x)⟩ = -|x|⁴`, and `|h(x)| = |d(x)| = |x|²` give `|d(x) + h(x)|² = 0`: the equality case of
Cauchy–Schwarz, written out.
-/
import Osserman.Proofs.Sec5b

namespace Osserman.Proofs.Sec5c

open Osserman Matrix

theorem prop_5_2_H_clifford_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    IsSymmCliffordSystem (fun i => blkXX (P i)) := by
  obtain ⟨hsymm, hnorm, -⟩ := Sec5bCore.prop_5_2_blocks_proved R μ κ h P hP hminus
  exact ⟨fun i => (hsymm i).2.1,
    Threshold.threshold_c (fun i => blkXX (P i)) (fun i => (hsymm i).2.1) hnorm (by norm_num) (by norm_num) hnc⟩

theorem prop_5_2_B_zero_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    ∀ i, blkXX (P i) * blkXX (P i) + (blkYX (P i))ᵀ * blkYX (P i) = 1 ∧ blkYX (P i) = 0 := by
  have hcl := prop_5_2_H_clifford_proved R μ κ h P hP hminus hnc
  intro i
  have hsq := Sec5bCore.sq_XX hP i
  refine ⟨hsq, ?_⟩
  have hH2 : blkXX (P i) * blkXX (P i) = 1 := CayleyProducts.system_square _ hcl i
  rw [hH2] at hsq
  have h0 : (blkYX (P i))ᵀ * blkYX (P i) = 0 := add_left_cancel (hsq.trans (add_zero 1).symm)
  rw [← conjTranspose_eq_transpose_of_trivial] at h0
  exact Matrix.conjTranspose_mul_self_eq_zero.mp h0

theorem prop_5_2_b_formula_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    ∀ x y : Vec 16, (Qmat R μ κ x *ᵥ y) ⬝ᵥ y =
      (1 / 2 : ℝ) * ((x ⬝ᵥ x) * (y ⬝ᵥ y) - hvec (fun i => blkXX (P i)) x ⬝ᵥ hvec (fun i => blkYY (P i)) y) := by
  have hB := fun i => (prop_5_2_B_zero_proved R μ κ h P hP hminus hnc i).2
  obtain ⟨-, hnx, hny⟩ := Sec5bCore.prop_5_2_blocks_proved R μ κ h P hP hminus
  intro x y
  have hterm : ∀ i, (Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32)) =
      hvec (fun i => blkXX (P i)) x i + hvec (fun i => blkYY (P i)) y i := fun i => by
    rw [Sec5bCore.quad_symm (hP.1 i), hB i, zero_mulVec, dotProduct_zero, mul_zero, add_zero]
    rfl
  have hsq : ∀ i, (hvec (fun i => blkXX (P i)) x i + hvec (fun i => blkYY (P i)) y i) ^ 2 =
      hvec (fun i => blkXX (P i)) x i ^ 2 +
        2 * (hvec (fun i => blkXX (P i)) x i * hvec (fun i => blkYY (P i)) y i) +
        hvec (fun i => blkYY (P i)) y i ^ 2 := fun i => by ring
  have hsum : ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2 =
      (x ⬝ᵥ x) ^ 2 + 2 * (hvec (fun i => blkXX (P i)) x ⬝ᵥ hvec (fun i => blkYY (P i)) y) + (y ⬝ᵥ y) ^ 2 := by
    simp only [hterm, hsq, Finset.sum_add_distrib, ← Finset.mul_sum, hnx x, hny y]
    rfl
  have e := hminus x y
  rw [hsum] at e
  linear_combination e / 4

theorem prop_5_2_d_eq_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    ∀ x : Vec 16, hvec (fun i => blkYY (P i)) x = -hvec (fun i => blkXX (P i)) x := by
  obtain ⟨-, hnx, hny⟩ := Sec5bCore.prop_5_2_blocks_proved R μ κ h P hP hminus
  intro x
  have hb := (Sec2.sec2_b_properties_proved R μ κ h).2.2.2 x
  rw [prop_5_2_b_formula_proved R μ κ h P hP hminus hnc x x] at hb
  have haa : hvec (fun i => blkXX (P i)) x ⬝ᵥ hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) ^ 2 := by
    rw [← hnx x]
    simp [dotProduct, sq]
  have hdd : hvec (fun i => blkYY (P i)) x ⬝ᵥ hvec (fun i => blkYY (P i)) x = (x ⬝ᵥ x) ^ 2 := by
    rw [← hny x]
    simp [dotProduct, sq]
  have had : hvec (fun i => blkXX (P i)) x ⬝ᵥ hvec (fun i => blkYY (P i)) x = -(x ⬝ᵥ x) ^ 2 := by
    linear_combination -2 * hb
  have hz : (hvec (fun i => blkYY (P i)) x + hvec (fun i => blkXX (P i)) x) ⬝ᵥ
      (hvec (fun i => blkYY (P i)) x + hvec (fun i => blkXX (P i)) x) = 0 := by
    rw [add_dotProduct, dotProduct_add, dotProduct_add, hdd, haa,
      dotProduct_comm (hvec (fun i => blkYY (P i)) x) (hvec (fun i => blkXX (P i)) x), had]
    ring
  exact eq_neg_of_add_eq_zero_left (dotProduct_self_eq_zero.mp hz)

theorem prop_5_2_D_eq_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    ∀ i, blkYY (P i) = -blkXX (P i) := by
  have hd := prop_5_2_d_eq_proved R μ κ h P hP hminus hnc
  obtain ⟨hsymm, -, -⟩ := Sec5bCore.prop_5_2_blocks_proved R μ κ h P hP hminus
  intro i
  have hz : blkYY (P i) + blkXX (P i) = 0 := by
    apply Sec5a.eq_zero_of_quad
    · rw [transpose_add, (hsymm i).2.2, (hsymm i).2.1]
    · intro x
      have e := congrFun (hd x) i
      simp only [hvec, Pi.neg_apply] at e
      rw [add_mulVec, dotProduct_add, e, neg_add_cancel]
  exact eq_neg_of_add_eq_zero_left hz

theorem prop_5_2_Q_cayley_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    ∀ x : Vec 16, Qmat R μ κ x = (1 / 2 : ℝ) • ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) +
      ∑ i, (x ⬝ᵥ (blkXX (P i) *ᵥ x)) • blkXX (P i)) := by
  have hd := prop_5_2_d_eq_proved R μ κ h P hP hminus hnc
  obtain ⟨hsymm, -, -⟩ := Sec5bCore.prop_5_2_blocks_proved R μ κ h P hP hminus
  intro x
  apply Threshold.symm_eq_of_quadratic
  · show (Qmat R μ κ x)ᵀ = Qmat R μ κ x
    rw [Qmat, transpose_add, Sec2.Amat_symm, transpose_vecMulVec]
  · show ((1 / 2 : ℝ) • ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) +
      ∑ i, (x ⬝ᵥ (blkXX (P i) *ᵥ x)) • blkXX (P i)))ᵀ = _
    rw [transpose_smul, transpose_add, transpose_smul, transpose_one, transpose_sum]
    simp only [transpose_smul, (hsymm _).2.1]
  · intro y
    have hhh : hvec (fun i => blkXX (P i)) x ⬝ᵥ hvec (fun i => blkXX (P i)) y =
        ∑ i, (x ⬝ᵥ (blkXX (P i) *ᵥ x)) * (y ⬝ᵥ (blkXX (P i) *ᵥ y)) := rfl
    rw [dotProduct_comm, prop_5_2_b_formula_proved R μ κ h P hP hminus hnc x y, hd y, dotProduct_neg, hhh]
    simp only [smul_mulVec, add_mulVec, one_mulVec, sum_mulVec, dotProduct_smul, dotProduct_add, dotProduct_sum,
      smul_eq_mul]
    ring

theorem prop_5_2_A_cayley_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    IsSymmCliffordSystem (fun i => blkXX (P i)) ∧ ∀ x : Vec 16, Amat R μ κ x = Acay (fun i => blkXX (P i)) x := by
  refine ⟨prop_5_2_H_clifford_proved R μ κ h P hP hminus hnc, fun x => ?_⟩
  simp only [Acay]
  rw [← prop_5_2_Q_cayley_proved R μ κ h P hP hminus hnc x, Qmat, add_sub_cancel_right]

/-! ### The closing rows -/

theorem prop_5_2_cases_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    ((∀ x y : Vec 16, x ⬝ᵥ x = 1 → y ⬝ᵥ y = 1 →
        hvec (fun i => blkXX (P i)) x = hvec (fun i => blkXX (P i)) y) → IsFormCl8 (Amat R μ κ)) ∧
      ((∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
        hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) → IsFormCayley (Amat R μ κ)) := by
  refine ⟨fun hconst => ?_, fun hnc => ?_⟩
  · obtain ⟨w, hw, hhw, -, -⟩ := Sec5b.prop_5_2_const_rotate_proved R μ κ h P hP hminus hconst
    obtain ⟨u, hu, huw⟩ := Sec5bCore.exists_orthonormal_perp (k := 8) w hw
    obtain ⟨hcl, hA⟩ := Sec5b.prop_5_2_A_Cl8_proved R μ κ h P hP hminus w hw hhw u hu huw
    exact ⟨_, hcl, hA⟩
  · obtain ⟨hcl, hA⟩ := prop_5_2_A_cayley_proved R μ κ h P hP hminus hnc
    exact ⟨_, hcl, hA⟩

theorem prop_5_2_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ)
    (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    IsFormCl8 (Amat R μ κ) ∨ IsFormCayley (Amat R μ κ) := by
  have hc := prop_5_2_cases_proved R μ κ h P hP hminus
  by_cases hconst : ∀ x y : Vec 16, x ⬝ᵥ x = 1 → y ⬝ᵥ y = 1 →
      hvec (fun i => blkXX (P i)) x = hvec (fun i => blkXX (P i)) y
  · exact Or.inl (hc.1 hconst)
  · refine Or.inr (hc.2 ?_)
    by_contra hne
    apply hconst
    intro x y hx hy
    by_contra hxy
    exact hne ⟨x, y, hx, hy, hxy⟩

end Osserman.Proofs.Sec5c
