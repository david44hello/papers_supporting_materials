/-
Osserman/Proofs/Lem21.lean — proofs of Lemma 2.1 of paper 013 (the quartic F on ℝ^32, l. 388-412): lem_2_1_b_steps,
lem_2_1_lap_b_trace, lem_2_1, lem_2_1_values.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

METHOD. `∂_{y_i} b = ∑_k Q_ik y_k + ∑_j Q_ji y_j` is computed as a polynomial (the entries `Q_jk` involve only the
`x`-variables). The `x`-derivatives come from the symmetry `b(x,y) = b(y,x)`: `bP` is fixed by the renaming `flip` that
swaps the two blocks of variables, so `∂_{x_i} b = flip(∂_{y_i} b)`. Polynomial identities are checked by
`MvPolynomial.funext` (equal values at every point `z = (x, y)`).
-/
import Osserman.Proofs.Sec2
import Osserman.Proofs.Spectral

namespace Osserman.Proofs.Lem21

open Osserman Matrix MvPolynomial

/-! ### Points of `ℝ^32 = ℝ^16 ⊕ ℝ^16` -/

lemma exists_append (z : Vec 32) : ∃ x y : Vec 16, z = Fin.append x y :=
  ⟨_, _, (Fin.append_castAdd_natAdd (m := 16) (n := 16) (f := z)).symm⟩

lemma dot_append (x y : Vec 16) : (Fin.append x y : Vec 32) ⬝ᵥ Fin.append x y = x ⬝ᵥ x + y ⬝ᵥ y := by
  rw [← Osserman.Proofs.Poly.eval_sqP, Osserman.Proofs.Sec2.eval_sqP_append]

lemma smul_append (c : ℝ) (x y : Vec 16) : c • (Fin.append x y : Vec 32) = Fin.append (c • x) (c • y) := by
  conv_lhs => rw [← Fin.append_castAdd_natAdd (m := 16) (n := 16) (f := c • (Fin.append x y : Vec 32))]
  congr 1 <;> funext a <;> simp only [Pi.smul_apply, Fin.append_left, Fin.append_right]

lemma sum_split {M : Type*} [AddCommMonoid M] (f : Fin 32 → M) :
    ∑ i, f i = ∑ a : Fin 16, f (Fin.castAdd 16 a) + ∑ a : Fin 16, f (Fin.natAdd 16 a) :=
  Fin.sum_univ_add (a := 16) (b := 16) f

/-! ### The flip `(x, y) ↦ (y, x)` -/

/-- The renaming of variables that swaps the `x`-block and the `y`-block. -/
def flip : Fin 32 ≃ Fin 32 := finAddFlip (m := 16) (n := 16)

lemma flip_castAdd (a : Fin 16) : flip (Fin.castAdd 16 a) = Fin.natAdd 16 a := finAddFlip_apply_castAdd a 16

lemma flip_natAdd (a : Fin 16) : flip (Fin.natAdd 16 a) = Fin.castAdd 16 a := finAddFlip_apply_natAdd a 16

lemma append_comp_flip (x y : Vec 16) : (Fin.append x y : Vec 32) ∘ flip = Fin.append y x := by
  rw [← Fin.append_castAdd_natAdd (m := 16) (n := 16) (f := (Fin.append x y : Vec 32) ∘ flip)]
  congr 1 <;> funext a <;>
    simp only [Function.comp_apply, flip_castAdd, flip_natAdd, Fin.append_left, Fin.append_right]

lemma eval_rename_flip (p : MvPolynomial (Fin 32) ℝ) (x y : Vec 16) :
    eval (Fin.append x y : Vec 32) (rename flip p) = eval (Fin.append y x : Vec 32) p := by
  rw [eval_rename, append_comp_flip]

lemma pderiv_castAdd_rename_flip (i : Fin 16) (p : MvPolynomial (Fin 32) ℝ) :
    pderiv (Fin.castAdd 16 i) (rename flip p) = rename flip (pderiv (Fin.natAdd 16 i) p) := by
  rw [← flip_natAdd i]
  exact pderiv_rename flip.injective _ _

/-! ### `Q(x)` is symmetric; `b` is symmetric in `x, y` -/

lemma Qmat_symm (R : CurvTensor 16) (μ κ : ℝ) (x : Vec 16) : (Qmat R μ κ x)ᵀ = Qmat R μ κ x := by
  rw [Qmat, transpose_add, Osserman.Proofs.Sec2.Amat_symm, transpose_vecMulVec]

lemma bP_flip (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) : rename flip (bP R μ κ) = bP R μ κ := by
  apply MvPolynomial.funext
  intro z
  obtain ⟨x, y, rfl⟩ := exists_append z
  rw [eval_rename_flip, Osserman.Proofs.Sec2.eval_bP, Osserman.Proofs.Sec2.eval_bP]
  exact ((Osserman.Proofs.Sec2.sec2_b_properties_proved R μ κ h).1 x y).symm

/-! ### Derivatives in the `y`-variables -/

lemma castAdd_ne_natAdd (a b : Fin 16) : (Fin.castAdd 16 a : Fin 32) ≠ Fin.natAdd 16 b := by
  intro e
  have hv := congrArg Fin.val e
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have := a.isLt
  omega

lemma pderiv_y_xP (i a : Fin 16) : pderiv (Fin.natAdd 16 i : Fin 32) (xP a) = 0 :=
  pderiv_X_of_ne (castAdd_ne_natAdd a i)

lemma pderiv_y_yP (i k : Fin 16) : pderiv (Fin.natAdd 16 i : Fin 32) (yP k) = if k = i then 1 else 0 := by
  split_ifs with hk
  · subst hk
    exact pderiv_X_self _
  · refine pderiv_X_of_ne fun e => hk (Fin.ext ?_)
    have hv := congrArg Fin.val e
    simp only [Fin.val_natAdd] at hv
    omega

lemma pderiv_y_jacEntryP (R : CurvTensor 16) (i j k : Fin 16) :
    pderiv (Fin.natAdd 16 i : Fin 32) (jacEntryP R j k) = 0 := by
  simp only [jacEntryP, map_sum, pderiv_mul, pderiv_C, pderiv_y_xP, mul_zero, zero_mul, add_zero,
    Finset.sum_const_zero]

lemma pderiv_y_piEntryP (i j k : Fin 16) : pderiv (Fin.natAdd 16 i : Fin 32) (piEntryP j k) = 0 := by
  unfold piEntryP
  split_ifs <;> simp only [map_sub, map_sum, map_zero, pderiv_mul, Osserman.Proofs.Poly.pderiv_sq, pderiv_y_xP,
    mul_zero, zero_mul, add_zero, sub_zero, Finset.sum_const_zero]

lemma pderiv_y_qEntryP (R : CurvTensor 16) (μ κ : ℝ) (i j k : Fin 16) :
    pderiv (Fin.natAdd 16 i : Fin 32) (qEntryP R μ κ j k) = 0 := by
  simp only [qEntryP, map_add, map_sub, pderiv_mul, pderiv_C, pderiv_y_xP, pderiv_y_jacEntryP, pderiv_y_piEntryP,
    mul_zero, zero_mul, add_zero, sub_zero]

/-- `∂_{y_i} b = ∑_k Q_ik y_k + ∑_j Q_ji y_j` (as polynomials). -/
lemma pderiv_y_bP (R : CurvTensor 16) (μ κ : ℝ) (i : Fin 16) :
    pderiv (Fin.natAdd 16 i : Fin 32) (bP R μ κ) =
      ∑ k, qEntryP R μ κ i k * yP k + ∑ j, qEntryP R μ κ j i * yP j := by
  have h1 : ∀ j k, pderiv (Fin.natAdd 16 i : Fin 32) (qEntryP R μ κ j k * yP j * yP k) =
      (if j = i then qEntryP R μ κ j k * yP k else 0) + (if k = i then qEntryP R μ κ j k * yP j else 0) := by
    intro j k
    rw [pderiv_mul, pderiv_mul, pderiv_y_qEntryP, pderiv_y_yP, pderiv_y_yP]
    split_ifs <;> ring
  have e1 : ∑ j, ∑ k, (if j = i then qEntryP R μ κ j k * yP k else 0) = ∑ k, qEntryP R μ κ i k * yP k := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have e2 : ∑ j, ∑ k, (if k = i then qEntryP R μ κ j k * yP j else 0) = ∑ j, qEntryP R μ κ j i * yP j := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [bP, map_sum]
  simp only [map_sum, h1, Finset.sum_add_distrib]
  rw [e1, e2]

/-- `∂_{y_i}∂_{y_i} b = 2Q_ii`. -/
lemma pderiv_y_y_bP (R : CurvTensor 16) (μ κ : ℝ) (i : Fin 16) :
    pderiv (Fin.natAdd 16 i : Fin 32) (pderiv (Fin.natAdd 16 i : Fin 32) (bP R μ κ)) = 2 * qEntryP R μ κ i i := by
  have h2 : ∀ j k l, pderiv (Fin.natAdd 16 i : Fin 32) (qEntryP R μ κ j k * yP l) =
      if l = i then qEntryP R μ κ j k else 0 := by
    intro j k l
    rw [pderiv_mul, pderiv_y_qEntryP, pderiv_y_yP]
    split_ifs <;> ring
  rw [pderiv_y_bP, map_add, map_sum, map_sum]
  simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- `∂_{y_i} b (x, y) = 2(Q(x)y)_i`. -/
lemma eval_pderiv_y_bP (R : CurvTensor 16) (μ κ : ℝ) (x y : Vec 16) (i : Fin 16) :
    eval (Fin.append x y : Vec 32) (pderiv (Fin.natAdd 16 i : Fin 32) (bP R μ κ)) = 2 * (Qmat R μ κ x *ᵥ y) i := by
  have hs : ∀ j, Qmat R μ κ x j i = Qmat R μ κ x i j := fun j => by
    rw [← transpose_apply (Qmat R μ κ x) i j, Qmat_symm]
  rw [pderiv_y_bP]
  simp only [map_add, map_sum, map_mul, Osserman.Proofs.Sec2.eval_qEntryP, Osserman.Proofs.Sec2.eval_yP, mulVec,
    dotProduct]
  rw [two_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hs]

/-! ### Derivatives in the `x`-variables, by the flip -/

lemma pderiv_x_bP (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) (i : Fin 16) :
    pderiv (Fin.castAdd 16 i : Fin 32) (bP R μ κ) = rename flip (pderiv (Fin.natAdd 16 i : Fin 32) (bP R μ κ)) := by
  conv_lhs => rw [← bP_flip R μ κ h]
  exact pderiv_castAdd_rename_flip i _

lemma eval_pderiv_x_bP (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) (x y : Vec 16) (i : Fin 16) :
    eval (Fin.append x y : Vec 32) (pderiv (Fin.castAdd 16 i : Fin 32) (bP R μ κ)) = 2 * (Qmat R μ κ y *ᵥ x) i := by
  rw [pderiv_x_bP R μ κ h, eval_rename_flip, eval_pderiv_y_bP]

lemma pderiv_x_x_bP (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) (i : Fin 16) :
    pderiv (Fin.castAdd 16 i : Fin 32) (pderiv (Fin.castAdd 16 i : Fin 32) (bP R μ κ)) =
      rename flip (2 * qEntryP R μ κ i i) := by
  rw [pderiv_x_bP R μ κ h, pderiv_castAdd_rename_flip, pderiv_y_y_bP]

/-! ### `|∇b|²`, `⟨z, ∇b⟩`, `Δb` -/

/-- `|Q(u)v|² = |u|²⟨Q(u)v, v⟩`, from `Q(u)² = |u|²Q(u)`. -/
lemma Qmat_norm_sq (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) (u v : Vec 16) :
    (Qmat R μ κ u *ᵥ v) ⬝ᵥ (Qmat R μ κ u *ᵥ v) = (u ⬝ᵥ u) * ((Qmat R μ κ u *ᵥ v) ⬝ᵥ v) := by
  have hQQ := ((Osserman.Proofs.Spectral.sec2_Q_properties_proved R μ κ h).1 u).1
  rw [Osserman.Proofs.Poly.mulVec_dotProduct_eq, Qmat_symm, mulVec_mulVec, hQQ, smul_mulVec, dotProduct_smul,
    smul_eq_mul, dotProduct_comm v]

lemma sum_two_mul_sq (w : Vec 16) : ∑ a, (2 * w a) ^ 2 = 4 * (w ⬝ᵥ w) := by
  simp only [dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma sum_mul_two_mul (v w : Vec 16) : ∑ a, v a * (2 * w a) = 2 * (w ⬝ᵥ v) := by
  simp only [dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma eval_X_castAdd (x y : Vec 16) (a : Fin 16) :
    eval (Fin.append x y : Vec 32) (X (Fin.castAdd 16 a)) = x a := by
  rw [eval_X, Fin.append_left]

lemma eval_X_natAdd (x y : Vec 16) (a : Fin 16) :
    eval (Fin.append x y : Vec 32) (X (Fin.natAdd 16 a)) = y a := by
  rw [eval_X, Fin.append_right]

lemma gradSqP_bP (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    gradSqP (bP R μ κ) = 4 * sqP 32 * bP R μ κ := by
  have hsym := (Osserman.Proofs.Sec2.sec2_b_properties_proved R μ κ h).1
  apply MvPolynomial.funext
  intro z
  obtain ⟨x, y, rfl⟩ := exists_append z
  rw [gradSqP, map_sum, sum_split]
  simp only [map_pow, eval_pderiv_x_bP R μ κ h, eval_pderiv_y_bP, sum_two_mul_sq, Qmat_norm_sq R μ κ h]
  rw [map_mul, map_mul, Osserman.Proofs.Sec2.eval_sqP_append, Osserman.Proofs.Sec2.eval_bP, map_ofNat, hsym y x]
  ring

lemma euler_bP (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    ∑ i, X i * pderiv i (bP R μ κ) = 4 * bP R μ κ := by
  have hsym := (Osserman.Proofs.Sec2.sec2_b_properties_proved R μ κ h).1
  apply MvPolynomial.funext
  intro z
  obtain ⟨x, y, rfl⟩ := exists_append z
  rw [map_sum, sum_split]
  simp only [map_mul, eval_X_castAdd, eval_X_natAdd, eval_pderiv_x_bP R μ κ h, eval_pderiv_y_bP, sum_mul_two_mul]
  rw [Osserman.Proofs.Sec2.eval_bP, map_ofNat, hsym y x]
  ring

lemma trace_eq_sum (M : Matrix (Fin 16) (Fin 16) ℝ) : M.trace = ∑ a, M a a := rfl

/-! ### The four statements -/

theorem lem_2_1_lap_b_trace_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) (x y : Vec 16) :
    eval (Fin.append x y : Vec 32) (lapP (bP R μ κ)) = 2 * (Qmat R μ κ x).trace + 2 * (Qmat R μ κ y).trace := by
  rw [lapP, map_sum, sum_split]
  simp only [pderiv_x_x_bP R μ κ h, pderiv_y_y_bP, eval_rename_flip, map_mul, map_ofNat,
    Osserman.Proofs.Sec2.eval_qEntryP, trace_eq_sum, Finset.mul_sum]
  ring

theorem lem_2_1_b_steps_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    (∀ (x y : Vec 16) (j : Fin 16),
        eval (Fin.append x y : Vec 32) (pderiv (Fin.natAdd 16 j) (bP R μ κ)) = 2 * (Qmat R μ κ x *ᵥ y) j ∧
        eval (Fin.append x y : Vec 32) (pderiv (Fin.castAdd 16 j) (bP R μ κ)) = 2 * (Qmat R μ κ y *ᵥ x) j) ∧
      gradSqP (bP R μ κ) = 4 * sqP 32 * bP R μ κ ∧ ∑ i, X i * pderiv i (bP R μ κ) = 4 * bP R μ κ ∧
      lapP (bP R μ κ) = 16 * sqP 32 := by
  refine ⟨fun x y j => ⟨eval_pderiv_y_bP R μ κ x y j, eval_pderiv_x_bP R μ κ h x y j⟩, gradSqP_bP R μ κ h,
    euler_bP R μ κ h, ?_⟩
  apply MvPolynomial.funext
  intro z
  obtain ⟨x, y, rfl⟩ := exists_append z
  have htr := fun u => ((Osserman.Proofs.Spectral.sec2_Q_properties_proved R μ κ h).1 u).2.2
  rw [lem_2_1_lap_b_trace_proved R μ κ h, htr, htr, map_mul, map_ofNat, Osserman.Proofs.Sec2.eval_sqP_append]
  ring

/-! ### Values -/

lemma inv_sqrt_two_sq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]

lemma Qmat_smul (R : CurvTensor 16) (μ κ : ℝ) (t : ℝ) (x : Vec 16) :
    Qmat R μ κ (t • x) = (t * t) • Qmat R μ κ x := by
  rw [Qmat, Qmat, Osserman.Proofs.Spectral.Amat_smul, smul_vecMulVec, vecMulVec_smul, smul_add, smul_smul]

/-- For unit `x` and `y ∈ L(x)`: `Q(x)y = y` (`Q(x) = |x|²Pr = Pr` and `Pr` fixes its range). -/
lemma Qmat_fix (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) {x y : Vec 16} (hx : x ⬝ᵥ x = 1)
    (hy : y ∈ Lsub R μ κ x) : Qmat R μ κ x *ᵥ y = y := by
  have hx0 : x ≠ 0 := fun h0 => by
    rw [h0, dotProduct_zero] at hx
    exact zero_ne_one hx
  obtain ⟨-, Pr, -, hPP, hrange, hQ⟩ := (Osserman.Proofs.Spectral.sec2_Q_properties_proved R μ κ h).2 x hx0
  rw [← hrange] at hy
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hy
  rw [hQ, hx, one_smul, Matrix.toLin'_apply, mulVec_mulVec, hPP]

theorem lem_2_1_values_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    (∀ x : Vec 16, x ⬝ᵥ x = 1 → eval (Fin.append x (0 : Vec 16) : Vec 32) (quarticP R μ κ) = 1) ∧
      ∀ x y : Vec 16, x ⬝ᵥ x = 1 → y ⬝ᵥ y = 1 → y ∈ Lsub R μ κ x →
        eval ((Real.sqrt 2)⁻¹ • (Fin.append x y : Vec 32)) (quarticP R μ κ) = -1 := by
  refine ⟨fun x hx => ?_, fun x y hx hy hyL => ?_⟩
  · rw [Osserman.Proofs.Sec2.sec2_F_eval_proved, hx, mulVec_zero, dotProduct_zero]
    norm_num
  · have ht := inv_sqrt_two_sq
    rw [smul_append, Osserman.Proofs.Sec2.sec2_F_eval_proved, Qmat_smul, smul_mulVec, mulVec_smul,
      Qmat_fix R μ κ h hx hyL]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hx, hy]
    linear_combination (-4 * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ + 1 / 2)) * ht

lemma mem_Lsub_self (R : CurvTensor 16) (μ κ : ℝ) (x : Vec 16) : x ∈ Lsub R μ κ x := by
  unfold Lsub
  exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self x)

/-- The unit vector `e_0` of `ℝ^16`. -/
noncomputable def e0 : Vec 16 := Pi.single 0 1

lemma e0_unit : e0 ⬝ᵥ e0 = 1 := by
  simp [e0]

lemma append_e0_zero_unit : (Fin.append e0 (0 : Vec 16) : Vec 32) ⬝ᵥ Fin.append e0 (0 : Vec 16) = 1 := by
  rw [dot_append, e0_unit, dotProduct_zero, add_zero]

lemma append_e0_e0_unit :
    ((Real.sqrt 2)⁻¹ • (Fin.append e0 e0 : Vec 32)) ⬝ᵥ ((Real.sqrt 2)⁻¹ • (Fin.append e0 e0 : Vec 32)) = 1 := by
  rw [smul_dotProduct, dotProduct_smul, dot_append, e0_unit, smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_sqrt_two_sq]
  norm_num

lemma gradSqP_quarticP (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    gradSqP (quarticP R μ κ) = 16 * sqP 32 ^ 3 := by
  obtain ⟨-, hgrad, heuler, -⟩ := lem_2_1_b_steps_proved R μ κ h
  rw [Osserman.Proofs.Sec2.lem_2_1_grad_expand_proved, heuler, hgrad]
  ring

lemma lapP_quarticP (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    lapP (quarticP R μ κ) = 8 * sqP 32 := by
  obtain ⟨-, -, -, hlap⟩ := lem_2_1_b_steps_proved R μ κ h
  rw [quarticP, Osserman.Proofs.Poly.lapP_sub, Osserman.Proofs.Sec2.eight_eq_C, Osserman.Proofs.Sec2.lapP_C_mul,
    Osserman.Proofs.Poly.lem_2_1_lap_s2_proved, hlap, ← Osserman.Proofs.Sec2.eight_eq_C]
  ring

theorem lem_2_1_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    gradSqP (quarticP R μ κ) = 16 * sqP 32 ^ 3 ∧ lapP (quarticP R μ κ) = 8 * sqP 32 ∧
      (∃ z : Vec 32, z ⬝ᵥ z = 1 ∧ eval z (quarticP R μ κ) = 1) ∧
      ∃ z : Vec 32, z ⬝ᵥ z = 1 ∧ eval z (quarticP R μ κ) = -1 := by
  obtain ⟨hv1, hv2⟩ := lem_2_1_values_proved R μ κ h
  exact ⟨gradSqP_quarticP R μ κ h, lapP_quarticP R μ κ h, ⟨_, append_e0_zero_unit, hv1 e0 e0_unit⟩,
    ⟨_, append_e0_e0_unit, hv2 e0 e0 e0_unit e0_unit (mem_Lsub_self R μ κ e0)⟩⟩

end Osserman.Proofs.Lem21
