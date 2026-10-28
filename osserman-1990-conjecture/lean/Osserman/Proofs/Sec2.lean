/-
Osserman/Proofs/Sec2.lean — proofs of six statements of paper 013 (§2 l. 375-408, §3 l. 474-475): the properties of b(x,y), the
quartic F (evaluation, homogeneity, gradient expansion), and ε, m from ΔF = 8s; plus reusable facts about J_x, A(x).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Curv
import Osserman.Proofs.Poly
import Osserman.Defs.TwoRoot

namespace Osserman.Proofs.Sec2

open Osserman Matrix MvPolynomial

variable {n : ℕ}

/-! ### Pair symmetry and the Jacobi operator -/

lemma anti_dot (R : CurvTensor n) (u v w z : Vec n) : R.op u v w ⬝ᵥ z = -(R.op v u w ⬝ᵥ z) := by
  rw [R.antisymm u v w, neg_dotProduct]

lemma bianchi_dot (R : CurvTensor n) (u v w z : Vec n) :
    R.op u v w ⬝ᵥ z + R.op v w u ⬝ᵥ z + R.op w u v ⬝ᵥ z = 0 := by
  rw [← add_dotProduct, ← add_dotProduct, R.bianchi, zero_dotProduct]

/-- Pair symmetry `⟨R(a,b)c,d⟩ = ⟨R(c,d)a,b⟩`: the sum of the four Bianchi identities (`u = b, v = c, w = a,
z = d`) gives `⟨R(a,b)c,d⟩ = ⟨R(d,c)b,a⟩`. -/
lemma pair_symm (R : CurvTensor n) (a b c d : Vec n) : R.op a b c ⬝ᵥ d = R.op c d a ⬝ᵥ b := by
  have B1 := bianchi_dot R b c a d
  have B2 := bianchi_dot R c a d b
  have B3 := bianchi_dot R a d b c
  have B4 := bianchi_dot R d b c a
  have s1 := R.skew b c d a
  have s2 := R.skew d b a c
  have s3 := R.skew c a d b
  have s4 := R.skew a d c b
  have s5 := R.skew a b d c
  have s6 := R.skew c d a b
  have s7 := R.skew c d b a
  have a1 := anti_dot R b a d c
  have a2 := anti_dot R d c a b
  linarith

/-- `J_x e_k = R(e_k, x)x`, entrywise. -/
lemma jacobi_apply (R : CurvTensor n) (x : Vec n) (j k : Fin n) :
    R.jacobi x j k = R.op (Pi.single k 1) x x j := rfl

/-- `J_x` is symmetric: `⟨R(e_k,x)x, e_j⟩ = ⟨R(x,e_j)e_k, x⟩ = -⟨R(x,e_j)x, e_k⟩ = ⟨R(e_j,x)x, e_k⟩`. -/
theorem jacobi_symm (R : CurvTensor n) (x : Vec n) : (R.jacobi x)ᵀ = R.jacobi x := by
  ext j k
  rw [transpose_apply, jacobi_apply, jacobi_apply]
  have h2 := pair_symm R (Pi.single k 1) x x (Pi.single j 1)
  have h3 := R.skew x (Pi.single j 1) (Pi.single k 1) x
  have h4 := anti_dot R x (Pi.single j 1) x (Pi.single k 1)
  simp only [dotProduct_single, mul_one] at h2 h3 h4
  linarith

/-- Trilinearity: `R(w,x)x = ∑_{a,b} x_a x_b R(w, e_a, e_b)`. -/
lemma op_expand (R : CurvTensor n) (w x : Vec n) :
    R.op w x x = ∑ a, ∑ b, (x a * x b) • R.op w (Pi.single a 1) (Pi.single b 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm (x b) (x a)]

theorem jacobi_quad (R : CurvTensor n) : IsQuadFamily R.jacobi := by
  refine ⟨fun a b => Matrix.of fun j k => R.op (Pi.single k 1) (Pi.single a 1) (Pi.single b 1) j, fun x => ?_⟩
  ext j k
  rw [jacobi_apply, op_expand]
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, of_apply, smul_eq_mul]

lemma op_self (R : CurvTensor n) (x : Vec n) : R.op x x x = 0 := by
  ext i
  have h := congrFun (R.antisymm x x x) i
  simp only [Pi.neg_apply] at h
  simp only [Pi.zero_apply]
  linarith

theorem jacobi_mulVec_self (R : CurvTensor n) (x : Vec n) : R.jacobi x *ᵥ x = 0 := by
  rw [Osserman.Proofs.Curv.jacobi_mulVec, op_self]

lemma jacobi_zero (R : CurvTensor n) : R.jacobi 0 = 0 := by
  ext j k
  simp [jacobi_apply]

/-! ### Quadratic families -/

lemma quad_add {A B : Vec n → Matrix (Fin n) (Fin n) ℝ} (hA : IsQuadFamily A) (hB : IsQuadFamily B) :
    IsQuadFamily (fun x => A x + B x) := by
  obtain ⟨M, hM⟩ := hA
  obtain ⟨M', hM'⟩ := hB
  exact ⟨fun a b => M a b + M' a b, fun x => by simp only [hM, hM', smul_add, Finset.sum_add_distrib]⟩

lemma quad_sub {A B : Vec n → Matrix (Fin n) (Fin n) ℝ} (hA : IsQuadFamily A) (hB : IsQuadFamily B) :
    IsQuadFamily (fun x => A x - B x) := by
  obtain ⟨M, hM⟩ := hA
  obtain ⟨M', hM'⟩ := hB
  exact ⟨fun a b => M a b - M' a b, fun x => by simp only [hM, hM', smul_sub, Finset.sum_sub_distrib]⟩

lemma quad_smul (c : ℝ) {A : Vec n → Matrix (Fin n) (Fin n) ℝ} (hA : IsQuadFamily A) :
    IsQuadFamily (fun x => c • A x) := by
  obtain ⟨M, hM⟩ := hA
  refine ⟨fun a b => c • M a b, fun x => ?_⟩
  show c • A x = ∑ a, ∑ b, (x a * x b) • (c • M a b)
  rw [hM, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => smul_comm _ _ _

lemma quad_sqOne : IsQuadFamily (fun x : Vec n => (x ⬝ᵥ x) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  classical
  refine ⟨fun a b => if a = b then 1 else 0, fun x => ?_⟩
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, dotProduct, Finset.sum_smul]

lemma quad_vecMulVec : IsQuadFamily (fun x : Vec n => vecMulVec x x) := by
  classical
  refine ⟨fun a b => vecMulVec (Pi.single a 1) (Pi.single b 1), fun x => ?_⟩
  ext i j
  simp [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply]

/-! ### `Π(x)` and `A(x)` -/

lemma Pi_mulVec_self (x : Vec n) : Osserman.Pi x *ᵥ x = 0 := by
  rw [← Osserman.Proofs.Curv.sec1_jacobi_R1_proved, R1fun, sub_self]

theorem Amat_quad (R : CurvTensor 16) (μ κ : ℝ) : IsQuadFamily (Amat R μ κ) :=
  quad_smul κ⁻¹ (quad_sub (jacobi_quad R) (quad_smul μ (quad_sub quad_sqOne quad_vecMulVec)))

theorem Amat_symm (R : CurvTensor 16) (μ κ : ℝ) (x : Vec 16) : (Amat R μ κ x)ᵀ = Amat R μ κ x := by
  simp only [Amat, Osserman.Pi, transpose_smul, transpose_sub, transpose_one, transpose_vecMulVec, jacobi_symm]

theorem Amat_mulVec_self (R : CurvTensor 16) (μ κ : ℝ) (x : Vec 16) : Amat R μ κ x *ᵥ x = 0 := by
  simp only [Amat, smul_mulVec, sub_mulVec, jacobi_mulVec_self, Pi_mulVec_self, smul_zero, sub_zero]

lemma Amat_zero (R : CurvTensor 16) (μ κ : ℝ) : Amat R μ κ 0 = 0 := by
  ext j k
  simp [Amat, jacobi_zero, Osserman.Pi]

/-! ### (1), (2): `b(x,y) = ⟨Q(x)y,y⟩` -/

lemma vecMulVec_mulVec_self (x y : Vec n) : vecMulVec x x *ᵥ y = (x ⬝ᵥ y) • x := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma vecMulVec_dot (x y : Vec n) : (vecMulVec x x *ᵥ y) ⬝ᵥ y = (x ⬝ᵥ y) ^ 2 := by
  rw [vecMulVec_mulVec_self, smul_dotProduct, smul_eq_mul, sq]

theorem sec2_b_expand_proved (R : CurvTensor 16) (μ κ : ℝ) (x y : Vec 16) :
    (Qmat R μ κ x *ᵥ y) ⬝ᵥ y = (Amat R μ κ x *ᵥ y) ⬝ᵥ y + (x ⬝ᵥ y) ^ 2 := by
  rw [Qmat, add_mulVec, add_dotProduct, vecMulVec_dot]

theorem sec2_b_properties_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    (∀ x y, (Qmat R μ κ x *ᵥ y) ⬝ᵥ y = (Qmat R μ κ y *ᵥ x) ⬝ᵥ x) ∧ (∀ y, (Qmat R μ κ 0 *ᵥ y) ⬝ᵥ y = 0) ∧
      (∀ x, (Qmat R μ κ x *ᵥ 0) ⬝ᵥ 0 = 0) ∧ ∀ x, (Qmat R μ κ x *ᵥ x) ⬝ᵥ x = (x ⬝ᵥ x) ^ 2 := by
  have hpol := (Osserman.Proofs.Curv.sec2_polarization_proved (Amat R μ κ) (Amat_quad R μ κ) (Amat_symm R μ κ)
    (Amat_mulVec_self R μ κ)).2
  refine ⟨fun x y => ?_, fun y => ?_, fun x => ?_, fun x => ?_⟩
  · rw [sec2_b_expand_proved, sec2_b_expand_proved, hpol x y, dotProduct_comm x y]
  · simp only [sec2_b_expand_proved, Amat_zero, zero_mulVec, zero_dotProduct]
    ring
  · rw [mulVec_zero, dotProduct_zero]
  · rw [sec2_b_expand_proved, Amat_mulVec_self, zero_dotProduct, zero_add]

/-! ### (3): evaluating the quartic `F` at `z = (x, y)` -/

lemma eval_xP (x y : Vec 16) (a : Fin 16) : eval (Fin.append x y : Vec 32) (xP a) = x a := by
  rw [xP, eval_X, Fin.append_left]

lemma eval_yP (x y : Vec 16) (a : Fin 16) : eval (Fin.append x y : Vec 32) (yP a) = y a := by
  rw [yP, eval_X, Fin.append_right]

lemma eval_jacEntryP (R : CurvTensor 16) (x y : Vec 16) (j k : Fin 16) :
    eval (Fin.append x y : Vec 32) (jacEntryP R j k) = R.jacobi x j k := by
  rw [jacobi_apply, op_expand]
  simp only [jacEntryP, map_sum, map_mul, eval_C, eval_xP, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma eval_piEntryP (x y : Vec 16) (j k : Fin 16) :
    eval (Fin.append x y : Vec 32) (piEntryP j k) = Osserman.Pi x j k := by
  by_cases hjk : j = k
  · simp [piEntryP, Osserman.Pi, hjk, eval_xP, dotProduct, sq, vecMulVec_apply, one_apply]
  · simp [piEntryP, Osserman.Pi, hjk, eval_xP, vecMulVec_apply, one_apply]

lemma eval_qEntryP (R : CurvTensor 16) (μ κ : ℝ) (x y : Vec 16) (j k : Fin 16) :
    eval (Fin.append x y : Vec 32) (qEntryP R μ κ j k) = Qmat R μ κ x j k := by
  simp only [qEntryP, Qmat, Amat, map_add, map_mul, map_sub, eval_C, eval_jacEntryP, eval_piEntryP, eval_xP,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, vecMulVec_apply, smul_eq_mul]

lemma eval_bP (R : CurvTensor 16) (μ κ : ℝ) (x y : Vec 16) :
    eval (Fin.append x y : Vec 32) (bP R μ κ) = (Qmat R μ κ x *ᵥ y) ⬝ᵥ y := by
  simp only [bP, map_sum, map_mul, eval_qEntryP, eval_yP, dotProduct, mulVec, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

lemma eval_sqP_append (x y : Vec 16) : eval (Fin.append x y : Vec 32) (sqP 32) = x ⬝ᵥ x + y ⬝ᵥ y := by
  rw [Osserman.Proofs.Poly.eval_sqP]
  show ∑ i : Fin (16 + 16), Fin.append x y i * Fin.append x y i = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, dotProduct]

theorem sec2_F_eval_proved (R : CurvTensor 16) (μ κ : ℝ) (x y : Vec 16) :
    eval (Fin.append x y : Vec 32) (quarticP R μ κ) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 - 8 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) := by
  simp only [quarticP, map_sub, map_pow, map_mul, map_ofNat, eval_sqP_append, eval_bP]

/-! ### (4): homogeneity -/

lemma eight_eq_C : (8 : MvPolynomial (Fin 32) ℝ) = C 8 := (map_ofNat C 8).symm

theorem sec2_F_homogeneous_proved (R : CurvTensor 16) (μ κ : ℝ) : (quarticP R μ κ).IsHomogeneous 4 := by
  have hx : ∀ a, (xP a).IsHomogeneous 1 := fun a => isHomogeneous_X ℝ _
  have hy : ∀ a, (yP a).IsHomogeneous 1 := fun a => isHomogeneous_X ℝ _
  have hjac : ∀ j k, (jacEntryP R j k).IsHomogeneous 2 := fun j k =>
    IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ =>
      ((isHomogeneous_C _ _).mul (hx a)).mul (hx b)
  have hpi : ∀ j k, (piEntryP j k).IsHomogeneous 2 := by
    intro j k
    refine IsHomogeneous.sub ?_ ((hx j).mul (hx k))
    split_ifs
    · exact IsHomogeneous.sum _ _ _ fun a _ => (hx a).pow 2
    · exact isHomogeneous_zero _ _ _
  have hq : ∀ j k, (qEntryP R μ κ j k).IsHomogeneous 2 := fun j k =>
    ((isHomogeneous_C _ _).mul ((hjac j k).sub ((isHomogeneous_C _ _).mul (hpi j k)))).add ((hx j).mul (hx k))
  have hb : (bP R μ κ).IsHomogeneous 4 :=
    IsHomogeneous.sum _ _ _ fun j _ => IsHomogeneous.sum _ _ _ fun k _ => ((hq j k).mul (hy j)).mul (hy k)
  rw [quarticP, eight_eq_C]
  exact (Osserman.Proofs.Poly.sqP_isHomogeneous.pow 2).sub ((isHomogeneous_C _ _).mul hb)

/-! ### (5): `|∇F|² = 16s³ - 64s⟨z,∇b⟩ + 64|∇b|²` -/

lemma pderiv_quarticP (R : CurvTensor 16) (μ κ : ℝ) (i : Fin 32) :
    pderiv i (quarticP R μ κ) = 4 * sqP 32 * X i - 8 * pderiv i (bP R μ κ) := by
  rw [quarticP, map_sub, Osserman.Proofs.Poly.pderiv_sq, Osserman.Proofs.Poly.pderiv_sqP, eight_eq_C, pderiv_C_mul]
  ring

theorem lem_2_1_grad_expand_proved (R : CurvTensor 16) (μ κ : ℝ) :
    gradSqP (quarticP R μ κ) =
      16 * sqP 32 ^ 3 - 64 * sqP 32 * ∑ i, X i * pderiv i (bP R μ κ) + 64 * gradSqP (bP R μ κ) := by
  have hs : sqP 32 = ∑ i : Fin 32, X i ^ 2 := rfl
  calc gradSqP (quarticP R μ κ)
        = ∑ i : Fin 32, (16 * sqP 32 ^ 2 * X i ^ 2 - 64 * sqP 32 * (X i * pderiv i (bP R μ κ)) +
            64 * pderiv i (bP R μ κ) ^ 2) := by
        rw [gradSqP]
        exact Finset.sum_congr rfl fun i _ => by rw [pderiv_quarticP]; ring
    _ = 16 * sqP 32 ^ 2 * ∑ i : Fin 32, X i ^ 2 - 64 * sqP 32 * ∑ i, X i * pderiv i (bP R μ κ) +
          64 * gradSqP (bP R μ κ) := by
        simp only [gradSqP, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by
        rw [← hs]
        ring

/-! ### (6): `ε` and `m` from `ΔF = 8s` -/

lemma lapP_C_mul {N : ℕ} (c : ℝ) (f : MvPolynomial (Fin N) ℝ) : lapP (C c * f) = C c * lapP f := by
  simp only [lapP, pderiv_C_mul, Finset.mul_sum]

theorem sec3_eps_m_proved (m : ℕ) (hm : 1 ≤ m) (P : Fin (m + 1) → Matrix (Fin 32) (Fin 32) ℝ)
    (hP : IsSymmCliffordSystem P) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (F : MvPolynomial (Fin 32) ℝ) (hlap : lapP F = 8 * sqP 32)
    (hF : ∀ z, eval z F = ε * eval z (FKMP P)) : (ε = 1 ∧ m = 7) ∨ (ε = -1 ∧ m = 8) := by
  have hFe : F = C ε * FKMP P := MvPolynomial.funext fun z => by rw [hF, map_mul, eval_C]
  rw [hFe, lapP_C_mul, Osserman.Proofs.Poly.sec3_lap_FKM_proved m hm P hP] at hlap
  have he := congrArg (eval (Pi.single 0 1 : Vec 32)) hlap
  simp only [map_mul, eval_C, map_ofNat, Osserman.Proofs.Poly.eval_sqP, dotProduct_single, Pi.single_eq_same,
    mul_one] at he
  rcases hε with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    have h7 : (m : ℝ) = 7 := by linarith
    exact_mod_cast h7
  · right
    refine ⟨rfl, ?_⟩
    have h8 : (m : ℝ) = 8 := by linarith
    exact_mod_cast h8

end Osserman.Proofs.Sec2
