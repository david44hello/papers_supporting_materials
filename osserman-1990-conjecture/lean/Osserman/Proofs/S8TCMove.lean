/-
S8TCMove.lean — constant coordinates in an eigenframe preserve Osserman under rank-one perturbation.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.S8TCFields
import Osserman.Proofs.Rem72b
import Osserman.Proofs.Lem82DivQ
import Osserman.Proofs.ThmEFrameConstruction

namespace Osserman.Proofs.S8TC

open Osserman Matrix Osserman.Proofs.Spectral Osserman.Proofs.Rem72a Osserman.Proofs.Rem72b

lemma roots_eigenvalues (e : Fin 16 → ℝ) :
    (∏ i, (Polynomial.X - Polynomial.C (e i))).roots = Finset.univ.val.map e := by
  rw [Finset.prod_eq_multiset_prod]
  have shape : Finset.univ.val.map (fun i => Polynomial.X - Polynomial.C (e i)) =
      (Finset.univ.val.map e).map (fun t => Polynomial.X - Polynomial.C t) := by
    rw [Multiset.map_map]
    rfl
  rw [shape, Polynomial.roots_multiset_prod_X_sub_C]

lemma redMult_of_equal_det (R : CurvTensor 16) (x y : Vec 16) (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1)
    (hdet : ∀ t : ℝ, (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R.jacobi x).det =
      (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R.jacobi y).det) (s : ℝ) : R.redMult x s = R.redMult y s := by
  classical
  let hX := Osserman.Proofs.OssTop.jacobi_isHermitian R x
  let hY := Osserman.Proofs.OssTop.jacobi_isHermitian R y
  have polys : (∏ i, (Polynomial.X - Polynomial.C (hX.eigenvalues i))) =
      ∏ i, (Polynomial.X - Polynomial.C (hY.eigenvalues i)) := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact (det_sub_eq_prod hX t).symm.trans ((hdet t).trans (det_sub_eq_prod hY t))
  have roots := congrArg Polynomial.roots polys
  rw [roots_eigenvalues, roots_eigenvalues] at roots
  have count := congrArg (Multiset.count s) roots
  rw [count_map_univ, count_map_univ, card_eig_jacobi R hx, card_eig_jacobi R hy] at count
  omega

section Frame

variable {k : ℕ} (R : CurvTensor 16) (F : Fin k → Vec 16 → Vec 16) (μ : Fin k → ℝ)
variable (hF : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i, F i x ∈ Module.End.eigenspace (R.jacobiMap x) (μ i) ⊓ perp x)
variable (hFo : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i l, F i x ⬝ᵥ F l x = if i = l then 1 else 0)
variable (J : Matrix (Fin 16) (Fin 16) ℝ) (c : Fin k → ℝ)
variable (hJ : ∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x = ∑ i, c i • F i x)

include hF hFo hJ

omit hFo in
lemma frame_resolvent (x : Vec 16) (hx : x ⬝ᵥ x = 1) (t : ℝ) (ht : ∀ i, t ≠ μ i) :
    (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R.jacobi x) *ᵥ
      (∑ i, (c i / (t - μ i)) • F i x) = J *ᵥ x := by
  rw [hJ x hx, Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro i _
  have eigen : R.jacobi x *ᵥ F i x = μ i • F i x := by
    rw [← jacobiMap_eq_mulVec]
    exact Module.End.mem_eigenspace_iff.mp (hF x hx i).1
  have action : (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R.jacobi x) *ᵥ F i x = (t - μ i) • F i x := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, eigen, sub_smul]
  rw [mulVec_smul, action, smul_smul, div_mul_cancel₀ _ (sub_ne_zero.mpr (ht i))]

omit hF in
lemma frame_resolvent_dot (x : Vec 16) (hx : x ⬝ᵥ x = 1) (t : ℝ) :
    (J *ᵥ x) ⬝ᵥ (∑ i, (c i / (t - μ i)) • F i x) = ∑ i, c i ^ 2 / (t - μ i) := by
  classical
  have coordinates (i : Fin k) : (J *ᵥ x) ⬝ᵥ F i x = c i := by
    rw [hJ x hx, sum_dotProduct]
    simp only [smul_dotProduct, hFo x hx, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [dotProduct_smul, coordinates]
  change (c i / (t - μ i)) * c i = c i ^ 2 / (t - μ i)
  ring

lemma constant_frame_osserman (R' : CurvTensor 16) (hO : R.IsOsserman) (Cc : ℝ)
    (hchange : ∀ x, R'.jacobi x = R.jacobi x - Cc • jfam J x) : R'.IsOsserman := by
  classical
  have determinant (x : Vec 16) (hx : x ⬝ᵥ x = 1) (t : ℝ) (ht : ∀ i, t ≠ μ i) :
      (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R'.jacobi x).det =
        (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R.jacobi x).det *
          (1 + Cc * ∑ i, c i ^ 2 / (t - μ i)) := by
    have same : t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R'.jacobi x =
        (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R.jacobi x) - (-Cc) • vecMulVec (J *ᵥ x) (J *ᵥ x) := by
      rw [hchange]
      simp only [jfam, neg_smul]
      abel
    rw [same, det_sub_rank_one (frame_resolvent R F μ hF J c hJ x hx t ht) (-Cc),
      frame_resolvent_dot F μ hFo J c hJ x hx t]
    ring
  intro x y hx hy s
  apply redMult_of_equal_det R' x y hx hy ?_ s
  have dense : Dense (Set.univ \ (↑(Finset.univ.image μ) : Set ℝ)) :=
    dense_univ.sdiff_finite (Finset.finite_toSet _)
  have continuous_x : Continuous (fun t : ℝ => (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R'.jacobi x).det) := by
    fun_prop
  have continuous_y : Continuous (fun t : ℝ => (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R'.jacobi y).det) := by
    fun_prop
  have equal := Continuous.ext_on dense continuous_x continuous_y (fun t ht => by
    have different (i : Fin k) : t ≠ μ i := by
      intro eq
      exact ht.2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, eq.symm⟩)
    rw [determinant x hx t different, determinant y hy t different, det_eq_of_osserman hO hx hy t])
  exact fun t => congrFun equal t

lemma move_frame_construct (hO : R.IsOsserman) (Cc : ℝ) :
    ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - Cc • RJfun J u v z) ∧ R'.IsOsserman := by
  have tangent (x : Vec 16) : (J *ᵥ x) ⬝ᵥ x = 0 := by
    obtain ⟨a, u, hu, rfl⟩ := exists_unit_scale x
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul, hJ u hu, sum_dotProduct]
    have each (i : Fin k) : F i u ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact (hF u hu i).2
    simp only [smul_dotProduct, each, smul_zero, Finset.sum_const_zero]
  have skew : Jᵀ = -J := Osserman.Proofs.Lem82DivQ.skew_of_forall tangent
  obtain ⟨B, hB, hBjac⟩ := (RJ_curv_proved J skew).2
  let R' := Osserman.Proofs.ThmEFrameConstruction.subTensor R B Cc
  have operator (u v z : Vec 16) : R'.op u v z = R.op u v z - Cc • RJfun J u v z := by
    rw [Osserman.Proofs.ThmEFrameConstruction.subTensor_op, hB]
  have change (x : Vec 16) : R'.jacobi x = R.jacobi x - Cc • jfam J x := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [sub_mulVec, smul_mulVec, Osserman.Proofs.Curv.jacobi_mulVec, operator,
      Osserman.Proofs.Curv.jacobi_mulVec, ← hBjac x, Osserman.Proofs.Curv.jacobi_mulVec, hB]
  exact ⟨R', operator, constant_frame_osserman R F μ hF hFo J c hJ R' hO Cc change⟩

end Frame

theorem s8_move_frame_proved {k : ℕ} (R : CurvTensor 16) (hO : R.IsOsserman) (F : Fin k → Vec 16 → Vec 16) (μ : Fin k → ℝ)
    (hF : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i, F i x ∈ Module.End.eigenspace (R.jacobiMap x) (μ i) ⊓ perp x)
    (hFo : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i l, F i x ⬝ᵥ F l x = if i = l then 1 else 0)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (cJ : Fin k → ℝ) (hJ : ∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x = ∑ i, cJ i • F i x)
    (Cc : ℝ) :
    ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - Cc • RJfun J u v z) ∧ R'.IsOsserman :=
  move_frame_construct R F μ hF hFo J cJ hJ hO Cc

theorem s8_tc_frame_osserman_proved (R : CurvTensor 16) (hO : R.IsOsserman) (μ : Fin 3 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (_hμ : μ 0 ≠ μ 1)
    (c1 c2 : ℝ) (J : Matrix (Fin 16) (Fin 16) ℝ) (_hc : c1 ^ 2 + c2 ^ 2 = 1)
    (hJ : ∀ x : Vec 16, c1 • evalField (P 0) x + c2 • evalField (P 1) x = (x ⬝ᵥ x) • (J *ᵥ x)) :
    (∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x = c1 • evalField (P 0) x + c2 • evalField (P 1) x) ∧
      ∀ Cc : ℝ, ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - Cc • RJfun J u v z) ∧ R'.IsOsserman := by
  have first (x : Vec 16) (hx : x ⬝ᵥ x = 1) : J *ᵥ x = c1 • evalField (P 0) x + c2 • evalField (P 1) x := by
    simpa only [hx, one_smul] using (hJ x).symm
  refine ⟨first, fun Cc => ?_⟩
  let embed : Fin 2 → Fin 3 := Fin.castLE (by decide)
  let F : Fin 2 → Vec 16 → Vec 16 := fun i x => evalField (P (embed i)) x
  let coeff : Fin 2 → ℝ := ![c1, c2]
  have member (x : Vec 16) (hx : x ⬝ᵥ x = 1) (i : Fin 2) :
      F i x ∈ Module.End.eigenspace (R.jacobiMap x) (μ (embed i)) ⊓ perp x := by
    simpa only [hx, mul_one] using h.2.1 (embed i) x
  have gram (x : Vec 16) (hx : x ⬝ᵥ x = 1) (i j : Fin 3) :
      evalField (P i) x ⬝ᵥ evalField (P j) x = if i = j then 1 else 0 := by
    by_cases same : i = j
    · subst j
      simpa only [hx, one_pow, ite_true] using h.2.2.2.1 x i
    · simpa only [ite_eq_right same] using h.2.2.1 x i j same
  have orthogonal (x : Vec 16) (hx : x ⬝ᵥ x = 1) (i j : Fin 2) :
      F i x ⬝ᵥ F j x = if i = j then 1 else 0 := by
    have equal := gram x hx (embed i) (embed j)
    fin_cases i <;> fin_cases j <;> simpa [F, embed] using equal
  have coordinates (x : Vec 16) (hx : x ⬝ᵥ x = 1) : J *ᵥ x = ∑ i, coeff i • F i x := by
    simpa [Fin.sum_univ_succ, coeff, F, embed] using first x hx
  exact s8_move_frame_proved R hO F (fun i => μ (embed i)) member orthogonal J coeff coordinates Cc

end Osserman.Proofs.S8TC

