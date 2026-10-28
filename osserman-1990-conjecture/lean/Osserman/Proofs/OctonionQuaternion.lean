/-
Osserman/Proofs/OctonionQuaternion.lean — every octonion lies in a quaternion subalgebra (paper 013, Lemma 7.1(b),
l. 733): `oct_quaternion_subalgebra`, by an explicit frame 1, I, J, K = IJ.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.OctonionFacts
import Osserman.Proofs.Threshold

namespace Osserman.Proofs.OctonionQuaternion

open Osserman Matrix Osserman.Proofs.OctonionLinear Osserman.Proofs.OctonionFacts
open Osserman.Proofs.Threshold

lemma oct_neg_left (a b : Vec 8) : omul (-a) b = -omul a b := by
  simpa only [neg_one_smul] using omul_smul_left a b (-1)

lemma oct_neg_right (a b : Vec 8) : omul a (-b) = -omul a b := by
  simpa only [neg_one_smul] using omul_smul_right a b (-1)

lemma conjugate_formula (a : Vec 8) : oconj a = (2 * a 0) • oone - a := by
  ext i
  fin_cases i <;> norm_num [oconj, oone, vecOfOct, octConj, octOfVec, Pi.single_apply] <;> ring

lemma conjugate_pure (a : Vec 8) (pure : a 0 = 0) : oconj a = -a := by
  rw [conjugate_formula, pure, mul_zero, zero_smul, zero_sub]

lemma dot_one (a : Vec 8) : a ⬝ᵥ oone = a 0 := by simp [oone]
lemma one_dot (a : Vec 8) : oone ⬝ᵥ a = a 0 := by simp [oone]

lemma oct_right_adjoint (a b c : Vec 8) : omul a b ⬝ᵥ c = a ⬝ᵥ omul c (oconj b) := by
  calc
    _ = oconj (omul a b) ⬝ᵥ oconj c := (oconj_dot _ _).symm
    _ = omul (oconj b) (oconj a) ⬝ᵥ oconj c := by rw [oct_conj_mul_proved]
    _ = oconj a ⬝ᵥ omul b (oconj c) := by rw [oct_adjoint_proved, oconj_invol]
    _ = a ⬝ᵥ oconj (omul b (oconj c)) := oconj_move _ _
    _ = _ := by rw [oct_conj_mul_proved, oconj_invol]

lemma oct_right_alt (a u : Vec 8) : omul (omul u (oconj a)) a = (a ⬝ᵥ a) • u := by
  have equal := swap_square_right a u
  rw [oct_conj_mul_proved, oconj_invol] at equal
  exact equal

lemma pure_square (a : Vec 8) (pure : a 0 = 0) : omul a a = -(a ⬝ᵥ a) • oone := by
  have equal := oct_left_alt_proved a oone
  rw [omul_one, conjugate_pure a pure, oct_neg_right] at equal
  have negated := congrArg (fun v : Vec 8 => -v) equal
  simpa only [neg_neg, neg_smul] using negated

lemma pure_anticommutator (a b : Vec 8) (ha : a 0 = 0) (hb : b 0 = 0) :
    omul a b + omul b a = (-2 * (a ⬝ᵥ b)) • oone := by
  have pure : (a + b) 0 = 0 := by simp [ha, hb]
  have square := pure_square (a + b) pure
  rw [omul_add_left, omul_add_right, omul_add_right, pure_square a ha, pure_square b hb, normsq_add] at square
  ext i
  have entry := congrFun square i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at entry ⊢
  linarith

lemma frame_products (I J : Vec 8) (hI : I 0 = 0) (hJ : J 0 = 0)
    (nI : I ⬝ᵥ I = 1) (nJ : J ⬝ᵥ J = 1) (orthogonal : I ⬝ᵥ J = 0) :
    let K := omul I J
    omul I I = -oone ∧ omul J J = -oone ∧ omul K K = -oone ∧
      omul J I = -K ∧ omul I K = -J ∧ omul K J = -I ∧ omul K I = J ∧ omul J K = I ∧
      K 0 = 0 ∧ K ⬝ᵥ K = 1 ∧ I ⬝ᵥ K = 0 ∧ J ⬝ᵥ K = 0 := by
  let K := omul I J
  have ii : omul I I = -oone := by rw [pure_square I hI, nI, neg_one_smul]
  have jj : omul J J = -oone := by rw [pure_square J hJ, nJ, neg_one_smul]
  have ji : omul J I = -K := by
    have sum := pure_anticommutator I J hI hJ
    rw [orthogonal, mul_zero, zero_smul] at sum
    exact eq_neg_of_add_eq_zero_right sum
  have barK : oconj K = -K := by
    dsimp only [K]
    rw [oct_conj_mul_proved, conjugate_pure J hJ, conjugate_pure I hI, oct_neg_left, oct_neg_right, neg_neg]
    exact ji
  have kPure : K 0 = 0 := by
    have entry := congrFun barK 0
    have realPart : (oconj K) 0 = K 0 := by simp [oconj, vecOfOct, octConj, octOfVec]
    rw [realPart, Pi.neg_apply] at entry
    linarith
  have normK : K ⬝ᵥ K = 1 := by
    change omul I J ⬝ᵥ omul I J = 1
    rw [oct_norm_mul_proved, nI, nJ, one_mul]
  have kk : omul K K = -oone := by rw [pure_square K kPure, normK, neg_one_smul]
  have ik : omul I K = -J := by
    have equal := oct_left_alt_proved I J
    rw [conjugate_pure I hI, oct_neg_left, oct_neg_right, nI, one_smul] at equal
    have negated := congrArg (fun v : Vec 8 => -v) equal
    simpa only [neg_neg] using negated
  have kj : omul K J = -I := by
    have equal := oct_right_alt J I
    rw [conjugate_pure J hJ, oct_neg_right, oct_neg_left, nJ, one_smul] at equal
    have negated := congrArg (fun v : Vec 8 => -v) equal
    simpa only [neg_neg] using negated
  have kiDot : K ⬝ᵥ I = 0 := by
    change omul I J ⬝ᵥ I = 0
    rw [oct_adjoint_proved, conjugate_pure I hI, oct_neg_left, ii, neg_neg, dot_one, hJ]
  have kjDot : K ⬝ᵥ J = 0 := by
    change omul I J ⬝ᵥ J = 0
    rw [oct_right_adjoint, conjugate_pure J hJ, oct_neg_right, jj, neg_neg, dot_one, hI]
  have ikDot : I ⬝ᵥ K = 0 := (dotProduct_comm _ _).trans kiDot
  have jkDot : J ⬝ᵥ K = 0 := (dotProduct_comm _ _).trans kjDot
  have ki : omul K I = J := by
    have sum := pure_anticommutator I K hI kPure
    rw [ikDot, mul_zero, zero_smul, ik] at sum
    simpa only [neg_neg] using eq_neg_of_add_eq_zero_right sum
  have jk : omul J K = I := by
    have sum := pure_anticommutator J K hJ kPure
    rw [jkDot, mul_zero, zero_smul, kj] at sum
    simpa only [neg_neg] using eq_neg_of_add_eq_zero_left sum
  exact ⟨ii, jj, kk, ji, ik, kj, ki, jk, kPure, normK, ikDot, jkDot⟩

lemma quaternion_embedding_of_pair (I J : Vec 8) (hI : I 0 = 0) (hJ : J 0 = 0)
    (nI : I ⬝ᵥ I = 1) (nJ : J ⬝ᵥ J = 1) (orthogonal : I ⬝ᵥ J = 0) :
    ∃ f : Quaternion ℝ →ₗ[ℝ] Vec 8, Function.Injective f ∧ f 1 = oone ∧
      (∀ p q : Quaternion ℝ, f (p * q) = omul (f p) (f q)) ∧
      ∀ r s : ℝ, f ⟨r, s, 0, 0⟩ = r • oone + s • I := by
  let K := omul I J
  obtain ⟨ii, jj, kk, ji, ik, kj, ki, jk, kPure, normK, ikDot, jkDot⟩ := frame_products I J hI hJ nI nJ orthogonal
  change omul K K = -oone at kk
  change omul J I = -K at ji
  change omul I K = -J at ik
  change omul K J = -I at kj
  change omul K I = J at ki
  change omul J K = I at jk
  change K 0 = 0 at kPure
  change K ⬝ᵥ K = 1 at normK
  change I ⬝ᵥ K = 0 at ikDot
  change J ⬝ᵥ K = 0 at jkDot
  let f : Quaternion ℝ →ₗ[ℝ] Vec 8 :=
    { toFun := fun p => p.re • oone + p.imI • I + p.imJ • J + p.imK • K
      map_add' := by intro p q; simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add]; module
      map_smul' := by intro c p; simp only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul, RingHom.id_apply, id_eq]; module }
  have coord0 (p : Quaternion ℝ) : oone ⬝ᵥ f p = p.re := by
    simp [f, dotProduct_add, dotProduct_smul, one_dot, hI, hJ, kPure, oone]
  have coordI (p : Quaternion ℝ) : I ⬝ᵥ f p = p.imI := by
    simp [f, dotProduct_add, dotProduct_smul, dot_one, hI, nI, orthogonal, ikDot]
  have coordJ (p : Quaternion ℝ) : J ⬝ᵥ f p = p.imJ := by
    have jiDot : J ⬝ᵥ I = 0 := (dotProduct_comm _ _).trans orthogonal
    simp [f, dotProduct_add, dotProduct_smul, dot_one, hJ, nJ, jiDot, jkDot]
  have coordK (p : Quaternion ℝ) : K ⬝ᵥ f p = p.imK := by
    have kiDot : K ⬝ᵥ I = 0 := (dotProduct_comm _ _).trans ikDot
    have kjDot : K ⬝ᵥ J = 0 := (dotProduct_comm _ _).trans jkDot
    simp [f, dotProduct_add, dotProduct_smul, dot_one, kPure, normK, kiDot, kjDot]
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro p q equal
    apply Quaternion.ext
    · rw [← coord0 p, ← coord0 q, equal]
    · rw [← coordI p, ← coordI q, equal]
    · rw [← coordJ p, ← coordJ q, equal]
    · rw [← coordK p, ← coordK q, equal]
  · simp [f]
  · intro p q
    change (p * q).re • oone + (p * q).imI • I + (p * q).imJ • J + (p * q).imK • K =
      omul (p.re • oone + p.imI • I + p.imJ • J + p.imK • K)
        (q.re • oone + q.imI • I + q.imJ • J + q.imK • K)
    have ij : omul I J = K := rfl
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      omul_add_left, omul_add_right, omul_smul_left, omul_smul_right, one_omul, omul_one,
      ii, jj, kk, ij, ji, ik, kj, ki, jk]
    module
  · intro r s
    simp [f]

lemma imaginary_unit_decomposition (γ : Vec 8) :
    ∃ (I : Vec 8) (s : ℝ), I 0 = 0 ∧ I ⬝ᵥ I = 1 ∧ γ = (γ 0) • oone + s • I := by
  let v := γ - (γ 0) • oone
  have pure : v 0 = 0 := by simp [v, oone]
  by_cases zero : v = 0
  · refine ⟨Pi.single 1 1, 0, by simp, by simp, ?_⟩
    simpa only [zero_smul, add_zero] using sub_eq_zero.mp zero
  · obtain ⟨c, unit⟩ := unit_rescale v zero
    have nonzero : c ≠ 0 := by
      intro equal
      rw [equal, zero_smul, zero_dotProduct] at unit
      norm_num at unit
    refine ⟨c • v, c⁻¹, ?_, unit, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, pure, mul_zero]
    · rw [smul_smul, inv_mul_cancel₀ nonzero, one_smul]
      dsimp only [v]
      module

lemma imaginary_unit_perpendicular (I : Vec 8) :
    ∃ J : Vec 8, J 0 = 0 ∧ J ⬝ᵥ J = 1 ∧ I ⬝ᵥ J = 0 := by
  by_cases first : I 1 = 0
  · exact ⟨Pi.single 1 1, by simp, by simp, by simpa using first⟩
  · let v : Vec 8 := (I 2) • Pi.single 1 1 - (I 1) • Pi.single 2 1
    have pure : v 0 = 0 := by simp [v]
    have nonzero : v ≠ 0 := by
      intro equal
      have entry := congrFun equal 2
      simp [v] at entry
      exact first entry
    have orthogonal : I ⬝ᵥ v = 0 := by
      simp only [v, dotProduct_sub, dotProduct_smul]
      simp
      ring
    obtain ⟨c, unit⟩ := unit_rescale v nonzero
    refine ⟨c • v, ?_, unit, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, pure, mul_zero]
    · rw [dotProduct_smul, orthogonal, smul_zero]

theorem oct_quaternion_subalgebra_proved (γ : Vec 8) :
    ∃ f : Quaternion ℝ →ₗ[ℝ] Vec 8, Function.Injective f ∧ f 1 = oone ∧
      (∀ p q : Quaternion ℝ, f (p * q) = omul (f p) (f q)) ∧ γ ∈ LinearMap.range f := by
  obtain ⟨I, s, pureI, unitI, decomposition⟩ := imaginary_unit_decomposition γ
  obtain ⟨J, pureJ, unitJ, perpendicular⟩ := imaginary_unit_perpendicular I
  obtain ⟨f, injective, one, multiplication, coordinates⟩ :=
    quaternion_embedding_of_pair I J pureI pureJ unitI unitJ perpendicular
  refine ⟨f, injective, one, multiplication, ⟨⟨γ 0, s, 0, 0⟩, ?_⟩⟩
  exact (coordinates (γ 0) s).trans decomposition.symm

end Osserman.Proofs.OctonionQuaternion
