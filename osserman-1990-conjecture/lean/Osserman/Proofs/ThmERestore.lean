/-
ThmERestore.lean — restoring the frame terms in Theorem E, paper 013, lines 773–779.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.ThmEMerge

namespace Osserman.Proofs.ThmERestore

open Osserman Matrix Osserman.Proofs.Curv Osserman.Proofs.ThmESpectral
open Osserman.Proofs.ThmEFrames Osserman.Proofs.ThmEProjection Osserman.Proofs.ThmETransfer

lemma maps_of_op_eq (R Q : CurvTensor 16) (h : ∀ u v w, R.op u v w = Q.op u v w) (x : Vec 16) :
    R.jacobiMap x = Q.jacobiMap x := by
  apply LinearMap.ext
  intro y
  exact h y x x

lemma osserman_of_op_eq (R Q : CurvTensor 16) (h : ∀ u v w, R.op u v w = Q.op u v w)
    (hQ : Q.IsOsserman) : R.IsOsserman := by
  have multiplicity (x : Vec 16) (μ : ℝ) : R.redMult x μ = Q.redMult x μ := by
    unfold CurvTensor.redMult
    rw [maps_of_op_eq R Q h]
  intro x y hx hy μ
  rw [multiplicity, multiplicity]
  exact hQ x y hx hy μ

lemma clifford_of_op_eq (R Q : CurvTensor 16) (h : ∀ u v w, R.op u v w = Q.op u v w)
    (hQ : Q.IsClifford) : R.IsClifford := by
  obtain ⟨ν, A, hA, l0, η, jacobi⟩ := hQ
  refine ⟨ν, A, hA, l0, η, ?_⟩
  intro x
  rw [CurvTensor.jacobi, maps_of_op_eq R Q h]
  exact jacobi x

theorem thm_E_restore_of_lem_nik_3_2_1
    (hNik : ∀ (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
      (c : ℝ) (hc : c ≠ 0) (hR' : ∀ u v w, R'.op u v w = R.op u v w - c • RJfun J u v w)
      (hO : R.IsOsserman) (hO' : R'.IsOsserman) (hC' : R'.IsClifford), R.IsClifford)
    (hRJ : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (hJ : Jᵀ = -J),
      (IsQuadFamily (jfam J) ∧ (∀ x, (jfam J x)ᵀ = jfam J x) ∧ (∀ x, jfam J x *ᵥ x = 0) ∧
        ∀ x y : Vec n, ((J *ᵥ x) ⬝ᵥ y) ^ 2 = ((J *ᵥ y) ⬝ᵥ x) ^ 2) ∧
      ∃ B : CurvTensor n, (∀ u v w, B.op u v w = RJfun J u v w) ∧ ∀ x, B.jacobi x = jfam J x)
    (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) (h : ThmEFrame R m ev J) (Rt : CurvTensor 16)
    (hRt : ∀ u v w, Rt.op u v w = R.op u v w - (ev 2 - ev 1) • ∑ a, RJfun (J a) u v w) (hC : Rt.IsClifford) :
    R.IsClifford := by
  classical
  let c := ev 2 - ev 1
  have cne : c ≠ 0 := sub_ne_zero.mpr (h.2.1.ne (by decide))
  have hJ := h.2.2.2.1
  have field := h.2.2.2.2
  have original_osserman := pattern_osserman R m h.1 ev h.2.1 h.2.2.1
  have orthogonal (a : Fin (m 2)) : (J a)ᵀ * J a = 1 :=
    (thm_E_frame_clifford_proved J
      (fun x hx => (clifford_frame J hJ x hx).1)
      (fun x hx => (clifford_frame J hJ x hx).2)).2 a
  have construct (S : Finset (Fin (m 2))) : ∃ Q : CurvTensor 16,
      (∀ u v w, Q.op u v w = R.op u v w - ∑ a ∈ S, c • RJfun (J a) u v w) ∧ Q.IsOsserman := by
    let s : Fin (m 2) → ℝ := fun a => if a ∈ S then c else 0
    obtain ⟨Q, operator, osserman⟩ := thm_E_intermediate_osserman_of_RJ_curv hRJ
      R original_osserman J hJ (ev 2) field s
    refine ⟨Q, ?_, osserman⟩
    intro u v w
    rw [operator]
    have sum : (∑ a, s a • RJfun (J a) u v w) = ∑ a ∈ S, c • RJfun (J a) u v w := by
      calc
        _ = ∑ a ∈ S, s a • RJfun (J a) u v w := by
          apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
          intro a _ ha
          simp only [s, ha, ite_false, zero_smul]
        _ = _ := Finset.sum_congr rfl (fun a ha => by simp only [s, ha, ite_true])
    rw [sum]
  have restore (S : Finset (Fin (m 2))) :
      ∀ Q : CurvTensor 16,
        (∀ u v w, Q.op u v w = R.op u v w - ∑ a ∈ S, c • RJfun (J a) u v w) →
        Q.IsOsserman → Q.IsClifford → R.IsClifford := by
    induction S using Finset.induction_on with
    | empty =>
      intro Q operator osserman clifford
      apply clifford_of_op_eq R Q
      · intro u v w
        simpa only [Finset.sum_empty, sub_zero] using (operator u v w).symm
      · exact clifford
    | @insert a S ha ih =>
      intro Q operator osserman clifford
      obtain ⟨P, hP, hPO⟩ := construct S
      have difference (u v w : Vec 16) : Q.op u v w = P.op u v w - c • RJfun (J a) u v w := by
        rw [operator, hP, Finset.sum_insert ha]
        module
      have p_clifford := hNik P Q (J a) (hJ.1 a) (orthogonal a) c cne difference hPO osserman clifford
      exact ih P hP hPO p_clifford
  obtain ⟨Q, hQ, hQO⟩ := construct Finset.univ
  have operators (u v w : Vec 16) : Rt.op u v w = Q.op u v w := by
    rw [hRt, hQ, ← Finset.smul_sum]
  have rt_osserman := osserman_of_op_eq Rt Q operators hQO
  apply restore Finset.univ Rt
  · intro u v w
    simpa only [Finset.smul_sum] using hRt u v w
  · exact rt_osserman
  · exact hC

end Osserman.Proofs.ThmERestore

