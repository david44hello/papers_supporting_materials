/-
S8Example.lean — §8 of paper 013: explicit Clifford examples for the non-vacuity rows (s8_3_opposite_nonvacuous,
s8_4_opposite_nonvacuous, s8_5_mixed_nonvacuous). Lean-only helpers; no row of its own.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Content. `Jcl a = S_0S_{a+1}` (`a < 8`, from the standard system; `CorDNonvacuous.Jcl`) is a `Cl(8)`-structure on `ℝ^16`.
For any weights `η : Fin 8 → ℝ` the tensor `R = ∑_a η_a R_{Jcl a}` has `J_x = ∑_a η_a (Jcl_a x)(Jcl_a x)ᵀ`, so its
reduced multiplicities are `#{a : η_a = t}` at `t ≠ 0` and `7 + #{a : η_a = 0}` at `0` (`Rem72d.clifford_multiplicity`),
and `P = q·Jcl_b x` is a homogeneous cubic eigenfield of `η_b` satisfying (8.1).
-/
import Osserman.Proofs.CorDNonvacuous
import Osserman.Proofs.ThmEFrames
import Osserman.Proofs.Rem72dCounts
import Osserman.Proofs.S83Move

namespace Osserman.Proofs.S8Example

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Tools Osserman.Proofs.CorDNonvacuous

/-! ### The `Cl(8)`-structure -/

lemma jcl_clifford : IsCliffordStr Jcl ∧ ∀ a, (Jcl a)ᵀ * Jcl a = 1 :=
  ThmEFrames.thm_E_frame_clifford_proved Jcl
    (fun x hx a b => by rw [frame_dot, hx])
    (fun x _ a => Rem72a.skew_dot_self (Jcl_skew a) x)

lemma jcl_sq (a : Fin 8) : Jcl a * Jcl a = -1 := by
  have h := jcl_clifford.2 a
  rw [Jcl_skew a, neg_mul] at h
  exact neg_eq_iff_eq_neg.mp h

/-! ### The tensor -/

/-- For skew `J_a` and any weights there is a tensor with Jacobi family `∑ η_a (J_a x)(J_a x)ᵀ`. -/
lemma exists_sum_RJ : ∀ {ν : ℕ} (J : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (_hJs : ∀ a, (J a)ᵀ = -J a)
    (η : Fin ν → ℝ), ∃ R : CurvTensor 16, ∀ x, R.jacobi x = ∑ a, η a • jfam (J a) x
  | 0, _, _, _ => by
    obtain ⟨-, B, -, hB⟩ := Rem72a.RJ_curv_proved (0 : Matrix (Fin 16) (Fin 16) ℝ) (by simp)
    exact ⟨B, fun x => by rw [hB, Finset.univ_eq_empty, Finset.sum_empty]; simp [jfam]⟩
  | ν + 1, J, hJs, η => by
    obtain ⟨R0, hR0⟩ := exists_sum_RJ (fun a => J a.succ) (fun a => hJs a.succ) (fun a => η a.succ)
    obtain ⟨-, B, hBop, -⟩ := Rem72a.RJ_curv_proved (J 0) (hJs 0)
    obtain ⟨R, hR⟩ := Rem72a.exists_sub R0 B (-η 0)
    have hop : ∀ u v w, R.op u v w = R0.op u v w - (-η 0) • RJfun (J 0) u v w := fun u v w => by
      rw [hR, hBop]
    refine ⟨R, fun x => ?_⟩
    have hs := (Rem72a.rem_7_2_jac_split_proved R0 R (J 0) (hJs 0) (-η 0) hop x).1
    have h0 := hR0 x
    rw [Fin.sum_univ_succ, ← h0, hs]
    module

/-- Reduced multiplicities of `∑ η_a R_{Jcl a}` for natural-number weights. -/
lemma nat_mult (ηn : Fin 8 → ℕ) {R : CurvTensor 16}
    (hR : ∀ x, R.jacobi x = ∑ a, ((ηn a : ℕ) : ℝ) • jfam (Jcl a) x) (x : Vec 16) (hx : x ⬝ᵥ x = 1) (k : ℕ) :
    R.redMult x (k : ℝ) = Fintype.card {a : Fin 8 // ηn a = k} + (if k = 0 then 7 else 0) := by
  rw [Rem72d.clifford_multiplicity R Jcl jcl_clifford.1 0 (fun a => ((ηn a : ℕ) : ℝ))
    (fun x => by rw [hR, zero_smul, zero_add]) x hx (k : ℝ)]
  congr 1
  · exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by simp)
  · by_cases hk : k = 0 <;> simp [hk]

/-! ### The cubic fields `q·Jx` -/

/-- The field `x ↦ q·Jx` as polynomials. -/
noncomputable def qfield (J : Matrix (Fin 16) (Fin 16) ℝ) : Fin 16 → MvPolynomial (Fin 16) ℝ :=
  fun j => sqP 16 * linP J j

lemma qfield_eval (J : Matrix (Fin 16) (Fin 16) ℝ) (x : Vec 16) :
    evalField (qfield J) x = (x ⬝ᵥ x) • (J *ᵥ x) :=
  S83.evalField_of_eq (fun _ => rfl) x

lemma qfield_homog (J : Matrix (Fin 16) (Fin 16) ℝ) (j : Fin 16) : (qfield J j).IsHomogeneous 3 :=
  Poly.sqP_isHomogeneous.mul (S83.linP_homogeneous J j)

lemma qfield_cubic {J : Matrix (Fin 16) (Fin 16) ℝ} (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1) :
    CubicIdentities (qfield J) := by
  intro x
  have hJJ : J * J = -1 := by
    have h := hJo
    rw [hJs, neg_mul] at h
    exact neg_eq_iff_eq_neg.mp h
  have hsk : (J *ᵥ x) ⬝ᵥ x = 0 := by rw [dotProduct_comm]; exact Rem72a.skew_dot_self hJs x
  have hno := S83.orth_norm hJo x
  have hsq : J *ᵥ (J *ᵥ x) = -x := by rw [Matrix.mulVec_mulVec, hJJ, Matrix.neg_mulVec, Matrix.one_mulVec]
  simp only [qfield_eval]
  refine ⟨?_, ?_, ?_⟩
  · rw [smul_dotProduct, hsk, smul_zero]
  · rw [smul_dotProduct, dotProduct_smul, hno, smul_eq_mul, smul_eq_mul]
    ring
  · rw [smul_dotProduct, dotProduct_smul, hno, Matrix.mulVec_smul, hsq, smul_eq_mul, smul_eq_mul]
    module

lemma qfield_eig (η : Fin 8 → ℝ) {R : CurvTensor 16} (hR : ∀ x, R.jacobi x = ∑ a, η a • jfam (Jcl a) x)
    (b : Fin 8) : IsEigenfield R (η b) (qfield (Jcl b)) := by
  intro x
  rw [qfield_eval]
  refine Submodule.mem_inf.mpr ⟨(mem_eig_iff R x _ _).mpr ?_, ?_⟩
  · have term (a : Fin 8) : (η a • jfam (Jcl a) x) *ᵥ ((x ⬝ᵥ x) • (Jcl b *ᵥ x)) =
        if a = b then (η b * (x ⬝ᵥ x)) • ((x ⬝ᵥ x) • (Jcl b *ᵥ x)) else 0 := by
      rw [Matrix.smul_mulVec, Rem72a.jfam_mulVec, dotProduct_smul, frame_dot]
      split_ifs with hab
      · subst hab
        module
      · simp
    rw [hR, Matrix.sum_mulVec, Finset.sum_congr rfl fun a _ => term a, Finset.sum_ite_eq']
    simp
  · show x ⬝ᵥ ((x ⬝ᵥ x) • (Jcl b *ᵥ x)) = 0
    rw [dotProduct_smul, Rem72a.skew_dot_self (Jcl_skew b), smul_zero]

end Osserman.Proofs.S8Example
