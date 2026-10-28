/-
S8TCWitness.lean — ordinary and distinct-eigenvalue witnesses for the three-column hypotheses.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.S8Example

namespace Osserman.Proofs.S8TC

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Example Osserman.Proofs.CorDNonvacuous

lemma qlin_threecol_witness :
    ∃ (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (wt : Fin 3 → ℝ),
      R.IsOsserman ∧ ThreeColHyp R μ P wt ∧ CubicIdentities (P 2) ∧ μ 0 ≠ μ 1 := by
  classical
  let η : Fin 8 → ℝ := fun a => (a.val : ℝ) + 1
  obtain ⟨R, hR⟩ := exists_sum_RJ Jcl (jcl_clifford.1.1) η
  let embed : Fin 3 → Fin 8 := Fin.castLE (by decide)
  let μ : Fin 3 → ℝ := fun i => η (embed i)
  let P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ := fun i => qfield (Jcl (embed i))
  let wt : Fin 3 → ℝ := ![1, 1, -1]
  have clifford : R.IsClifford := by
    refine ⟨8, Jcl, jcl_clifford.1, 0, η, fun x => ?_⟩
    rw [zero_smul, zero_add]
    exact hR x
  refine ⟨R, μ, P, wt, Osserman.Proofs.S83.clifford_osserman clifford, ?_, ?_, ?_⟩
  · refine ⟨fun i a => qfield_homog _ _, fun i => qfield_eig η hR (embed i), ?_, ?_,
      by norm_num [wt], by norm_num [wt], by norm_num [wt], ?_⟩
    · intro x i j different
      have indices : embed i ≠ embed j := fun same => different (Fin.castLE_injective _ same)
      change evalField (qfield (Jcl (embed i))) x ⬝ᵥ evalField (qfield (Jcl (embed j))) x = 0
      rw [qfield_eval, qfield_eval, smul_dotProduct, dotProduct_smul, frame_dot]
      simp [indices]
    · intro x i
      change evalField (qfield (Jcl (embed i))) x ⬝ᵥ evalField (qfield (Jcl (embed i))) x = _
      rw [qfield_eval, smul_dotProduct, dotProduct_smul, frame_dot]
      simp only [ite_true, smul_eq_mul]
      ring
    · intro a b
      apply Finset.dvd_sum
      intro i _
      change sqP 16 ∣ C (wt i) * (sqP 16 * linP (Jcl (embed i)) a) * (sqP 16 * linP (Jcl (embed i)) b)
      refine ⟨C (wt i) * linP (Jcl (embed i)) a * (sqP 16 * linP (Jcl (embed i)) b), ?_⟩
      ring
  · exact qfield_cubic (jcl_clifford.1.1 (embed 2)) (jcl_clifford.2 (embed 2))
  · norm_num [μ, η, embed]

theorem s8_threeCol_nonvacuous_proved :
    ∃ (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (wt : Fin 3 → ℝ),
      ThreeColHyp R μ P wt ∧ CubicIdentities (P 2) := by
  obtain ⟨R, μ, P, wt, _, h, cubic, _⟩ := qlin_threecol_witness
  exact ⟨R, μ, P, wt, h, cubic⟩

theorem s8_threeCol_distinct_nonvacuous_proved :
    ∃ (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (wt : Fin 3 → ℝ),
      R.IsOsserman ∧ ThreeColHyp R μ P wt ∧ CubicIdentities (P 2) ∧ μ 0 ≠ μ 1 :=
  qlin_threecol_witness

end Osserman.Proofs.S8TC

