/-
Osserman/Proofs/FKMWitness.lean — a concrete symmetric Clifford system of eight 32×32 matrices meets every hypothesis
of the cited result (A) (paper 013, §3 non-vacuity): `sec3_axiom_nonvacuous`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.StdSystem
import Osserman.Proofs.CayleyEigenspaces
import Osserman.Proofs.Poly

namespace Osserman.Proofs.FKMWitness

open Osserman Matrix MvPolynomial Osserman.Proofs.StdSystem Osserman.Proofs.CayleyEigenspaces
open Osserman.Proofs.Threshold Osserman.Proofs.Poly

def duplicate (M : Matrix (Fin 16) (Fin 16) ℝ) : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ finSumFinEquiv (Matrix.fromBlocks M 0 0 M)

lemma duplicate_mul (A B : Matrix (Fin 16) (Fin 16) ℝ) : duplicate A * duplicate B = duplicate (A * B) := by
  unfold duplicate
  rw [← map_mul]
  congr 1
  simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

lemma duplicate_add (A B : Matrix (Fin 16) (Fin 16) ℝ) : duplicate A + duplicate B = duplicate (A + B) := by
  unfold duplicate
  rw [← map_add]
  congr 1
  rw [Matrix.fromBlocks_add]
  simp only [add_zero]

lemma duplicate_one : duplicate 1 = 1 := by
  simp only [duplicate, Matrix.fromBlocks_one, map_one]

lemma duplicate_zero : duplicate 0 = 0 := by
  simp only [duplicate, Matrix.fromBlocks_zero, map_zero]

lemma duplicate_two : duplicate 2 = 2 := by
  have two : (2 : Matrix (Fin 16) (Fin 16) ℝ) = 1 + 1 := by norm_num
  rw [two, ← duplicate_add, duplicate_one]
  norm_num

lemma duplicate_symmetric (M : Matrix (Fin 16) (Fin 16) ℝ) (hM : Mᵀ = M) : (duplicate M)ᵀ = duplicate M := by
  change (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 M))ᵀ =
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 M)
  rw [Matrix.transpose_reindex, Matrix.fromBlocks_transpose, hM, Matrix.transpose_zero]

lemma duplicate_action (M : Matrix (Fin 16) (Fin 16) ℝ) (u v : Vec 16) :
    duplicate M *ᵥ Fin.append u v = Fin.append (M *ᵥ u) (M *ᵥ v) := by
  change (Matrix.fromBlocks M 0 0 M).submatrix finSumFinEquiv.symm finSumFinEquiv.symm *ᵥ Fin.append u v = _
  rw [Matrix.submatrix_mulVec_equiv]
  have composed : Fin.append u v ∘ finSumFinEquiv = Sum.elim u v := by
    funext i
    cases i <;> simp only [Function.comp_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Fin.append_left, Fin.append_right, Sum.elim_inl, Sum.elim_inr]
  simp only [Equiv.symm_symm]
  rw [composed, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero, zero_add]
  funext i
  refine Fin.addCases (m := 16) (n := 16) (fun j => ?_) (fun j => ?_) i <;>
    simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Sum.elim_inl, Sum.elim_inr, Fin.append_left, Fin.append_right]

lemma append_dot (a b c d : Vec 16) : Fin.append a b ⬝ᵥ Fin.append c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp only [dotProduct]
  rw [Fin.sum_univ_add (a := 16) (b := 16)]
  simp only [Fin.append_left, Fin.append_right]

def witnessSystem (i : Fin 8) : Matrix (Fin 32) (Fin 32) ℝ := duplicate (stdSys i.castSucc)

lemma witnessSystem_clifford : IsSymmCliffordSystem witnessSystem := by
  refine ⟨fun i => duplicate_symmetric _ (sec6_std_system_proved.2.1 i.castSucc), ?_⟩
  intro i j
  change duplicate (stdSys i.castSucc) * duplicate (stdSys j.castSucc) +
    duplicate (stdSys j.castSucc) * duplicate (stdSys i.castSucc) = _
  rw [duplicate_mul, duplicate_mul, duplicate_add, sec6_std_system_proved.2.2]
  by_cases same : i = j
  · subst j
    rw [ite_eq_left rfl, ite_eq_left rfl, duplicate_two]
  · have distinct : i.castSucc ≠ j.castSucc := fun equal => same (Fin.castSucc_injective 8 equal)
    rw [ite_eq_right distinct, ite_eq_right same, duplicate_zero]

lemma eval_FKMP (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (z : Vec 32) :
    eval z (FKMP P) = (z ⬝ᵥ z) ^ 2 - 2 * ∑ i, (z ⬝ᵥ (P i *ᵥ z)) ^ 2 := by
  simp only [FKMP, map_sub, map_mul, map_pow, map_ofNat, map_sum, eval_sqP, eval_quadP]

theorem sec3_axiom_nonvacuous_proved : ∃ P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ, IsSymmCliffordSystem P ∧
    (FKMP P).IsHomogeneous 4 ∧ gradSqP (FKMP P) = 16 * sqP 32 ^ 3 ∧ lapP (FKMP P) = 8 * sqP 32 ∧
    ∃ z w : Vec 32, z ⬝ᵥ z = 1 ∧ w ⬝ᵥ w = 1 ∧ eval z (FKMP P) ≠ eval w (FKMP P) := by
  have system := sec6_std_system_proved.2
  have onto := threshold_onto stdSys (fun i => system.1 i) (system_norm_identity stdSys system)
    rfl (by norm_num) (system_nonconstant stdSys system)
  obtain ⟨u, hu, imageU⟩ := onto (Pi.single (8 : Fin 9) 1) (by simp)
  obtain ⟨v, hv, imageV⟩ := onto (Pi.single (0 : Fin 9) 1) (by simp)
  let z : Vec 32 := Fin.append u (0 : Vec 16)
  let w : Vec 32 := Fin.append v (0 : Vec 16)
  have hz : z ⬝ᵥ z = 1 := by dsimp only [z]; rw [append_dot, hu]; simp
  have hw : w ⬝ᵥ w = 1 := by dsimp only [w]; rw [append_dot, hv]; simp
  have z_coeff (i : Fin 8) : z ⬝ᵥ (witnessSystem i *ᵥ z) = 0 := by
    dsimp only [witnessSystem, z]
    rw [duplicate_action, append_dot]
    simp only [zero_dotProduct, add_zero]
    change hvec stdSys u i.castSucc = 0
    rw [imageU]
    have distinct : (8 : Fin 9) ≠ i.castSucc := by intro equal; have := congrArg Fin.val equal; simp at this; omega
    simp [Pi.single_apply, distinct]
  have w_coeff (i : Fin 8) : w ⬝ᵥ (witnessSystem i *ᵥ w) = if i = 0 then 1 else 0 := by
    dsimp only [witnessSystem, w]
    rw [duplicate_action, append_dot]
    simp only [zero_dotProduct, add_zero]
    change hvec stdSys v i.castSucc = _
    rw [imageV]
    by_cases zero : i = 0
    · subst i
      simp
    · have distinct : (0 : Fin 9) ≠ i.castSucc := by intro equal; apply zero; apply Fin.ext; have := congrArg Fin.val equal; simpa using this.symm
      simp [Pi.single_apply, distinct, zero]
  have valueZ : eval z (FKMP witnessSystem) = 1 := by
    rw [eval_FKMP, hz]
    norm_num [z_coeff]
  have valueW : eval w (FKMP witnessSystem) = -1 := by
    rw [eval_FKMP, hw]
    norm_num [w_coeff]
  refine ⟨witnessSystem, witnessSystem_clifford, FKMP_homogeneous_proved _,
    gradSq_FKM_proved _ witnessSystem_clifford, ?_, z, w, hz, hw, ?_⟩
  · have lap := sec3_lap_FKM_proved 7 (by norm_num) witnessSystem witnessSystem_clifford
    norm_num at lap
    exact lap
  · rw [valueZ, valueW]
    norm_num

end Osserman.Proofs.FKMWitness
