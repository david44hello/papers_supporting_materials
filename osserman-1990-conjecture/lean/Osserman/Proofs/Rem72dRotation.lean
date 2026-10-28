/-
Rem72dRotation.lean — block rotations of real coefficient vectors, paper 013, Remark 7.2.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Rem72a

namespace Osserman.Proofs.Rem72d

open Osserman Matrix

noncomputable def reflector {ν : ℕ} (g : Fin ν → ℝ) : Matrix (Fin ν) (Fin ν) ℝ :=
  1 - (2 / (g ⬝ᵥ g)) • vecMulVec g g

lemma reflector_action {ν : ℕ} (g y : Fin ν → ℝ) :
    reflector g *ᵥ y = y - (2 * (g ⬝ᵥ y) / (g ⬝ᵥ g)) • g := by
  rw [reflector, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec]
  simp only [op_smul_eq_smul, smul_smul]
  congr 2
  ring

lemma reflector_symm {ν : ℕ} (g : Fin ν → ℝ) : (reflector g)ᵀ = reflector g := by
  simp only [reflector, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]

lemma reflector_orthogonal {ν : ℕ} (g : Fin ν → ℝ) :
    reflector g ∈ Matrix.orthogonalGroup (Fin ν) ℝ := by
  classical
  apply (Matrix.mem_orthogonalGroup_iff (Fin ν) ℝ).mpr
  rw [reflector_symm]
  apply Matrix.ext_iff_mulVec.mpr
  intro y
  rw [← mulVec_mulVec, reflector_action, reflector_action, one_mulVec]
  by_cases zero : g = 0
  · simp [zero]
  · have nonzero : g ⬝ᵥ g ≠ 0 := fun h => zero (dotProduct_self_eq_zero.mp h)
    rw [dotProduct_sub, dotProduct_smul]
    simp only [smul_eq_mul]
    have scalar : 2 * (g ⬝ᵥ y - (2 * (g ⬝ᵥ y) / (g ⬝ᵥ g)) * (g ⬝ᵥ g)) /
        (g ⬝ᵥ g) = -(2 * (g ⬝ᵥ y) / (g ⬝ᵥ g)) := by
      field_simp [nonzero]
      <;> ring
    rw [scalar, neg_smul]
    abel

lemma reflector_maps {ν : ℕ} (v w : Fin ν → ℝ) (equal : v ⬝ᵥ v = w ⬝ᵥ w) :
    reflector (v - w) *ᵥ v = w := by
  rw [reflector_action]
  by_cases same : v = w
  · subst w
    simp
  · have nonzero : (v - w) ⬝ᵥ (v - w) ≠ 0 := by
      intro zero
      exact same (sub_eq_zero.mp (dotProduct_self_eq_zero.mp zero))
    have relation : 2 * ((v - w) ⬝ᵥ v) = (v - w) ⬝ᵥ (v - w) := by
      simp only [sub_dotProduct, dotProduct_sub]
      rw [dotProduct_comm w v, equal]
      ring
    rw [relation, div_self nonzero, one_smul]
    abel

lemma reflector_fixed_coordinate {ν : ℕ} (g y : Fin ν → ℝ) (a : Fin ν) (zero : g a = 0) :
    (reflector g *ᵥ y) a = y a := by
  rw [reflector_action]
  simp [zero]

lemma reflector_block {ν : ℕ} (μ g : Fin ν → ℝ) (ℓ : ℝ)
    (support : ∀ a, μ a ≠ ℓ → g a = 0) :
    ∀ a b, μ a ≠ μ b → reflector g a b = 0 := by
  classical
  intro a b different
  have indices : a ≠ b := fun equal => different (congrArg μ equal)
  have product : g a * g b = 0 := by
    by_cases first : μ a = ℓ
    · have second : μ b ≠ ℓ := fun h => different (first.trans h.symm)
      rw [support b second, mul_zero]
    · rw [support a first, zero_mul]
  simp [reflector, indices, vecMulVec, product]

lemma concentrate_one_block {ν : ℕ} (μ d : Fin ν → ℝ) (ℓ : ℝ) (a0 : Fin ν) (ha0 : μ a0 = ℓ) :
    ∃ H ∈ Matrix.orthogonalGroup (Fin ν) ℝ,
      (∀ a b, μ a ≠ μ b → H a b = 0) ∧
      (∀ a, μ a ≠ ℓ → ∀ y, (H *ᵥ y) a = y a) ∧
      ∀ a, μ a = ℓ → a ≠ a0 → (H *ᵥ d) a = 0 := by
  classical
  let v : Fin ν → ℝ := fun a => if μ a = ℓ then d a else 0
  let w : Fin ν → ℝ := Pi.single a0 (Real.sqrt (v ⬝ᵥ v))
  let g := v - w
  have nonnegative : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun a _ => mul_self_nonneg (v a)
  have equal : v ⬝ᵥ v = w ⬝ᵥ w := by
    simp only [w, dotProduct_single, Pi.single_eq_same]
    nlinarith [Real.sq_sqrt nonnegative]
  have support : ∀ a, μ a ≠ ℓ → g a = 0 := by
    intro a different
    have index : a ≠ a0 := fun equal => different ((congrArg μ equal).trans ha0)
    simp [g, v, w, different, index]
  have dot : g ⬝ᵥ d = g ⬝ᵥ v := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases inside : μ a = ℓ
    · simp [v, inside]
    · rw [support a inside]
      simp
  refine ⟨reflector g, reflector_orthogonal g, reflector_block μ g ℓ support,
    fun a outside y => reflector_fixed_coordinate g y a (support a outside), ?_⟩
  intro a inside different
  have image := congrFun (reflector_maps v w equal) a
  rw [reflector_action, ← dot] at image
  have same : d a = v a := by simp [v, inside]
  rw [reflector_action]
  change d a - _ = 0
  rw [same]
  convert image using 1
  simp [w, different]

lemma block_mul {ν : ℕ} (μ : Fin ν → ℝ) (A B : Matrix (Fin ν) (Fin ν) ℝ)
    (hA : ∀ a b, μ a ≠ μ b → A a b = 0) (hB : ∀ a b, μ a ≠ μ b → B a b = 0) :
    ∀ a b, μ a ≠ μ b → (A * B) a b = 0 := by
  classical
  intro a b different
  change (∑ k, A a k * B k b) = 0
  apply Finset.sum_eq_zero
  intro k _
  by_cases first : μ a = μ k
  · rw [hB k b (fun second => different (first.trans second)), mul_zero]
  · rw [hA a k first, zero_mul]

theorem concentrate_blocks {ν : ℕ} (μ e : Fin ν → ℝ) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin ν) ℝ,
      (∀ a b, μ a ≠ μ b → O a b = 0) ∧
      ∀ a b, a ≠ b → μ a = μ b → (O *ᵥ e) a = 0 ∨ (O *ᵥ e) b = 0 := by
  classical
  have step (S : Finset ℝ) : ∃ O ∈ Matrix.orthogonalGroup (Fin ν) ℝ,
      (∀ a b, μ a ≠ μ b → O a b = 0) ∧
      ∀ ℓ ∈ S, ∀ a b, μ a = ℓ → μ b = ℓ → a ≠ b →
        (O *ᵥ e) a = 0 ∨ (O *ᵥ e) b = 0 := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨1, (Matrix.orthogonalGroup (Fin ν) ℝ).one_mem, ?_, by simp⟩
      intro a b different
      have indices : a ≠ b := fun equal => different (congrArg μ equal)
      simp [indices]
    | @insert ℓ S notin ih =>
      obtain ⟨O, hO, block, sparse⟩ := ih
      by_cases exists_index : ∃ a, μ a = ℓ
      · obtain ⟨a0, ha0⟩ := exists_index
        obtain ⟨H, hH, hblock, fixed, concentrated⟩ := concentrate_one_block μ (O *ᵥ e) ℓ a0 ha0
        refine ⟨H * O, (Matrix.orthogonalGroup (Fin ν) ℝ).mul_mem hH hO,
          block_mul μ H O hblock block, ?_⟩
        intro k hk a b ha hb different
        rw [← mulVec_mulVec]
        rcases Finset.mem_insert.mp hk with rfl | hk
        · by_cases same : a = a0
          · exact Or.inr (concentrated b hb (by intro h; exact different (same.trans h.symm)))
          · exact Or.inl (concentrated a ha same)
        · have outside : k ≠ ℓ := fun equal => notin (equal ▸ hk)
          rw [fixed a (fun equal => outside (ha.symm.trans equal)),
            fixed b (fun equal => outside (hb.symm.trans equal))]
          exact sparse k hk a b ha hb different
      · refine ⟨O, hO, block, ?_⟩
        intro k hk a b ha hb different
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact False.elim (exists_index ⟨a, ha⟩)
        · exact sparse k hk a b ha hb different
  obtain ⟨O, hO, block, sparse⟩ := step (Finset.univ.image μ)
  exact ⟨O, hO, block, fun a b different equal =>
    sparse (μ a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩) a b rfl equal.symm different⟩

end Osserman.Proofs.Rem72d
