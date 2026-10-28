/-
ThmEMerge.lean — merging frame eigenvalues in Theorem E, paper 013, lines 762–782.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.ThmETransfer

namespace Osserman.Proofs.ThmEMerge

open Osserman Matrix Osserman.Proofs.Spectral Osserman.Proofs.ThmESpectral
open Osserman.Proofs.ThmEProjection Osserman.Proofs.ThmEPerturbation Osserman.Proofs.ThmETransfer

theorem thm_E_tilde_of_RJ_curv
    (hRJ : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (hJ : Jᵀ = -J),
      (IsQuadFamily (jfam J) ∧ (∀ x, (jfam J x)ᵀ = jfam J x) ∧ (∀ x, jfam J x *ᵥ x = 0) ∧
        ∀ x y : Vec n, ((J *ᵥ x) ⬝ᵥ y) ^ 2 = ((J *ᵥ y) ⬝ᵥ x) ^ 2) ∧
      ∃ B : CurvTensor n, (∀ u v w, B.op u v w = RJfun J u v w) ∧ ∀ x, B.jacobi x = jfam J x)
    (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) (h : ThmEFrame R m ev J) :
    ∃ Rt : CurvTensor 16, (∀ u v w, Rt.op u v w = R.op u v w - (ev 2 - ev 1) • ∑ a, RJfun (J a) u v w) ∧
      (∀ x, Rt.jacobi x = R.jacobi x - (ev 2 - ev 1) • ∑ a, jfam (J a) x) ∧ Rt.IsOsserman ∧
      (∀ x : Vec 16, x ⬝ᵥ x = 1 → Rt.redMult x (ev 0) = m 0 ∧ Rt.redMult x (ev 1) = m 1 + m 2) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ a, J a *ᵥ x ∈ Module.End.eigenspace (Rt.jacobiMap x) (ev 1) := by
  classical
  let c := ev 2 - ev 1
  have hJ := h.2.2.2.1
  have field := h.2.2.2.2
  have hO := pattern_osserman R m h.1 ev h.2.1 h.2.2.1
  obtain ⟨Rt, operator, jacobi⟩ := perturb_tensor (fun J hJ => (hRJ J hJ).2) R J hJ (fun _ => c)
  have shifted : ev 2 - c = ev 1 := by dsimp only [c]; ring
  have ne01 : ev 0 ≠ ev 1 := h.2.1.ne (by decide)
  have ne02 : ev 0 ≠ ev 2 := h.2.1.ne (by decide)
  have ne12 : ev 1 ≠ ev 2 := h.2.1.ne (by decide)
  have formula (x : Vec 16) (hx : x ⬝ᵥ x = 1) (μ : ℝ) :
      Rt.redMult x μ = R.redMult x μ - (if μ = ev 2 then m 2 else 0) +
        Fintype.card {a : Fin (m 2) // ev 2 - c = μ} := by
    have frame := clifford_frame J hJ x hx
    have eigen (a : Fin (m 2)) : R.op (J a *ᵥ x) x x = ev 2 • (J a *ᵥ x) :=
      Module.End.mem_eigenspace_iff.mp (field x hx a)
    exact multiplicity_update R Rt x (fun a => J a *ᵥ x) (fun _ => c) (ev 2)
      frame.1 frame.2 eigen (by simpa only [jfam] using jacobi x) μ
  refine ⟨Rt, ?_, ?_, perturbed_osserman R Rt hO J hJ (ev 2) field (fun _ => c) jacobi, ?_, ?_⟩
  · intro u v w
    rw [operator, ← Finset.smul_sum]
  · intro x
    rw [jacobi, ← Finset.smul_sum]
  · intro x hx
    constructor
    · rw [formula x hx]
      simp [shifted, ne02, Ne.symm ne01, h.2.2.1 x hx 0]
    · rw [formula x hx]
      simp [shifted, ne12, h.2.2.1 x hx 1]
  · intro x hx a
    apply Module.End.mem_eigenspace_iff.mpr
    change Rt.op (J a *ᵥ x) x x = ev 1 • (J a *ᵥ x)
    have frame := clifford_frame J hJ x hx
    have eigen (b : Fin (m 2)) : R.op (J b *ᵥ x) x x = ev 2 • (J b *ᵥ x) :=
      Module.End.mem_eigenspace_iff.mp (field x hx b)
    rw [updated_frame R Rt x (fun a => J a *ᵥ x) (fun _ => c) (ev 2) frame.1 eigen
      (by simpa only [jfam] using jacobi x), shifted]

theorem thm_E_intermediate_pattern_of_RJ_curv
    (hRJ : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (hJ : Jᵀ = -J),
      (IsQuadFamily (jfam J) ∧ (∀ x, (jfam J x)ᵀ = jfam J x) ∧ (∀ x, jfam J x *ᵥ x = 0) ∧
        ∀ x y : Vec n, ((J *ᵥ x) ⬝ᵥ y) ^ 2 = ((J *ᵥ y) ⬝ᵥ x) ^ 2) ∧
      ∃ B : CurvTensor n, (∀ u v w, B.op u v w = RJfun J u v w) ∧ ∀ x, B.jacobi x = jfam J x)
    (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) (h : ThmEFrame R m ev J) (h2 : m 2 = 2) (a : Fin (m 2)) :
    ∃ R' : CurvTensor 16, (∀ u v w, R'.op u v w = R.op u v w - (ev 2 - ev 1) • RJfun (J a) u v w) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 →
        R'.redMult x (ev 0) = m 0 ∧ R'.redMult x (ev 1) = m 1 + 1 ∧ R'.redMult x (ev 2) = 1 := by
  classical
  let c := ev 2 - ev 1
  let s : Fin (m 2) → ℝ := fun b => if b = a then c else 0
  have hJ := h.2.2.2.1
  have field := h.2.2.2.2
  obtain ⟨R', operator, jacobi⟩ := perturb_tensor (fun J hJ => (hRJ J hJ).2) R J hJ s
  have ne01 : ev 0 ≠ ev 1 := h.2.1.ne (by decide)
  have ne02 : ev 0 ≠ ev 2 := h.2.1.ne (by decide)
  have ne12 : ev 1 ≠ ev 2 := h.2.1.ne (by decide)
  have shifted : ev 2 - c = ev 1 := by dsimp only [c]; ring
  have cne : c ≠ 0 := sub_ne_zero.mpr (Ne.symm ne12)
  have pred0 (b : Fin (m 2)) : (ev 2 - s b = ev 0) ↔ False := by
    by_cases equal : b = a <;> simp [s, equal, shifted, Ne.symm ne01, Ne.symm ne02]
  have pred1 (b : Fin (m 2)) : (ev 2 - s b = ev 1) ↔ b = a := by
    by_cases equal : b = a <;> simp [s, equal, shifted, Ne.symm ne12]
  have pred2 (b : Fin (m 2)) : (ev 2 - s b = ev 2) ↔ b ≠ a := by
    by_cases equal : b = a <;> simp [s, equal, sub_eq_self, cne]
  have card0 : Fintype.card {b : Fin (m 2) // ev 2 - s b = ev 0} = 0 := by simp only [pred0]; simp
  have card1 : Fintype.card {b : Fin (m 2) // ev 2 - s b = ev 1} = 1 := by
    simpa only [Fintype.card_subtype_eq] using Fintype.card_congr (Equiv.subtypeEquivRight pred1)
  have card2 : Fintype.card {b : Fin (m 2) // ev 2 - s b = ev 2} = 1 := by
    have cards := Fintype.card_congr (Equiv.subtypeEquivRight pred2)
    rw [Fintype.card_subtype_compl (fun b : Fin (m 2) => b = a), Fintype.card_subtype_eq,
      Fintype.card_fin] at cards
    exact cards.trans (show m 2 - 1 = 1 by omega)
  refine ⟨R', ?_, ?_⟩
  · intro u v w
    rw [operator]
    simp only [s, c, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · intro x hx
    have frame := clifford_frame J hJ x hx
    have eigen (b : Fin (m 2)) : R.op (J b *ᵥ x) x x = ev 2 • (J b *ᵥ x) :=
      Module.End.mem_eigenspace_iff.mp (field x hx b)
    have formula (μ : ℝ) := multiplicity_update R R' x (fun a => J a *ᵥ x) s (ev 2)
      frame.1 frame.2 eigen (by simpa only [jfam] using jacobi x) μ
    refine ⟨?_, ?_, ?_⟩
    · rw [formula, card0, h.2.2.1 x hx 0]
      simp [ne02]
    · rw [formula, card1, h.2.2.1 x hx 1]
      simp [ne12]
    · rw [formula, card2, h.2.2.1 x hx 2]
      simp

end Osserman.Proofs.ThmEMerge

