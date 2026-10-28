/-
NagataHigman/Proofs/Lemma31.lean — Lemma 3.1 (one-corner step, paper lines 422-432): `C_{n²} ∩ B_n^{(n²)} = 0`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route (the paper's). For `f ∈ C_N ∩ I_λ` and `σ` fixing `top = N-1`, `σ⁻¹` is not an `N`-cycle, so `f(σ⁻¹) = 0`;
Fourier inversion on one block turns this into `tr(ρ_λ(σ) ρ_λ(f)) = 0`. If every standard tableau of `λ` has `top`
in a cell of content 0, the Young basis gives `ρ_λ(J_top) = 0`, and the restriction fact `hres` says the `ρ_λ(σ)`,
`σ ∈ S_{N-1}`, span all matrices; so `ρ_λ(f) = 0` and `f = 0`. For the square, the two Young-combinatorics facts
(the square is the only shape in the box; every SYT of the square has `N-1` in the corner `(n-1, n-1)`) enter as
hypotheses `hsq`, `hcorner` (proved elsewhere).
Everything is for an ARBITRARY Young system `Y`. Imports: Mathlib + Defs + Proofs.Blocks/BlocksOrth only.
-/
import NagataHigman.Proofs.BlocksOrth

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman Equiv Finset Matrix

variable {F : Type*} [Field F]

/-- An element of `C_N` has zero coefficient at every permutation that is not an `N`-cycle. -/
lemma coeff_eq_zero_of_mem_cycleSpan {N : ℕ} {f : GrpAlg F N} (hf : f ∈ cycleSpan F N) {σ : Perm (Fin N)}
    (hσ : ¬ IsFullCycle σ) : f.coeff σ = 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨τ, hτ, rfl⟩ := hx
    rw [coeff_perm, ite_eq_right]
    rintro rfl
    exact hσ hτ
  | zero => simp [MonoidAlgebra.coeff_zero]
  | add x y _ _ hx hy => rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy, add_zero]
  | smul r x _ hx => rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, hx, smul_zero]

/-- A permutation with a fixed point is not an `N`-cycle. -/
lemma not_isFullCycle_of_fixed {N : ℕ} {σ : Perm (Fin N)} {top : Fin N} (h : σ top = top) : ¬ IsFullCycle σ := by
  rintro ⟨_, hsupp⟩
  have hmem : top ∈ σ.support := hsupp ▸ Finset.mem_univ top
  exact (Perm.mem_support.1 hmem) h

namespace YoungSystem

variable {N : ℕ} (Y : YoungSystem F N)

/-- If every standard tableau of `λ` has `top` in a cell of content 0, then `ρ_λ(J_top) = 0` (Young basis (T1)). -/
lemma rhoAlg_jucysMurphy_eq_zero (lam : Shape N) (top : Fin N) (h : ∀ T : SYT lam, T.content top = 0) :
    Y.rhoAlg lam (jucysMurphy F top) = 0 := by
  obtain ⟨b, hb⟩ := Y.youngBasis lam
  apply Matrix.toLin'.injective
  apply b.ext
  intro T
  rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]
  have hT := hb T top
  rw [h T, Int.cast_zero, zero_smul] at hT
  exact hT

/-- If `ρ_λ(J_top) = 0` (`top = N-1`), every matrix is in the span of `ρ_λ(S_{N-1})` (restriction fact `hres`). -/
lemma mem_span_rho_stab
    (hres : ∀ (lam : Shape N) (top : Fin N), (top : ℕ) + 1 = N →
      ∀ X : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F,
        X ∈ Submodule.span F ((Y.rho lam : Perm (Fin N) → Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) '' stab top) ↔
          X * Y.rhoAlg lam (jucysMurphy F top) = Y.rhoAlg lam (jucysMurphy F top) * X)
    (lam : Shape N) (top : Fin N) (htop : (top : ℕ) + 1 = N)
    (hJ : Y.rhoAlg lam (jucysMurphy F top) = 0) (X : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) :
    X ∈ Submodule.span F ((Y.rho lam : Perm (Fin N) → Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) '' stab top) := by
  rw [hres lam top htop X, hJ, Matrix.mul_zero, Matrix.zero_mul]

/-- The one-corner step for a general shape: if every SYT of `λ` has `top = N-1` in a cell of content 0, then
`C_N ∩ I_λ = 0`. -/
theorem cycleSpan_inf_block_eq_bot_of_content [CharZero F]
    (hres : ∀ (lam : Shape N) (top : Fin N), (top : ℕ) + 1 = N →
      ∀ X : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F,
        X ∈ Submodule.span F ((Y.rho lam : Perm (Fin N) → Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) '' stab top) ↔
          X * Y.rhoAlg lam (jucysMurphy F top) = Y.rhoAlg lam (jucysMurphy F top) * X)
    {lam : Shape N} (top : Fin N)
    (htop : (top : ℕ) + 1 = N) (hcont : ∀ T : SYT lam, T.content top = 0) :
    cycleSpan F N ⊓ Y.block lam = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_inf] at hf
  obtain ⟨hfC, hfB⟩ := hf
  rw [Submodule.mem_bot]
  have hM : Y.rhoAlg lam f = 0 := by
    by_cases hd : Y.dim lam = 0
    · have : IsEmpty (Fin (Y.dim lam)) := by rw [hd]; infer_instance
      exact Matrix.ext fun i => isEmptyElim i
    have hc : ((Y.dim lam : F) / (N.factorial : F)) ≠ 0 :=
      div_ne_zero (Nat.cast_ne_zero.2 hd) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero N))
    have hstab : ∀ σ ∈ stab top, trace (Y.rho lam σ * Y.rhoAlg lam f) = 0 := by
      intro σ hσ
      have hσ' : σ⁻¹ top = top := by
        rw [Perm.inv_eq_iff_eq]
        exact hσ.symm
      have h0 := coeff_eq_zero_of_mem_cycleSpan hfC (not_isFullCycle_of_fixed hσ')
      rw [coeff_of_mem_block Y hfB, inv_inv] at h0
      exact (mul_eq_zero.1 h0).resolve_left hc
    have hJ := rhoAlg_jucysMurphy_eq_zero Y lam top hcont
    apply eq_zero_of_trace_mul
    intro E
    have hE := mem_span_rho_stab Y hres lam top htop hJ E
    rw [Matrix.trace_mul_comm]
    induction hE using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨σ, hσ, rfl⟩ := hx
      exact hstab σ hσ
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, trace_add, hx, hy, add_zero]
    | smul r x _ hx => rw [Matrix.smul_mul, trace_smul, hx, smul_zero]
  apply eq_zero_of_forall_rhoAlg Y
  intro mu
  by_cases hmu : mu = lam
  · subst hmu
    exact hM
  · exact (mem_block_iff Y).1 hfB mu hmu

end YoungSystem

/-- **Lemma 3.1** (paper lines 422-432), for an arbitrary Young system: for `n ≥ 2`, `C_{n²} ∩ B_n^{(n²)} = 0`,
given the two Young-combinatorics facts about the square `(n^n)`. -/
theorem lemma_3_1_of [CharZero F] {n : ℕ} (hn : 2 ≤ n) (Y : YoungSystem F (n ^ 2))
    (hres : ∀ (lam : Shape (n ^ 2)) (top : Fin (n ^ 2)), (top : ℕ) + 1 = n ^ 2 →
      ∀ X : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F,
        X ∈ Submodule.span F
            ((Y.rho lam : Perm (Fin (n ^ 2)) → Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) '' stab top) ↔
          X * Y.rhoAlg lam (jucysMurphy F top) = Y.rhoAlg lam (jucysMurphy F top) * X)
    (hsq : ∀ lam : Shape (n ^ 2), lam.InBox n → lam.parts = Multiset.replicate n n)
    (hcorner : ∀ lam : Shape (n ^ 2), lam.parts = Multiset.replicate n n →
      ∀ (T : SYT lam) (top : Fin (n ^ 2)), (top : ℕ) + 1 = n ^ 2 → T.pos top = (n - 1, n - 1)) :
    cycleSpan F (n ^ 2) ⊓ Y.boxSum n = ⊥ := by
  have hN : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
  let top : Fin (n ^ 2) := ⟨n ^ 2 - 1, by omega⟩
  have htop : (top : ℕ) + 1 = n ^ 2 := by
    show n ^ 2 - 1 + 1 = n ^ 2
    omega
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_inf] at hf
  obtain ⟨hfC, hfB⟩ := hf
  rw [Submodule.mem_bot]
  unfold NagataHigman.YoungSystem.boxSum at hfB
  rw [YoungSystem.mem_blockSum_iff Y] at hfB
  by_cases hex : ∃ lam : Shape (n ^ 2), lam.InBox n
  · obtain ⟨lam, hlam⟩ := hex
    have hfl : f ∈ Y.block lam := by
      rw [YoungSystem.mem_block_iff Y]
      intro mu hmu
      apply hfB
      intro hmuBox
      apply hmu
      exact Nat.Partition.ext ((hsq mu hmuBox).trans (hsq lam hlam).symm)
    have hcont : ∀ T : SYT lam, T.content top = 0 := by
      intro T
      simp [SYT.content, hcorner lam (hsq lam hlam) T top htop]
    have hbot := YoungSystem.cycleSpan_inf_block_eq_bot_of_content Y hres top htop hcont
    rw [eq_bot_iff] at hbot
    exact (Submodule.mem_bot F).1 (hbot (Submodule.mem_inf.2 ⟨hfC, hfl⟩))
  · simp only [not_exists] at hex
    apply YoungSystem.eq_zero_of_forall_rhoAlg Y
    intro mu
    exact hfB mu (hex mu)

end NagataHigman.Proofs

end
