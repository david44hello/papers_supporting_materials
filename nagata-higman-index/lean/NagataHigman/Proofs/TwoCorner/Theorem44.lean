/-
NagataHigman/Proofs/TwoCorner/Theorem44.lean — Lemma 4.3 (v1.02 tex 451-469): for n ≥ 3, C_{n²-1} ∩ B_n^{(n²-1)} = 0,
over ℂ for any Young system with Frobenius' splitting (the paper works over ℂ in Section 4, v1.02 l. 339).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof as in the paper: for f ∈ C_N ∩ I_ν and M = ρ_ν(f), Lemma 4.1 makes M anticommute with every Y_j; Γ anticommutes
with every Y_j (each X^{(j)} is a sum of transpositions); so ΓM commutes with every Y_j and is a scalar c (Lemma 4.2);
Γ² = d ≠ 0 gives M = (c/d)Γ. By Fourier inversion f(σ) = (f^ν/N!)(c/d) ψ(σ⁻¹), ψ(σ) = tr(ρ(σ)Γ), so by (T3) f
vanishes on every σ whose cycle type is not h(ν). For n ≥ 3, h(ν) = (2n-1, …, 5, 3) has n-1 ≥ 2 cycles, so it is not
the type of an N-cycle: f vanishes on the N-cycles. As f ∈ C_N, f vanishes off them too. So f = 0 (l. 590-604).
-/
import NagataHigman.Proofs.TwoCorner.Section4
import NagataHigman.Proofs.TwoCorner.GammaC
import NagataHigman.Proofs.TwoCorner.Lemma42Chain
import NagataHigman.Proofs.Lemma31

noncomputable section

namespace NagataHigman.Proofs

open Equiv Finset Matrix NagataHigman

/-- `Γ` anticommutes with every star: each `X^{(j)}` is a sum of transpositions (paper v1.02 l. 459). -/
theorem gamma_anticomm_star {F : Type*} [Field F] {N : ℕ} (Y : YoungSystem F N) (lam : Shape N)
    (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F)
    (hΓ : ∀ σ : Perm (Fin N), Γ * Y.rho lam σ = ((Perm.sign σ : ℤ) : F) • (Y.rho lam σ * Γ)) (j : Fin N) :
    Γ * Y.rhoAlg lam (starElem F j) = -(Y.rhoAlg lam (starElem F j) * Γ) := by
  unfold starElem
  rw [map_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hij : i ≠ j := (Finset.mem_filter.1 hi).2
  rw [rhoAlg_perm, hΓ, Perm.sign_swap hij]
  simp

/-- Lemma 4.3, proof (v1.02 l. 459): for `f ∈ C_N ∩ I_ν` and any invertible `Γ` with `Γρ(σ) = sgn(σ)ρ(σ)Γ`, `M = ρ_ν(f)`
anticommutes with every `Y_j` (Lemma 4.1), so `ΓM` commutes with them and is a scalar `c` (Lemma 4.2); `Γ² = d ≠ 0`
gives `M = (c/d)Γ`. -/
theorem rhoAlg_nu_eq_smul_gamma {F : Type*} [Field F] [CharZero F] (n : ℕ) (hn : 2 ≤ n)
    (Y : YoungSystem F (n ^ 2 - 1)) (lam : Shape (n ^ 2 - 1)) (hlam : lam.InBox n)
    (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) (hΓu : IsUnit Γ)
    (hΓ : ∀ σ : Perm (Fin (n ^ 2 - 1)), Γ * Y.rho lam σ = ((Perm.sign σ : ℤ) : F) • (Y.rho lam σ * Γ))
    {f : GrpAlg F (n ^ 2 - 1)} (hC : f ∈ cycleSpan F (n ^ 2 - 1)) (hf : f ∈ Y.block lam) :
    ∃ c : F, Y.rhoAlg lam f = c • Γ := by
  -- Lemma 4.1: `M` anticommutes with every `Y_j` (a permutation with a fixed point is not an `N`-cycle)
  have hanti := (lem_4_1_nu n hn Y lam hlam hf).1 fun σ ⟨j, hj⟩ =>
    coeff_eq_zero_of_mem_cycleSpan hC fun hfull => by
      have hj' : j ∈ σ.support := by rw [hfull.2]; exact Finset.mem_univ j
      exact (Perm.mem_support.1 hj') hj
  -- `ΓM` is a scalar by Lemma 4.2 (the paper's chain (a)-(e), Lemma42Chain.lean)
  have hΓY := gamma_anticomm_star Y lam Γ hΓ
  obtain ⟨c, hc⟩ := lem_4_2_general_chain n hn Y lam hlam (Γ * Y.rhoAlg lam f) fun j => by
    rw [mul_assoc, hanti j, mul_neg, ← mul_assoc, hΓY j, neg_mul, neg_neg, mul_assoc]
  obtain ⟨d, hd0, hd⟩ := gamma_sq_scalar Y lam Γ hΓu hΓ
  refine ⟨c / d, ?_⟩
  have h1 : Γ * (Γ * Y.rhoAlg lam f) = c • Γ := by rw [hc, mul_smul_comm, mul_one]
  rw [← mul_assoc, hd, smul_mul_assoc, one_mul] at h1
  rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hd0, one_smul]

/-- Lemma 4.3, proof (l. 595-596): for `f ∈ C_N ∩ I_ν`, `f(σ) = κ' ψ(σ⁻¹)`, so by (T3) `f` vanishes on every
permutation whose cycle type is not `h(ν)` (`n ≥ 3`, over ℂ, with Frobenius' splitting). -/
theorem coeff_nu_eq_zero_off_hooks (n : ℕ) (hn : 3 ≤ n) (Y : YoungSystem ℂ (n ^ 2 - 1)) (hsplit : AlternatingSplit Y)
    (lam : Shape (n ^ 2 - 1)) (hlam : lam.InBox n) {f : GrpAlg ℂ (n ^ 2 - 1)}
    (hC : f ∈ cycleSpan ℂ (n ^ 2 - 1)) (hf : f ∈ Y.block lam) (σ : Perm (Fin (n ^ 2 - 1)))
    (hσ : σ.partition.parts ≠ lam.diagonalHooks) : f.coeff σ = 0 := by
  have hn2 : 2 ≤ n := by omega
  have h9 : 9 ≤ n ^ 2 := by nlinarith
  have hself := thm_4_4_selfconj_proved n hn2 lam hlam
  obtain ⟨Γ, hΓu, hΓ⟩ := gamma_exists Y lam hself
  obtain ⟨e, hMΓ⟩ := rhoAlg_nu_eq_smul_gamma n hn2 Y lam hlam Γ hΓu hΓ hC hf
  have hinv : σ⁻¹.partition = σ.partition :=
    Perm.partition_eq_of_isConj.1 (Perm.isConj_iff_cycleType_eq.2 (Perm.cycleType_inv σ))
  have htr : trace (Y.rho lam σ⁻¹ * Γ) = 0 := by
    by_contra h
    exact hσ (hinv ▸ (gamma_support_C Y hsplit (by omega) lam hself Γ hΓu hΓ σ⁻¹).1 h)
  rw [YoungSystem.coeff_of_mem_block Y hf, hMΓ, Matrix.mul_smul, trace_smul, htr, smul_zero, mul_zero]

/-- Lemma 4.3, end of proof (l. 596-604): for `n ≥ 3` the type `h(ν)` is not that of an `N`-cycle, so `f` vanishes
on the `N`-cycles; `f ∈ C_N` vanishes off them; so `f = 0`. -/
theorem nu_cycle_block_eq_zero (n : ℕ) (hn : 3 ≤ n) (Y : YoungSystem ℂ (n ^ 2 - 1)) (hsplit : AlternatingSplit Y)
    (lam : Shape (n ^ 2 - 1)) (hlam : lam.InBox n) {f : GrpAlg ℂ (n ^ 2 - 1)}
    (hC : f ∈ cycleSpan ℂ (n ^ 2 - 1)) (hf : f ∈ Y.block lam) : f = 0 := by
  have hn2 : 2 ≤ n := by omega
  apply MonoidAlgebra.ext
  ext σ
  rw [MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_cases hfull : IsFullCycle σ
  · refine coeff_nu_eq_zero_off_hooks n hn Y hsplit lam hlam hC hf σ fun hσ => ?_
    exact (perm_hooks_sign_proved n hn σ (by rw [hσ, thm_4_4_hooks_proved n hn2 lam hlam])).2 hfull
  · exact coeff_eq_zero_of_mem_cycleSpan hC hfull

/-- **Lemma 4.3** (v1.02 tex 451-453), over ℂ: for `n ≥ 3`, `C_{n²-1} ∩ B_n^{(n²-1)} = 0`, for every Young system over ℂ
with Frobenius' splitting. -/
theorem thm_4_4_general (n : ℕ) (hn : 3 ≤ n) (Y : YoungSystem ℂ (n ^ 2 - 1)) (hsplit : AlternatingSplit Y) :
    cycleSpan ℂ (n ^ 2 - 1) ⊓ Y.boxSum n = ⊥ := by
  rw [eq_bot_iff]
  rintro f ⟨hC, hB⟩
  rw [Submodule.mem_bot]
  apply YoungSystem.eq_zero_of_forall_rhoAlg Y f
  intro lam
  by_cases hlam : lam.InBox n
  swap
  · exact (YoungSystem.mem_blockSum_iff Y).1 hB lam hlam
  have hf : f ∈ Y.block lam := by
    rw [YoungSystem.mem_block_iff Y]
    intro mu hmu
    apply (YoungSystem.mem_blockSum_iff Y).1 hB mu
    intro hmuB
    exact hmu (Nat.Partition.ext (by
      rw [sec_4_1_nu_proved n (by omega) mu hmuB, sec_4_1_nu_proved n (by omega) lam hlam]))
  rw [nu_cycle_block_eq_zero n hn Y hsplit lam hlam hC hf, map_zero]

end NagataHigman.Proofs
