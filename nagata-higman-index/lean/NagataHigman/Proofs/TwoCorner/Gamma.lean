/-
NagataHigman/Proofs/TwoCorner/Gamma.lean — consequences of the Young-system fields used in Section 4: Burnside
(ρ_λ onto), scalar commutant, trace nondegeneracy, and the (T3) lemmas of the paper (tex v1.02 lines 368-385).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Proofs.Blocks

noncomputable section

namespace NagataHigman.Proofs

open Equiv Finset Matrix NagataHigman

variable {F : Type*} [Field F] {N : ℕ} (Y : YoungSystem F N)

/-- A property of matrices that holds on every `ρ_λ(σ)` and is closed under `+` and scalars holds on all of
`ρ_λ(F[S_N])`, hence on every matrix. -/
theorem forall_matrix_of_forall_rho (lam : Shape N) (P : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F → Prop)
    (hadd : ∀ A B, P A → P B → P (A + B)) (hsmul : ∀ (c : F) A, P A → P (c • A))
    (hσ : ∀ σ, P (Y.rho lam σ)) : ∀ X, P X := by
  intro X
  obtain ⟨a, rfl⟩ := YoungSystem.rhoAlg_surjective Y lam X
  induction a using MonoidAlgebra.induction_on with
  | of σ => simpa [YoungSystem.rhoAlg, MonoidAlgebra.lift_of] using hσ σ
  | add a b ha hb => simpa [map_add] using hadd _ _ ha hb
  | smul c a ha => simpa [map_smul] using hsmul c _ ha

/-- A matrix commuting with every `ρ_λ(σ)` is a scalar (Schur, via Burnside). -/
theorem eq_scalar_of_commute_rho (lam : Shape N) (Z : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F)
    (h : ∀ σ, Z * Y.rho lam σ = Y.rho lam σ * Z) : ∃ c : F, Z = c • 1 := by
  have hall : ∀ X, Z * X = X * Z :=
    forall_matrix_of_forall_rho Y lam (fun X => Z * X = X * Z)
      (fun A B hA hB => by rw [mul_add, add_mul, hA, hB]) (fun c A hA => by rw [mul_smul_comm, smul_mul_assoc, hA])
      h
  obtain ⟨c, hc⟩ := mem_range_scalar_of_commute_single (M := Z) (fun i j _ => (hall _).symm)
  exact ⟨c, by rw [← hc, scalar_apply, smul_one_eq_diagonal]⟩

/-- Trace nondegeneracy on `ρ_λ(S_N)`: if `tr(ρ_λ(σ) Z) = 0` for every `σ` then `Z = 0`. -/
theorem eq_zero_of_trace_rho (lam : Shape N) (Z : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F)
    (h : ∀ σ, trace (Y.rho lam σ * Z) = 0) : Z = 0 := by
  have hall : ∀ X, trace (X * Z) = 0 :=
    forall_matrix_of_forall_rho Y lam (fun X => trace (X * Z) = 0)
      (fun A B hA hB => by rw [add_mul, trace_add, hA, hB, add_zero])
      (fun c A hA => by rw [smul_mul_assoc, trace_smul, hA, smul_zero]) h
  exact (ext_iff_trace_mul_left).2 fun X => by rw [hall X, mul_zero, trace_zero]

/-- **(T3), line 428**: `ψ(σ) = tr(ρ(σ)Γ)` vanishes at odd `σ` (characteristic 0). -/
theorem gamma_odd [CharZero F] (lam : Shape N) (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F)
    (hΓ : ∀ σ : Perm (Fin N), Γ * Y.rho lam σ = ((Perm.sign σ : ℤ) : F) • (Y.rho lam σ * Γ))
    (σ : Perm (Fin N)) (hσ : Perm.sign σ = -1) : trace (Y.rho lam σ * Γ) = 0 := by
  have h1 : trace (Y.rho lam σ * Γ) = - trace (Y.rho lam σ * Γ) := by
    calc trace (Y.rho lam σ * Γ) = trace (Γ * Y.rho lam σ) := trace_mul_comm _ _
      _ = - trace (Y.rho lam σ * Γ) := by rw [hΓ σ, hσ, trace_smul]; simp
  have h2 : (2 : F) * trace (Y.rho lam σ * Γ) = 0 := by linear_combination h1
  simpa using h2

/-- **(T3), v1.02 lines 368-369**: for `λ = λ'` there is an invertible `Γ` with `Γ ρ(σ) = sgn(σ) ρ(σ) Γ`
(from the sign-twist field `S^{λ'} ≅ S^λ ⊗ sgn`). -/
theorem gamma_exists (lam : Shape N) (h : lam.conjugate = lam) :
    ∃ Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F, IsUnit Γ ∧
      ∀ σ : Perm (Fin N), Γ * Y.rho lam σ = ((Perm.sign σ : ℤ) : F) • (Y.rho lam σ * Γ) := by
  have key : ∀ mu : Shape N, mu = lam.conjugate →
      ∃ G : (Fin (Y.dim mu) → F) ≃ₗ[F] (Fin (Y.dim lam) → F), ∀ (σ : Perm (Fin N)) (v : Fin (Y.dim mu) → F),
        G (Y.rho mu σ *ᵥ v) = ((Perm.sign σ : ℤ) : F) • (Y.rho lam σ *ᵥ G v) := by
    intro mu hmu
    subst hmu
    exact Y.signTwist lam
  obtain ⟨G, hG⟩ := key lam h.symm
  refine ⟨LinearMap.toMatrix' (G : (Fin (Y.dim lam) → F) →ₗ[F] (Fin (Y.dim lam) → F)), ?_, fun σ => ?_⟩
  · exact LinearMap.isUnit_toMatrix'_iff.2 ((Module.End.isUnit_iff _).2 G.bijective)
  · refine (ext_iff_mulVec).2 fun v => ?_
    rw [← mulVec_mulVec, LinearMap.toMatrix'_mulVec, Matrix.smul_mulVec, ← mulVec_mulVec,
      LinearMap.toMatrix'_mulVec]
    exact hG σ v

/-- **(T3), v1.02 lines 370-371**: `Γ²` commutes with `ρ(S_N)`, so it is a nonzero scalar. -/
theorem gamma_sq_scalar (lam : Shape N) (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) (hΓu : IsUnit Γ)
    (hΓ : ∀ σ : Perm (Fin N), Γ * Y.rho lam σ = ((Perm.sign σ : ℤ) : F) • (Y.rho lam σ * Γ)) :
    ∃ c : F, c ≠ 0 ∧ Γ * Γ = c • 1 := by
  obtain ⟨c, hc⟩ := eq_scalar_of_commute_rho Y lam (Γ * Γ) fun σ => by
    rw [mul_assoc, hΓ σ, mul_smul_comm, ← mul_assoc, hΓ σ, smul_mul_assoc, smul_smul, mul_assoc]
    rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs <;> simp [hs]
  by_cases hc0 : c = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    have hunit : IsUnit (Γ * Γ) := hΓu.mul hΓu
    rw [hc, hc0, zero_smul] at hunit
    have : Subsingleton (Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) :=
      subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hunit)
    exact Subsingleton.elim _ _
  · exact ⟨c, hc0, hc⟩

end NagataHigman.Proofs

end
