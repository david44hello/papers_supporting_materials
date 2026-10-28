/-
NagataHigman/Proofs/YoungIdemCoeff.lean — the Jucys–Murphy idempotent `e_λ` (Defs/CentralIdempotent.lean) is the paper's
`e_λ = (f^λ/N!) Σ_σ χ_λ(σ) σ` (v1.02 tex 186-187): its coefficient at `σ` is `(f^λ/N!) tr ρ_λ(σ)`, in every Young system.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route: Fourier inversion (`fourier`) gives `e_λ(σ) = Σ_μ (f^μ/N!) tr(ρ_μ(σ⁻¹) ρ_μ(e_λ))`; `ρ_μ(e_λ) = δ_{λμ}`
(rhoAlg_youngIdem) leaves `(f^λ/N!) tr ρ_λ(σ⁻¹)`; and `σ⁻¹` is conjugate to `σ`, so the traces agree (trace_rho_inv).
-/
import NagataHigman.Proofs.CentralIdempotent
import NagataHigman.Proofs.BlocksOrth

noncomputable section

namespace NagataHigman.Proofs.YoungSystem

open NagataHigman Finset Matrix

variable {F : Type*} [Field F] {N : ℕ} (Y : YoungSystem F N)

/-- **`e_λ = (f^λ/N!) Σ_σ χ_λ(σ) σ`** (v1.02 tex 186-187): the coefficient of `e_λ` at `σ` is `(f^λ/N!) tr ρ_λ(σ)`. -/
theorem youngIdem_coeff [CharZero F] (lam : Shape N) (σ : Equiv.Perm (Fin N)) :
    (youngIdem F lam).coeff σ = ((Y.dim lam : F) / (N.factorial : F)) * trace (Y.rho lam σ) := by
  rw [Y.fourier, Finset.sum_eq_single lam]
  · rw [show MonoidAlgebra.lift F _ _ (Y.rho lam) (youngIdem F lam) = Y.rhoAlg lam (youngIdem F lam) from rfl,
      rhoAlg_youngIdem Y]
    simp only [↓reduceIte, Matrix.mul_one]
    rw [trace_rho_inv Y]
  · intro mu _ hmu
    rw [show MonoidAlgebra.lift F _ _ (Y.rho mu) (youngIdem F lam) = Y.rhoAlg mu (youngIdem F lam) from rfl,
      rhoAlg_youngIdem Y]
    simp only [hmu, ↓reduceIte, Matrix.trace_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ lam) h

end NagataHigman.Proofs.YoungSystem

end
