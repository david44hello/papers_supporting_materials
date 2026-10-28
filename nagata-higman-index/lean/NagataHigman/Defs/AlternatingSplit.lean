/-
NagataHigman/Defs/AlternatingSplit.lean — what JK81 2.5.7 + 2.5.13 say, for a Young system over ℂ: for λ = λ' (N ≥ 2)
the restriction of S^λ to A_N is V₊ ⊕ V₋, two irreducible non-isomorphic constituents, whose characters agree at every
even σ whose cycle type is not h(λ). The cited existence statement is in NagataHigman/Cited/Classical.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Defs.YoungSystem

noncomputable section

namespace NagataHigman

open Equiv Matrix

variable {N : ℕ} (Y : YoungSystem ℂ N) (lam : Shape N)

/-- `V` is an `A_N`-subspace of `S^λ`: invariant under `ρ_λ(σ)` for every even `σ`. -/
def IsAltInvariant (V : Submodule ℂ (Fin (Y.dim lam) → ℂ)) : Prop :=
  ∀ σ : Perm (Fin N), Perm.sign σ = 1 → ∀ v ∈ V, Y.rho lam σ *ᵥ v ∈ V

/-- `Φ` commutes with every `ρ_λ(σ)`, `σ` even (an `A_N`-map `S^λ → S^λ`). -/
def IsAltEquivariant (Φ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ) : Prop :=
  ∀ σ : Perm (Fin N), Perm.sign σ = 1 → Φ * Y.rho lam σ = Y.rho lam σ * Φ

/-- The splitting of `Res_{A_N} S^λ` (paper l. 414-416) [JK81 2.5.7]:
* `V₊ ⊕ V₋ = S^λ`, both `A_N`-invariant, nonzero and irreducible;
* non-isomorphic: every `A_N`-map `V₊ → V₋` (and `V₋ → V₊`) is zero — written on `S^λ` as an equivariant matrix that kills
  one constituent and maps the other into the first. -/
structure AltDecomp where
  Vp : Submodule ℂ (Fin (Y.dim lam) → ℂ)
  Vm : Submodule ℂ (Fin (Y.dim lam) → ℂ)
  compl : IsCompl Vp Vm
  inv_p : IsAltInvariant Y lam Vp
  inv_m : IsAltInvariant Y lam Vm
  ne_bot_p : Vp ≠ ⊥
  ne_bot_m : Vm ≠ ⊥
  irred_p : ∀ W : Submodule ℂ (Fin (Y.dim lam) → ℂ), W ≤ Vp → IsAltInvariant Y lam W → W = ⊥ ∨ W = Vp
  irred_m : ∀ W : Submodule ℂ (Fin (Y.dim lam) → ℂ), W ≤ Vm → IsAltInvariant Y lam W → W = ⊥ ∨ W = Vm
  noniso_pm : ∀ Φ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ, IsAltEquivariant Y lam Φ →
    (∀ v ∈ Vm, Φ *ᵥ v = 0) → (∀ v ∈ Vp, Φ *ᵥ v ∈ Vm) → Φ = 0
  noniso_mp : ∀ Φ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ, IsAltEquivariant Y lam Φ →
    (∀ v ∈ Vp, Φ *ᵥ v = 0) → (∀ v ∈ Vm, Φ *ᵥ v ∈ Vp) → Φ = 0

/-- The splitting of `Res_{A_N} S^λ` and Frobenius' theorem (paper l. 414-416, 370-371): the splitting `AltDecomp`, and
* Frobenius [JK81 2.5.13]: `χ₊(σ) = χ₋(σ)` for every even `σ` whose cycle type (with fixed points) is not `h(λ)`,
  `χ±(σ)` = the trace of `ρ_λ(σ)` restricted to `V±`. -/
structure AltSplit extends AltDecomp Y lam where
  frobenius : ∀ (σ : Perm (Fin N)) (hσ : Perm.sign σ = 1), σ.partition.parts ≠ lam.diagonalHooks →
    LinearMap.trace ℂ Vp ((Matrix.mulVecLin (Y.rho lam σ)).restrict (inv_p σ hσ)) =
      LinearMap.trace ℂ Vm ((Matrix.mulVecLin (Y.rho lam σ)).restrict (inv_m σ hσ))

/-- JK81 2.5.7 + 2.5.13 hold for `Y`: every self-conjugate shape with `N ≥ 2` splits as in `AltSplit`. -/
def AlternatingSplit : Prop :=
  ∀ lam : Shape N, lam.conjugate = lam → 2 ≤ N → Nonempty (AltSplit Y lam)

end NagataHigman

end
