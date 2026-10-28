/-
NagataHigman/Defs/YoungSystem.lean — what a "Young system" is: matrix forms of the irreducible representations of S_N
over F, one per shape, with the classical properties that the paper cites. The cited existence statement lives in
NagataHigman/Cited/Classical.lean; THIS file only says what is claimed to exist.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

The intended model: `rho λ` = the Specht module `S^λ` written in Young's seminormal basis (rational matrices,
so valid over every field of characteristic 0). Each field below is a classical theorem about that model:
  wedderburn   (F2)  [Ja78 Thm 4.12: the Specht modules over ℚ are absolutely irreducible and give all ordinary
                     irreducible representations] + Wedderburn: F[S_N] ≅ ∏_λ End(S^λ) via (ρ_λ)_λ   (paper l. 221-225)
  fourier      (F2)  Fourier inversion a(σ) = ∑_λ (f^λ/N!) tr(ρ_λ(σ⁻¹) ρ_λ(a)) (paper l. 226-229, citing [Ja78]; the
                     formula is standard, e.g. Serre, Linear Representations of Finite Groups, §6.2). Derivable from
                     `wedderburn` (trace of left multiplication); kept as a cited clause.
  youngBasis   (T1)   [Ju74, Mu81, OV96] a basis {v_T} indexed by standard tableaux with J_k v_T = c_T(k) v_T (l. 399-400)
  signTwist    (F7)  [Ja78 Thm 6.7 with self-duality, Thm 4.12] S^{λ'} ≅ S^λ ⊗ sgn (l. 250-251, 357). Derivable from
                     `wedderburn` + `youngBasis`; kept as a cited clause.
The paper's uses of branching (F5) + Burnside (F6) (l. 370-372, 386-389) are PROVED in NagataHigman/Proofs/ from
`wedderburn` + `youngBasis` (Okounkov–Vershik argument); Frobenius' theorem is cited over ℂ in Defs/AlternatingSplit.lean.
The labels are pinned by `youngBasis`: the joint J-spectrum of ρ_λ is the set of content vectors of the standard
tableaux of shape λ, which determines λ. So `block λ` below is the true isotypic block I_λ = F[S_N] e_λ.
-/
import NagataHigman.Defs.GroupAlgebra
import NagataHigman.Defs.Young

noncomputable section

namespace NagataHigman

open Equiv Finset Matrix

/-- A Young system for `S_N` over `F` (see the file header for the source of every field). -/
structure YoungSystem (F : Type*) [Field F] (N : ℕ) where
  /-- `f^λ = dim S^λ`. -/
  dim : Shape N → ℕ
  /-- The matrix representation `ρ_λ : S_N → GL_{f^λ}(F)`. -/
  rho : (lam : Shape N) → Perm (Fin N) →* Matrix (Fin (dim lam)) (Fin (dim lam)) F
  /-- (F2) Wedderburn: `a ↦ (ρ_λ(a))_λ` is a bijection `F[S_N] → ∏_λ Mat_{f^λ}(F)`. -/
  wedderburn : Function.Bijective
    (fun (a : GrpAlg F N) (lam : Shape N) => MonoidAlgebra.lift F _ (Perm (Fin N)) (rho lam) a)
  /-- (F2) Fourier inversion. -/
  fourier : ∀ (a : GrpAlg F N) (σ : Perm (Fin N)),
    a.coeff σ = ∑ lam : Shape N, ((dim lam : F) / (N.factorial : F)) *
      trace (rho lam σ⁻¹ * MonoidAlgebra.lift F _ (Perm (Fin N)) (rho lam) a)
  /-- (T1) The Young (Gelfand–Tsetlin) basis: `J_k v_T = c_T(k) v_T`. -/
  youngBasis : ∀ lam : Shape N, ∃ b : Module.Basis (SYT lam) F (Fin (dim lam) → F),
    ∀ (T : SYT lam) (k : Fin N),
      MonoidAlgebra.lift F _ (Perm (Fin N)) (rho lam) (jucysMurphy F k) *ᵥ b T = ((T.content k : ℤ) : F) • b T
  /-- (F7) `S^{λ'} ≅ S^λ ⊗ sgn`. -/
  signTwist : ∀ lam : Shape N, ∃ Γ : (Fin (dim lam.conjugate) → F) ≃ₗ[F] (Fin (dim lam) → F),
    ∀ (σ : Perm (Fin N)) (v : Fin (dim lam.conjugate) → F),
      Γ (rho lam.conjugate σ *ᵥ v) = ((Perm.sign σ : ℤ) : F) • (rho lam σ *ᵥ Γ v)

namespace YoungSystem

variable {F : Type*} [Field F] {N : ℕ} (Y : YoungSystem F N)

/-- `ρ_λ` extended linearly to `F[S_N]`. -/
def rhoAlg (lam : Shape N) : GrpAlg F N →ₐ[F] Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F :=
  MonoidAlgebra.lift F _ (Perm (Fin N)) (Y.rho lam)

/-- The isotypic block `I_λ`: the elements on which every other `ρ_μ` vanishes (paper lines 153-154). -/
def block (lam : Shape N) : Submodule F (GrpAlg F N) :=
  ⨅ (mu : Shape N) (_ : mu ≠ lam), LinearMap.ker (Y.rhoAlg mu).toLinearMap

/-- `⊕_{λ ∈ S} I_λ` for a set `S` of shapes. -/
def blockSum (S : Set (Shape N)) : Submodule F (GrpAlg F N) := ⨆ lam ∈ S, Y.block lam

/-- `A = ⊕_{ℓ(λ) ≤ n} I_λ` (paper line 261). -/
def rowSum (n : ℕ) : Submodule F (GrpAlg F N) := Y.blockSum {lam | lam.numRows ≤ n}

/-- `A' = ⊕_{λ_1 ≤ n} I_λ` (paper line 261). -/
def colSum (n : ℕ) : Submodule F (GrpAlg F N) := Y.blockSum {lam | lam.firstRow ≤ n}

/-- `B_n = B_n^{(N)} = ⊕_{λ ⊆ (n^n)} I_λ` (paper line 262). -/
def boxSum (n : ℕ) : Submodule F (GrpAlg F N) := Y.blockSum {lam | lam.InBox n}

end YoungSystem

end NagataHigman

end
