/-
NagataHigman/Defs/CentralIdempotent.lean — the central idempotent `e_λ` of `F[S_N]` (paper line 235), built from the
Jucys–Murphy elements alone, with no Young system:
  e_λ = Σ_{T ∈ SYT(λ)} Π_k Π_{c ∈ (-N, N), c ≠ c_T(k)} (J_k - c)/(c_T(k) - c).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

The inner product over `c` is Mathlib's Lagrange basis polynomial `Lagrange.basis (contentRange N) (↑) x` (nodes
`c ∈ (-N, N)`, value 1 at `x`, 0 at the other nodes), evaluated at `J_k`; the product over `k` is taken in the order
`0, …, N-1` (the `J_k` commute, so the order does not matter). Facts (Proofs/CentralIdempotent.lean): for every Young
system `Y`, `ρ_μ(e_λ) = δ_{λμ} · 1`; `e_λ` is a central idempotent; `Y.block λ = F[S_N] · e_λ`.
-/
import NagataHigman.Defs.GroupAlgebra
import NagataHigman.Defs.Young

noncomputable section

namespace NagataHigman

/-- A standard tableau is determined by its cells, a map `Fin N → cells`; so there are finitely many. -/
instance SYT.instFinite {N : ℕ} (lam : Shape N) : Finite (SYT lam) := by
  refine Finite.of_injective (fun T : SYT lam => fun k => (⟨T.pos k, T.pos_mem k⟩ : lam.diagram.cells)) ?_
  intro T T' h
  cases T
  cases T'
  congr
  funext k
  exact congrArg Subtype.val (congrFun h k)

/-- The content range `(-N, N)`: every content of a standard tableau of a shape of `N` lies in it. -/
def contentRange (N : ℕ) : Finset ℤ := Finset.Ioo (-(N : ℤ)) N

variable (F : Type*) [Field F]

/-- `Π_{c ∈ (-N, N), c ≠ x} (J_k - c)/(x - c)`: the Lagrange basis polynomial of the nodes `(-N, N)` at `x`,
evaluated at `J_k`. -/
def jmFactor {N : ℕ} (k : Fin N) (x : ℤ) : GrpAlg F N :=
  Polynomial.aeval (jucysMurphy F k) (Lagrange.basis (contentRange N) (fun c : ℤ => (c : F)) x)

/-- `e_λ = Σ_{T ∈ SYT(λ)} Π_k Π_{c ≠ c_T(k)} (J_k - c)/(c_T(k) - c)` (paper line 235's `e_λ`). -/
def youngIdem {N : ℕ} (lam : Shape N) : GrpAlg F N :=
  letI := Fintype.ofFinite (SYT lam)
  ∑ T : SYT lam, ((List.finRange N).map fun k => jmFactor F k (T.content k)).prod

end NagataHigman

end
