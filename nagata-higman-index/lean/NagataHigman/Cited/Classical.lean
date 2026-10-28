/-
NagataHigman/Cited/Classical.lean — the paper's cited results on the representations of S_N and A_N (two axioms).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Rule (Dave): results cited from other papers may be assumed; every claim of the paper itself is proved.
Each statement below must be TRUE and NO STRONGER than its source. The docstrings quote the paper's citing sentences
verbatim (paper v1.10).
Exact-arithmetic model checks (Young's seminormal form): every `YoungSystem` clause, N = 0..6, with negative controls,
scripts/modelcheck_youngsystem.py (+ .log); every `AltSplit` clause of `youngSystemC_exists` (irreducible,
non-isomorphic, Frobenius off h(λ)) for all self-conjugate λ with 2 ≤ N ≤ 9, scripts/altsplit_check.py (+ .log).
-/
import NagataHigman.Defs.AlternatingSplit
import NagataHigman.Defs.FreeAlgebra

universe u

noncomputable section

namespace NagataHigman.Cited

/-- **Classical representation theory of `S_N` in characteristic 0**: facts (F2), (T1), (F7) of the paper, packaged as
the existence of a `YoungSystem` (`NagataHigman/Defs/YoungSystem.lean`; its header gives the source of each clause).
The witness is the family of Specht modules in Young's seminormal form (rational matrices, so every char-0 field works).
The paper cites them as follows (verbatim, v1.10):
* (F2) "\emph{Wedderburn decomposition} \cite[Thm.~4.12]{Ja78}, \cite[Ch.~1]{CST10}. ... We have
  $F[S_N]=\bigoplus_{\lambda\vdash N}I_\lambda$ with $I_\lambda=F[S_N]e_\lambda$, where
  $e_\lambda=(\dim S^\lambda/N!)\sum_\sigma\chi_\lambda(\sigma)\sigma$ is a central primitive idempotent, and
  $\rho_\lambda$ restricts to an isomorphism $I_\lambda\cong\End(S^\lambda)$ ... Fourier inversion reads \[
  f(\sigma)=\sum_\lambda\frac{\dim S^\lambda}{N!}\tr\bigl(\rho_\lambda(\sigma^{-1})\rho_\lambda(f)\bigr). \]"
  (lines 257-265) [Ja78 Thm 4.12; CST10 Ch. 1]
* (T1) "In the Young (Gelfand--Tsetlin) basis $\{v_T\}$, $\rho(J_k)v_T=c_T(k)v_T$ \cite{Ju74,Mu81,OV96}" (lines 465-466),
  where "The \emph{Young basis} $\{v_T\}$ of $S^\lambda$ is defined, up to nonzero scalars, by following $T$ down the
  chain $S_N\supset S_{N-1}\supset\dots\supset S_1$ \cite{OV96}, \cite[\S3.2]{CST10}: ... the last of these submodules is a
  line, and $v_T$ spans it." (lines 457-461). Lean's `youngBasis` clause asks only for a basis indexed by the standard
  tableaux with these Jucys–Murphy eigenvalues; the branching description is not assumed (route item 1).
* (F7) "$\varepsilon(\sigma):=\sgn(\sigma)\sigma$, extends to an algebra automorphism of $F[S_N]$ with
  $\varepsilon(I_\lambda)=I_{\lambda'}$, since $S^\lambda\otimes\sgn\cong S^{\lambda'}$" (lines 287-288) and (T3)
  "Let $\lambda=\lambda'$ with $N\ge2$. Then, by (F7), $S^\lambda\otimes\sgn\cong S^\lambda$" (lines 479-480)
  [Ja78 Thm 6.7, with
  self-duality Thm 4.12]. -/
axiom youngSystem_exists (F : Type u) [Field F] [CharZero F] (N : ℕ) : Nonempty (YoungSystem F N)

/-- A fixed Young system for `S_N` over `F` (chosen once). Paper/Statements.lean states every claim on S_N
representations for an ARBITRARY Young system, so no claim depends on this choice. -/
def youngSystem (F : Type u) [Field F] [CharZero F] (N : ℕ) : YoungSystem F N :=
  Classical.choice (youngSystem_exists F N)

/-- **Frobenius' theorem on the characters of `A_N`, over ℂ** [JK81, §2.5 and Thm 2.5.13]: there is a Young system over
ℂ in which, for every self-conjugate `λ` with `N ≥ 2`, `Res_{A_N} S^λ = V₊ ⊕ V₋` with `V±` irreducible and
non-isomorphic, and `χ₊(σ) = χ₋(σ)` unless `σ` has cycle type `h(λ)` (`NagataHigman/Defs/AlternatingSplit.lean`).
Paper (verbatim, v1.10; its `U±` are Lean's `V±`): "the restriction of $S^\lambda$ to $A_N$ is the sum
$U_+\oplus U_-$ of two non-isomorphic irreducible modules, with characters $\chi_\pm$ \cite[\S2.5]{JK81}" (lines
482-484) and "\emph{Frobenius' theorem} \cite{Fr01},
\cite[Thm.~2.5.13]{JK81} says that $\chi_+(\sigma)=\chi_-(\sigma)$ unless $\sigma$ has cycle type $h(\lambda)$."
(lines 495-496). Only the "unless" (equality) half is assumed, not the values on the class `h(λ)`. The witness is
Young's seminormal form over ℂ with `V±` its two `A_N`-constituents. Everything else in the paper's (T3) paragraph
(lines 479-497) is proved in NagataHigman/Proofs/TwoCorner/GammaC.lean and Proofs/DiagonalHooks.lean; the field step
(lines 445-446 and 607-608, "by (F1)") is the claim `F1_field`, PROVED in NagataHigman/Proofs/FieldIndep.lean with no
Young system at all; `thm_B` uses it to pass from ℂ to `F`. -/
axiom youngSystemC_exists (N : ℕ) : ∃ Y : YoungSystem ℂ N, AlternatingSplit Y

/-- The Young system over ℂ used for Section 4 (paper: "from now on we take $F=\mathbb{C}$", line 446). -/
def youngSystemC (N : ℕ) : YoungSystem ℂ N := Classical.choose (youngSystemC_exists N)

theorem youngSystemC_split (N : ℕ) : AlternatingSplit (youngSystemC N) :=
  Classical.choose_spec (youngSystemC_exists N)

end NagataHigman.Cited

end
