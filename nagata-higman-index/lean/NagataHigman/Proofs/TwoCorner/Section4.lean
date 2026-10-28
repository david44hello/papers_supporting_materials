/-
NagataHigman/Proofs/TwoCorner/Section4.lean — Section 4 on ν for an arbitrary Young system: Lemma 4.1 with every
hypothesis discharged (tex 524-546), and Lemma 4.3.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Proofs.TwoCorner.Lemma41
import NagataHigman.Proofs.TwoCorner.Lemma42
import NagataHigman.Proofs.Restriction

noncomputable section

namespace NagataHigman.Proofs

open Equiv Finset Matrix NagataHigman

variable {F : Type*} [Field F] [CharZero F]

/-- `f^λ ≠ 0` in `F`: a Young basis is indexed by the standard tableaux, and there is at least one. -/
theorem dim_ne_zero {N : ℕ} (Y : YoungSystem F N) (lam : Shape N) : (Y.dim lam : F) ≠ 0 := by
  obtain ⟨b, -⟩ := Y.youngBasis lam
  obtain ⟨T⟩ := syt_nonempty lam
  intro h
  have h0 : Y.dim lam = 0 := by exact_mod_cast h
  apply b.ne_zero T
  funext i
  have := i.isLt
  omega

omit [CharZero F] in
/-- On `ν`, `Y_top² = 1`: the top entry has content `±1` in every standard tableau (paper v1.02 l. 398). -/
theorem jucysMurphy_top_sq_nu (n : ℕ) (hn : 2 ≤ n) (Y : YoungSystem F (n ^ 2 - 1)) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.InBox n) (top : Fin (n ^ 2 - 1)) (htop : (top : ℕ) + 1 = n ^ 2 - 1) :
    Y.rhoAlg lam (jucysMurphy F top) * Y.rhoAlg lam (jucysMurphy F top) = 1 := by
  have hparts := sec_4_1_nu_proved n hn lam hlam
  obtain ⟨b, hb⟩ := Y.youngBasis lam
  apply matrix_eq_of_basis Y b
  intro T
  have hbT : Y.rhoAlg lam (jucysMurphy F top) *ᵥ b T = ((T.content top : ℤ) : F) • b T := hb T top
  rw [← Matrix.mulVec_mulVec, hbT, Matrix.mulVec_smul, hbT, smul_smul, Matrix.one_mulVec]
  rcases nu_content_top n hn lam hparts T top htop with h | h <;> rw [h] <;> norm_num

/-- **Lemma 4.1** on `ν` (tex 524-546), every hypothesis of `lem_4_1_general` discharged. -/
theorem lem_4_1_nu (n : ℕ) (hn : 2 ≤ n) (Y : YoungSystem F (n ^ 2 - 1)) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.InBox n) {f : GrpAlg F (n ^ 2 - 1)} (hf : f ∈ Y.block lam) :
    (∀ σ : Perm (Fin (n ^ 2 - 1)), (∃ j, σ j = j) → f.coeff σ = 0) ↔
      ∀ j : Fin (n ^ 2 - 1), Y.rhoAlg lam f * Y.rhoAlg lam (starElem F j) =
        -(Y.rhoAlg lam (starElem F j) * Y.rhoAlg lam f) := by
  have h4 : 4 ≤ n ^ 2 := by nlinarith
  let top : Fin (n ^ 2 - 1) := ⟨n ^ 2 - 2, by omega⟩
  have htop : (top : ℕ) + 1 = n ^ 2 - 1 := by simp only [top]; omega
  exact lem_4_1_general Y lam top htop (jucysMurphy_top_sq_nu n hn Y lam hlam top htop)
    (restriction_of_young Y lam top htop) (dim_ne_zero Y lam) (fun g j => perm_conj_starElem F g j)
    (starElem_top F top htop) hf

end NagataHigman.Proofs
