/-
NagataHigman/Proofs/Blocks.lean — the block layer of F[S_N]: what follows from a Young system's Wedderburn, Fourier
and sign-twist fields (paper (F2), (F3), (F7), Section 1.4 Method).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Everything is proved for an ARBITRARY Young system `Y : YoungSystem F N`; Statements instantiates the cited one.
Imports: Mathlib + NagataHigman.Defs only (not Cited, not Statements).
-/
import Mathlib
import NagataHigman.Defs.YoungSystem

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman Equiv Finset Matrix

variable {F : Type*} [Field F] {N : ℕ}

/-! ### Group algebra basics -/

lemma coeff_perm (σ τ : Perm (Fin N)) : (perm F σ).coeff τ = if σ = τ then 1 else 0 := by
  simp [perm, MonoidAlgebra.coeff_single, Finsupp.single_apply]

lemma coeff_sum_smul_perm (c : Perm (Fin N) → F) (τ : Perm (Fin N)) :
    (∑ σ, c σ • perm F σ).coeff τ = c τ := by
  simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, coeff_perm, Finsupp.finsetSum_apply]

lemma sum_coeff_smul_perm (a : GrpAlg F N) : ∑ σ, a.coeff σ • perm F σ = a :=
  MonoidAlgebra.ext (Finsupp.ext fun τ => coeff_sum_smul_perm _ τ)

lemma perm_mul (σ τ : Perm (Fin N)) : perm F (σ * τ) = perm F σ * perm F τ := by
  simp [perm, MonoidAlgebra.single_mul_single]

lemma perm_one : perm F (1 : Perm (Fin N)) = 1 := by
  simp [perm, MonoidAlgebra.one_def]

/-- `⟨a, σ⟩ = a(σ)`. -/
lemma coeffPairing_perm (a : GrpAlg F N) (σ : Perm (Fin N)) : coeffPairing F a (perm F σ) = a.coeff σ := by
  simp [coeffPairing, coeff_perm]

/-- **(F3)**, nondegeneracy (paper line 243): `⟨a, b⟩ = 0` for all `b` forces `a = 0`. -/
theorem coeffPairing_nondegenerate (a : GrpAlg F N) (h : ∀ b : GrpAlg F N, coeffPairing F a b = 0) : a = 0 := by
  apply MonoidAlgebra.ext
  ext σ
  rw [← coeffPairing_perm a σ, h]
  simp [MonoidAlgebra.coeff_zero]

namespace YoungSystem

variable (Y : YoungSystem F N)

/-! ### Wedderburn: injectivity and surjectivity of `(ρ_λ)_λ` -/

lemma rhoAlg_perm (lam : Shape N) (σ : Perm (Fin N)) : Y.rhoAlg lam (perm F σ) = Y.rho lam σ := by
  simp [NagataHigman.YoungSystem.rhoAlg, perm, MonoidAlgebra.lift_single]

lemma rhoAlg_eq_sum (lam : Shape N) (a : GrpAlg F N) : Y.rhoAlg lam a = ∑ σ, a.coeff σ • Y.rho lam σ := by
  conv_lhs => rw [← sum_coeff_smul_perm a]
  simp [map_sum, map_smul, rhoAlg_perm]

lemma eq_zero_of_forall_rhoAlg (a : GrpAlg F N) (h : ∀ lam, Y.rhoAlg lam a = 0) : a = 0 := by
  apply Y.wedderburn.1
  funext lam
  show Y.rhoAlg lam a = Y.rhoAlg lam 0
  rw [h lam, map_zero]

lemma ext_of_rhoAlg (a b : GrpAlg F N) (h : ∀ lam, Y.rhoAlg lam a = Y.rhoAlg lam b) : a = b :=
  sub_eq_zero.mp ((eq_zero_of_forall_rhoAlg Y) (a - b) fun lam => by rw [map_sub, h, sub_self])

lemma exists_rhoAlg (M : (lam : Shape N) → Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) :
    ∃ a : GrpAlg F N, ∀ lam, Y.rhoAlg lam a = M lam := by
  obtain ⟨a, ha⟩ := Y.wedderburn.2 M
  exact ⟨a, fun lam => congrFun ha lam⟩

/-! ### C1-C5 -/

/-- C1: `a ∈ I_λ` iff every other `ρ_μ` kills `a`. -/
lemma mem_block_iff {lam : Shape N} {a : GrpAlg F N} :
    a ∈ Y.block lam ↔ ∀ mu, mu ≠ lam → Y.rhoAlg mu a = 0 := by
  simp [NagataHigman.YoungSystem.block, Submodule.mem_iInf, LinearMap.mem_ker]

/-- C4: every matrix is `ρ_λ` of an element of the block `I_λ`. -/
lemma exists_mem_block (lam : Shape N) (M : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) :
    ∃ a ∈ Y.block lam, Y.rhoAlg lam a = M := by
  obtain ⟨a, ha⟩ := (exists_rhoAlg Y)
    (Function.update (fun mu => (0 : Matrix (Fin (Y.dim mu)) (Fin (Y.dim mu)) F)) lam M)
  refine ⟨a, (mem_block_iff Y).2 fun mu hmu => ?_, ?_⟩
  · rw [ha mu, Function.update_of_ne hmu]
  · rw [ha lam, Function.update_self]

/-- C4: `ρ_λ` is surjective. -/
lemma rhoAlg_surjective (lam : Shape N) : Function.Surjective (Y.rhoAlg lam) := fun M =>
  let ⟨a, _, h⟩ := (exists_mem_block Y) lam M
  ⟨a, h⟩

/-- C3: `ρ_λ` is injective on `I_λ`. -/
lemma eq_of_mem_block {lam : Shape N} {a b : GrpAlg F N} (ha : a ∈ Y.block lam) (hb : b ∈ Y.block lam)
    (h : Y.rhoAlg lam a = Y.rhoAlg lam b) : a = b := by
  apply (ext_of_rhoAlg Y)
  intro mu
  by_cases hmu : mu = lam
  · subst hmu
    exact h
  · rw [(mem_block_iff Y).1 ha mu hmu, (mem_block_iff Y).1 hb mu hmu]

lemma block_le_blockSum {S : Set (Shape N)} {lam : Shape N} (hlam : lam ∈ S) : Y.block lam ≤ Y.blockSum S := by
  unfold NagataHigman.YoungSystem.blockSum
  exact le_iSup₂ (f := fun lam (_ : lam ∈ S) => Y.block lam) lam hlam

/-- C2: `a ∈ ⊕_{λ ∈ S} I_λ` iff every `ρ_μ`, `μ ∉ S`, kills `a`. -/
lemma mem_blockSum_iff {S : Set (Shape N)} {a : GrpAlg F N} :
    a ∈ Y.blockSum S ↔ ∀ mu, mu ∉ S → Y.rhoAlg mu a = 0 := by
  constructor
  · intro ha mu hmu
    have hle : Y.blockSum S ≤ LinearMap.ker (Y.rhoAlg mu).toLinearMap := by
      apply iSup₂_le
      intro lam hlam b hb
      have hne : mu ≠ lam := fun h => hmu (h ▸ hlam)
      exact (mem_block_iff Y).1 hb mu hne
    exact hle ha
  · intro h
    choose b hb hbρ using fun lam => (exists_mem_block Y) lam (Y.rhoAlg lam a)
    have hsum : a = ∑ lam, b lam := by
      apply (ext_of_rhoAlg Y)
      intro mu
      rw [map_sum, Finset.sum_eq_single mu]
      · exact (hbρ mu).symm
      · intro lam _ hne
        exact (mem_block_iff Y).1 (hb lam) mu (Ne.symm hne)
      · intro hmu
        exact absurd (Finset.mem_univ mu) hmu
    rw [hsum]
    apply Submodule.sum_mem
    intro lam _
    by_cases hlam : lam ∈ S
    · exact (block_le_blockSum Y) hlam (hb lam)
    · have hzero : b lam = 0 := by
        apply (eq_zero_of_forall_rhoAlg Y)
        intro mu
        by_cases hmu : mu = lam
        · subst hmu
          rw [hbρ, h _ hlam]
        · exact (mem_block_iff Y).1 (hb lam) mu hmu
      rw [hzero]
      exact Submodule.zero_mem _

/-- C5: Fourier inversion on one block. -/
lemma coeff_of_mem_block {lam : Shape N} {a : GrpAlg F N} (ha : a ∈ Y.block lam) (σ : Perm (Fin N)) :
    a.coeff σ = ((Y.dim lam : F) / (N.factorial : F)) * trace (Y.rho lam σ⁻¹ * Y.rhoAlg lam a) := by
  rw [Y.fourier a σ, Finset.sum_eq_single lam]
  · rfl
  · intro mu _ hmu
    change _ * trace (_ * Y.rhoAlg mu a) = 0
    rw [(mem_block_iff Y).1 ha mu hmu, mul_zero, trace_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ lam) h

/-- C5: the coefficient of the identity, `a(1) = ∑_λ (f^λ / N!) tr ρ_λ(a)`. -/
lemma coeff_one_eq (a : GrpAlg F N) :
    a.coeff 1 = ∑ lam, ((Y.dim lam : F) / (N.factorial : F)) * trace (Y.rhoAlg lam a) := by
  rw [Y.fourier a 1]
  simp only [inv_one, map_one, one_mul]
  rfl

end YoungSystem

end NagataHigman.Proofs

end
