/-
NagataHigman/Proofs/SignTwist.lean — the sign twist ε (paper (F7), line 250-252) and the Section 1.4 Method claim.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route: ε is `MonoidAlgebra.lift` of the monoid hom `σ ↦ sgn(σ) σ` (`signTwist_eq_lift`), hence an algebra map;
`ρ_μ(ε a) = 0 ↔ ρ_{μ'}(a) = 0` comes from the intertwiner Γ of the Young system's `signTwist` field.
Everything is for an ARBITRARY Young system `Y`. Imports: Mathlib + Defs + Proofs.BlocksOrth only.
-/
import NagataHigman.Proofs.BlocksOrth

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman Equiv Finset Matrix

variable {F : Type*} [Field F] {N : ℕ}

/-! ### ε as an algebra map -/

/-- `σ ↦ sgn(σ) σ` as a monoid hom `S_N → F[S_N]`. -/
def sgnPerm (F : Type*) [Field F] (N : ℕ) : Perm (Fin N) →* GrpAlg F N where
  toFun σ := ((Perm.sign σ : ℤ) : F) • perm F σ
  map_one' := by simp [perm_one]
  map_mul' σ τ := by
    rw [smul_mul_smul_comm, ← perm_mul, map_mul, Units.val_mul, Int.cast_mul]

lemma sgnPerm_apply (σ : Perm (Fin N)) : sgnPerm F N σ = ((Perm.sign σ : ℤ) : F) • perm F σ := rfl

lemma lift_sgnPerm_perm (σ : Perm (Fin N)) :
    MonoidAlgebra.lift F (GrpAlg F N) (Perm (Fin N)) (sgnPerm F N) (perm F σ) = sgnPerm F N σ := by
  rw [perm, MonoidAlgebra.lift_single, one_smul]

lemma coeff_signTwist (a : GrpAlg F N) (τ : Perm (Fin N)) :
    (signTwist F a).coeff τ = ((Perm.sign τ : ℤ) : F) * a.coeff τ := by
  unfold signTwist
  exact coeff_sum_smul_perm _ τ

/-- ε is the linear extension of `σ ↦ sgn(σ) σ`. -/
lemma signTwist_eq_lift (a : GrpAlg F N) :
    signTwist F a = MonoidAlgebra.lift F (GrpAlg F N) (Perm (Fin N)) (sgnPerm F N) a := by
  conv_rhs => rw [← sum_coeff_smul_perm a]
  rw [map_sum]
  unfold signTwist
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_smul, lift_sgnPerm_perm, sgnPerm_apply, smul_smul, mul_comm]

lemma signTwist_perm (σ : Perm (Fin N)) : signTwist F (perm F σ) = ((Perm.sign σ : ℤ) : F) • perm F σ := by
  rw [signTwist_eq_lift, lift_sgnPerm_perm, sgnPerm_apply]

lemma signTwist_add (a b : GrpAlg F N) : signTwist F (a + b) = signTwist F a + signTwist F b := by
  simp only [signTwist_eq_lift, map_add]

lemma signTwist_smul (r : F) (a : GrpAlg F N) : signTwist F (r • a) = r • signTwist F a := by
  simp only [signTwist_eq_lift, map_smul]

lemma signTwist_zero : signTwist F (0 : GrpAlg F N) = 0 := by
  simp only [signTwist_eq_lift, map_zero]

/-- **(F7)** (line 250): ε is multiplicative. -/
theorem signTwist_mul (a b : GrpAlg F N) : signTwist F (a * b) = signTwist F a * signTwist F b := by
  simp only [signTwist_eq_lift, map_mul]

lemma sign_mul_sign (σ : Perm (Fin N)) : ((Perm.sign σ : ℤ) : F) * ((Perm.sign σ : ℤ) : F) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/-- **(F7)** (line 250): ε is an involution. -/
theorem signTwist_involutive (a : GrpAlg F N) : signTwist F (signTwist F a) = a := by
  apply MonoidAlgebra.ext
  ext τ
  rw [coeff_signTwist, coeff_signTwist, ← mul_assoc, sign_mul_sign, one_mul]

/-- ε preserves the coefficient pairing. -/
theorem coeffPairing_signTwist (a b : GrpAlg F N) :
    coeffPairing F (signTwist F a) (signTwist F b) = coeffPairing F a b := by
  unfold coeffPairing
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coeff_signTwist, coeff_signTwist]
  linear_combination (a.coeff σ * b.coeff σ) * sign_mul_sign (F := F) σ

/-- **(F7)** (lines 251-252): on `C_N`, ε is the scalar `(-1)^{N-1}`. -/
theorem signTwist_of_mem_cycleSpan {c : GrpAlg F N} (hc : c ∈ cycleSpan F N) :
    signTwist F c = ((-1 : F) ^ (N - 1)) • c := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    rw [signTwist_perm]
    congr 1
    have hs := hσ.1.sign
    rw [hσ.2, Finset.card_univ, Fintype.card_fin] at hs
    rw [hs]
    rcases N with _ | M
    · exact absurd (Subsingleton.elim σ 1) hσ.1.ne_one
    · push_cast
      rw [pow_succ]
      simp
  | zero => rw [signTwist_zero, smul_zero]
  | add x y _ _ hx hy => rw [signTwist_add, hx, hy, smul_add]
  | smul r x _ hx => rw [signTwist_smul, hx, smul_comm]

namespace YoungSystem

variable (Y : YoungSystem F N)

lemma rhoAlg_signTwist (mu : Shape N) (a : GrpAlg F N) :
    Y.rhoAlg mu (signTwist F a) = ∑ σ, (((Perm.sign σ : ℤ) : F) * a.coeff σ) • Y.rho mu σ := by
  rw [rhoAlg_eq_sum Y]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coeff_signTwist]

/-- `ρ_μ(ε a) = 0 ↔ ρ_{μ'}(a) = 0`, from the intertwiner `S^{μ'} ≅ S^μ ⊗ sgn` (paper (F7), line 251). -/
theorem rhoAlg_signTwist_eq_zero_iff (mu : Shape N) (a : GrpAlg F N) :
    Y.rhoAlg mu (signTwist F a) = 0 ↔ Y.rhoAlg mu.conjugate a = 0 := by
  obtain ⟨Γ, hΓ⟩ := Y.signTwist mu
  have key : ∀ v, Γ (Y.rhoAlg mu.conjugate a *ᵥ v) = Y.rhoAlg mu (signTwist F a) *ᵥ Γ v := by
    intro v
    rw [rhoAlg_eq_sum Y mu.conjugate a, rhoAlg_signTwist, Matrix.sum_mulVec, Matrix.sum_mulVec, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Matrix.smul_mulVec, map_smul, hΓ σ v, Matrix.smul_mulVec, smul_smul, mul_comm]
  constructor
  · intro h
    apply Matrix.ext_of_mulVec_single
    intro i
    apply Γ.injective
    rw [key, h, Matrix.zero_mulVec, Matrix.zero_mulVec, map_zero]
  · intro h
    apply Matrix.ext_of_mulVec_single
    intro i
    obtain ⟨v, hv⟩ := Γ.surjective (Pi.single i 1)
    rw [← hv, ← key, h, Matrix.zero_mulVec, map_zero, Matrix.zero_mulVec]

/-- **(F7)** (line 251): `ε(I_λ) = I_{λ'}`. -/
theorem mem_block_iff_signTwist (lam : Shape N) (a : GrpAlg F N) :
    a ∈ Y.block lam ↔ signTwist F a ∈ Y.block lam.conjugate := by
  rw [mem_block_iff Y, mem_block_iff Y]
  constructor
  · intro h mu hmu
    rw [rhoAlg_signTwist_eq_zero_iff]
    apply h
    intro heq
    apply hmu
    rw [← heq, Nat.Partition.conjugate_conjugate]
  · intro h mu hmu
    have hne : mu.conjugate ≠ lam.conjugate := by
      intro heq
      apply hmu
      have h2 := congrArg Nat.Partition.conjugate heq
      rwa [Nat.Partition.conjugate_conjugate, Nat.Partition.conjugate_conjugate] at h2
    have h3 := h mu.conjugate hne
    rwa [rhoAlg_signTwist_eq_zero_iff, Nat.Partition.conjugate_conjugate] at h3

/-- An element in two different blocks is zero. -/
lemma eq_zero_of_mem_block_of_mem_block {lam mu : Shape N} (hne : lam ≠ mu) {a : GrpAlg F N}
    (ha : a ∈ Y.block lam) (hb : a ∈ Y.block mu) : a = 0 := by
  apply eq_zero_of_forall_rhoAlg Y
  intro nu
  by_cases hnu : nu = lam
  · subst hnu
    exact (mem_block_iff Y).1 hb nu hne
  · exact (mem_block_iff Y).1 ha nu hnu

/-- **Section 1.4, Method** (v1.02 lines 146-147): `C_N ∩ I_λ = 0` unless `λ = λ'`. -/
theorem cycleSpan_inf_block_eq_bot (lam : Shape N) (h : lam.conjugate ≠ lam) :
    cycleSpan F N ⊓ Y.block lam = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Submodule.mem_inf] at hc
  rw [Submodule.mem_bot]
  have h1 := (mem_block_iff_signTwist Y lam c).1 hc.2
  rw [signTwist_of_mem_cycleSpan hc.1] at h1
  have hs : ((-1 : F) ^ (N - 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have h2 : c ∈ Y.block lam.conjugate := by
    have h3 := Submodule.smul_mem _ ((-1 : F) ^ (N - 1))⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at h3
  exact eq_zero_of_mem_block_of_mem_block Y (Ne.symm h) hc.2 h2

end YoungSystem

end NagataHigman.Proofs

end
