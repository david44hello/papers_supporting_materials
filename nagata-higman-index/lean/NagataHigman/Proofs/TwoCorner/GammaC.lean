/- NagataHigman/Proofs/TwoCorner/GammaC.lean — the (T3) paragraph over ℂ (tex v1.02 lines 368-385): ψ = tr(ρ(·)Γ) is supported exactly on cycle type h(λ).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib
import NagataHigman.Defs.AlternatingSplit
import NagataHigman.Proofs.TwoCorner.Gamma
import NagataHigman.Proofs.Shapes

noncomputable section

namespace NagataHigman.Proofs

open Equiv Matrix NagataHigman

section General

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A projection along a complement commutes with any map preserving both summands. -/
theorem projection_map_comm {p q : Submodule K V} (hpq : IsCompl p q) (f : V →ₗ[K] V)
    (hp : ∀ v ∈ p, f v ∈ p) (hq : ∀ v ∈ q, f v ∈ q) (x : V) :
    p.projection q hpq (f x) = f (p.projection q hpq x) := by
  have hx := Submodule.projection_add_projection_eq_self hpq x
  conv_lhs => rw [← hx]
  rw [map_add, map_add,
    Submodule.projection_apply_of_mem_left hpq (hp _ (Submodule.projection_apply_mem hpq x)),
    (Submodule.projection_apply_eq_zero_iff hpq).2 (hq _ (Submodule.projection_apply_mem hpq.symm x)),
    add_zero]

/-- The trace over a complementary pair of invariant subspaces is the sum of the two traces. -/
theorem trace_eq_add_of_isCompl [FiniteDimensional K V] {p q : Submodule K V} (hpq : IsCompl p q)
    (f : V →ₗ[K] V) (hp : ∀ v ∈ p, f v ∈ p) (hq : ∀ v ∈ q, f v ∈ q) :
    LinearMap.trace K V f = LinearMap.trace K p (f.restrict hp) + LinearMap.trace K q (f.restrict hq) := by
  let A : Bool → Submodule K V := fun b => cond b p q
  have hA : DirectSum.IsInternal A :=
    (DirectSum.isInternal_submodule_iff_isCompl A (i := true) (j := false) (by decide)
      (by ext b; cases b <;> simp)).2 hpq
  have hf : ∀ b, Set.MapsTo f (A b) (A b) := fun b => by cases b; exacts [hq, hp]
  rw [LinearMap.trace_eq_sum_trace_restrict hA hf, Fintype.sum_bool]
  rfl

end General

variable {N : ℕ} (Y : YoungSystem ℂ N) {lam : Shape N}

/-- An invertible matrix sends a nonzero vector to a nonzero vector. -/
theorem mulVec_ne_zero_of_isUnit {n : ℕ} {Γ : Matrix (Fin n) (Fin n) ℂ} (hΓu : IsUnit Γ) {v : Fin n → ℂ}
    (hv : v ≠ 0) : Γ *ᵥ v ≠ 0 := by
  obtain ⟨u, rfl⟩ := hΓu
  intro h0
  apply hv
  rw [← one_mulVec v, ← u.inv_mul, ← mulVec_mulVec, h0, mulVec_zero]

/-- **Step 1a**: `Γ` commutes with `ρ(σ)` for even `σ`. -/
theorem gamma_altEquivariant (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ)
    (hΓ : ∀ σ : Perm (Fin N), Γ * Y.rho lam σ = ((Perm.sign σ : ℤ) : ℂ) • (Y.rho lam σ * Γ)) :
    IsAltEquivariant Y lam Γ := fun σ hσ => by
  rw [hΓ σ, hσ]
  simp

/-- **Step 1b** (one constituent): an `A_N`-equivariant `Γ` maps `p` into `p`, when `p ⊕ q = S^λ` are invariant
and every `A_N`-map `p → q` (killing `q`) is zero. -/
theorem mapsTo_of_noniso (p q : Submodule ℂ (Fin (Y.dim lam) → ℂ)) (hpq : IsCompl p q)
    (hp : IsAltInvariant Y lam p) (hq : IsAltInvariant Y lam q)
    (hnon : ∀ Φ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ, IsAltEquivariant Y lam Φ →
      (∀ v ∈ q, Φ *ᵥ v = 0) → (∀ v ∈ p, Φ *ᵥ v ∈ q) → Φ = 0)
    (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ) (hΓ : IsAltEquivariant Y lam Γ) :
    ∀ v ∈ p, Γ *ᵥ v ∈ p := by
  set Pp := p.projection q hpq
  set Pq := q.projection p hpq.symm
  set Φ := LinearMap.toMatrix' (Pq ∘ₗ Matrix.mulVecLin Γ ∘ₗ Pp) with hΦdef
  have hΦ : ∀ v, Φ *ᵥ v = Pq (Γ *ᵥ Pp v) := fun v => by
    rw [hΦdef, LinearMap.toMatrix'_mulVec]
    rfl
  have hcomm : ∀ σ : Perm (Fin N), Perm.sign σ = 1 → ∀ v,
      Pp (Y.rho lam σ *ᵥ v) = Y.rho lam σ *ᵥ Pp v ∧ Pq (Y.rho lam σ *ᵥ v) = Y.rho lam σ *ᵥ Pq v :=
    fun σ hσ v => ⟨projection_map_comm hpq (Matrix.mulVecLin (Y.rho lam σ)) (hp σ hσ) (hq σ hσ) v,
      projection_map_comm hpq.symm (Matrix.mulVecLin (Y.rho lam σ)) (hq σ hσ) (hp σ hσ) v⟩
  have hequiv : IsAltEquivariant Y lam Φ := fun σ hσ => by
    refine ext_iff_mulVec.2 fun v => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, hΦ, hΦ, (hcomm σ hσ v).1, mulVec_mulVec, hΓ σ hσ,
      ← mulVec_mulVec, (hcomm σ hσ _).2]
  have hzero := hnon Φ hequiv
    (fun v hv => by rw [hΦ, (Submodule.projection_apply_eq_zero_iff hpq).2 hv, mulVec_zero, map_zero])
    (fun v _ => by rw [hΦ]; exact Submodule.projection_apply_mem hpq.symm _)
  intro v hv
  have h0 : Pq (Γ *ᵥ v) = 0 := by
    rw [← Submodule.projection_apply_of_mem_left hpq hv, ← hΦ, hzero, zero_mulVec]
  exact (Submodule.projection_apply_eq_zero_iff hpq.symm).1 h0

/-- **Step 2** (Schur over ℂ): an `A_N`-equivariant `Γ` preserving an irreducible constituent `p` is a scalar on it. -/
theorem eq_smul_on_of_irred (p : Submodule ℂ (Fin (Y.dim lam) → ℂ)) (hp : IsAltInvariant Y lam p) (hne : p ≠ ⊥)
    (hirr : ∀ W : Submodule ℂ (Fin (Y.dim lam) → ℂ), W ≤ p → IsAltInvariant Y lam W → W = ⊥ ∨ W = p)
    (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ) (hΓ : IsAltEquivariant Y lam Γ)
    (hΓp : ∀ v ∈ p, Γ *ᵥ v ∈ p) : ∃ a : ℂ, ∀ v ∈ p, Γ *ᵥ v = a • v := by
  have : Nontrivial p := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue ((Matrix.mulVecLin Γ).restrict hΓp)
  obtain ⟨x, hx⟩ := ha.exists_hasEigenvector
  refine ⟨a, ?_⟩
  set W := p ⊓ Module.End.eigenspace (Matrix.mulVecLin Γ) a
  have hxW : (x : Fin (Y.dim lam) → ℂ) ∈ W := by
    exact ⟨x.2, Module.End.mem_eigenspace_iff.2 (congrArg Subtype.val hx.apply_eq_smul)⟩
  have hWinv : IsAltInvariant Y lam W := fun σ hσ v hv => by
    refine ⟨hp σ hσ v hv.1, Module.End.mem_eigenspace_iff.2 ?_⟩
    have hv2 : Γ *ᵥ v = a • v := Module.End.mem_eigenspace_iff.1 hv.2
    simp only [Matrix.mulVecLin_apply]
    rw [mulVec_mulVec, hΓ σ hσ, ← mulVec_mulVec, hv2, mulVec_smul]
  have hWne : W ≠ ⊥ := by
    intro hbot
    have : (x : Fin (Y.dim lam) → ℂ) = 0 := by simpa [hbot] using hxW
    exact hx.2 (Subtype.ext this)
  have hWp : W = p := (hirr W inf_le_left hWinv).resolve_left hWne
  intro v hv
  rw [← hWp] at hv
  exact Module.End.mem_eigenspace_iff.1 hv.2

/-- A scalar acting on a nonzero vector is determined by the vector. -/
theorem smul_cancel {n : ℕ} {v : Fin n → ℂ} (hv : v ≠ 0) {a b : ℂ} (h : a • v = b • v) : a = b :=
  smul_left_injective ℂ hv h

/-- **Step 3**: `Γ = a` on `V₊` and `Γ = -a` on `V₋`. -/
theorem gamma_pm (S : AltDecomp Y lam) (hN : 2 ≤ N) (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ)
    (hΓu : IsUnit Γ)
    (hΓ : ∀ σ : Perm (Fin N), Γ * Y.rho lam σ = ((Perm.sign σ : ℤ) : ℂ) • (Y.rho lam σ * Γ)) :
    ∃ a : ℂ, (∀ v ∈ S.Vp, Γ *ᵥ v = a • v) ∧ (∀ v ∈ S.Vm, Γ *ᵥ v = (-a) • v) := by
  have hE := gamma_altEquivariant Y Γ hΓ
  obtain ⟨a, ha⟩ := eq_smul_on_of_irred Y S.Vp S.inv_p S.ne_bot_p S.irred_p Γ hE
    (mapsTo_of_noniso Y S.Vp S.Vm S.compl S.inv_p S.inv_m S.noniso_pm Γ hE)
  obtain ⟨b, hb⟩ := eq_smul_on_of_irred Y S.Vm S.inv_m S.ne_bot_m S.irred_m Γ hE
    (mapsTo_of_noniso Y S.Vm S.Vp S.compl.symm S.inv_m S.inv_p S.noniso_mp Γ hE)
  obtain ⟨vp, hvp, hvp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot S.ne_bot_p
  obtain ⟨vm, hvm, hvm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot S.ne_bot_m
  -- a ≠ b: otherwise Γ = a·1, which cannot anticommute with ρ of a transposition.
  have hab : a ≠ b := by
    intro hab
    subst hab
    have hall : ∀ v, Γ *ᵥ v = a • v := fun v => by
      rw [← Submodule.projection_add_projection_eq_self S.compl v, mulVec_add, smul_add,
        ha _ (Submodule.projection_apply_mem _ _), hb _ (Submodule.projection_apply_mem _ _)]
    set τ : Perm (Fin N) := swap ⟨0, by omega⟩ ⟨1, by omega⟩
    have hτ : Perm.sign τ = -1 := Perm.sign_swap (by simp [Fin.ext_iff])
    have hττ : Y.rho lam τ * Y.rho lam τ = 1 := by rw [← map_mul, Equiv.swap_mul_self, map_one]
    have key : a • vp = -(a • vp) := by
      have h1 := congrArg (· *ᵥ (Y.rho lam τ *ᵥ vp)) (hΓ τ)
      simp only [hτ, ← mulVec_mulVec, smul_mulVec, hall] at h1
      rw [mulVec_smul, mulVec_mulVec, hττ, one_mulVec] at h1
      simpa using h1
    have hne : a • vp ≠ 0 := by rw [← hall]; exact mulVec_ne_zero_of_isUnit hΓu hvp0
    apply hne
    have h2 : (2 : ℂ) • (a • vp) = 0 := by
      rw [two_smul]
      nth_rw 2 [key]
      exact add_neg_cancel _
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  -- a² = b² = c (Γ² = c·1), hence b = -a.
  obtain ⟨c, -, hc⟩ := gamma_sq_scalar Y lam Γ hΓu hΓ
  have hsq : ∀ (d : ℂ) (v : Fin (Y.dim lam) → ℂ), v ≠ 0 → Γ *ᵥ v = d • v → d * d = c := fun d v hv hd => by
    apply smul_cancel hv
    have := congrArg (· *ᵥ v) hc
    simp only [← mulVec_mulVec, hd, mulVec_smul, smul_mulVec, one_mulVec, smul_smul] at this
    exact this
  have haa := hsq a vp hvp0 (ha vp hvp)
  have hbb := hsq b vm hvm0 (hb vm hvm)
  have hba : b = -a := by
    have hprod : (a - b) * (a + b) = 0 := by linear_combination haa - hbb
    rcases mul_eq_zero.1 hprod with h0 | h0
    · exact absurd (sub_eq_zero.1 h0) hab
    · linear_combination h0
  exact ⟨a, ha, fun v hv => by rw [hb v hv, hba]⟩

/-- **Step 4a**: for even `σ`, `ψ(σ) = a·(χ₊(σ) − χ₋(σ))`. -/
theorem trace_even_eq (S : AltDecomp Y lam) (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ) (a : ℂ)
    (hp : ∀ v ∈ S.Vp, Γ *ᵥ v = a • v) (hm : ∀ v ∈ S.Vm, Γ *ᵥ v = (-a) • v)
    (σ : Perm (Fin N)) (hσ : Perm.sign σ = 1) :
    trace (Y.rho lam σ * Γ) =
      a * (LinearMap.trace ℂ S.Vp ((Matrix.mulVecLin (Y.rho lam σ)).restrict (S.inv_p σ hσ)) -
        LinearMap.trace ℂ S.Vm ((Matrix.mulVecLin (Y.rho lam σ)).restrict (S.inv_m σ hσ))) := by
  have hp' : ∀ v ∈ S.Vp, Matrix.mulVecLin (Y.rho lam σ * Γ) v ∈ S.Vp := fun v hv => by
    rw [Matrix.mulVecLin_apply, ← mulVec_mulVec, hp v hv, mulVec_smul]
    exact S.Vp.smul_mem _ (S.inv_p σ hσ v hv)
  have hm' : ∀ v ∈ S.Vm, Matrix.mulVecLin (Y.rho lam σ * Γ) v ∈ S.Vm := fun v hv => by
    rw [Matrix.mulVecLin_apply, ← mulVec_mulVec, hm v hv, mulVec_smul]
    exact S.Vm.smul_mem _ (S.inv_m σ hσ v hv)
  have hrp : (Matrix.mulVecLin (Y.rho lam σ * Γ)).restrict hp' =
      a • (Matrix.mulVecLin (Y.rho lam σ)).restrict (S.inv_p σ hσ) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show (Y.rho lam σ * Γ) *ᵥ (x : Fin (Y.dim lam) → ℂ) = a • (Y.rho lam σ *ᵥ (x : Fin (Y.dim lam) → ℂ))
    rw [← mulVec_mulVec, hp x x.2, mulVec_smul]
  have hrm : (Matrix.mulVecLin (Y.rho lam σ * Γ)).restrict hm' =
      (-a) • (Matrix.mulVecLin (Y.rho lam σ)).restrict (S.inv_m σ hσ) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show (Y.rho lam σ * Γ) *ᵥ (x : Fin (Y.dim lam) → ℂ) = (-a) • (Y.rho lam σ *ᵥ (x : Fin (Y.dim lam) → ℂ))
    rw [← mulVec_mulVec, hm x x.2, mulVec_smul]
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_apply', trace_eq_add_of_isCompl S.compl _ hp' hm', hrp, hrm,
    map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **Step 4b**: `ψ(σ) = 0` unless `σ` has cycle type `h(λ)` (Frobenius at even `σ`, `gamma_odd` at odd `σ`). -/
theorem trace_eq_zero_of_ne (S : AltSplit Y lam) (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ)
    (hΓ : ∀ σ : Perm (Fin N), Γ * Y.rho lam σ = ((Perm.sign σ : ℤ) : ℂ) • (Y.rho lam σ * Γ)) (a : ℂ)
    (hp : ∀ v ∈ S.Vp, Γ *ᵥ v = a • v) (hm : ∀ v ∈ S.Vm, Γ *ᵥ v = (-a) • v)
    (σ : Perm (Fin N)) (hne : σ.partition.parts ≠ lam.diagonalHooks) : trace (Y.rho lam σ * Γ) = 0 := by
  rcases Int.units_eq_one_or (Perm.sign σ) with hσ | hσ
  · rw [trace_even_eq Y S.toAltDecomp Γ a hp hm σ hσ, S.frobenius σ hσ hne, sub_self, mul_zero]
  · exact gamma_odd Y lam Γ hΓ σ hσ

/-- **Step 5a**: `ψ(g σ g⁻¹) = sgn(g) ψ(σ)`. -/
theorem trace_conj (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ)
    (hΓ : ∀ σ : Perm (Fin N), Γ * Y.rho lam σ = ((Perm.sign σ : ℤ) : ℂ) • (Y.rho lam σ * Γ))
    (g σ : Perm (Fin N)) :
    trace (Y.rho lam (g * σ * g⁻¹) * Γ) = ((Perm.sign g : ℤ) : ℂ) * trace (Y.rho lam σ * Γ) := by
  have hgg : Y.rho lam g⁻¹ * Y.rho lam g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [map_mul, map_mul, mul_assoc, mul_assoc, trace_mul_comm, mul_assoc, mul_assoc, hΓ g, mul_smul_comm,
    mul_smul_comm, trace_smul, ← mul_assoc (Y.rho lam g⁻¹), hgg, one_mul, smul_eq_mul]

/-- `Γ ≠ 0` (it is invertible on the nonzero space `S^λ ⊇ V₊ ≠ 0`). -/
theorem gamma_ne_zero (S : AltDecomp Y lam) (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ) (hΓu : IsUnit Γ) :
    Γ ≠ 0 := by
  obtain ⟨v, -, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot S.ne_bot_p
  intro h0
  exact mulVec_ne_zero_of_isUnit hΓu hv0 (by rw [h0, zero_mulVec])

/-- **(T3), v1.02 lines 368-385, over ℂ**, from the cited splitting of the one shape `λ`: `ψ(σ) = tr(ρ(σ)Γ)` is supported
exactly on the permutations of cycle type `h(λ)`. -/
theorem gamma_support_of_split {N : ℕ} (Y : YoungSystem ℂ N) (lam : Shape N) (S : AltSplit Y lam) (hN : 2 ≤ N)
    (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ) (hΓu : IsUnit Γ)
    (hΓ : ∀ σ : Equiv.Perm (Fin N), Γ * Y.rho lam σ = ((Equiv.Perm.sign σ : ℤ) : ℂ) • (Y.rho lam σ * Γ))
    (σ : Equiv.Perm (Fin N)) :
    Matrix.trace (Y.rho lam σ * Γ) ≠ 0 ↔ σ.partition.parts = lam.diagonalHooks := by
  obtain ⟨a, hp, hm⟩ := gamma_pm Y S.toAltDecomp hN Γ hΓu hΓ
  have hsupp : ∀ τ : Perm (Fin N), trace (Y.rho lam τ * Γ) ≠ 0 → τ.partition.parts = lam.diagonalHooks :=
    fun τ hτ => by
      by_contra hc
      exact hτ (trace_eq_zero_of_ne Y S Γ hΓ a hp hm τ hc)
  refine ⟨hsupp σ, fun hσ => ?_⟩
  obtain ⟨σ₀, h0⟩ : ∃ σ₀ : Perm (Fin N), trace (Y.rho lam σ₀ * Γ) ≠ 0 := by
    by_contra hall
    exact gamma_ne_zero Y S.toAltDecomp Γ hΓu
      (eq_zero_of_trace_rho Y lam Γ fun τ => not_not.1 fun hne => hall ⟨τ, hne⟩)
  have hconj : IsConj σ₀ σ :=
    Perm.partition_eq_of_isConj.2 (Nat.Partition.ext ((hsupp σ₀ h0).trans hσ.symm))
  obtain ⟨g, rfl⟩ := isConj_iff.1 hconj
  rw [trace_conj Y Γ hΓ g σ₀]
  exact mul_ne_zero (by rcases Int.units_eq_one_or (Perm.sign g) with hg | hg <;> simp [hg]) h0

/-- **(T3), v1.02 lines 368-385, over ℂ**, for a Young system with the cited splitting of every self-conjugate shape. -/
theorem gamma_support_C {N : ℕ} (Y : YoungSystem ℂ N) (hsplit : AlternatingSplit Y) (hN : 2 ≤ N) (lam : Shape N)
    (h : lam.conjugate = lam)
    (Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ) (hΓu : IsUnit Γ)
    (hΓ : ∀ σ : Equiv.Perm (Fin N), Γ * Y.rho lam σ = ((Equiv.Perm.sign σ : ℤ) : ℂ) • (Y.rho lam σ * Γ))
    (σ : Equiv.Perm (Fin N)) :
    Matrix.trace (Y.rho lam σ * Γ) ≠ 0 ↔ σ.partition.parts = lam.diagonalHooks :=
  gamma_support_of_split Y lam (hsplit lam h hN).some hN Γ hΓu hΓ σ

end NagataHigman.Proofs

end
