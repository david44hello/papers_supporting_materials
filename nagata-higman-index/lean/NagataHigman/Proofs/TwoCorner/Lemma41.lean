/-
NagataHigman/Proofs/TwoCorner/Lemma41.lean — Lemma 4.1 (fixed points and stars), tex lines 524-545.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Proofs.TwoCorner.Gamma

noncomputable section

namespace NagataHigman.Proofs

open Equiv Finset Matrix NagataHigman

variable {F : Type*} [Field F] [CharZero F]

section MatrixCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Q₊ = (1 + Y)/2`. -/
abbrev qP (Yt : Matrix ι ι F) : Matrix ι ι F := (1 / 2 : F) • (1 + Yt)
/-- `Q₋ = (1 - Y)/2`. -/
abbrev qM (Yt : Matrix ι ι F) : Matrix ι ι F := (1 / 2 : F) • (1 - Yt)

omit [Fintype ι] in
theorem qP_add_qM (Yt : Matrix ι ι F) : qP Yt + qM Yt = 1 := by
  rw [qP, qM, ← smul_add]
  rw [show (1 + Yt) + (1 - Yt) = (2 : F) • (1 : Matrix ι ι F) by rw [two_smul]; abel, smul_smul]
  norm_num

omit [CharZero F] in
theorem Y_mul_qP (Yt : Matrix ι ι F) (hY : Yt * Yt = 1) : Yt * qP Yt = qP Yt := by
  rw [qP, mul_smul_comm, mul_add, mul_one, hY, add_comm]

omit [CharZero F] in
theorem Y_mul_qM (Yt : Matrix ι ι F) (hY : Yt * Yt = 1) : Yt * qM Yt = -qM Yt := by
  rw [qM, mul_smul_comm, mul_sub, mul_one, hY, ← smul_neg, neg_sub]

theorem qP_mul_self (Yt : Matrix ι ι F) (hY : Yt * Yt = 1) : qP Yt * qP Yt = qP Yt := by
  rw [show qP Yt * qP Yt = (1 / 2 : F) • ((1 + Yt) * qP Yt) by rw [qP, smul_mul_assoc],
    add_mul, one_mul, Y_mul_qP Yt hY, ← two_smul F (qP Yt), smul_smul]
  norm_num

theorem qM_mul_self (Yt : Matrix ι ι F) (hY : Yt * Yt = 1) : qM Yt * qM Yt = qM Yt := by
  rw [show qM Yt * qM Yt = (1 / 2 : F) • ((1 - Yt) * qM Yt) by rw [qM, smul_mul_assoc],
    sub_mul, one_mul, Y_mul_qM Yt hY, sub_neg_eq_add, ← two_smul F (qM Yt), smul_smul]
  norm_num

theorem qP_mul_qM (Yt : Matrix ι ι F) (hY : Yt * Yt = 1) : qP Yt * qM Yt = 0 := by
  rw [show qP Yt * qM Yt = (1 / 2 : F) • ((1 + Yt) * qM Yt) by rw [qP, smul_mul_assoc],
    add_mul, one_mul, Y_mul_qM Yt hY, add_neg_cancel, smul_zero]

theorem qM_mul_qP (Yt : Matrix ι ι F) (hY : Yt * Yt = 1) : qM Yt * qP Yt = 0 := by
  rw [show qM Yt * qP Yt = (1 / 2 : F) • ((1 - Yt) * qP Yt) by rw [qM, smul_mul_assoc],
    sub_mul, one_mul, Y_mul_qP Yt hY, sub_self, smul_zero]

omit [Fintype ι] in
theorem Y_eq_qP_sub_qM (Yt : Matrix ι ι F) : Yt = qP Yt - qM Yt := by
  rw [qP, qM, ← smul_sub, show (1 + Yt) - (1 - Yt) = (2 : F) • Yt by rw [two_smul]; abel, smul_smul]
  norm_num

/-- Lemma 4.1, proof: `M` is trace-orthogonal to every operator commuting with the involution `Y` (the operators
preserving both eigenspaces) iff `Q₊ M Q₊ = 0 = Q₋ M Q₋`. -/
theorem trace_perp_commutant_iff_blocks (Yt M : Matrix ι ι F) (hY : Yt * Yt = 1) :
    (∀ X : Matrix ι ι F, X * Yt = Yt * X → trace (X * M) = 0) ↔
      qP Yt * M * qP Yt = 0 ∧ qM Yt * M * qM Yt = 0 := by
  have hPP := qP_mul_self Yt hY
  have hMM := qM_mul_self Yt hY
  constructor
  · intro h
    -- for `Q = Q±`: `Q Y = Y Q = ±Q`, so `Q Z Q` commutes with `Y` for every `Z`
    have key : ∀ (Q : Matrix ι ι F) (s : F), Q * Yt = s • Q → Yt * Q = s • Q → Q * M * Q = 0 := by
      intro Q s hQ1 hQ2
      refine (ext_iff_trace_mul_left).2 fun Z => ?_
      have hc : (Q * Z * Q) * Yt = Yt * (Q * Z * Q) := by
        rw [mul_assoc, hQ1, ← mul_assoc, ← mul_assoc, hQ2, mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
      rw [mul_zero, trace_zero, ← h _ hc]
      rw [show Q * Z * Q * M = Q * (Z * (Q * M)) by simp only [mul_assoc], trace_mul_comm Q]
      simp only [mul_assoc]
    have hP1 : qP Yt * Yt = (1 : F) • qP Yt := by
      rw [one_smul, qP, smul_mul_assoc, add_mul, one_mul, hY, add_comm]
    have hM1 : qM Yt * Yt = (-1 : F) • qM Yt := by
      rw [neg_one_smul, qM, smul_mul_assoc, sub_mul, one_mul, hY, ← smul_neg, neg_sub]
    have hP2 : Yt * qP Yt = (1 : F) • qP Yt := by rw [one_smul, Y_mul_qP Yt hY]
    have hM2 : Yt * qM Yt = (-1 : F) • qM Yt := by rw [neg_one_smul, Y_mul_qM Yt hY]
    exact ⟨key _ _ hP1 hP2, key _ _ hM1 hM2⟩
  · rintro ⟨hp, hm⟩ X hX
    have hXP : X * qP Yt = qP Yt * X := by
      rw [qP, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul, hX]
    have hXM : X * qM Yt = qM Yt * X := by
      rw [qM, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul, hX]
    have c1 : qP Yt * X * qM Yt = 0 := by rw [← hXP, mul_assoc, qP_mul_qM Yt hY, mul_zero]
    have c2 : qM Yt * X * qP Yt = 0 := by rw [← hXM, mul_assoc, qM_mul_qP Yt hY, mul_zero]
    have hsplit : X = qP Yt * X * qP Yt + qM Yt * X * qM Yt := by
      calc X = (qP Yt + qM Yt) * X * (qP Yt + qM Yt) := by rw [qP_add_qM, one_mul, mul_one]
        _ = qP Yt * X * qP Yt + qP Yt * X * qM Yt + (qM Yt * X * qP Yt + qM Yt * X * qM Yt) := by
          simp only [add_mul, mul_add]; abel
        _ = _ := by rw [c1, c2, add_zero, zero_add]
    rw [hsplit, add_mul, trace_add]
    have t1 : trace (qP Yt * X * qP Yt * M) = trace (X * (qP Yt * M * qP Yt)) := by
      rw [show qP Yt * X * qP Yt * M = qP Yt * (X * qP Yt * M) by simp only [mul_assoc], trace_mul_comm]
      simp only [mul_assoc]
    have t2 : trace (qM Yt * X * qM Yt * M) = trace (X * (qM Yt * M * qM Yt)) := by
      rw [show qM Yt * X * qM Yt * M = qM Yt * (X * qM Yt * M) by simp only [mul_assoc], trace_mul_comm]
      simp only [mul_assoc]
    rw [t1, t2, hp, hm, mul_zero, trace_zero, add_zero]

/-- Lemma 4.1, proof: since `Y` is an involution and `Q±` project onto its `±1`-eigenspaces, `Q₊ M Q₊ = 0 = Q₋ M Q₋`
says that `M` maps each eigenspace of `Y` into the other. -/
theorem blocks_iff_swaps_eigenspaces (Yt M : Matrix ι ι F) (hY : Yt * Yt = 1) :
    (qP Yt * M * qP Yt = 0 ∧ qM Yt * M * qM Yt = 0) ↔
      ((∀ v : ι → F, Yt *ᵥ v = v → Yt *ᵥ (M *ᵥ v) = -(M *ᵥ v)) ∧
        (∀ v : ι → F, Yt *ᵥ v = -v → Yt *ᵥ (M *ᵥ v) = M *ᵥ v)) := by
  have hYP := Y_mul_qP Yt hY
  have hYM := Y_mul_qM Yt hY
  have hsum := qP_add_qM Yt
  -- `Q₊ v = v` on the `+1`-eigenspace, `Q₋ v = v` on the `-1`-eigenspace
  have hPv : ∀ v : ι → F, Yt *ᵥ v = v → qP Yt *ᵥ v = v := fun v hv => by
    rw [qP, smul_mulVec, add_mulVec, one_mulVec, hv, ← two_smul F v, smul_smul]; norm_num
  have hMv : ∀ v : ι → F, Yt *ᵥ v = -v → qM Yt *ᵥ v = v := fun v hv => by
    rw [qM, smul_mulVec, sub_mulVec, one_mulVec, hv, sub_neg_eq_add, ← two_smul F v, smul_smul]; norm_num
  have hPkill : ∀ v : ι → F, Yt *ᵥ v = -v → qP Yt *ᵥ v = 0 := fun v hv => by
    rw [qP, smul_mulVec, add_mulVec, one_mulVec, hv, add_neg_cancel, smul_zero]
  have hMkill : ∀ v : ι → F, Yt *ᵥ v = v → qM Yt *ᵥ v = 0 := fun v hv => by
    rw [qM, smul_mulVec, sub_mulVec, one_mulVec, hv, sub_self, smul_zero]
  constructor
  · rintro ⟨hp, hm⟩
    constructor
    · intro v hv
      have h0 : qP Yt *ᵥ (M *ᵥ v) = 0 := by
        rw [← hPv v hv, mulVec_mulVec, mulVec_mulVec, hp, zero_mulVec]
      have hw : M *ᵥ v = qM Yt *ᵥ (M *ᵥ v) := by
        rw [← zero_add (qM Yt *ᵥ (M *ᵥ v)), ← h0, ← add_mulVec, hsum, one_mulVec]
      rw [hw, mulVec_mulVec, hYM, neg_mulVec]
    · intro v hv
      have h0 : qM Yt *ᵥ (M *ᵥ v) = 0 := by
        rw [← hMv v hv, mulVec_mulVec, mulVec_mulVec, hm, zero_mulVec]
      have hw : M *ᵥ v = qP Yt *ᵥ (M *ᵥ v) := by
        rw [← add_zero (qP Yt *ᵥ (M *ᵥ v)), ← h0, ← add_mulVec, hsum, one_mulVec]
      rw [hw, mulVec_mulVec, hYP]
  · rintro ⟨hp, hm⟩
    have hPe : ∀ v : ι → F, Yt *ᵥ (qP Yt *ᵥ v) = qP Yt *ᵥ v := fun v => by rw [mulVec_mulVec, hYP]
    have hMe : ∀ v : ι → F, Yt *ᵥ (qM Yt *ᵥ v) = -(qM Yt *ᵥ v) := fun v => by
      rw [mulVec_mulVec, hYM, neg_mulVec]
    constructor
    · apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, ← mulVec_mulVec, ← mulVec_mulVec]
      exact hPkill _ (hp _ (hPe v))
    · apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, ← mulVec_mulVec, ← mulVec_mulVec]
      exact hMkill _ (hm _ (hMe v))

/-- Lemma 4.1, proof: `M` maps each eigenspace of the involution `Y` into the other iff `Y M = -M Y`. -/
theorem swaps_eigenspaces_iff_anticomm (Yt M : Matrix ι ι F) (hY : Yt * Yt = 1) :
    ((∀ v : ι → F, Yt *ᵥ v = v → Yt *ᵥ (M *ᵥ v) = -(M *ᵥ v)) ∧
        (∀ v : ι → F, Yt *ᵥ v = -v → Yt *ᵥ (M *ᵥ v) = M *ᵥ v)) ↔ Yt * M = -(M * Yt) := by
  constructor
  · rintro ⟨hp, hm⟩
    have hYP := Y_mul_qP Yt hY
    have hYM := Y_mul_qM Yt hY
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_apply]
    have hv : v = qP Yt *ᵥ v + qM Yt *ᵥ v := by rw [← add_mulVec, qP_add_qM, one_mulVec]
    have e1 := hp (qP Yt *ᵥ v) (by rw [mulVec_mulVec, hYP])
    have e2 := hm (qM Yt *ᵥ v) (by rw [mulVec_mulVec, hYM, neg_mulVec])
    have hYv : Yt *ᵥ v = qP Yt *ᵥ v - qM Yt *ᵥ v := by rw [← sub_mulVec, ← Y_eq_qP_sub_qM]
    calc (Yt * M) *ᵥ v = Yt *ᵥ (M *ᵥ (qP Yt *ᵥ v + qM Yt *ᵥ v)) := by
          rw [← mulVec_mulVec, ← hv]
      _ = Yt *ᵥ (M *ᵥ (qP Yt *ᵥ v)) + Yt *ᵥ (M *ᵥ (qM Yt *ᵥ v)) := by rw [mulVec_add, mulVec_add]
      _ = -(M *ᵥ (qP Yt *ᵥ v)) + M *ᵥ (qM Yt *ᵥ v) := by rw [e1, e2]
      _ = -(M *ᵥ (qP Yt *ᵥ v - qM Yt *ᵥ v)) := by rw [mulVec_sub]; abel
      _ = (-(M * Yt)) *ᵥ v := by rw [← hYv, neg_mulVec, mulVec_mulVec]
  · intro h
    constructor
    · intro v hv
      rw [mulVec_mulVec, h, neg_mulVec, ← mulVec_mulVec, hv]
    · intro v hv
      rw [mulVec_mulVec, h, neg_mulVec, ← mulVec_mulVec, hv, mulVec_neg, neg_neg]

/-- For `Y² = 1` (characteristic 0): `M` is trace-orthogonal to every matrix commuting with `Y` iff `Y M + M Y = 0`,
along the paper's chain (l. 535-540): trace-orthogonal iff `Q₊ M Q₊ = 0 = Q₋ M Q₋`
(`trace_perp_commutant_iff_blocks`), iff `M` maps each eigenspace of `Y` into the other
(`blocks_iff_swaps_eigenspaces`), iff `Y M = -M Y` (`swaps_eigenspaces_iff_anticomm`). -/
theorem trace_perp_commutant_iff (Yt M : Matrix ι ι F) (hY : Yt * Yt = 1) :
    (∀ X : Matrix ι ι F, X * Yt = Yt * X → trace (X * M) = 0) ↔ Yt * M + M * Yt = 0 := by
  rw [trace_perp_commutant_iff_blocks Yt M hY, blocks_iff_swaps_eigenspaces Yt M hY,
    swaps_eigenspaces_iff_anticomm Yt M hY]
  constructor
  · intro h
    rw [h, neg_add_cancel]
  · intro h
    exact eq_neg_of_add_eq_zero_left h

end MatrixCore

section Lemma41

variable {N : ℕ} (Y : YoungSystem F N)

/-- The case `Stab(top)` (paper v1.02 l. 397-402): for any matrix `M'`, `tr(ρ(τ) M') = 0` for every `τ` fixing `top` iff
`M'` anticommutes with `ρ(J_top)` (needs `ρ(J_top)² = 1`, true for `ν`: its two corners have contents `±1`). -/
theorem trace_stab_iff (lam : Shape N) (top : Fin N) (htop : (top : ℕ) + 1 = N)
    (hY : Y.rhoAlg lam (jucysMurphy F top) * Y.rhoAlg lam (jucysMurphy F top) = 1)
    (hres : ∀ X : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F,
      X ∈ Submodule.span F ((Y.rho lam : Perm (Fin N) → Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) '' stab top) ↔
        X * Y.rhoAlg lam (jucysMurphy F top) = Y.rhoAlg lam (jucysMurphy F top) * X)
    (M' : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) :
    (∀ τ ∈ stab top, trace (Y.rho lam τ * M') = 0) ↔
      Y.rhoAlg lam (jucysMurphy F top) * M' + M' * Y.rhoAlg lam (jucysMurphy F top) = 0 := by
  rw [← trace_perp_commutant_iff _ M' hY]
  constructor
  · intro h X hX
    have hXspan := (hres X).2 hX
    clear hX
    induction hXspan using Submodule.span_induction with
    | mem x hx => obtain ⟨τ, hτ, rfl⟩ := hx; exact h τ hτ
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, trace_add, hx, hy, add_zero]
    | smul c x _ hx => rw [smul_mul_assoc, trace_smul, hx, smul_zero]
  · intro h τ hτ
    exact h _ ((hres _).1 (Submodule.subset_span ⟨τ, hτ, rfl⟩))

omit [CharZero F] in
/-- `ρ` of a conjugate: `ρ(g a g⁻¹) = ρ(g) ρ(a) ρ(g)⁻¹` with `ρ(g)⁻¹ = ρ(g⁻¹)`. -/
theorem rhoAlg_conj (lam : Shape N) (g : Perm (Fin N)) (a : GrpAlg F N) :
    Y.rhoAlg lam (perm F g * a * perm F g⁻¹) = Y.rho lam g * Y.rhoAlg lam a * Y.rho lam g⁻¹ := by
  rw [map_mul, map_mul, YoungSystem.rhoAlg_perm, YoungSystem.rhoAlg_perm]

/-- The transfer to `Stab(j)` (paper v1.02 l. 404-409), for an element `f` of the block `I_λ` with `M = ρ_λ(f)`:
`f` vanishes on `Stab(j)` iff `M` anticommutes with `Y_j = ρ_λ(X^{(j)})`. -/
theorem coeff_stab_iff (lam : Shape N) (top : Fin N) (htop : (top : ℕ) + 1 = N)
    (hY : Y.rhoAlg lam (jucysMurphy F top) * Y.rhoAlg lam (jucysMurphy F top) = 1)
    (hres : ∀ X : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F,
      X ∈ Submodule.span F ((Y.rho lam : Perm (Fin N) → Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) '' stab top) ↔
        X * Y.rhoAlg lam (jucysMurphy F top) = Y.rhoAlg lam (jucysMurphy F top) * X)
    (hdim : (Y.dim lam : F) ≠ 0)
    (hconj : ∀ (g : Perm (Fin N)) (j : Fin N), perm F g * starElem F j * perm F g⁻¹ = starElem F (g j))
    (htopstar : starElem F top = jucysMurphy F top)
    {f : GrpAlg F N} (hf : f ∈ Y.block lam) (j : Fin N) :
    (∀ σ ∈ stab j, f.coeff σ = 0) ↔
      Y.rhoAlg lam (starElem F j) * Y.rhoAlg lam f + Y.rhoAlg lam f * Y.rhoAlg lam (starElem F j) = 0 := by
  set g : Perm (Fin N) := swap j top with hg
  set M := Y.rhoAlg lam f
  set M' := Y.rho lam g⁻¹ * M * Y.rho lam g with hM'
  have hc : (Y.dim lam : F) / (N.factorial : F) ≠ 0 :=
    div_ne_zero hdim (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero N))
  have hgtop : g top = j := by simp [hg]
  have hginv : g⁻¹ = g := by simp [hg]
  -- Step 1: vanishing on Stab(j) ↔ trace condition for M' on Stab(top).
  have step1 : (∀ σ ∈ stab j, f.coeff σ = 0) ↔ ∀ τ ∈ stab top, trace (Y.rho lam τ * M') = 0 := by
    have key : ∀ τ : Perm (Fin N), f.coeff (g * τ⁻¹ * g⁻¹) =
        (Y.dim lam : F) / (N.factorial : F) * trace (Y.rho lam τ * M') := by
      intro τ
      rw [YoungSystem.coeff_of_mem_block Y hf]
      congr 1
      rw [show (g * τ⁻¹ * g⁻¹)⁻¹ = g * τ * g⁻¹ by group, map_mul, map_mul, hM',
        show Y.rho lam g * Y.rho lam τ * Y.rho lam g⁻¹ * M =
          Y.rho lam g * (Y.rho lam τ * Y.rho lam g⁻¹ * M) by simp only [mul_assoc], trace_mul_comm]
      simp only [mul_assoc]
    have hmem : ∀ τ : Perm (Fin N), τ ∈ stab top ↔ g * τ⁻¹ * g⁻¹ ∈ stab j := by
      intro τ
      simp only [stab, Set.mem_ofPred_eq, Perm.mul_apply, ← hgtop]
      rw [hginv, show g (g top) = top by simp [hg]]
      constructor
      · intro h
        rw [show τ⁻¹ top = top by rw [Perm.inv_eq_iff_eq, h]]
      · intro h
        have h' : τ⁻¹ top = top := by
          have := congrArg g h
          simpa [hg] using this
        rw [Perm.inv_eq_iff_eq] at h'
        exact h'.symm
    constructor
    · intro h τ hτ
      have := h _ ((hmem τ).1 hτ)
      rw [key τ] at this
      exact (mul_eq_zero.1 this).resolve_left hc
    · intro h σ hσ
      have hτ : (g⁻¹ * σ * g)⁻¹ ∈ stab top := by
        rw [hmem]; convert hσ using 1; group
      have := key (g⁻¹ * σ * g)⁻¹
      rw [show g * (g⁻¹ * σ * g)⁻¹⁻¹ * g⁻¹ = σ by group] at this
      rw [this, h _ hτ, mul_zero]
  -- Step 2: the trace condition ↔ anticommutation of M' with Y_top ↔ anticommutation of M with Y_j.
  rw [step1, trace_stab_iff Y lam top htop hY hres M']
  have hYj : Y.rhoAlg lam (starElem F j) = Y.rho lam g * Y.rhoAlg lam (jucysMurphy F top) * Y.rho lam g⁻¹ := by
    rw [← htopstar, ← rhoAlg_conj, hconj, hgtop]
  have hgg : Y.rho lam g * Y.rho lam g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hgg' : Y.rho lam g⁻¹ * Y.rho lam g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [hYj]
  set Yt := Y.rhoAlg lam (jucysMurphy F top)
  constructor
  · intro h
    have := congrArg (fun Z => Y.rho lam g * Z * Y.rho lam g⁻¹) h
    simp only [mul_zero, zero_mul, mul_add, add_mul, hM'] at this
    calc Y.rho lam g * Yt * Y.rho lam g⁻¹ * M + M * (Y.rho lam g * Yt * Y.rho lam g⁻¹)
        = Y.rho lam g * Yt * (Y.rho lam g⁻¹ * M * Y.rho lam g) * Y.rho lam g⁻¹ +
          Y.rho lam g * (Y.rho lam g⁻¹ * M * Y.rho lam g) * Yt * Y.rho lam g⁻¹ := by
          simp only [mul_assoc, hgg, mul_one]
          simp only [← mul_assoc, hgg, one_mul]
      _ = 0 := by simpa only [mul_assoc] using this
  · intro h
    have := congrArg (fun Z => Y.rho lam g⁻¹ * Z * Y.rho lam g) h
    simp only [mul_zero, zero_mul, mul_add, add_mul] at this
    rw [hM']
    calc Yt * (Y.rho lam g⁻¹ * M * Y.rho lam g) + Y.rho lam g⁻¹ * M * Y.rho lam g * Yt
        = Y.rho lam g⁻¹ * (Y.rho lam g * Yt * Y.rho lam g⁻¹) * M * Y.rho lam g +
          Y.rho lam g⁻¹ * M * (Y.rho lam g * Yt * Y.rho lam g⁻¹) * Y.rho lam g := by
          simp only [mul_assoc, hgg', mul_one]
          simp only [← mul_assoc, hgg', one_mul]
      _ = 0 := by simpa only [mul_assoc] using this

/-- **Lemma 4.1** (general form): for `f ∈ I_λ`, `M = ρ_λ(f)`, `f` vanishes on every permutation with a fixed point
iff `M Y_j = -Y_j M` for all `j`. -/
theorem lem_4_1_general (lam : Shape N) (top : Fin N) (htop : (top : ℕ) + 1 = N)
    (hY : Y.rhoAlg lam (jucysMurphy F top) * Y.rhoAlg lam (jucysMurphy F top) = 1)
    (hres : ∀ X : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F,
      X ∈ Submodule.span F ((Y.rho lam : Perm (Fin N) → Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) '' stab top) ↔
        X * Y.rhoAlg lam (jucysMurphy F top) = Y.rhoAlg lam (jucysMurphy F top) * X)
    (hdim : (Y.dim lam : F) ≠ 0)
    (hconj : ∀ (g : Perm (Fin N)) (j : Fin N), perm F g * starElem F j * perm F g⁻¹ = starElem F (g j))
    (htopstar : starElem F top = jucysMurphy F top)
    {f : GrpAlg F N} (hf : f ∈ Y.block lam) :
    (∀ σ : Perm (Fin N), (∃ j, σ j = j) → f.coeff σ = 0) ↔
      ∀ j : Fin N, Y.rhoAlg lam f * Y.rhoAlg lam (starElem F j) =
        -(Y.rhoAlg lam (starElem F j) * Y.rhoAlg lam f) := by
  have hj := fun j => coeff_stab_iff Y lam top htop hY hres hdim hconj htopstar hf j
  constructor
  · intro h j
    have := (hj j).1 fun σ hσ => h σ ⟨j, hσ⟩
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact this)
  · rintro h σ ⟨j, hσ⟩
    refine (hj j).2 ?_ σ hσ
    rw [h j, add_neg_cancel]

end Lemma41

end NagataHigman.Proofs

end
