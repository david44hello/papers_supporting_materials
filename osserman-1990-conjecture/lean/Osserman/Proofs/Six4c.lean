/-
Osserman/Proofs/Six4c.lean — Theorem G (paper 013, §9.4, sec_polynomial_gram.tex l. 237-267), batch 3: the shift
`J'_x = J_x - μ₀Π(x)` (rank `15 - m`, semidefinite, definite `Λ`).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Six4b
import Osserman.Proofs.Spectral

namespace Osserman.Proofs.Six4

open Osserman Matrix

section shift

variable (R : CurvTensor 16) (μ0 : ℝ)

/-- `J'_x = J_x - μ₀Π(x)`. -/
noncomputable def Jsh (x : Vec 16) : Matrix (Fin 16) (Fin 16) ℝ := R.jacobi x - μ0 • Osserman.Pi x

lemma Jsh_mulVec (x y : Vec 16) : Jsh R μ0 x *ᵥ y = R.op y x x - μ0 • ((x ⬝ᵥ x) • y - (y ⬝ᵥ x) • x) := by
  rw [Jsh, sub_mulVec, smul_mulVec, Curv.jacobi_mulVec, Spectral.Pi_mulVec]

lemma Jsh_transpose (x : Vec 16) : (Jsh R μ0 x)ᵀ = Jsh R μ0 x := by
  rw [Jsh, transpose_sub, transpose_smul, Spectral.jacobi_transpose, Spectral.Pi_transpose]

lemma Jsh_self (x : Vec 16) : Jsh R μ0 x *ᵥ x = 0 := by
  rw [Jsh, sub_mulVec, smul_mulVec, Spectral.jacobi_self, Spectral.Pi_self, smul_zero, sub_zero]

lemma Jsh_smul (t : ℝ) (x : Vec 16) : Jsh R μ0 (t • x) = (t * t) • Jsh R μ0 x := by
  rw [Jsh, Jsh, Spectral.jacobi_smul, Spectral.Pi_smul, smul_sub, smul_comm μ0 (t * t)]

lemma Jsh_herm (x : Vec 16) : (Jsh R μ0 x).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, Jsh_transpose]

lemma Jsh_dot (x y z : Vec 16) : y ⬝ᵥ (Jsh R μ0 x *ᵥ z) = (Jsh R μ0 x *ᵥ y) ⬝ᵥ z := by
  rw [dotProduct_mulVec, ← mulVec_transpose, Jsh_transpose]

/-- The kernel of `J'_x` at a unit `x` is `ℝx ⊕ E_{μ₀}(x)`. -/
lemma Jsh_ker (x : Vec 16) (hx : x ⬝ᵥ x = 1) :
    LinearMap.ker (Jsh R μ0 x).mulVecLin = (ℝ ∙ x) ⊔ Spectral.Esp R x μ0 := by
  ext v
  constructor
  · intro hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
    set w := v - (x ⬝ᵥ v) • x with hw_def
    have hw : x ⬝ᵥ w = 0 := by
      rw [hw_def, dotProduct_sub, dotProduct_smul, hx, smul_eq_mul, mul_one, sub_self]
    have hMw : Jsh R μ0 x *ᵥ w = 0 := by
      rw [hw_def, mulVec_sub, mulVec_smul, hv, Jsh_self, smul_zero, sub_zero]
    refine Submodule.mem_sup.2 ⟨(x ⬝ᵥ v) • x, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x), w, ?_,
      by rw [hw_def]; abel⟩
    refine Spectral.mem_Esp.2 ⟨?_, hw⟩
    rw [Jsh_mulVec, hx, one_smul, dotProduct_comm w x, hw, zero_smul, sub_zero] at hMw
    exact sub_eq_zero.1 hMw
  · intro hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    obtain ⟨hb1, hb2⟩ := Spectral.mem_Esp.1 hb
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, mulVec_add, mulVec_smul, Jsh_self, smul_zero, zero_add,
      Jsh_mulVec, hb1, hx, one_smul, dotProduct_comm b x, hb2, zero_smul, sub_zero, sub_self]

lemma Jsh_rank (x : Vec 16) (hx : x ⬝ᵥ x = 1) {m : ℕ} (hm : R.redMult x μ0 = m) :
    (Jsh R μ0 x).rank = 15 - m := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hrn : Module.finrank ℝ (LinearMap.range (Jsh R μ0 x).mulVecLin) +
      Module.finrank ℝ ↥((ℝ ∙ x) ⊔ Spectral.Esp R x μ0) = 16 := by
    have h := LinearMap.finrank_range_add_finrank_ker (Jsh R μ0 x).mulVecLin
    rwa [Jsh_ker R μ0 x hx, Module.finrank_fin_fun] at h
  have hdisj : (ℝ ∙ x) ⊓ Spectral.Esp R x μ0 = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv.1
    have h2 := (Spectral.mem_Esp.1 hv.2).2
    rw [dotProduct_smul, hx, smul_eq_mul, mul_one] at h2
    rw [h2, zero_smul]
  have hE : Module.finrank ℝ ↥(Spectral.Esp R x μ0) = m := hm
  have hs : Module.finrank ℝ ↥((ℝ ∙ x) ⊔ Spectral.Esp R x μ0) = 1 + m := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ x) (Spectral.Esp R x μ0)
    rw [hdisj, finrank_bot, finrank_span_singleton hx0, hE] at h
    omega
  have hle : m ≤ 15 := by
    have h1 : Module.finrank ℝ ↥(Spectral.Esp R x μ0) ≤ Module.finrank ℝ ↥(perp x) :=
      Submodule.finrank_mono inf_le_right
    have h2 := Spectral.finrank_perp hx
    omega
  show Module.finrank ℝ (LinearMap.range (Jsh R μ0 x).mulVecLin) = 15 - m
  omega

/-- At a unit `x`, a nonzero eigenvalue `λ` of `J'_x` makes `λ + μ₀` a reduced eigenvalue of `J_x`. -/
lemma Jsh_eig_red (x : Vec 16) (hx : x ⬝ᵥ x = 1) {u : Vec 16} (hu0 : u ≠ 0) {lam : ℝ} (hlam : lam ≠ 0)
    (hu : Jsh R μ0 x *ᵥ u = lam • u) : 0 < R.redMult x (lam + μ0) := by
  have hxu : x ⬝ᵥ u = 0 := by
    have h := Jsh_dot R μ0 x x u
    rw [hu, Jsh_self, zero_dotProduct, dotProduct_smul, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left hlam
  have hop : R.op u x x = (lam + μ0) • u := by
    rw [Jsh_mulVec, hx, one_smul, dotProduct_comm u x, hxu, zero_smul, sub_zero] at hu
    rw [add_smul, ← hu]
    abel
  have hmem : u ∈ Spectral.Esp R x (lam + μ0) := Spectral.mem_Esp.2 ⟨hop, hxu⟩
  have h1 := Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem u _).2 hmem)
  rw [finrank_span_singleton hu0] at h1
  exact h1

/-- The eigenvectors of a real symmetric matrix are nonzero functions. -/
lemma eigvec_ne_zero {N : Matrix (Fin 16) (Fin 16) ℝ} (hN : N.IsHermitian) (i : Fin 16) :
    (⇑(hN.eigenvectorBasis i) : Vec 16) ≠ 0 := by
  intro h
  apply hN.eigenvectorBasis.orthonormal.ne_zero i
  apply PiLp.ext
  intro j
  simpa using congrFun h j

lemma Jsh_psd_unit (hS : IsSmallestRed R μ0) (x : Vec 16) (hx : x ⬝ᵥ x = 1) : (Jsh R μ0 x).PosSemidef := by
  have hH := Jsh_herm R μ0 x
  rw [hH.posSemidef_iff_eigenvalues_nonneg]
  intro i
  by_contra hneg
  have hlt : hH.eigenvalues i < 0 := lt_of_not_ge hneg
  have hpos := Jsh_eig_red R μ0 x hx (eigvec_ne_zero hH i) hlt.ne (hH.mulVec_eigenvectorBasis i)
  have := hS x hx _ hpos
  linarith

lemma Jsh_nsd_unit (hL : IsLargestRed R μ0) (x : Vec 16) (hx : x ⬝ᵥ x = 1) : (-Jsh R μ0 x).PosSemidef := by
  have hH : (-Jsh R μ0 x).IsHermitian := (Jsh_herm R μ0 x).neg
  rw [hH.posSemidef_iff_eigenvalues_nonneg]
  intro i
  by_contra hneg
  have hlt : hH.eigenvalues i < 0 := lt_of_not_ge hneg
  have hu : Jsh R μ0 x *ᵥ ⇑(hH.eigenvectorBasis i) = (-hH.eigenvalues i) • ⇑(hH.eigenvectorBasis i) := by
    have h := hH.mulVec_eigenvectorBasis i
    rw [neg_mulVec] at h
    rw [neg_smul, ← h, neg_neg]
  have hpos := Jsh_eig_red R μ0 x hx (eigvec_ne_zero hH i) (neg_ne_zero.2 hlt.ne) hu
  have := hL x hx _ hpos
  linarith

/-- Semidefiniteness at every `x` from unit `x` (`J'_{tx} = t²J'_x`). -/
lemma Jsh_scale {P : Matrix (Fin 16) (Fin 16) ℝ → Prop} (h0 : P 0)
    (hsm : ∀ (M : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ), P M → 0 ≤ c → P (c • M))
    (hunit : ∀ x : Vec 16, x ⬝ᵥ x = 1 → P (Jsh R μ0 x)) (x : Vec 16) : P (Jsh R μ0 x) := by
  by_cases hx0 : x = 0
  · subst hx0
    have h := Jsh_smul R μ0 0 0
    rw [zero_smul, zero_mul, zero_smul] at h
    rw [h]
    exact h0
  · have hq : 0 < x ⬝ᵥ x := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))
      (fun e => hx0 (dotProduct_self_eq_zero.mp e.symm))
    set c := Real.sqrt (x ⬝ᵥ x) with hc
    have hc0 : 0 < c := Real.sqrt_pos.2 hq
    have hcc : c * c = x ⬝ᵥ x := Real.mul_self_sqrt hq.le
    have hu : (c⁻¹ • x) ⬝ᵥ (c⁻¹ • x) = 1 := by
      rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← hcc]
      field_simp
    have hxe : x = c • (c⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]
    rw [hxe, Jsh_smul]
    exact hsm _ _ (hunit _ hu) (mul_self_nonneg c)

/-- An orthonormal frame `M_X` of `Im N` for a symmetric semidefinite `N`: `Λ = M_XᵀNM_X` is definite. -/
lemma frame_posDef {ν : ℕ} (N : Matrix (Fin 16) (Fin 16) ℝ) (hNT : Nᵀ = N) (hN : N.PosSemidef)
    (MX : Matrix (Fin 16) (Fin ν) ℝ) (hMX : MXᵀ * MX = 1)
    (hrange : LinearMap.range (Matrix.toLin' MX) = LinearMap.range (Matrix.toLin' N)) :
    (MXᵀ * N * MX).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_mul, transpose_transpose, hNT,
      Matrix.mul_assoc]
  · rw [star_trivial]
    have e : v ⬝ᵥ ((MXᵀ * N * MX) *ᵥ v) = (MX *ᵥ v) ⬝ᵥ (N *ᵥ (MX *ᵥ v)) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    rw [e]
    have hnn := hN.dotProduct_mulVec_nonneg (MX *ᵥ v)
    rw [star_trivial] at hnn
    refine lt_of_le_of_ne hnn fun h0 => hv ?_
    have hker : N *ᵥ (MX *ᵥ v) = 0 := by
      have := (hN.dotProduct_mulVec_zero_iff (x := MX *ᵥ v)).1
      rw [star_trivial] at this
      exact this h0.symm
    obtain ⟨z, hz⟩ : MX *ᵥ v ∈ LinearMap.range (Matrix.toLin' N) := by
      rw [← hrange]
      exact ⟨v, rfl⟩
    rw [Matrix.toLin'_apply] at hz
    have hzz : (MX *ᵥ v) ⬝ᵥ (MX *ᵥ v) = 0 := by
      calc (MX *ᵥ v) ⬝ᵥ (MX *ᵥ v) = (N *ᵥ z) ⬝ᵥ (MX *ᵥ v) := by rw [hz]
        _ = z ⬝ᵥ (N *ᵥ (MX *ᵥ v)) := by
          rw [dotProduct_mulVec z N (MX *ᵥ v), ← mulVec_transpose, hNT]
        _ = 0 := by rw [hker, dotProduct_zero]
    have hMv : MX *ᵥ v = 0 := dotProduct_self_eq_zero.1 hzz
    calc v = (MXᵀ * MX) *ᵥ v := by rw [hMX, one_mulVec]
      _ = 0 := by rw [← mulVec_mulVec, hMv, mulVec_zero]

end shift

theorem thm_G_shift_proved (R : CurvTensor 16) (_hO : R.IsOsserman) (μ0 : ℝ) (m : ℕ) (_hm : m = 7 ∨ m = 8)
    (hmult : ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ0 = m) :
    (∀ x : Vec 16, x ⬝ᵥ x = 1 → (R.jacobi x - μ0 • Pi x).rank = 15 - m) ∧
      (IsSmallestRed R μ0 → ∀ x : Vec 16, (R.jacobi x - μ0 • Pi x).PosSemidef) ∧
      (IsLargestRed R μ0 → ∀ x : Vec 16, (-(R.jacobi x - μ0 • Pi x)).PosSemidef) ∧
      ∀ Xa : Vec 16, Xa ⬝ᵥ Xa = 1 → ∀ (ν : ℕ) (MX : Matrix (Fin 16) (Fin ν) ℝ) (Λ : Matrix (Fin ν) (Fin ν) ℝ),
        MXᵀ * MX = 1 → LinearMap.range (Matrix.toLin' MX) = LinearMap.range (Matrix.toLin' (R.jacobi Xa - μ0 • Pi Xa)) →
        R.jacobi Xa - μ0 • Pi Xa = MX * Λ * MXᵀ →
        ν = 15 - m ∧ (IsSmallestRed R μ0 → Λ.PosDef) ∧ (IsLargestRed R μ0 → (-Λ).PosDef) := by
  have hrank : ∀ x : Vec 16, x ⬝ᵥ x = 1 → (Jsh R μ0 x).rank = 15 - m := fun x hx => Jsh_rank R μ0 x hx (hmult x hx)
  have hpsd : IsSmallestRed R μ0 → ∀ x : Vec 16, (Jsh R μ0 x).PosSemidef := fun hS =>
    Jsh_scale R μ0 PosSemidef.zero (fun _ _ hM hc => hM.smul hc) (Jsh_psd_unit R μ0 hS)
  have hnsd : IsLargestRed R μ0 → ∀ x : Vec 16, (-Jsh R μ0 x).PosSemidef := fun hL x =>
    Jsh_scale R μ0 (P := fun M => (-M).PosSemidef) (by simpa using PosSemidef.zero)
      (fun M c hM hc => by rw [← smul_neg]; exact hM.smul hc) (Jsh_nsd_unit R μ0 hL) x
  refine ⟨hrank, hpsd, hnsd, fun Xa hXa ν MX Λ hMX hrange hfac => ?_⟩
  have hΛ : Λ = MXᵀ * Jsh R μ0 Xa * MX := by
    change R.jacobi Xa - μ0 • Pi Xa = MX * Λ * MXᵀ at hfac
    rw [Jsh, hfac]
    calc Λ = (MXᵀ * MX) * Λ * (MXᵀ * MX) := by rw [hMX, Matrix.one_mul, Matrix.mul_one]
      _ = MXᵀ * (MX * Λ * MXᵀ) * MX := by simp only [Matrix.mul_assoc]
  refine ⟨?_, fun hS => ?_, fun hL => ?_⟩
  · have hinj : Function.Injective (Matrix.toLin' MX) := by
      intro a b hab
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at hab
      calc a = (MXᵀ * MX) *ᵥ a := by rw [hMX, one_mulVec]
        _ = (MXᵀ * MX) *ᵥ b := by rw [← mulVec_mulVec, hab, mulVec_mulVec]
        _ = b := by rw [hMX, one_mulVec]
    have h1 := LinearMap.finrank_range_of_inj hinj
    rw [hrange, Module.finrank_fin_fun] at h1
    have h2 := hrank Xa hXa
    unfold Matrix.rank at h2
    rw [← Matrix.toLin'_apply'] at h2
    change Module.finrank ℝ (LinearMap.range (Matrix.toLin' (Jsh R μ0 Xa))) = ν at h1
    omega
  · rw [hΛ]
    exact frame_posDef _ (Jsh_transpose R μ0 Xa) (hpsd hS Xa) MX hMX hrange
  · have h := frame_posDef (-Jsh R μ0 Xa) (by rw [transpose_neg, Jsh_transpose]) (hnsd hL Xa) MX hMX
      (by rw [hrange, map_neg, LinearMap.range_neg]; rfl)
    rw [hΛ]
    simpa [Matrix.mul_neg, Matrix.neg_mul] using h

end Osserman.Proofs.Six4
