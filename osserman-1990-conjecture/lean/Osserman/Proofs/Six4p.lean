/-
Osserman/Proofs/Six4p.lean — Theorem G (paper 013, §9.4, sec_polynomial_gram.tex l. 237-267), batch 4: the spectral
pencil (eq:spectralpencil) from the Osserman condition.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Six4c

namespace Osserman.Proofs.Six4

open Osserman Matrix Polynomial

/-! ### Real symmetric matrices: the characteristic polynomial from the eigenspace dimensions -/

section symm

variable {n : ℕ}

/-- For a symmetric endomorphism `g`, `g^k v = 0` forces `g v = 0`. -/
lemma symm_pow_ker (g : Module.End ℝ (Vec n)) (hg : ∀ a b, g a ⬝ᵥ b = a ⬝ᵥ g b) :
    ∀ (k : ℕ) (v : Vec n), (g ^ k) v = 0 → g v = 0 := by
  intro k
  induction k with
  | zero =>
    intro v hv
    rw [pow_zero, Module.End.one_apply] at hv
    rw [hv, map_zero]
  | succ k ih =>
    intro v hv
    rw [pow_succ, Module.End.mul_apply] at hv
    have hgg := ih (g v) hv
    have h0 : g v ⬝ᵥ g v = 0 := by rw [hg, hgg, dotProduct_zero]
    exact dotProduct_self_eq_zero.1 h0

/-- For a real symmetric matrix, the multiplicity of `κ` as a root of the characteristic polynomial is the dimension
of the `κ`-eigenspace. -/
lemma rootMult_eq_finrank {N : Matrix (Fin n) (Fin n) ℝ} (hN : Nᵀ = N) (κ : ℝ) :
    N.charpoly.rootMultiplicity κ = Module.finrank ℝ (Module.End.eigenspace (toLin' N) κ) := by
  have hle : Module.End.maxGenEigenspace (toLin' N) κ ≤ Module.End.eigenspace (toLin' N) κ := by
    intro v hv
    rw [Module.End.mem_maxGenEigenspace] at hv
    obtain ⟨k, hk⟩ := hv
    have hg : ∀ a b, (toLin' N - κ • (1 : Module.End ℝ (Vec n))) a ⬝ᵥ b =
        a ⬝ᵥ (toLin' N - κ • (1 : Module.End ℝ (Vec n))) b := by
      intro a b
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, toLin'_apply, sub_dotProduct,
        dotProduct_sub, smul_dotProduct, dotProduct_smul]
      rw [dotProduct_mulVec a N b, ← mulVec_transpose, hN]
    have h := symm_pow_ker _ hg k v hk
    rw [Module.End.mem_eigenspace_iff]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
    exact h
  have h1 := LinearMap.finrank_maxGenEigenspace_eq (toLin' N) κ
  have h2 := LinearMap.finrank_eigenspace_le (toLin' N) κ
  have h3 := Submodule.finrank_mono hle
  rw [Matrix.charpoly_toLin'] at h1 h2
  omega

/-- A real symmetric matrix: its characteristic polynomial is the product over its roots. -/
lemma charpoly_roots_prod {N : Matrix (Fin n) (Fin n) ℝ} (hN : Nᵀ = N) :
    (N.charpoly.roots.map fun a => X - C a).prod = N.charpoly := by
  have hH : N.IsHermitian := by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hN]
  refine prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic N) ?_
  rw [hH.roots_charpoly_eq_eigenvalues, Multiset.card_map, Finset.card_val, Finset.card_univ,
    charpoly_natDegree_eq_dim]

/-- Real symmetric matrices with the same eigenspace dimensions have the same characteristic polynomial. -/
lemma charpoly_eq_of_finrank {N N' : Matrix (Fin n) (Fin n) ℝ} (hN : Nᵀ = N) (hN' : N'ᵀ = N')
    (h : ∀ κ, Module.finrank ℝ (Module.End.eigenspace (toLin' N) κ) =
      Module.finrank ℝ (Module.End.eigenspace (toLin' N') κ)) : N.charpoly = N'.charpoly := by
  classical
  have hr : N.charpoly.roots = N'.charpoly.roots := by
    ext κ
    rw [count_roots, count_roots, rootMult_eq_finrank hN, rootMult_eq_finrank hN', h κ]
  rw [← charpoly_roots_prod hN, ← charpoly_roots_prod hN', hr]

lemma eigenspace_smul {N : Matrix (Fin n) (Fin n) ℝ} {q : ℝ} (hq : q ≠ 0) (κ : ℝ) :
    Module.End.eigenspace (toLin' (q • N)) κ = Module.End.eigenspace (toLin' N) (κ / q) := by
  ext v
  rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, toLin'_apply, toLin'_apply, smul_mulVec]
  constructor
  · intro hv
    calc N *ᵥ v = q⁻¹ • (q • (N *ᵥ v)) := by rw [smul_smul, inv_mul_cancel₀ hq, one_smul]
      _ = (κ / q) • v := by rw [hv, smul_smul, div_eq_inv_mul]
  · intro hv
    rw [hv, smul_smul]
    congr 1
    field_simp

end symm

/-- An orthonormal frame `M_X` (`M_XᵀM_X = I`) has at most `16` columns. -/
lemma nu_le {ν : ℕ} {MX : Matrix (Fin 16) (Fin ν) ℝ} (hMX : MXᵀ * MX = 1) : ν ≤ 16 := by
  have hinj : Function.Injective (toLin' MX) := by
    intro a b hab
    rw [toLin'_apply, toLin'_apply] at hab
    calc a = (MXᵀ * MX) *ᵥ a := by rw [hMX, one_mulVec]
      _ = (MXᵀ * MX) *ᵥ b := by rw [← mulVec_mulVec, hab, mulVec_mulVec]
      _ = b := by rw [hMX, one_mulVec]
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

/-- `χ(q M_X diag(μ) M_Xᵀ) = t^{16-ν} ∏ (t - qμ_i)` for an orthonormal frame `M_X`. -/
lemma frame_charpoly {ν : ℕ} (μ : Fin ν → ℝ) (MX : Matrix (Fin 16) (Fin ν) ℝ) (hMX : MXᵀ * MX = 1) (q : ℝ) :
    (q • (MX * diagonal μ * MXᵀ)).charpoly = X ^ (16 - ν) * ∏ i, (X - C (q * μ i)) := by
  have e : q • (MX * diagonal μ * MXᵀ) = MX * (diagonal (fun i => q * μ i) * MXᵀ) := by
    have hd : diagonal (fun i => q * μ i) = q • diagonal μ := by
      ext i j
      by_cases h : i = j <;> simp [h]
    rw [hd, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rw [e, charpoly_mul_comm_of_le _ _ (by simpa using nu_le hMX), Fintype.card_fin, Fintype.card_fin,
    Matrix.mul_assoc, hMX, Matrix.mul_one, charpoly_diagonal]

/-! ### The Osserman transfer: `χ(J'_z) = t^{16-ν} ∏ (t - |z|²μ_i)` for every real `z` -/

section osserman

variable (R : CurvTensor 16) (μ0 : ℝ)

/-- At a unit `x`, the `κ`-eigenspace of `J'_x` for `κ ≠ 0` is the reduced eigenspace `E_{κ+μ₀}(x)`. -/
lemma Jsh_eigenspace (x : Vec 16) (hx : x ⬝ᵥ x = 1) {κ : ℝ} (hκ : κ ≠ 0) :
    Module.End.eigenspace (toLin' (Jsh R μ0 x)) κ = Spectral.Esp R x (κ + μ0) := by
  ext v
  rw [Module.End.mem_eigenspace_iff, toLin'_apply, Spectral.mem_Esp]
  constructor
  · intro hv
    have hxv : x ⬝ᵥ v = 0 := by
      have h := Jsh_dot R μ0 x x v
      rw [hv, Jsh_self, zero_dotProduct, dotProduct_smul, smul_eq_mul] at h
      exact (mul_eq_zero.1 h).resolve_left hκ
    refine ⟨?_, hxv⟩
    rw [Jsh_mulVec, hx, one_smul, dotProduct_comm v x, hxv, zero_smul, sub_zero] at hv
    rw [add_smul, ← hv]
    abel
  · rintro ⟨hop, hxv⟩
    rw [Jsh_mulVec, hop, hx, one_smul, dotProduct_comm v x, hxv, zero_smul, sub_zero, add_smul,
      add_sub_cancel_right]

/-- Osserman: the eigenspace dimensions of `J'_x` are the same at all unit `x`. -/
lemma Jsh_finrank_eq (hO : R.IsOsserman) (x y : Vec 16) (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1) (κ : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace (toLin' (Jsh R μ0 x)) κ) =
      Module.finrank ℝ (Module.End.eigenspace (toLin' (Jsh R μ0 y)) κ) := by
  by_cases hκ : κ = 0
  · subst hκ
    rw [Module.End.eigenspace_zero, Module.End.eigenspace_zero]
    have hrk : ∀ z : Vec 16, Module.finrank ℝ (LinearMap.range (toLin' (Jsh R μ0 z))) +
        Module.finrank ℝ (LinearMap.ker (toLin' (Jsh R μ0 z))) = 16 := fun z => by
      have h := LinearMap.finrank_range_add_finrank_ker (toLin' (Jsh R μ0 z))
      rwa [Module.finrank_fin_fun] at h
    have h1 := Jsh_rank R μ0 x hx rfl
    have h2 := Jsh_rank R μ0 y hy rfl
    rw [hO x y hx hy μ0] at h1
    unfold Matrix.rank at h1 h2
    rw [← Matrix.toLin'_apply'] at h1 h2
    have := hrk x
    have := hrk y
    omega
  · rw [Jsh_eigenspace R μ0 x hx hκ, Jsh_eigenspace R μ0 y hy hκ]
    exact hO x y hx hy (κ + μ0)

/-- `χ(J'_z) = χ(|z|² J'_X)` for every real `z` and unit `X` (Osserman; `J'_{tx} = t²J'_x`). -/
lemma Jsh_charpoly_scale (hO : R.IsOsserman) (Xa : Vec 16) (hXa : Xa ⬝ᵥ Xa = 1) (z : Vec 16) :
    (Jsh R μ0 z).charpoly = ((z ⬝ᵥ z) • Jsh R μ0 Xa).charpoly := by
  by_cases hz : z = 0
  · subst hz
    have h := Jsh_smul R μ0 0 0
    rw [zero_smul, zero_mul, zero_smul] at h
    rw [h, zero_dotProduct, zero_smul]
  · have hq : 0 < z ⬝ᵥ z := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (z i))
      (fun e => hz (dotProduct_self_eq_zero.mp e.symm))
    obtain ⟨c, hc0, hcc⟩ : ∃ c : ℝ, 0 < c ∧ c * c = z ⬝ᵥ z :=
      ⟨Real.sqrt _, Real.sqrt_pos.2 hq, Real.mul_self_sqrt hq.le⟩
    have hu : (c⁻¹ • z) ⬝ᵥ (c⁻¹ • z) = 1 := by
      rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← hcc]
      field_simp
    have hJ := Jsh_smul R μ0 c (c⁻¹ • z)
    rw [smul_smul, mul_inv_cancel₀ hc0.ne', one_smul, hcc] at hJ
    rw [hJ]
    refine charpoly_eq_of_finrank (by rw [transpose_smul, Jsh_transpose])
      (by rw [transpose_smul, Jsh_transpose]) fun κ => ?_
    rw [eigenspace_smul hq.ne', eigenspace_smul hq.ne']
    exact Jsh_finrank_eq R μ0 hO _ _ hu hXa _

end osserman

/-- `χ(J'_z) = t^{16-ν} ∏ (t - |z|²μ_i)` for every real `z`, from the eigenframe at `X`. -/
lemma Jsh_charpoly (R : CurvTensor 16) (hO : R.IsOsserman) (μ0 : ℝ) {ν : ℕ} (μ : Fin ν → ℝ) (Xa : Vec 16)
    (hXa : Xa ⬝ᵥ Xa = 1) (MX : Matrix (Fin 16) (Fin ν) ℝ) (hMX : MXᵀ * MX = 1)
    (hfac : R.jacobi Xa - μ0 • Osserman.Pi Xa = MX * diagonal μ * MXᵀ) (z : Vec 16) :
    (Jsh R μ0 z).charpoly = X ^ (16 - ν) * ∏ i, (X - C ((z ⬝ᵥ z) * μ i)) := by
  have hJ : Jsh R μ0 Xa = MX * diagonal μ * MXᵀ := hfac
  rw [Jsh_charpoly_scale R μ0 hO Xa hXa z, hJ]
  exact frame_charpoly μ MX hMX _

/-! ### The universal shifted Jacobi matrix over `ℝ[z_0, …, z_15]` -/

/-- `jacAlg` commutes with ring maps. -/
lemma jacAlg_map {A B : Type*} [CommRing A] [CommRing B] (R : CurvTensor 16) (μ0 : ℝ) (φ : ℝ →+* A)
    (z : Fin 16 → A) (g : A →+* B) : (jacAlg R μ0 φ z).map g = jacAlg R μ0 (g.comp φ) (g ∘ z) := by
  ext j k
  simp only [jacAlg, Matrix.map_apply, Matrix.of_apply, map_sub, map_mul, map_sum, RingHom.comp_apply,
    Function.comp_apply]
  split_ifs <;> simp

/-- The universal shifted Jacobi matrix `J'_z` with polynomial coordinates `z`. -/
noncomputable def Juniv (R : CurvTensor 16) (μ0 : ℝ) : Matrix (Fin 16) (Fin 16) (MvPolynomial (Fin 16) ℝ) :=
  jacAlg R μ0 MvPolynomial.C MvPolynomial.X

lemma Juniv_eval (R : CurvTensor 16) (μ0 : ℝ) (z : Vec 16) :
    (Juniv R μ0).map (MvPolynomial.eval z) = Jsh R μ0 z := by
  rw [Juniv, jacAlg_map]
  show _ = R.jacobi z - μ0 • Osserman.Pi z
  rw [← jacAlg_real_proved]
  congr 1
  · exact RingHom.ext fun r => by simp
  · funext a
    simp

/-- The target `t^{16-ν} ∏ (t - μ_i |z|²)` over `ℝ[z_0, …, z_15]` (one term, so that every use shares its
instances). -/
noncomputable def univTarget {ν : ℕ} (μ : Fin ν → ℝ) : Polynomial (MvPolynomial (Fin 16) ℝ) :=
  X ^ (16 - ν) * ∏ i, (X - C (MvPolynomial.C (μ i) * sqP 16))

/-- The image of `t^{16-ν} ∏ (t - μ_i |z|²)` under evaluation at a real `z`. -/
lemma univ_target_eval {ν : ℕ} (μ : Fin ν → ℝ) (z : Vec 16) :
    (univTarget μ).map (MvPolynomial.eval z) = X ^ (16 - ν) * ∏ i, (X - C ((z ⬝ᵥ z) * μ i)) := by
  rw [univTarget]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_C]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  simp only [map_mul, MvPolynomial.eval_C, sqP, map_sum, MvPolynomial.eval_X, dotProduct, pow_two]
  ring

/-- Polynomials over `ℝ[z_0, …, z_15]` that agree after evaluation at every real `z` are equal. (Stated for
arbitrary `P, Q`: applying `Polynomial.ext` directly to `(Juniv R μ0).charpoly` overflows the kernel's recursion.) -/
lemma polyEq_of_eval (P Q : Polynomial (MvPolynomial (Fin 16) ℝ))
    (h : ∀ z : Fin 16 → ℝ, P.map (MvPolynomial.eval z) = Q.map (MvPolynomial.eval z)) : P = Q := by
  refine Polynomial.ext fun k => MvPolynomial.funext fun z => ?_
  rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, h z]

lemma Juniv_charpoly_eval (R : CurvTensor 16) (hO : R.IsOsserman) (μ0 : ℝ) {ν : ℕ} (μ : Fin ν → ℝ)
    (Xa : Vec 16) (hXa : Xa ⬝ᵥ Xa = 1) (MX : Matrix (Fin 16) (Fin ν) ℝ) (hMX : MXᵀ * MX = 1)
    (hfac : R.jacobi Xa - μ0 • Osserman.Pi Xa = MX * diagonal μ * MXᵀ) (z : Vec 16) :
    (Juniv R μ0).charpoly.map (MvPolynomial.eval z) = X ^ (16 - ν) * ∏ i, (X - C ((z ⬝ᵥ z) * μ i)) := by
  rw [← charpoly_map, Juniv_eval]
  exact Jsh_charpoly R hO μ0 μ Xa hXa MX hMX hfac z

/-- `χ(J'_z) = t^{16-ν} ∏ (t - μ_i |z|²)` as an identity of polynomials in `(z, t)`. -/
lemma Juniv_charpoly (R : CurvTensor 16) (hO : R.IsOsserman) (μ0 : ℝ) {ν : ℕ} (μ : Fin ν → ℝ) (Xa : Vec 16)
    (hXa : Xa ⬝ᵥ Xa = 1) (MX : Matrix (Fin 16) (Fin ν) ℝ) (hMX : MXᵀ * MX = 1)
    (hfac : R.jacobi Xa - μ0 • Osserman.Pi Xa = MX * diagonal μ * MXᵀ) :
    (Juniv R μ0).charpoly = univTarget μ :=
  polyEq_of_eval _ _ fun z => (Juniv_charpoly_eval R hO μ0 μ Xa hXa MX hMX hfac z).trans (univ_target_eval μ z).symm

/-! ### The spectral pencil -/

theorem thm_G_spectral_pencil_proved (R : CurvTensor 16) (hO : R.IsOsserman) (μ0 : ℝ) {ν : ℕ} (μ : Fin ν → ℝ)
    (_hμ : ∀ i, μ i ≠ 0) (Xa : Vec 16) (f : Fin 15 → Vec 16) (MX : Matrix (Fin 16) (Fin ν) ℝ)
    (MY : Matrix (Fin 16) (Fin ν) RatF15) (hP : IsRationalPartner R μ0 (diagonal μ) Xa f MX MY) :
    SpectralPencil μ (Phi1 MX MY) (Phi0 MY) := by
  obtain ⟨hXa, hXf, hf, hMX, hfac, hpen⟩ := hP
  set ψ : MvPolynomial (Fin 16) ℝ →+* Polynomial RatF15 :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp ofRealF) (pointS Xa f) with hψ
  have hψC : ∀ r, ψ (MvPolynomial.C r) = Polynomial.C (ofRealF r) := fun r => by
    rw [hψ, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
  have hψX : ∀ a, ψ (MvPolynomial.X a) = pointS Xa f a := fun a => by
    rw [hψ, MvPolynomial.eval₂Hom_X']
  have hU : (Juniv R μ0).map ψ = jacAlg R μ0 (Polynomial.C.comp ofRealF) (pointS Xa f) := by
    rw [Juniv, jacAlg_map]
    congr 1
    · exact RingHom.ext fun r => by rw [RingHom.comp_apply, hψC, RingHom.comp_apply]
    · funext a
      rw [Function.comp_apply, hψX]
  have hsq : ψ (sqP 16) = Polynomial.X ^ 2 + Polynomial.C dF := by
    rw [sqP, map_sum]
    simp only [map_pow, hψX]
    exact thm_G_q_pointS_proved Xa f hXa hXf hf
  have hle : Fintype.card (Fin ν) ≤ Fintype.card (Fin 16) := by simpa using nu_le hMX
  have hchi : (factorS MX MY * ((diagonal μ).map (Polynomial.C.comp ofRealF) * (factorS MX MY)ᵀ)).charpoly =
      X ^ (16 - ν) * ∏ i, (X - C (Polynomial.C (ofRealF (μ i)) * (Polynomial.X ^ 2 + Polynomial.C dF))) := by
    rw [← Matrix.mul_assoc, ← hpen, ← hU, charpoly_map, Juniv_charpoly R hO μ0 μ Xa hXa MX hMX hfac, univTarget]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_C, map_mul, hsq, hψC]
  rw [charpoly_mul_comm_of_le _ _ hle, Fintype.card_fin, Fintype.card_fin, Matrix.mul_assoc,
    (thm_G_gram_pencil_proved MX MY hMX).1] at hchi
  have hX : (X ^ (16 - ν) : Polynomial (Polynomial RatF15)) ≠ 0 := pow_ne_zero _ X_ne_zero
  unfold SpectralPencil
  rw [mul_left_cancel₀ hX hchi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_comm]

end Osserman.Proofs.Six4

