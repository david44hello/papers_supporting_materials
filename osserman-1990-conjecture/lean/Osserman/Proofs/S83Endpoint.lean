/-
Osserman/Proofs/S83Endpoint.lean — §8.3 of paper 013, opposite signs: the endpoint `R - C R_J` (row s8_3_endpoint;
statement copied verbatim from Osserman/Paper/Statements8.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof. At a unit `x` let `p_0 = P_1(x)`, `p_1 = εP_2(x)` (orthonormal, eigenvalues `μ, σ`) and `u = Jx`, so that
`su = ap_0 - bp_1` with `s = √(a²+b²)`. Then `J_x(R') = J_x - C uuᵀ` fixes every old eigenvector of `0` and of `λ`
(they are orthogonal to `p_0, p_1`, hence to `u`), and in the frame it has the eigenvectors
`f_0 = ((μ-λ)/a)p_0 + ((σ-λ)/b)p_1` (eigenvalue `0`) and `f_λ = (μ/a)p_0 + (σ/b)p_1` (eigenvalue `λ`); this uses
`a² = μ(μ-λ)`, `b² = -σ(σ-λ)` and `C(μ-σ) = s²`. So the new eigenspaces contain `E_0 ⊕ ℝf_0` and `E_λ ⊕ ℝf_λ`, of
dimensions `M+1` and `N+1`; they are independent in `x^⊥`, of dimension `15 = (M+1)+(N+1)`, so equality holds. The
projection of `u` onto `E_0 ⊕ ℝf_0` is `(⟨u,f_0⟩/|f_0|²)f_0` (`u ⊥ E_0`), whose squared length
`⟨u,f_0⟩²/|f_0|²` is a constant (the frame coordinates are constants); likewise for `λ`.
-/
import Osserman.Proofs.S83Opp1
import Osserman.Proofs.S83Algebra

namespace Osserman.Proofs.S83

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Tools

section Frame

variable {R R' : CurvTensor 16} {x p0 p1 u : Vec 16} {μ σ C s a b : ℝ}

/-- A reduced eigenvector of `t` is orthogonal to an eigenvector of `ν ≠ t`. -/
lemma esp_dot_eig {t ν : ℝ} (hne : t ≠ ν) {y p : Vec 16} (hy : y ∈ Spectral.Esp R x t)
    (hp : R.jacobi x *ᵥ p = ν • p) : y ⬝ᵥ p = 0 := by
  have hy' := (mem_eig_iff R x y t).mp (Submodule.mem_inf.mp hy).1
  have sym : (R.jacobi x *ᵥ y) ⬝ᵥ p = y ⬝ᵥ (R.jacobi x *ᵥ p) := by
    rw [← Matrix.vecMul_transpose, Spectral.jacobi_transpose, ← Matrix.dotProduct_mulVec]
  rw [hy', hp, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at sym
  have h : (t - ν) * (y ⬝ᵥ p) = 0 := by linarith
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)

lemma u_eq (hs : s ≠ 0) (hu : s • u = a • p0 - b • p1) : u = s⁻¹ • (a • p0 - b • p1) := by
  rw [← hu, smul_smul, inv_mul_cancel₀ hs, one_smul]

lemma u_dot (h00 : p0 ⬝ᵥ p0 = 1) (h11 : p1 ⬝ᵥ p1 = 1) (h01 : p0 ⬝ᵥ p1 = 0) (hs : s ≠ 0)
    (hu : s • u = a • p0 - b • p1) (α β : ℝ) : u ⬝ᵥ (α • p0 + β • p1) = s⁻¹ * (a * α - b * β) := by
  have h10 : p1 ⬝ᵥ p0 = 0 := by rw [dotProduct_comm]; exact h01
  rw [u_eq hs hu]
  simp only [smul_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_smul, h00, h11, h01, h10, smul_eq_mul]
  ring

/-- The action of `J_x(R')` on the frame. -/
lemma frame_act (hjac : ∀ y, R'.jacobi x *ᵥ y = R.jacobi x *ᵥ y - C • ((u ⬝ᵥ y) • u))
    (hA0 : R.jacobi x *ᵥ p0 = μ • p0) (hA1 : R.jacobi x *ᵥ p1 = σ • p1) (h00 : p0 ⬝ᵥ p0 = 1)
    (h11 : p1 ⬝ᵥ p1 = 1) (h01 : p0 ⬝ᵥ p1 = 0) (hs : s ≠ 0) (hu : s • u = a • p0 - b • p1) (α β : ℝ) :
    R'.jacobi x *ᵥ (α • p0 + β • p1) =
      (α * μ - C * (s⁻¹ * (a * α - b * β)) * (s⁻¹ * a)) • p0 +
        (β * σ + C * (s⁻¹ * (a * α - b * β)) * (s⁻¹ * b)) • p1 := by
  rw [hjac, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hA0, hA1, u_dot h00 h11 h01 hs hu,
    u_eq hs hu]
  module

/-- A frame vector with the right coefficients is a reduced eigenvector of `R'`. -/
lemma new_eig (hjac : ∀ y, R'.jacobi x *ᵥ y = R.jacobi x *ᵥ y - C • ((u ⬝ᵥ y) • u))
    (hA0 : R.jacobi x *ᵥ p0 = μ • p0) (hA1 : R.jacobi x *ᵥ p1 = σ • p1) (h00 : p0 ⬝ᵥ p0 = 1)
    (h11 : p1 ⬝ᵥ p1 = 1) (h01 : p0 ⬝ᵥ p1 = 0) (hs : s ≠ 0) (hu : s • u = a • p0 - b • p1)
    (hp0x : x ⬝ᵥ p0 = 0) (hp1x : x ⬝ᵥ p1 = 0) (t α β : ℝ)
    (c0 : α * μ - C * (s⁻¹ * (a * α - b * β)) * (s⁻¹ * a) = t * α)
    (c1 : β * σ + C * (s⁻¹ * (a * α - b * β)) * (s⁻¹ * b) = t * β) :
    α • p0 + β • p1 ∈ Spectral.Esp R' x t := by
  refine Submodule.mem_inf.mpr ⟨(mem_eig_iff R' x _ _).mpr ?_, ?_⟩
  · rw [frame_act hjac hA0 hA1 h00 h11 h01 hs hu, c0, c1]
    module
  · show x ⬝ᵥ (α • p0 + β • p1) = 0
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hp0x, hp1x, smul_zero, smul_zero, add_zero]

/-- Old reduced eigenvectors of `t ≠ μ, σ` are orthogonal to the frame and to `u`, and stay eigenvectors. -/
lemma old_facts {t : ℝ} (ht0 : t ≠ μ) (ht1 : t ≠ σ) (hjac : ∀ y, R'.jacobi x *ᵥ y = R.jacobi x *ᵥ y - C • ((u ⬝ᵥ y) • u))
    (hA0 : R.jacobi x *ᵥ p0 = μ • p0) (hA1 : R.jacobi x *ᵥ p1 = σ • p1) (hs : s ≠ 0)
    (hu : s • u = a • p0 - b • p1) {y : Vec 16} (hy : y ∈ Spectral.Esp R x t) :
    (∀ α β : ℝ, y ⬝ᵥ (α • p0 + β • p1) = 0) ∧ y ⬝ᵥ u = 0 ∧ y ∈ Spectral.Esp R' x t := by
  have d0 := esp_dot_eig ht0 hy hA0
  have d1 := esp_dot_eig ht1 hy hA1
  have hf : ∀ α β : ℝ, y ⬝ᵥ (α • p0 + β • p1) = 0 := fun α β => by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, d0, d1, smul_zero, smul_zero, add_zero]
  have hyu : y ⬝ᵥ u = 0 := by
    rw [u_eq hs hu, dotProduct_smul, dotProduct_sub, dotProduct_smul, dotProduct_smul, d0, d1]
    simp
  have hy2 := Submodule.mem_inf.mp hy
  refine ⟨hf, hyu, Submodule.mem_inf.mpr ⟨(mem_eig_iff R' x _ _).mpr ?_, hy2.2⟩⟩
  rw [hjac, dotProduct_comm, hyu, zero_smul, smul_zero, sub_zero]
  exact (mem_eig_iff R x y t).mp hy2.1

end Frame

/-! ### Dimension and projection -/

lemma dim_add_one {E : Submodule ℝ (Vec 16)} {f : Vec 16} (hf : f ≠ 0) (horth : ∀ y ∈ E, y ⬝ᵥ f = 0) :
    Module.finrank ℝ ↥(E ⊔ Submodule.span ℝ {f}) = Module.finrank ℝ ↥E + 1 := by
  have hff : f ⬝ᵥ f ≠ 0 := fun h => hf (dotProduct_self_eq_zero.mp h)
  have hinf : E ⊓ Submodule.span ℝ {f} = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzE, hzf⟩ := Submodule.mem_inf.mp hz
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hzf
    have h := horth _ hzE
    rw [smul_dotProduct, smul_eq_mul] at h
    rw [(mul_eq_zero.mp h).resolve_right hff, zero_smul]
    exact Submodule.zero_mem _
  have h := Submodule.finrank_sup_add_finrank_inf_eq E (Submodule.span ℝ {f})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hf] at h
  exact h

lemma proj_new {E : Submodule ℝ (Vec 16)} {f u : Vec 16} (hf : f ≠ 0) (hE : ∀ y ∈ E, y ⬝ᵥ f = 0)
    (hEu : ∀ y ∈ E, y ⬝ᵥ u = 0) :
    IsOrthProj (E ⊔ Submodule.span ℝ {f}) u (((u ⬝ᵥ f) / (f ⬝ᵥ f)) • f) ∧
      (((u ⬝ᵥ f) / (f ⬝ᵥ f)) • f) ⬝ᵥ (((u ⬝ᵥ f) / (f ⬝ᵥ f)) • f) = (u ⬝ᵥ f) ^ 2 / (f ⬝ᵥ f) := by
  have hff : f ⬝ᵥ f ≠ 0 := fun h => hf (dotProduct_self_eq_zero.mp h)
  refine ⟨⟨Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f)), ?_⟩, ?_⟩
  · show ∀ w ∈ E ⊔ Submodule.span ℝ {f}, w ⬝ᵥ (u - ((u ⬝ᵥ f) / (f ⬝ᵥ f)) • f) = 0
    intro z hz
    obtain ⟨y, hy, z2, hz2, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hz2
    simp only [add_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, hEu y hy, hE y hy, smul_eq_mul]
    rw [dotProduct_comm f u]
    field_simp
    ring
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    field_simp

/-- Two new eigenvectors in the complement of the old eigenspaces fill `x^⊥`. -/
lemma endpoint_dims {R R' : CurvTensor 16} {x : Vec 16} (hx : x ⬝ᵥ x = 1) {t1 t2 : ℝ} (ht : t1 ≠ t2)
    {f1 f2 : Vec 16} (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0) (hf1e : f1 ∈ Spectral.Esp R' x t1)
    (hf2e : f2 ∈ Spectral.Esp R' x t2) (ho1 : ∀ y ∈ Spectral.Esp R x t1, y ⬝ᵥ f1 = 0)
    (ho2 : ∀ y ∈ Spectral.Esp R x t2, y ⬝ᵥ f2 = 0) (hle1 : Spectral.Esp R x t1 ≤ Spectral.Esp R' x t1)
    (hle2 : Spectral.Esp R x t2 ≤ Spectral.Esp R' x t2) {m1 m2 : ℕ} (hm1 : R.redMult x t1 = m1)
    (hm2 : R.redMult x t2 = m2) (hsum : m1 + m2 + 2 = 15) :
    R'.redMult x t1 = m1 + 1 ∧ R'.redMult x t2 = m2 + 1 ∧
      Spectral.Esp R' x t1 = Spectral.Esp R x t1 ⊔ Submodule.span ℝ {f1} ∧
      Spectral.Esp R' x t2 = Spectral.Esp R x t2 ⊔ Submodule.span ℝ {f2} := by
  have le1 : Spectral.Esp R x t1 ⊔ Submodule.span ℝ {f1} ≤ Spectral.Esp R' x t1 :=
    sup_le hle1 ((Submodule.span_singleton_le_iff_mem _ _).mpr hf1e)
  have le2 : Spectral.Esp R x t2 ⊔ Submodule.span ℝ {f2} ≤ Spectral.Esp R' x t2 :=
    sup_le hle2 ((Submodule.span_singleton_le_iff_mem _ _).mpr hf2e)
  have d1 := dim_add_one hf1 ho1
  have d2 := dim_add_one hf2 ho2
  have r1 : Module.finrank ℝ ↥(Spectral.Esp R x t1) = m1 := hm1
  have r2 : Module.finrank ℝ ↥(Spectral.Esp R x t2) = m2 := hm2
  have g1 := Submodule.finrank_mono le1
  have g2 := Submodule.finrank_mono le2
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (Spectral.Esp R' x t1) (Spectral.Esp R' x t2)
  rw [Spectral.Esp_inf R' x ht, finrank_bot, add_zero] at hsup
  have hle : Module.finrank ℝ ↥(Spectral.Esp R' x t1 ⊔ Spectral.Esp R' x t2) ≤ Module.finrank ℝ ↥(perp x) :=
    Submodule.finrank_mono (sup_le inf_le_right inf_le_right)
  have hp := Spectral.finrank_perp hx
  have e1 : Module.finrank ℝ ↥(Spectral.Esp R' x t1) = m1 + 1 := by omega
  have e2 : Module.finrank ℝ ↥(Spectral.Esp R' x t2) = m2 + 1 := by omega
  refine ⟨e1, e2, (Submodule.eq_of_le_of_finrank_eq le1 (by omega)).symm,
    (Submodule.eq_of_le_of_finrank_eq le2 (by omega)).symm⟩

/-! ### The row -/

/-- Row `s8_3_endpoint`. -/
theorem s8_3_endpoint_proved (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec83Data R M N ev P) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ha2 : a ^ 2 = ev 2 * (ev 2 - ev 1))
    (hb2 : b ^ 2 = -(ev 3 * (ev 3 - ev 1))) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (J : Matrix (Fin 16) (Fin 16) ℝ)
    (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (hJ : ∀ x : Vec 16, a • evalField (P 0) x - (ε * b) • evalField (P 1) x =
      (Real.sqrt (a ^ 2 + b ^ 2) * (x ⬝ᵥ x)) • (J *ᵥ x)) :
    ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - (ev 2 + ev 3 - ev 1) • RJfun J u v z) ∧
      PatternEv R' ![M + 1, N + 1] ![0, ev 1] ∧
      ∀ ℓ ∈ ({0, ev 1} : Set ℝ), ∃ c : ℝ, ∀ x : Vec 16, x ⬝ᵥ x = 1 →
        ∃ w, IsOrthProj (Module.End.eigenspace (R'.jacobiMap x) ℓ ⊓ perp x) (J *ᵥ x) w ∧ w ⬝ᵥ w = c := by
  -- names and scalar facts
  set μ := ev 2 with hμdef
  set σ := ev 3 with hσdef
  set lam := ev 1 with hlamdef
  set C := μ + σ - lam with hCdef
  set s := Real.sqrt (a ^ 2 + b ^ 2) with hsdef
  have hfacts := sec83_unit_facts h
  obtain ⟨hMN, hR, h0, -, -, he2, he3⟩ := h
  have hne (i j : Fin 4) (hij : i ≠ j) : ev i ≠ ev j := fun e => hij (hR.1 e)
  have hμ0 : μ ≠ 0 := by rw [← h0]; exact hne 2 0 (by decide)
  have hσ0 : σ ≠ 0 := by rw [← h0]; exact hne 3 0 (by decide)
  have hlam0 : lam ≠ 0 := by rw [← h0]; exact hne 1 0 (by decide)
  have hmulam : μ ≠ lam := hne 2 1 (by decide)
  have hsiglam : σ ≠ lam := hne 3 1 (by decide)
  have hμσ : μ ≠ σ := hne 2 3 (by decide)
  obtain ⟨hsum2, hC0⟩ := s8_3_C_ne_zero_proved lam μ σ a b hμσ ha hb ha2 hb2
  have hS : 0 < a ^ 2 + b ^ 2 := by positivity
  have hs0 : s ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  have hss : s * s = (μ - σ) * C := by rw [Real.mul_self_sqrt hS.le, hsum2]
  have hK : C * (μ - σ) * (s⁻¹ * s⁻¹) = 1 := by
    have hC0' : C ≠ 0 := hC0
    rw [← mul_inv, hss, mul_comm (μ - σ) C, mul_inv_cancel₀ (mul_ne_zero hC0' (sub_ne_zero.mpr hμσ))]
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
  have hib : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0
  -- the two new eigenvectors, as frame coordinates
  set α0 := (μ - lam) * a⁻¹
  set β0 := (σ - lam) * b⁻¹
  set αl := μ * a⁻¹
  set βl := σ * b⁻¹
  have hD0 : a * α0 - b * β0 = μ - σ := by linear_combination (μ - lam) * hia - (σ - lam) * hib
  have hDl : a * αl - b * βl = μ - σ := by linear_combination μ * hia - σ * hib
  have hcoef (D : ℝ) (hD : D = μ - σ) (z : ℝ) : C * (s⁻¹ * D) * (s⁻¹ * z) = z := by
    rw [hD]; linear_combination z * hK
  have c00 : α0 * μ - C * (s⁻¹ * (a * α0 - b * β0)) * (s⁻¹ * a) = 0 * α0 := by
    rw [hcoef _ hD0]; linear_combination (-a⁻¹) * ha2 + a * hia
  have c01 : β0 * σ + C * (s⁻¹ * (a * α0 - b * β0)) * (s⁻¹ * b) = 0 * β0 := by
    rw [hcoef _ hD0]; linear_combination (b⁻¹) * hb2 - b * hib
  have cl0 : αl * μ - C * (s⁻¹ * (a * αl - b * βl)) * (s⁻¹ * a) = lam * αl := by
    rw [hcoef _ hDl]; linear_combination (-a⁻¹) * ha2 + a * hia
  have cl1 : βl * σ + C * (s⁻¹ * (a * αl - b * βl)) * (s⁻¹ * b) = lam * βl := by
    rw [hcoef _ hDl]; linear_combination (b⁻¹) * hb2 - b * hib
  have hα0 : α0 ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hmulam) (inv_ne_zero ha0)
  have hαl : αl ≠ 0 := mul_ne_zero hμ0 (inv_ne_zero ha0)
  -- the tensor `R' = R - C R_J`
  obtain ⟨-, B, hBop, hBjac⟩ := Rem72a.RJ_curv_proved J hJs
  obtain ⟨R', hR'B⟩ := Rem72a.exists_sub R B C
  have hR' : ∀ u v z, R'.op u v z = R.op u v z - C • RJfun J u v z := fun u v z => by rw [hR'B, hBop]
  have hjac (x y : Vec 16) : R'.jacobi x *ᵥ y = R.jacobi x *ᵥ y - C • (((J *ᵥ x) ⬝ᵥ y) • (J *ᵥ x)) := by
    rw [(Rem72a.rem_7_2_jac_split_proved R R' J hJs C hR' x).1, Matrix.add_mulVec, Matrix.smul_mulVec,
      Rem72a.jfam_mulVec]
    abel
  -- the frame at a unit `x`
  have frame (x : Vec 16) (hx : x ⬝ᵥ x = 1) :
      R.jacobi x *ᵥ evalField (P 0) x = μ • evalField (P 0) x ∧
        R.jacobi x *ᵥ (ε • evalField (P 1) x) = σ • (ε • evalField (P 1) x) ∧
        evalField (P 0) x ⬝ᵥ evalField (P 0) x = 1 ∧ (ε • evalField (P 1) x) ⬝ᵥ (ε • evalField (P 1) x) = 1 ∧
        evalField (P 0) x ⬝ᵥ (ε • evalField (P 1) x) = 0 ∧ x ⬝ᵥ evalField (P 0) x = 0 ∧
        x ⬝ᵥ (ε • evalField (P 1) x) = 0 ∧ s • (J *ᵥ x) = a • evalField (P 0) x - b • (ε • evalField (P 1) x) := by
    obtain ⟨n0, n1, o01, t0, t1⟩ := hfacts x
    rw [hx] at n0 n1
    have e2 := (mem_eig_iff R x _ _).mp (Submodule.mem_inf.mp (he2 x)).1
    have e3 := (mem_eig_iff R x _ _).mp (Submodule.mem_inf.mp (he3 x)).1
    rw [hx, mul_one] at e2 e3
    refine ⟨e2, by rw [Matrix.mulVec_smul, e3, smul_comm], by rw [n0]; norm_num, ?_, ?_, ?_, ?_, ?_⟩
    · rw [smul_dotProduct, dotProduct_smul, n1]; rcases hε with rfl | rfl <;> norm_num
    · rw [dotProduct_smul, o01, smul_zero]
    · rw [dotProduct_comm]; exact t0
    · rw [dotProduct_smul, dotProduct_comm, t1, smul_zero]
    · have e := hJ x
      rw [hx, mul_one] at e
      rw [← e, smul_smul, mul_comm b ε]
  have fdot (p0 p1 : Vec 16) (h00 : p0 ⬝ᵥ p0 = 1) (h11 : p1 ⬝ᵥ p1 = 1) (h01 : p0 ⬝ᵥ p1 = 0) (α β : ℝ) :
      (α • p0 + β • p1) ⬝ᵥ (α • p0 + β • p1) = α ^ 2 + β ^ 2 ∧ (α • p0 + β • p1) ⬝ᵥ p0 = α := by
    have h10 : p1 ⬝ᵥ p0 = 0 := by rw [dotProduct_comm]; exact h01
    constructor
    · simp only [dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul, h00, h11, h01, h10, smul_eq_mul]
      ring
    · simp only [add_dotProduct, smul_dotProduct, h00, h10, smul_eq_mul]; ring
  have hm0 (x : Vec 16) (hx : x ⬝ᵥ x = 1) : R.redMult x 0 = M := by simpa [h0] using hR.2 x hx 0
  have hml (x : Vec 16) (hx : x ⬝ᵥ x = 1) : R.redMult x lam = N := by simpa using hR.2 x hx 1
  have hMNs : M + N + 2 = 15 := by rcases hMN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  -- everything at a unit `x`
  have key (x : Vec 16) (hx : x ⬝ᵥ x = 1) :
      R'.redMult x 0 = M + 1 ∧ R'.redMult x lam = N + 1 ∧
        Spectral.Esp R' x 0 = Spectral.Esp R x 0 ⊔
          Submodule.span ℝ {α0 • evalField (P 0) x + β0 • (ε • evalField (P 1) x)} ∧
        Spectral.Esp R' x lam = Spectral.Esp R x lam ⊔
          Submodule.span ℝ {αl • evalField (P 0) x + βl • (ε • evalField (P 1) x)} ∧
        (∀ y ∈ Spectral.Esp R x 0, y ⬝ᵥ (α0 • evalField (P 0) x + β0 • (ε • evalField (P 1) x)) = 0 ∧
          y ⬝ᵥ (J *ᵥ x) = 0) ∧
        (∀ y ∈ Spectral.Esp R x lam, y ⬝ᵥ (αl • evalField (P 0) x + βl • (ε • evalField (P 1) x)) = 0 ∧
          y ⬝ᵥ (J *ᵥ x) = 0) := by
    obtain ⟨hA0, hA1, h00, h11, h01, hp0x, hp1x, hu⟩ := frame x hx
    have hj := hjac x
    have of0 := fun {y} (hy : y ∈ Spectral.Esp R x 0) =>
      old_facts hμ0.symm hσ0.symm hj hA0 hA1 hs0 hu hy
    have ofl := fun {y} (hy : y ∈ Spectral.Esp R x lam) =>
      old_facts hmulam.symm hsiglam.symm hj hA0 hA1 hs0 hu hy
    have hf0 := new_eig hj hA0 hA1 h00 h11 h01 hs0 hu hp0x hp1x 0 α0 β0 c00 c01
    have hfl := new_eig hj hA0 hA1 h00 h11 h01 hs0 hu hp0x hp1x lam αl βl cl0 cl1
    have nz (α β : ℝ) (hα : α ≠ 0) : α • evalField (P 0) x + β • (ε • evalField (P 1) x) ≠ 0 := by
      intro e
      have := (fdot _ _ h00 h11 h01 α β).2
      rw [e, zero_dotProduct] at this
      exact hα this.symm
    obtain ⟨r0, rl, q0, ql⟩ := endpoint_dims hx hlam0.symm (nz α0 β0 hα0) (nz αl βl hαl) hf0 hfl
      (fun y hy => (of0 hy).1 α0 β0) (fun y hy => (ofl hy).1 αl βl) (fun y hy => (of0 hy).2.2)
      (fun y hy => (ofl hy).2.2) (hm0 x hx) (hml x hx) hMNs
    exact ⟨r0, rl, q0, ql, fun y hy => ⟨(of0 hy).1 α0 β0, (of0 hy).2.1⟩,
      fun y hy => ⟨(ofl hy).1 αl βl, (ofl hy).2.1⟩⟩
  refine ⟨R', hR', ⟨inj_comp hR.1 ![0, 1] (by decide) (by funext i; fin_cases i <;> simp [h0, hlamdef]),
    fun x hx i => ?_⟩, fun ℓ hℓ => ?_⟩
  · obtain ⟨r0, rl, -⟩ := key x hx
    fin_cases i
    · simpa using r0
    · simpa using rl
  · -- the projections
    have proj (α β : ℝ) (hα : α ≠ 0) (hD : a * α - b * β = μ - σ) (t : ℝ)
        (hEq : ∀ x : Vec 16, x ⬝ᵥ x = 1 → Spectral.Esp R' x t = Spectral.Esp R x t ⊔
          Submodule.span ℝ {α • evalField (P 0) x + β • (ε • evalField (P 1) x)})
        (hortho : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ y ∈ Spectral.Esp R x t,
          y ⬝ᵥ (α • evalField (P 0) x + β • (ε • evalField (P 1) x)) = 0 ∧ y ⬝ᵥ (J *ᵥ x) = 0) :
        ∃ c : ℝ, ∀ x : Vec 16, x ⬝ᵥ x = 1 →
          ∃ w, IsOrthProj (Module.End.eigenspace (R'.jacobiMap x) t ⊓ perp x) (J *ᵥ x) w ∧ w ⬝ᵥ w = c := by
      refine ⟨(s⁻¹ * (μ - σ)) ^ 2 / (α ^ 2 + β ^ 2), fun x hx => ?_⟩
      obtain ⟨-, -, h00, h11, h01, -, -, hu⟩ := frame x hx
      have hf : α • evalField (P 0) x + β • (ε • evalField (P 1) x) ≠ 0 := by
        intro e
        have := (fdot _ _ h00 h11 h01 α β).2
        rw [e, zero_dotProduct] at this
        exact hα this.symm
      obtain ⟨hp, hw⟩ := proj_new hf (fun y hy => (hortho x hx y hy).1) (fun y hy => (hortho x hx y hy).2)
      refine ⟨(((J *ᵥ x) ⬝ᵥ (α • evalField (P 0) x + β • (ε • evalField (P 1) x))) /
        ((α • evalField (P 0) x + β • (ε • evalField (P 1) x)) ⬝ᵥ (α • evalField (P 0) x + β • (ε • evalField (P 1) x)))) •
        (α • evalField (P 0) x + β • (ε • evalField (P 1) x)), ?_, ?_⟩
      · rw [show Module.End.eigenspace (R'.jacobiMap x) t ⊓ perp x = Spectral.Esp R' x t from rfl, hEq x hx]
        exact hp
      · rw [hw, u_dot h00 h11 h01 hs0 hu, hD, (fdot _ _ h00 h11 h01 α β).1]
    rcases hℓ with rfl | hℓ
    · exact proj α0 β0 hα0 hD0 0 (fun x hx => (key x hx).2.2.1) (fun x hx => (key x hx).2.2.2.2.1)
    · rw [Set.mem_singleton_iff] at hℓ
      subst hℓ
      exact proj αl βl hαl hDl lam (fun x hx => (key x hx).2.2.2.1) (fun x hx => (key x hx).2.2.2.2.2)

end Osserman.Proofs.S83
