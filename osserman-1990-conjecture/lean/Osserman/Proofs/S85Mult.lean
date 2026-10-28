/-
S85Mult.lean — §8.5 of paper 013 (sec_small_roots.tex of the posting copy, lines 267-275): the multiplicities of the endpoint
`R - CR_J` when (eq:linearcombination) mixes `μ_1, μ_2` (row s8_5_endpoint_mult).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Premise row (leading argument with its exact type): s8_move_frame (`MoveFrameHyp` below).
Proof. At a unit `x` the fields give an orthonormal frame `p_0 = P_1(x)`, `p_1 = P_2(x)` of eigenvectors of `μ_1, μ_2`
and `Jx = c_1p_0 + c_2p_1` (so `J` is skew). `J_x(R') = J_x - C(Jx)(Jx)ᵀ` keeps every old eigenvector of an eigenvalue
other than `μ_1, μ_2` (it is orthogonal to the frame), and on the frame it is the block
`diag(μ_1, μ_2) - C(c_1,c_2)(c_1,c_2)ᵀ`, whose characteristic polynomial is `(t - z)(t - θ)` (rows s8_5_char_eq,
s8_5_theta): a root gives an eigenvector in the frame plane, and a double root makes the block scalar. These lower
bounds add up to `15 = M + N + 1 + 1 + 1`; the eigenspaces of `R'` are independent in `x^⊥`, so they are the
multiplicities, coincidences included. `R'` is Osserman by the premise row (constant frame coordinates).
-/
import Osserman.Proofs.S85Fields
import Osserman.Proofs.S85Alg
import Osserman.Proofs.S83Endpoint
import Osserman.Proofs.Lem82DivQ

namespace Osserman.Proofs.S85

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Tools Osserman.Proofs.S83

/-- The type of row `s8_move_frame`. -/
abbrev MoveFrameHyp : Prop :=
  ∀ {k : ℕ} (R : CurvTensor 16) (_hO : R.IsOsserman) (F : Fin k → Vec 16 → Vec 16) (μ : Fin k → ℝ)
    (_hF : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i, F i x ∈ Module.End.eigenspace (R.jacobiMap x) (μ i) ⊓ perp x)
    (_hFo : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i l, F i x ⬝ᵥ F l x = if i = l then 1 else 0)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (cJ : Fin k → ℝ)
    (_hJ : ∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x = ∑ i, cJ i • F i x) (Cc : ℝ),
    ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - Cc • RJfun J u v z) ∧ R'.IsOsserman

/-! ### Counting: lower bounds that fill `x^⊥` are the multiplicities -/

/-- If `∑_k [ν = t_k] d_k ≤ mult(ν)` for every `ν` and `∑ d_k = 15`, these are the multiplicities. -/
lemma mult_of_lower {K : ℕ} (R' : CurvTensor 16) {x : Vec 16} (hx : x ⬝ᵥ x = 1) (t : Fin K → ℝ) (d : Fin K → ℕ)
    (hd : ∑ k, d k = 15) (hlow : ∀ ν, (∑ k, if ν = t k then d k else 0) ≤ R'.redMult x ν) (ν : ℝ) :
    R'.redMult x ν = ∑ k, if ν = t k then d k else 0 := by
  classical
  let S : Finset ℝ := insert ν (Finset.univ.image t)
  have hW : iSupIndep (Spectral.Esp R' x) :=
    (Module.End.eigenspaces_iSupIndep (R'.jacobiMap x)).mono fun _ => inf_le_left
  have hle : (⨆ μ ∈ S, Spectral.Esp R' x μ) ≤ perp x := iSup₂_le fun _ _ => inf_le_right
  have h1 := Submodule.finrank_mono hle
  rw [CorD.finrank_biSup_eq hW] at h1
  have hp := Spectral.finrank_perp hx
  have hred : ∑ μ ∈ S, Module.finrank ℝ ↥(Spectral.Esp R' x μ) = ∑ μ ∈ S, R'.redMult x μ := rfl
  have hc : ∑ μ ∈ S, (∑ k, if μ = t k then d k else 0) = 15 := by
    rw [Finset.sum_comm, ← hd]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_ite_eq']
    simp [S]
  have heq : ∑ μ ∈ S, (∑ k, if μ = t k then d k else 0) = ∑ μ ∈ S, R'.redMult x μ :=
    le_antisymm (Finset.sum_le_sum fun μ _ => hlow μ) (by omega)
  exact ((Finset.sum_eq_sum_iff_of_le fun μ _ => hlow μ).mp heq ν (Finset.mem_insert_self _ _)).symm

/-- Two orthogonal subspaces of one eigenspace: their dimensions add. -/
lemma lower_of_pieces {R' : CurvTensor 16} {x : Vec 16} {ν : ℝ} {Old New : Submodule ℝ (Vec 16)}
    (hO : Old ≤ Spectral.Esp R' x ν) (hN : New ≤ Spectral.Esp R' x ν)
    (horth : ∀ y ∈ Old, ∀ f ∈ New, y ⬝ᵥ f = 0) :
    Module.finrank ℝ ↥Old + Module.finrank ℝ ↥New ≤ R'.redMult x ν := by
  have hinf : Old ⊓ New = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hy
    exact (Submodule.mem_bot ℝ).mpr (dotProduct_self_eq_zero.mp (horth y h1 y h2))
  have h := Submodule.finrank_sup_add_finrank_inf_eq Old New
  rw [hinf, finrank_bot, add_zero] at h
  have hle := Submodule.finrank_mono (sup_le hO hN)
  have hr : Module.finrank ℝ ↥(Spectral.Esp R' x ν) = R'.redMult x ν := rfl
  omega

/-- A `2 × 2` symmetric system of determinant zero has a nonzero solution. -/
lemma ker2 (a b e : ℝ) (h : a * e - b ^ 2 = 0) :
    ∃ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) ∧ a * α + b * β = 0 ∧ b * α + e * β = 0 := by
  by_cases hab : a = 0 ∧ b = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hab.1, hab.2], by simp [hab.2]⟩
  · refine ⟨b, -a, ?_, by ring, by linear_combination (-1 : ℝ) * h⟩
    rcases not_and_or.mp hab with ha | hb
    · exact Or.inr (neg_ne_zero.mpr ha)
    · exact Or.inl hb

/-! ### The frame at a unit `x` -/

section Frame

variable {R R' : CurvTensor 16} {x p0 p1 : Vec 16} {μ1 μ2 C c1 c2 : ℝ}

/-- A frame vector whose coordinates solve the block system for `t` is a reduced eigenvector of `R'`. -/
lemma new_eig2 (hjac : ∀ y, R'.jacobi x *ᵥ y = R.jacobi x *ᵥ y - C • (((c1 • p0 + c2 • p1) ⬝ᵥ y) • (c1 • p0 + c2 • p1)))
    (hA0 : R.jacobi x *ᵥ p0 = μ1 • p0) (hA1 : R.jacobi x *ᵥ p1 = μ2 • p1) (h00 : p0 ⬝ᵥ p0 = 1)
    (h11 : p1 ⬝ᵥ p1 = 1) (h01 : p0 ⬝ᵥ p1 = 0) (hp0x : x ⬝ᵥ p0 = 0) (hp1x : x ⬝ᵥ p1 = 0) (t α β : ℝ)
    (e1 : (μ1 - C * c1 ^ 2 - t) * α + -(C * c1 * c2) * β = 0)
    (e2 : -(C * c1 * c2) * α + (μ2 - C * c2 ^ 2 - t) * β = 0) :
    α • p0 + β • p1 ∈ Spectral.Esp R' x t := by
  have h10 : p1 ⬝ᵥ p0 = 0 := by rw [dotProduct_comm]; exact h01
  have hdot : (c1 • p0 + c2 • p1) ⬝ᵥ (α • p0 + β • p1) = c1 * α + c2 * β := by
    simp only [dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul, h00, h11, h01, h10, smul_eq_mul]
    ring
  refine Submodule.mem_inf.mpr ⟨(mem_eig_iff R' x _ _).mpr ?_, ?_⟩
  · rw [hjac, hdot, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hA0, hA1]
    match_scalars
    · linear_combination e1
    · linear_combination e2
  · show x ⬝ᵥ (α • p0 + β • p1) = 0
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hp0x, hp1x, smul_zero, smul_zero, add_zero]

/-- Old reduced eigenvectors of `ν ≠ μ_1, μ_2` are orthogonal to the frame and stay eigenvectors of `R'`. -/
lemma old_at (hjac : ∀ y, R'.jacobi x *ᵥ y = R.jacobi x *ᵥ y - C • (((c1 • p0 + c2 • p1) ⬝ᵥ y) • (c1 • p0 + c2 • p1)))
    (hA0 : R.jacobi x *ᵥ p0 = μ1 • p0) (hA1 : R.jacobi x *ᵥ p1 = μ2 • p1) {ν : ℝ} (h1 : ν ≠ μ1) (h2 : ν ≠ μ2) :
    Spectral.Esp R x ν ≤ Spectral.Esp R' x ν ∧ ∀ y ∈ Spectral.Esp R x ν, y ⬝ᵥ p0 = 0 ∧ y ⬝ᵥ p1 = 0 := by
  have orth : ∀ y ∈ Spectral.Esp R x ν, y ⬝ᵥ p0 = 0 ∧ y ⬝ᵥ p1 = 0 := fun y hy =>
    ⟨esp_dot_eig h1 hy hA0, esp_dot_eig h2 hy hA1⟩
  refine ⟨fun y hy => ?_, orth⟩
  obtain ⟨a0, a1⟩ := orth y hy
  have hyu : (c1 • p0 + c2 • p1) ⬝ᵥ y = 0 := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_comm p0, dotProduct_comm p1, a0, a1]
    simp
  have hy2 := Submodule.mem_inf.mp hy
  refine Submodule.mem_inf.mpr ⟨(mem_eig_iff R' x _ _).mpr ?_, hy2.2⟩
  rw [hjac, hyu, zero_smul, smul_zero, sub_zero]
  exact (mem_eig_iff R x y ν).mp hy2.1

/-- The new part: a subspace of the frame plane inside the `ν`-eigenspace of `R'`, of dimension at least
`[ν = z] + [ν = θ]`. -/
lemma new_part (hjac : ∀ y, R'.jacobi x *ᵥ y = R.jacobi x *ᵥ y - C • (((c1 • p0 + c2 • p1) ⬝ᵥ y) • (c1 • p0 + c2 • p1)))
    (hA0 : R.jacobi x *ᵥ p0 = μ1 • p0) (hA1 : R.jacobi x *ᵥ p1 = μ2 • p1) (h00 : p0 ⬝ᵥ p0 = 1)
    (h11 : p1 ⬝ᵥ p1 = 1) (h01 : p0 ⬝ᵥ p1 = 0) (hp0x : x ⬝ᵥ p0 = 0) (hp1x : x ⬝ᵥ p1 = 0)
    (hc : c1 ^ 2 + c2 ^ 2 = 1) {z θ : ℝ}
    (hchar : ∀ t, (μ1 - t) * (μ2 - t) - C * ((μ1 * c2 ^ 2 + μ2 * c1 ^ 2) - t) = (t - z) * (t - θ)) (ν : ℝ) :
    ∃ New : Submodule ℝ (Vec 16), New ≤ Spectral.Esp R' x ν ∧
      (if ν = z then 1 else 0) + (if ν = θ then 1 else 0) ≤ Module.finrank ℝ ↥New ∧
      ∀ f ∈ New, ∃ α β : ℝ, f = α • p0 + β • p1 := by
  have h10 : p1 ⬝ᵥ p0 = 0 := by rw [dotProduct_comm]; exact h01
  have fd0 (α β : ℝ) : (α • p0 + β • p1) ⬝ᵥ p0 = α := by
    simp only [add_dotProduct, smul_dotProduct, h00, h10, smul_eq_mul]; ring
  have fd1 (α β : ℝ) : (α • p0 + β • p1) ⬝ᵥ p1 = β := by
    simp only [add_dotProduct, smul_dotProduct, h11, h01, smul_eq_mul]; ring
  have hp0 : p0 ≠ 0 := fun e => by rw [e, zero_dotProduct] at h00; exact zero_ne_one h00
  have hp1 : p1 ≠ 0 := fun e => by rw [e, zero_dotProduct] at h11; exact zero_ne_one h11
  -- one eigenvector for a root `t` of the characteristic polynomial
  have one (t : ℝ) (ht : (t - z) * (t - θ) = 0) :
      ∃ New : Submodule ℝ (Vec 16), New ≤ Spectral.Esp R' x t ∧ 1 ≤ Module.finrank ℝ ↥New ∧
        ∀ f ∈ New, ∃ α β : ℝ, f = α • p0 + β • p1 := by
    have hdet : (μ1 - C * c1 ^ 2 - t) * (μ2 - C * c2 ^ 2 - t) - (-(C * c1 * c2)) ^ 2 = 0 := by
      linear_combination hchar t + ht + (C * t) * hc
    obtain ⟨α, β, hne, e1, e2⟩ := ker2 _ _ _ hdet
    have hf := new_eig2 hjac hA0 hA1 h00 h11 h01 hp0x hp1x t α β e1 e2
    have hf0 : α • p0 + β • p1 ≠ 0 := by
      intro e
      rcases hne with hα | hβ
      · exact hα (by rw [← fd0 α β, e, zero_dotProduct])
      · exact hβ (by rw [← fd1 α β, e, zero_dotProduct])
    refine ⟨Submodule.span ℝ {α • p0 + β • p1}, (Submodule.span_singleton_le_iff_mem _ _).mpr hf,
      (finrank_span_singleton hf0).ge, fun f hfm => ?_⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hfm
    exact ⟨r * α, r * β, by rw [smul_add, smul_smul, smul_smul]⟩
  by_cases hz' : ν = z <;> by_cases hθ' : ν = θ
  · -- a double root: the block is `ν • 1`, the whole frame plane is in the eigenspace
    have c0 := hchar 0
    have c1' := hchar 1
    have cν := hchar ν
    rw [← hz', ← hθ'] at c0 c1'
    rw [← hz', ← hθ', sub_self, zero_mul] at cν
    have htr : μ1 + μ2 - C = 2 * ν := by linarith
    have hae : (μ1 - C * c1 ^ 2 - ν) + (μ2 - C * c2 ^ 2 - ν) = 0 := by linear_combination htr - C * hc
    have hdet : (μ1 - C * c1 ^ 2 - ν) * (μ2 - C * c2 ^ 2 - ν) - (C * c1 * c2) ^ 2 = 0 := by
      linear_combination cν + (C * ν) * hc
    have hsq : (μ1 - C * c1 ^ 2 - ν) ^ 2 + (C * c1 * c2) ^ 2 = 0 := by
      linear_combination (-1 : ℝ) * hdet + (μ1 - C * c1 ^ 2 - ν) * hae
    have A0 : μ1 - C * c1 ^ 2 - ν = 0 := by
      nlinarith [sq_nonneg (μ1 - C * c1 ^ 2 - ν), sq_nonneg (C * c1 * c2)]
    have B0 : C * c1 * c2 = 0 := by nlinarith [sq_nonneg (μ1 - C * c1 ^ 2 - ν), sq_nonneg (C * c1 * c2)]
    have E0 : μ2 - C * c2 ^ 2 - ν = 0 := by linarith
    have m0 : p0 ∈ Spectral.Esp R' x ν := by
      have := new_eig2 hjac hA0 hA1 h00 h11 h01 hp0x hp1x ν 1 0 (by linear_combination A0)
        (by linear_combination (-1 : ℝ) * B0)
      simpa using this
    have m1 : p1 ∈ Spectral.Esp R' x ν := by
      have := new_eig2 hjac hA0 hA1 h00 h11 h01 hp0x hp1x ν 0 1 (by linear_combination (-1 : ℝ) * B0)
        (by linear_combination E0)
      simpa using this
    have hspan : Submodule.span ℝ {p0, p1} = Submodule.span ℝ {p0} ⊔ Submodule.span ℝ {p1} := by
      rw [Submodule.span_insert]
    have hdim : Module.finrank ℝ ↥(Submodule.span ℝ {p0} ⊔ Submodule.span ℝ {p1}) = 2 := by
      rw [dim_add_one hp1 fun y hy => ?_, finrank_span_singleton hp0]
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [smul_dotProduct, h01, smul_zero]
    refine ⟨Submodule.span ℝ {p0, p1}, Submodule.span_le.mpr (Set.insert_subset_iff.mpr ⟨m0,
      Set.singleton_subset_iff.mpr m1⟩), by rw [ite_eq_left hz', ite_eq_left hθ', hspan, hdim], fun f hf => ?_⟩
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hf
    exact ⟨α, β, rfl⟩
  · obtain ⟨New, h1, h2, h3⟩ := one ν (by rw [hz', sub_self, zero_mul])
    exact ⟨New, h1, by rw [ite_eq_left hz', ite_eq_right hθ']; omega, h3⟩
  · obtain ⟨New, h1, h2, h3⟩ := one ν (by rw [hθ', sub_self, mul_zero])
    exact ⟨New, h1, by rw [ite_eq_right hz', ite_eq_left hθ']; omega, h3⟩
  · refine ⟨⊥, bot_le, by rw [ite_eq_right hz', ite_eq_right hθ']; omega, fun f hf => ⟨0, 0, ?_⟩⟩
    rw [(Submodule.mem_bot ℝ).mp hf, zero_smul, zero_smul, add_zero]

end Frame

/-! ### The row -/

/-- **§8.5** (lines 267-275), row `s8_5_endpoint_mult`. -/
theorem s8_5_endpoint_mult_proved (hFrame : MoveFrameHyp) (R : CurvTensor 16) (M N : ℕ)
    (hMN : (M = 7 ∧ N = 5) ∨ (M = 8 ∧ N = 4))
    (ev : Fin 5 → ℝ) (hR : PatternEv R ![M, N, 1, 1, 1] ev) (h0 : ev 0 = 0)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (hP : ∀ (i : Fin 2) (x : Vec 16), evalField (P i) x ⬝ᵥ evalField (P i) x = (x ⬝ᵥ x) ^ 3)
    (hPe : IsEigenfield R (ev 2) (P 0) ∧ IsEigenfield R (ev 3) (P 1)) (c1 c2 : ℝ) (hc : c1 ^ 2 + c2 ^ 2 = 1)
    (J : Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : ∀ x : Vec 16, c1 • evalField (P 0) x + c2 • evalField (P 1) x = (x ⬝ᵥ x) • (J *ᵥ x))
    (z : ℝ) (_hz : z = 0 ∨ z = ev 1) (hdz : ev 2 * c2 ^ 2 + ev 3 * c1 ^ 2 ≠ z) :
    let d := ev 2 * c2 ^ 2 + ev 3 * c1 ^ 2
    let Cc := (ev 2 - z) * (ev 3 - z) / (d - z)
    let θ := ev 2 + ev 3 - Cc - z
    ∃ R' : CurvTensor 16, (∀ u v w, R'.op u v w = R.op u v w - Cc • RJfun J u v w) ∧ R'.IsOsserman ∧
      (0 ≠ ev 1 ∧ 0 ≠ ev 4 ∧ ev 1 ≠ ev 4) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ ν : ℝ, R'.redMult x ν =
        (if ν = 0 then M else 0) + (if ν = ev 1 then N else 0) + (if ν = ev 4 then 1 else 0) +
          (if ν = z then 1 else 0) + (if ν = θ then 1 else 0) := by
  intro d Cc θ
  obtain ⟨hsum, -⟩ := pattern_facts5 hMN
  have hMNs : M + N + 3 = 15 := by rcases hMN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hsum16 : ∑ i, (![M, N, 1, 1, 1] : Fin 5 → ℕ) i + 1 = 16 := by omega
  have hO : R.IsOsserman := (CorD.hasPattern_osserman_proved R _ hsum16 ⟨ev, hR⟩).1
  have hne (i j : Fin 5) (hij : i ≠ j) : ev i ≠ ev j := fun e => hij (hR.1 e)
  have e01 : (0 : ℝ) ≠ ev 1 := h0 ▸ hne 0 1 (by decide)
  have e04 : (0 : ℝ) ≠ ev 4 := h0 ▸ hne 0 4 (by decide)
  have e14 : ev 1 ≠ ev 4 := hne 1 4 (by decide)
  have hchar : ∀ t, (ev 2 - t) * (ev 3 - t) - Cc * (d - t) = (t - z) * (t - θ) :=
    s8_5_theta_proved (ev 2) (ev 3) d z hdz
  -- the frame at a unit `x`
  have frame (x : Vec 16) (hx : x ⬝ᵥ x = 1) :
      evalField (P 0) x ∈ Spectral.Esp R x (ev 2) ∧ evalField (P 1) x ∈ Spectral.Esp R x (ev 3) ∧
        R.jacobi x *ᵥ evalField (P 0) x = ev 2 • evalField (P 0) x ∧
        R.jacobi x *ᵥ evalField (P 1) x = ev 3 • evalField (P 1) x ∧
        evalField (P 0) x ⬝ᵥ evalField (P 0) x = 1 ∧ evalField (P 1) x ⬝ᵥ evalField (P 1) x = 1 ∧
        evalField (P 0) x ⬝ᵥ evalField (P 1) x = 0 ∧ x ⬝ᵥ evalField (P 0) x = 0 ∧ x ⬝ᵥ evalField (P 1) x = 0 ∧
        J *ᵥ x = c1 • evalField (P 0) x + c2 • evalField (P 1) x := by
    have m0 := hPe.1 x
    have m1 := hPe.2 x
    rw [hx, mul_one] at m0 m1
    have e2 := (mem_eig_iff R x _ _).mp (Submodule.mem_inf.mp m0).1
    have e3 := (mem_eig_iff R x _ _).mp (Submodule.mem_inf.mp m1).1
    have e := hJ x
    rw [hx, one_smul] at e
    exact ⟨m0, m1, e2, e3, by rw [hP 0 x, hx]; norm_num, by rw [hP 1 x, hx]; norm_num,
      esp_dot_eig (hne 2 3 (by decide)) m0 e3, (Submodule.mem_inf.mp m0).2, (Submodule.mem_inf.mp m1).2, e.symm⟩
  -- `J` is skew: `Jx` is a combination of fields orthogonal to `x`
  have hJs : Jᵀ = -J := Lem82DivQ.skew_of_forall fun x => by
    by_cases hx0 : x = 0
    · simp [hx0]
    have hq : x ⬝ᵥ x ≠ 0 := fun h => hx0 (dotProduct_self_eq_zero.mp h)
    have t0 : x ⬝ᵥ evalField (P 0) x = 0 := (Submodule.mem_inf.mp (hPe.1 x)).2
    have t1 : x ⬝ᵥ evalField (P 1) x = 0 := (Submodule.mem_inf.mp (hPe.2 x)).2
    have e := congrArg (· ⬝ᵥ x) (hJ x)
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at e
    rw [dotProduct_comm (evalField (P 0) x), dotProduct_comm (evalField (P 1) x), t0, t1] at e
    have h2 : (x ⬝ᵥ x) * ((J *ᵥ x) ⬝ᵥ x) = 0 := by linarith
    exact (mul_eq_zero.mp h2).resolve_left hq
  -- the tensor `R - CR_J`, Osserman by the premise row
  obtain ⟨R', hR', hO'⟩ := hFrame R hO (fun i x => evalField (P i) x) ![ev 2, ev 3]
    (fun x hx i => by
      fin_cases i
      · exact (frame x hx).1
      · exact (frame x hx).2.1)
    (fun x hx i l => by
      obtain ⟨-, -, -, -, n0, n1, o01, -⟩ := frame x hx
      have o10 : evalField (P 1) x ⬝ᵥ evalField (P 0) x = 0 := by rw [dotProduct_comm]; exact o01
      fin_cases i <;> fin_cases l <;> simp [n0, n1, o01, o10])
    J ![c1, c2] (fun x hx => by
      simp only [Fin.sum_univ_two]
      exact (frame x hx).2.2.2.2.2.2.2.2.2)
    Cc
  have hjac (x : Vec 16) (hx : x ⬝ᵥ x = 1) (y : Vec 16) :
      R'.jacobi x *ᵥ y = R.jacobi x *ᵥ y - Cc • (((c1 • evalField (P 0) x + c2 • evalField (P 1) x) ⬝ᵥ y) •
        (c1 • evalField (P 0) x + c2 • evalField (P 1) x)) := by
    rw [(Rem72a.rem_7_2_jac_split_proved R R' J hJs Cc hR' x).1, Matrix.add_mulVec, Matrix.smul_mulVec,
      Rem72a.jfam_mulVec, (frame x hx).2.2.2.2.2.2.2.2.2]
    abel
  have hsplit (ν : ℝ) :
      (∑ k, if ν = (![0, ev 1, ev 4, z, θ] : Fin 5 → ℝ) k then (![M, N, 1, 1, 1] : Fin 5 → ℕ) k else 0) =
        (if ν = 0 then M else 0) + (if ν = ev 1 then N else 0) + (if ν = ev 4 then 1 else 0) +
          (if ν = z then 1 else 0) + (if ν = θ then 1 else 0) := by
    rw [Fin.sum_univ_five]
    rfl
  -- the lower bounds at a unit `x`
  have count (x : Vec 16) (hx : x ⬝ᵥ x = 1) (ν : ℝ) :
      (∑ k, if ν = (![0, ev 1, ev 4, z, θ] : Fin 5 → ℝ) k then (![M, N, 1, 1, 1] : Fin 5 → ℕ) k else 0) ≤
        R'.redMult x ν := by
    obtain ⟨-, -, hA0, hA1, h00, h11, h01, hp0x, hp1x, -⟩ := frame x hx
    have hold : ∃ Old : Submodule ℝ (Vec 16), Old ≤ Spectral.Esp R' x ν ∧
        Module.finrank ℝ ↥Old = (if ν = 0 then M else 0) + (if ν = ev 1 then N else 0) + (if ν = ev 4 then 1 else 0) ∧
        ∀ y ∈ Old, y ⬝ᵥ evalField (P 0) x = 0 ∧ y ⬝ᵥ evalField (P 1) x = 0 := by
      by_cases h23 : ν = ev 2 ∨ ν = ev 3
      · refine ⟨⊥, bot_le, ?_, fun y hy => ?_⟩
        · rw [finrank_bot]
          rcases h23 with rfl | rfl
          · simp [h0 ▸ hne 2 0 (by decide), hne 2 1 (by decide), hne 2 4 (by decide)]
          · simp [h0 ▸ hne 3 0 (by decide), hne 3 1 (by decide), hne 3 4 (by decide)]
        · rw [(Submodule.mem_bot ℝ).mp hy, zero_dotProduct, zero_dotProduct]
          exact ⟨rfl, rfl⟩
      · obtain ⟨n2, n3⟩ := not_or.mp h23
        obtain ⟨hle, horth⟩ := old_at (hjac x hx) hA0 hA1 n2 n3
        refine ⟨_, hle, ?_, horth⟩
        have hm := hR.2 x hx
        show R.redMult x ν = _
        by_cases a0 : ν = 0
        · subst a0
          have := hm 0
          rw [h0] at this
          rw [this]
          simp [e01, e04]
        by_cases a1 : ν = ev 1
        · subst a1
          rw [hm 1]
          simp [e01.symm, e14]
        by_cases a4 : ν = ev 4
        · subst a4
          rw [hm 4]
          simp [e04.symm, e14.symm]
        rw [CorD.redMult_other R hR.1 hsum16 hx hm (μ := ν) fun i => by
          fin_cases i
          exacts [h0 ▸ a0, a1, n2, n3, a4]]
        simp [a0, a1, a4]
    obtain ⟨Old, hOle, hOdim, hOorth⟩ := hold
    obtain ⟨New, hNle, hNdim, hNV⟩ := new_part (hjac x hx) hA0 hA1 h00 h11 h01 hp0x hp1x hc hchar ν
    have horth : ∀ y ∈ Old, ∀ f ∈ New, y ⬝ᵥ f = 0 := fun y hy f hf => by
      obtain ⟨α, β, rfl⟩ := hNV f hf
      obtain ⟨a0, a1⟩ := hOorth y hy
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, a0, a1, smul_zero, smul_zero, add_zero]
    have hlow := lower_of_pieces hOle hNle horth
    rw [hsplit]
    omega
  refine ⟨R', hR', hO', ⟨e01, e04, e14⟩, fun x hx ν => ?_⟩
  rw [mult_of_lower R' hx ![0, ev 1, ev 4, z, θ] ![M, N, 1, 1, 1] (by simp [Fin.sum_univ_five]; omega) (count x hx) ν,
    hsplit]

end Osserman.Proofs.S85
