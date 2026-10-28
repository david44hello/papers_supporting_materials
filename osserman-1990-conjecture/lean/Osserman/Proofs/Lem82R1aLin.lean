/-
Lem82R1aLin.lean — Lemma 8.2, proof, case r = 1, the linear-algebra rows (paper 013, sec_small_roots.tex lines
120-124): "A quadratic form divisible by a linear form has rank at most two and vanishes at a nonzero vector of every
plane, so it is definite on no plane; as every eigenvalue of the symmetric matrix I + C̃² has even multiplicity,
I + C̃² = 0, and C̃ is orthogonal."
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route. (1) `x ⬝ Mq x = ⟨f,x⟩ g(x)` vanishes on `f^⊥`; polarization (Mq symmetric) gives `Mq (f^⊥) ⊆ span f`, so
`range Mq ⊆ span {f, Mq f}`; every subspace of dimension `≥ 2` meets `f^⊥ = ker ⟨f,·⟩` (dimension count).
(2) Even dimension: if `S` is skew, `S V ⊆ V` and `S` is injective on `V`, the matrix `N = Bᵀ S B` of a basis `B` of
`V` is skew and nonsingular, so `det N = (-1)^d det N` forces `d` even. For `μ ≠ 1`, `V` = the eigenspace; for `μ = 1`
the eigenspace is `ker S` (as `|Sx|² = -⟨x, S²x⟩`), and `dim ker S = 16 - dim range S` with `V = range S`.
(3) A nonzero symmetric matrix has an eigenvector with eigenvalue `t ≠ 0` (Mathlib, spectral theorem); its eigenspace
has even dimension `≥ 2`, so it holds `v ≠ 0` with `⟨f,v⟩ = 0`, and `v ⬝ Mq v = t |v|² ≠ 0`, a contradiction.
-/
import Osserman.Proofs.Lem82Common

namespace Osserman.Proofs.Lem82R1a

open Osserman Matrix MvPolynomial Osserman.Proofs.Lem82Common

/-! ### Evaluation and dot-product facts -/

/-- `⟨u, Mw⟩ = ⟨Mᵀu, w⟩`. -/
lemma dot_mulVec (M : Matrix (Fin 16) (Fin 16) ℝ) (u w : Vec 16) :
    u ⬝ᵥ (M *ᵥ w) = (Mᵀ *ᵥ u) ⬝ᵥ w := by
  rw [dotProduct_mulVec, mulVec_transpose]

/-- `⟨u, Sw⟩ = -⟨Su, w⟩` for skew `S`. -/
lemma skew_dot {S : Matrix (Fin 16) (Fin 16) ℝ} (hS : Sᵀ = -S) (u w : Vec 16) :
    u ⬝ᵥ (S *ᵥ w) = -((S *ᵥ u) ⬝ᵥ w) := by
  rw [dot_mulVec, hS, neg_mulVec, neg_dotProduct]

/-- For skew `S`, `S²x = 0` implies `Sx = 0` (as `|Sx|² = -⟨S²x, x⟩`). -/
lemma skew_eq_zero_of_sq {S : Matrix (Fin 16) (Fin 16) ℝ} (hS : Sᵀ = -S) {x : Vec 16}
    (h : S *ᵥ (S *ᵥ x) = 0) : S *ᵥ x = 0 := by
  apply dotProduct_self_eq_zero.mp
  rw [skew_dot hS, h, zero_dotProduct, neg_zero]

/-! ### Row 1: a quadratic form divisible by a linear form -/

/-- The quadratic form vanishes on `f^⊥`. -/
lemma quad_zero_of_perp {f : Vec 16} {Mq : Matrix (Fin 16) (Fin 16) ℝ} (hdiv : formP f ∣ quadP Mq)
    {v : Vec 16} (hv : f ⬝ᵥ v = 0) : v ⬝ᵥ (Mq *ᵥ v) = 0 := by
  obtain ⟨g, hg⟩ := hdiv
  have h := congrArg (eval v) hg
  rw [eval_quadP, map_mul, eval_formP, hv, zero_mul, dotProduct_comm] at h
  exact h

/-- Polarization: `⟨y, Mq x⟩ = 0` for `x, y ∈ f^⊥`. -/
lemma bilin_zero_of_perp {f : Vec 16} {Mq : Matrix (Fin 16) (Fin 16) ℝ} (hM : Mqᵀ = Mq)
    (hdiv : formP f ∣ quadP Mq) {x y : Vec 16} (hx : f ⬝ᵥ x = 0) (hy : f ⬝ᵥ y = 0) :
    y ⬝ᵥ (Mq *ᵥ x) = 0 := by
  have hxy : f ⬝ᵥ (x + y) = 0 := by rw [dotProduct_add, hx, hy, add_zero]
  have h1 := quad_zero_of_perp hdiv hxy
  have h2 := quad_zero_of_perp hdiv hx
  have h3 := quad_zero_of_perp hdiv hy
  have hsym : x ⬝ᵥ (Mq *ᵥ y) = y ⬝ᵥ (Mq *ᵥ x) := by
    rw [dot_mulVec, hM, dotProduct_comm]
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, h2, h3, hsym] at h1
  linarith

/-- `Mq` maps `f^⊥` into `span f`. -/
lemma mulVec_eq_smul_of_perp {f : Vec 16} (hf : f ≠ 0) {Mq : Matrix (Fin 16) (Fin 16) ℝ} (hM : Mqᵀ = Mq)
    (hdiv : formP f ∣ quadP Mq) {x : Vec 16} (hx : f ⬝ᵥ x = 0) :
    Mq *ᵥ x = ((f ⬝ᵥ (Mq *ᵥ x)) / (f ⬝ᵥ f)) • f := by
  have hff : f ⬝ᵥ f ≠ 0 := fun h => hf (dotProduct_self_eq_zero.mp h)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (f ⬝ᵥ (Mq *ᵥ x)) / (f ⬝ᵥ f) := ⟨_, rfl⟩
  rw [← hc]
  have hyf : f ⬝ᵥ (Mq *ᵥ x - c • f) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hc, div_mul_cancel₀ _ hff, sub_self]
  have hyz : (Mq *ᵥ x - c • f) ⬝ᵥ (Mq *ᵥ x) = 0 := bilin_zero_of_perp hM hdiv hx hyf
  have hyy : (Mq *ᵥ x - c • f) ⬝ᵥ (Mq *ᵥ x - c • f) = 0 := by
    rw [dotProduct_sub (Mq *ᵥ x - c • f), dotProduct_smul, hyz, smul_eq_mul, dotProduct_comm _ f, hyf]
    ring
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hyy)

/-- `rank Mq ≤ 2`: `range Mq ⊆ span {f, Mq f}`. -/
lemma rank_le_two {f : Vec 16} (hf : f ≠ 0) {Mq : Matrix (Fin 16) (Fin 16) ℝ} (hM : Mqᵀ = Mq)
    (hdiv : formP f ∣ quadP Mq) : Mq.rank ≤ 2 := by
  have hff : f ⬝ᵥ f ≠ 0 := fun h => hf (dotProduct_self_eq_zero.mp h)
  have hle : LinearMap.range Mq.mulVecLin ≤ Submodule.span ℝ (Set.range ![f, Mq *ᵥ f]) := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (f ⬝ᵥ x) / (f ⬝ᵥ f) := ⟨_, rfl⟩
    have hx' : f ⬝ᵥ (x - t • f) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ht, div_mul_cancel₀ _ hff, sub_self]
    have hdec : Mq *ᵥ x = Mq *ᵥ (x - t • f) + t • (Mq *ᵥ f) := by
      rw [mulVec_sub, mulVec_smul]
      abel
    rw [hdec, mulVec_eq_smul_of_perp hf hM hdiv hx']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp⟩))
  calc Mq.rank = Module.finrank ℝ (LinearMap.range Mq.mulVecLin) := rfl
    _ ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range ![f, Mq *ᵥ f])) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin 2) := finrank_range_le_card _
    _ = 2 := Fintype.card_fin 2

/-- The linear form `x ↦ ⟨f, x⟩`. -/
noncomputable def dotForm (f : Vec 16) : Vec 16 →ₗ[ℝ] ℝ where
  toFun x := f ⬝ᵥ x
  map_add' x y := dotProduct_add f x y
  map_smul' c x := by simp [dotProduct_smul]

/-- Every subspace of dimension `≥ 2` contains a nonzero vector of `f^⊥` (dimension count). -/
lemma exists_perp_of_two_le (f : Vec 16) (W : Submodule ℝ (Vec 16)) (hW : 2 ≤ Module.finrank ℝ W) :
    ∃ v ∈ W, v ≠ 0 ∧ f ⬝ᵥ v = 0 := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (dotForm f)
  rw [Module.finrank_fin_fun] at hrk
  have hr1 : Module.finrank ℝ (LinearMap.range (dotForm f)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (dotForm f))
    rwa [Module.finrank_self] at this
  have hsup : Module.finrank ℝ ↥(W ⊔ LinearMap.ker (dotForm f)) ≤ 16 := by
    have := Submodule.finrank_le (W ⊔ LinearMap.ker (dotForm f))
    rwa [Module.finrank_fin_fun] at this
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker (dotForm f))
  have hne : W ⊓ LinearMap.ker (dotForm f) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hsum
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Submodule.mem_inf] at hv
  exact ⟨v, hv.1, hv0, LinearMap.mem_ker.mp hv.2⟩

theorem quad_div_linear_proved (f : Vec 16) (hf : f ≠ 0) (Mq : Matrix (Fin 16) (Fin 16) ℝ) (hM : Mqᵀ = Mq)
    (hdiv : formP f ∣ quadP Mq) :
    Mq.rank ≤ 2 ∧ ∀ W : Submodule ℝ (Vec 16), Module.finrank ℝ W = 2 →
      ∃ v ∈ W, v ≠ 0 ∧ v ⬝ᵥ (Mq *ᵥ v) = 0 := by
  refine ⟨rank_le_two hf hM hdiv, fun W hW => ?_⟩
  obtain ⟨v, hvW, hv0, hfv⟩ := exists_perp_of_two_le f W hW.ge
  exact ⟨v, hvW, hv0, quad_zero_of_perp hdiv hfv⟩

/-! ### Row 2: even multiplicities for `1 + S²`, `S` skew -/

section EvenDim

variable {V : Submodule ℝ (Vec 16)} {d : ℕ} (b : Module.Basis (Fin d) ℝ V)

/-- The `16 × d` matrix whose columns are the basis vectors. -/
noncomputable def basisMat : Matrix (Fin 16) (Fin d) ℝ := Matrix.of fun i k => (b k : Vec 16) i

lemma basisMat_mulVec (v : Fin d → ℝ) : basisMat b *ᵥ v = ∑ k, v k • (b k : Vec 16) := by
  ext i
  simp only [basisMat, mulVec, dotProduct, of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

lemma basisMat_mulVec_mem (v : Fin d → ℝ) : basisMat b *ᵥ v ∈ V := by
  rw [basisMat_mulVec]
  exact V.sum_mem fun k _ => V.smul_mem _ (b k).2

lemma exists_basisMat_mulVec {z : Vec 16} (hz : z ∈ V) : ∃ c, basisMat b *ᵥ c = z := by
  refine ⟨b.repr ⟨z, hz⟩, ?_⟩
  rw [basisMat_mulVec]
  have h := congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)
  rw [Submodule.coe_sum] at h
  simpa only [Submodule.coe_smul] using h

lemma basisMat_mulVec_inj {v : Fin d → ℝ} (h : basisMat b *ᵥ v = 0) : v = 0 := by
  rw [basisMat_mulVec] at h
  have h' : ∑ k, v k • b k = 0 := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_zero]
    simpa only [Submodule.coe_smul] using h
  funext k
  exact Fintype.linearIndependent_iff.mp b.linearIndependent v h' k

lemma basisMat_dot (c : Fin d → ℝ) (w : Vec 16) : (basisMat b *ᵥ c) ⬝ᵥ w = c ⬝ᵥ ((basisMat b)ᵀ *ᵥ w) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

end EvenDim

/-- A subspace `V` with `S V ⊆ V` on which a skew `S` is injective has even dimension: with `B` a basis matrix of `V`,
`N = Bᵀ S B` is skew and nonsingular, and `det N = det Nᵀ = (-1)^d det N`. -/
lemma even_finrank_of_skew_inj {S : Matrix (Fin 16) (Fin 16) ℝ} (hS : Sᵀ = -S) (V : Submodule ℝ (Vec 16))
    (hinv : ∀ y ∈ V, S *ᵥ y ∈ V) (hinj : ∀ y ∈ V, S *ᵥ y = 0 → y = 0) :
    Even (Module.finrank ℝ V) := by
  set d := Module.finrank ℝ V
  let b : Module.Basis (Fin d) ℝ V := Module.finBasis ℝ V
  let B := basisMat b
  let N := Bᵀ * S * B
  have hNt : Nᵀ = -N := by
    simp only [N, transpose_mul, transpose_transpose, hS, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hdet : N.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hNv⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have hNv' : Bᵀ *ᵥ (S *ᵥ (B *ᵥ v)) = 0 := by
      rw [mulVec_mulVec, mulVec_mulVec]
      exact hNv
    have hyV : B *ᵥ v ∈ V := basisMat_mulVec_mem b v
    obtain ⟨c, hc⟩ := exists_basisMat_mulVec b (hinv _ hyV)
    have hSy : S *ᵥ (B *ᵥ v) = 0 := by
      apply dotProduct_self_eq_zero.mp
      conv_lhs => arg 1; rw [← hc]
      rw [basisMat_dot, hNv', dotProduct_zero]
    exact hv0 (basisMat_mulVec_inj b (hinj _ hyV hSy))
  have h1 : N.det = (-1) ^ d * N.det :=
    calc N.det = Nᵀ.det := (det_transpose N).symm
      _ = (-N).det := by rw [hNt]
      _ = (-1) ^ d * N.det := by rw [det_neg, Fintype.card_fin]
  have h2 : ((-1 : ℝ)) ^ d = 1 := mul_right_cancel₀ hdet (by rw [one_mul]; exact h1.symm)
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h2

lemma mem_eig_iff' (S : Matrix (Fin 16) (Fin 16) ℝ) (μ : ℝ) (x : Vec 16) :
    x ∈ Module.End.eigenspace (Matrix.toLin' (1 + S * S)) μ ↔ (1 + S * S) *ᵥ x = μ • x := by
  rw [Module.End.mem_eigenspace_iff, toLin'_apply]

/-- The eigenspaces of `1 + S²` are `S`-invariant. -/
lemma eig_invariant (S : Matrix (Fin 16) (Fin 16) ℝ) (μ : ℝ) :
    ∀ y ∈ Module.End.eigenspace (Matrix.toLin' (1 + S * S)) μ,
      S *ᵥ y ∈ Module.End.eigenspace (Matrix.toLin' (1 + S * S)) μ := by
  intro y hy
  rw [mem_eig_iff'] at hy ⊢
  have hcomm : (1 + S * S) * S = S * (1 + S * S) := by
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.mul_assoc]
  rw [mulVec_mulVec, hcomm, ← mulVec_mulVec, hy, mulVec_smul]

/-- For `μ ≠ 1`, `S` is injective on the `μ`-eigenspace of `1 + S²`. -/
lemma eig_inj (S : Matrix (Fin 16) (Fin 16) ℝ) {μ : ℝ} (hμ : μ ≠ 1) :
    ∀ y ∈ Module.End.eigenspace (Matrix.toLin' (1 + S * S)) μ, S *ᵥ y = 0 → y = 0 := by
  intro y hy hSy
  rw [mem_eig_iff', add_mulVec, one_mulVec, ← mulVec_mulVec, hSy, mulVec_zero, add_zero] at hy
  have h : (1 - μ) • y = 0 := by rw [sub_smul, one_smul, ← hy, sub_self]
  exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (Ne.symm hμ))

/-- The `1`-eigenspace of `1 + S²` is `ker S`. -/
lemma eig_one_eq_ker {S : Matrix (Fin 16) (Fin 16) ℝ} (hS : Sᵀ = -S) :
    Module.End.eigenspace (Matrix.toLin' (1 + S * S)) 1 = LinearMap.ker (Matrix.toLin' S) := by
  ext x
  rw [mem_eig_iff', LinearMap.mem_ker, toLin'_apply, one_smul, add_mulVec, one_mulVec, ← mulVec_mulVec]
  constructor
  · intro h
    exact skew_eq_zero_of_sq hS (by simpa using h)
  · intro h
    rw [h, mulVec_zero, add_zero]

/-- `dim ker S` is even for skew `S` on `ℝ^16` (here `16` even is used). -/
lemma even_finrank_ker {S : Matrix (Fin 16) (Fin 16) ℝ} (hS : Sᵀ = -S) :
    Even (Module.finrank ℝ (LinearMap.ker (Matrix.toLin' S))) := by
  have hrk : Module.finrank ℝ (LinearMap.range (Matrix.toLin' S)) +
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' S)) = 16 := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' S)
    rwa [Module.finrank_fin_fun] at h
  have hinv : ∀ y ∈ LinearMap.range (Matrix.toLin' S), S *ᵥ y ∈ LinearMap.range (Matrix.toLin' S) :=
    fun y _ => LinearMap.mem_range.mpr ⟨y, toLin'_apply S y⟩
  have hinj : ∀ y ∈ LinearMap.range (Matrix.toLin' S), S *ᵥ y = 0 → y = 0 := by
    rintro _ ⟨z, rfl⟩ h
    rw [toLin'_apply] at h ⊢
    exact skew_eq_zero_of_sq hS h
  have hev : Even (Module.finrank ℝ (LinearMap.range (Matrix.toLin' S))) := even_finrank_of_skew_inj hS _ hinv hinj
  obtain ⟨m, hm⟩ := hev
  exact ⟨8 - m, by omega⟩

theorem skew16_even_mult_proved (S : Matrix (Fin 16) (Fin 16) ℝ) (hS : Sᵀ = -S) (μ : ℝ) :
    Even (Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' (1 + S * S)) μ)) := by
  by_cases hμ : μ = 1
  · subst hμ
    rw [eig_one_eq_ker hS]
    exact even_finrank_ker hS
  · exact even_finrank_of_skew_inj hS _ (eig_invariant S μ) (eig_inj S hμ)

/-! ### Row 3: `1 + S² = 0` -/

theorem lem_8_2_r1_orth_proved (S : Matrix (Fin 16) (Fin 16) ℝ) (hS : Sᵀ = -S) (f : Vec 16) (_hf : f ≠ 0)
    (hdiv : formP f ∣ quadP (1 + S * S)) : 1 + S * S = 0 ∧ Sᵀ * S = 1 := by
  have hA : 1 + S * S = 0 := by
    by_contra hne
    have hsym : (1 + S * S).IsHermitian := by
      rw [isHermitian_iff_isSymm]
      show (1 + S * S)ᵀ = 1 + S * S
      rw [transpose_add, transpose_one, transpose_mul, hS, neg_mul_neg]
    obtain ⟨v, t, ht, hv0, hAv⟩ := hsym.exists_eigenvector_of_ne_zero hne
    have hvE : v ∈ Module.End.eigenspace (Matrix.toLin' (1 + S * S)) t := (mem_eig_iff' S t v).mpr hAv
    have hpos : Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' (1 + S * S)) t) ≠ 0 := by
      intro h
      rw [Submodule.finrank_eq_zero] at h
      rw [h] at hvE
      exact hv0 ((Submodule.mem_bot ℝ).mp hvE)
    obtain ⟨m, hm⟩ := skew16_even_mult_proved S hS t
    obtain ⟨w, hwE, hw0, hfw⟩ := exists_perp_of_two_le f _ (by omega : 2 ≤ Module.finrank ℝ
      ↥(Module.End.eigenspace (Matrix.toLin' (1 + S * S)) t))
    have hq := quad_zero_of_perp hdiv hfw
    rw [(mem_eig_iff' S t w).mp hwE, dotProduct_smul, smul_eq_mul] at hq
    exact mul_ne_zero ht (fun h => hw0 (dotProduct_self_eq_zero.mp h)) hq
  refine ⟨hA, ?_⟩
  have hSS : S * S = -1 := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hA)
  rw [hS, Matrix.neg_mul, hSS, neg_neg]

end Osserman.Proofs.Lem82R1a

