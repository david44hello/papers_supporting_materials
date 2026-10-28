/-
Osserman/Proofs/Rem72a.lean — Remark 7.2 of paper 013, first part: the tensor `R_J`, the shift by `R_1`, the split
`J_x(R) = J_x(R - cR_J) + c(Jx)(Jx)ᵀ`, orthogonal changes of a Clifford structure, and the eigenspaces of a Clifford
form `J_x = λ_0Π(x) + ∑ η_α(J_αx)(J_αx)ᵀ` (rows RJ_curv, shift_R1, rem_7_2_jac_split, cliffordStr_orth_comb,
rem_7_2_block_rotation, rem_7_2_eigenspaces; statements copied verbatim from Osserman/Paper/Statements7.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Shared tools for the later parts: `cliff_dot` (`⟨J_αx, J_βx⟩ = δ_αβ|x|²`), `jac_apply_perp` (a Clifford form on
`x^⊥`), `eig_clifford` (its reduced eigenspaces: `span{J_αx : λ_0 + η_α = ℓ}`, plus `W(x) = x^⊥ ∩ ⋂_α (J_αx)^⊥` when
`ℓ = λ_0`) and `sum_smul_vecMulVec_comb` (a weighted sum of `(∑_β p_aβ v_β)(∑_β p_aβ v_β)ᵀ` in the `v_βv_γᵀ`).
-/
import Osserman.Defs.ThreeRoot
import Osserman.Proofs.Curv
import Osserman.Proofs.Spectral

namespace Osserman.Proofs.Rem72a

open Osserman Matrix

variable {n : ℕ}

/-! ### Skew matrices and the rank-one family `(Jx)(Jx)ᵀ` -/

lemma skew_dot_swap {J : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J) (x y : Vec n) :
    (J *ᵥ x) ⬝ᵥ y = -((J *ᵥ y) ⬝ᵥ x) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hJ, neg_mulVec, neg_dotProduct]

lemma skew_dot_self {J : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J) (x : Vec n) : x ⬝ᵥ (J *ᵥ x) = 0 := by
  have h := skew_dot_swap hJ x x
  rw [dotProduct_comm]
  linarith

lemma jfam_mulVec (J : Matrix (Fin n) (Fin n) ℝ) (x y : Vec n) :
    jfam J x *ᵥ y = ((J *ᵥ x) ⬝ᵥ y) • (J *ᵥ x) := by
  rw [jfam, vecMulVec_mulVec, op_smul_eq_smul]

lemma jfam_quad (J : Matrix (Fin n) (Fin n) ℝ) : IsQuadFamily (jfam J) := by
  refine ⟨fun a b => of fun i j => J i a * J j b, fun x => ?_⟩
  ext i j
  simp only [jfam, vecMulVec, mulVec, dotProduct, of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **Row RJ_curv.** -/
theorem RJ_curv_proved {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (hJ : Jᵀ = -J) :
    (IsQuadFamily (jfam J) ∧ (∀ x, (jfam J x)ᵀ = jfam J x) ∧ (∀ x, jfam J x *ᵥ x = 0) ∧
        ∀ x y : Vec n, ((J *ᵥ x) ⬝ᵥ y) ^ 2 = ((J *ᵥ y) ⬝ᵥ x) ^ 2) ∧
      ∃ R : CurvTensor n, (∀ u v w, R.op u v w = RJfun J u v w) ∧ ∀ x, R.jacobi x = jfam J x := by
  have hs : ∀ x, (jfam J x)ᵀ = jfam J x := fun x => transpose_vecMulVec _ _
  have hk : ∀ x, jfam J x *ᵥ x = 0 := fun x => by
    rw [jfam_mulVec, dotProduct_comm, skew_dot_self hJ, zero_smul]
  exact ⟨⟨jfam_quad J, hs, hk, fun x y => by rw [skew_dot_swap hJ x y, neg_sq]⟩,
    Curv.sec2_reconstruct_proved (jfam J) (jfam_quad J) hs hk⟩

/-! ### Differences of curvature tensors and the shift by `R_1` -/

lemma exists_sub (R S : CurvTensor n) (c : ℝ) :
    ∃ R0 : CurvTensor n, ∀ u v w, R0.op u v w = R.op u v w - c • S.op u v w := by
  refine Curv.exists_curv (fun u v w => R.op u v w - c • S.op u v w) (fun u u' v w => ?_) (fun a u v w => ?_)
    (fun u v v' w => ?_) (fun a u v w => ?_) (fun u v w w' => ?_) (fun a u v w => ?_) (fun u v w => ?_)
    (fun u v w z => ?_) (fun u v w => ?_)

  · simp only [map_add, LinearMap.add_apply]; module
  · simp only [map_smul, LinearMap.smul_apply]; module
  · simp only [map_add, LinearMap.add_apply]; module
  · simp only [map_smul, LinearMap.smul_apply]; module
  · simp only [map_add]; module
  · simp only [map_smul]; module
  · rw [R.antisymm u v w, S.antisymm u v w]; module
  · simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [R.skew u v w z, S.skew u v w z]
    ring
  · calc _ = (R.op u v w + R.op v w u + R.op w u v) - c • (S.op u v w + S.op v w u + S.op w u v) := by module
      _ = 0 := by rw [R.bianchi, S.bianchi, smul_zero, sub_zero]

lemma jacobiMap_eq_mulVec (R : CurvTensor n) (x y : Vec n) : R.jacobiMap x y = R.jacobi x *ᵥ y :=
  (Curv.jacobi_mulVec R x y).symm

lemma shift_apply {R R0 : CurvTensor n} {c : ℝ} (hR0 : ∀ u v w, R0.op u v w = R.op u v w - c • R1fun u v w)
    {x y : Vec n} (hx : x ⬝ᵥ x = 1) (hy : x ⬝ᵥ y = 0) : R0.jacobiMap x y = R.jacobiMap x y - c • y := by
  show R0.op y x x = R.op y x x - c • y
  rw [hR0, R1fun, hx, one_smul, dotProduct_comm y x, hy, zero_smul, sub_zero]

lemma shift_eig {R R0 : CurvTensor n} {c : ℝ} (hR0 : ∀ u v w, R0.op u v w = R.op u v w - c • R1fun u v w)
    {x : Vec n} (hx : x ⬝ᵥ x = 1) (μ : ℝ) :
    Module.End.eigenspace (R0.jacobiMap x) μ ⊓ perp x = Module.End.eigenspace (R.jacobiMap x) (μ + c) ⊓ perp x := by
  ext y
  simp only [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨h, hy⟩
    rw [shift_apply hR0 hx hy] at h
    exact ⟨by rw [add_smul, ← h, sub_add_cancel], hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨by rw [shift_apply hR0 hx hy, h, add_smul, add_sub_cancel_right], hy⟩

/-- **Row shift_R1.** -/
theorem shift_R1_proved {n : ℕ} (R : CurvTensor n) (c : ℝ) :
    ∃ R0 : CurvTensor n, (∀ u v w, R0.op u v w = R.op u v w - c • R1fun u v w) ∧
      (∀ x, R0.jacobi x = R.jacobi x - c • Pi x) ∧ (R0.IsOsserman ↔ R.IsOsserman) ∧
      (R0.IsClifford ↔ R.IsClifford) := by
  obtain ⟨R1, hR1⟩ := Curv.sec1_R1_curv_proved n
  obtain ⟨R0, hR0'⟩ := exists_sub R R1 c
  have hR0 : ∀ u v w, R0.op u v w = R.op u v w - c • R1fun u v w := fun u v w => by rw [hR0', hR1]
  have hjac : ∀ x, R0.jacobi x = R.jacobi x - c • Pi x := fun x => Matrix.ext_iff_mulVec.2 fun y => by
    rw [Curv.jacobi_mulVec, hR0, sub_mulVec, smul_mulVec, Curv.jacobi_mulVec, Curv.sec1_jacobi_R1_proved]
  have hred : ∀ x : Vec n, x ⬝ᵥ x = 1 → ∀ μ, R0.redMult x μ = R.redMult x (μ + c) := fun x hx μ => by
    unfold CurvTensor.redMult
    rw [shift_eig hR0 hx]
  refine ⟨R0, hR0, hjac, ?_, ?_⟩
  · unfold CurvTensor.IsOsserman
    constructor
    · intro h x y hx hy μ
      have e := h x y hx hy (μ - c)
      rwa [hred x hx, hred y hy, sub_add_cancel] at e
    · intro h x y hx hy μ
      rw [hred x hx, hred y hy]
      exact h x y hx hy _
  · unfold CurvTensor.IsClifford
    have hR : ∀ x, R.jacobi x = R0.jacobi x + c • Pi x := fun x => by rw [hjac]; abel
    constructor
    · rintro ⟨ν, J, hJ, l0, η, h⟩
      exact ⟨ν, J, hJ, l0 + c, η, fun x => by rw [hR, h, add_smul]; abel⟩
    · rintro ⟨ν, J, hJ, l0, η, h⟩
      exact ⟨ν, J, hJ, l0 - c, η, fun x => by rw [hjac, h, sub_smul]; abel⟩

/-- **Row rem_7_2_jac_split.** -/
theorem rem_7_2_jac_split_proved {n : ℕ} (R R' : CurvTensor n) (J : Matrix (Fin n) (Fin n) ℝ) (hJs : Jᵀ = -J)
    (c : ℝ) (hR' : ∀ u v w, R'.op u v w = R.op u v w - c • RJfun J u v w) :
    ∀ x : Vec n, R.jacobi x = R'.jacobi x + c • jfam J x ∧ x ⬝ᵥ (J *ᵥ x) = 0 := by
  obtain ⟨-, RJ, hRJop, hRJjac⟩ := RJ_curv_proved J hJs
  intro x
  refine ⟨Matrix.ext_iff_mulVec.2 fun y => ?_, skew_dot_self hJs x⟩
  rw [add_mulVec, smul_mulVec, Curv.jacobi_mulVec, Curv.jacobi_mulVec, hR', ← hRJjac x, Curv.jacobi_mulVec, hRJop]
  abel

/-! ### Combinations of a Clifford structure -/

/-- `⟨J_αx, J_βx⟩ = δ_αβ|x|²` for a `Cl(ν)`-structure. -/
lemma cliff_dot {ν : ℕ} {J : Fin ν → Matrix (Fin n) (Fin n) ℝ} (hJ : IsCliffordStr J) (x : Vec n) (α β : Fin ν) :
    (J α *ᵥ x) ⬝ᵥ (J β *ᵥ x) = if α = β then x ⬝ᵥ x else 0 := by
  have h1 : x ⬝ᵥ (J α *ᵥ (J β *ᵥ x)) = -((J α *ᵥ x) ⬝ᵥ (J β *ᵥ x)) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hJ.1 α, neg_mulVec, neg_dotProduct]
  have h2 : x ⬝ᵥ (J β *ᵥ (J α *ᵥ x)) = -((J α *ᵥ x) ⬝ᵥ (J β *ᵥ x)) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hJ.1 β, neg_mulVec, neg_dotProduct, dotProduct_comm]
  have h3 : x ⬝ᵥ ((J α * J β + J β * J α) *ᵥ x) = -2 * ((J α *ᵥ x) ⬝ᵥ (J β *ᵥ x)) := by
    rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_add, h1, h2]
    ring
  rw [hJ.2 α β] at h3
  split_ifs at h3 ⊢ with h
  · rw [neg_mulVec, ofNat_mulVec, dotProduct_neg, dotProduct_smul, smul_eq_mul] at h3
    linarith
  · rw [zero_mulVec, dotProduct_zero] at h3
    linarith

lemma comb_anticomm {ν : ℕ} {J : Fin ν → Matrix (Fin n) (Fin n) ℝ} (hJ : IsCliffordStr J) (p q : Fin ν → ℝ) :
    (∑ b, p b • J b) * (∑ d, q d • J d) + (∑ d, q d • J d) * (∑ b, p b • J b) =
      (p ⬝ᵥ q) • (-2 : Matrix (Fin n) (Fin n) ℝ) := by
  have h1 : (∑ b, p b • J b) * (∑ d, q d • J d) + (∑ d, q d • J d) * (∑ b, p b • J b) =
      ∑ b, ∑ d, (p b * q d) • (J b * J d + J d * J b) := by
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, smul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by rw [mul_comm]
  rw [h1]
  simp only [hJ.2, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [dotProduct, Finset.sum_smul]

/-- **Row cliffordStr_orth_comb.** -/
theorem cliffordStr_orth_comb_proved {n ν : ℕ} (J : Fin ν → Matrix (Fin n) (Fin n) ℝ) (hJ : IsCliffordStr J)
    (O : Matrix (Fin ν) (Fin ν) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin ν) ℝ) :
    IsCliffordStr (fun a => ∑ b, O a b • J b) := by
  have hOO : O * Oᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin ν) ℝ).mp hO
  refine ⟨fun a => ?_, fun a c => ?_⟩
  · rw [transpose_sum]
    simp only [transpose_smul, hJ.1, smul_neg, Finset.sum_neg_distrib]
  · rw [comb_anticomm hJ (O a) (O c)]
    have e : O a ⬝ᵥ O c = (O * Oᵀ) a c := by simp only [mul_apply, transpose_apply, dotProduct]
    rw [e, hOO, one_apply]
    split_ifs <;> simp

/-- A weighted sum of `(∑_β p_aβ v_β)(∑_β p_aβ v_β)ᵀ`, written in the `v_βv_γᵀ`. -/
lemma sum_smul_vecMulVec_comb {m ν : ℕ} (w : Fin m → ℝ) (p : Fin m → Fin ν → ℝ) (v : Fin ν → Vec n) :
    ∑ a, w a • vecMulVec (∑ β, p a β • v β) (∑ β, p a β • v β) =
      ∑ β, ∑ γ, (∑ a, w a * (p a β * p a γ)) • vecMulVec (v β) (v γ) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun a _ => by ring

lemma comb_mulVec {ν : ℕ} (J : Fin ν → Matrix (Fin n) (Fin n) ℝ) (p : Fin ν → ℝ) (x : Vec n) :
    (∑ β, p β • J β) *ᵥ x = ∑ β, p β • (J β *ᵥ x) := by
  rw [sum_mulVec]
  simp only [smul_mulVec]

/-- **Row rem_7_2_block_rotation.** -/
theorem rem_7_2_block_rotation_proved {n ν : ℕ} (Jα : Fin ν → Matrix (Fin n) (Fin n) ℝ) (μ : Fin ν → ℝ)
    (hJ : IsCliffordStr Jα) (O : Matrix (Fin ν) (Fin ν) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin ν) ℝ)
    (hblk : ∀ α β, O α β ≠ 0 → μ α = μ β) :
    IsCliffordStr (fun α => ∑ β, O α β • Jα β) ∧
      ∀ x : Vec n, ∑ α, μ α • jfam (∑ β, O α β • Jα β) x = ∑ α, μ α • jfam (Jα α) x := by
  refine ⟨cliffordStr_orth_comb_proved Jα hJ O hO, fun x => ?_⟩
  have hOtO : Oᵀ * O = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin ν) ℝ).mp hO
  have hmu : ∀ α β, μ α * O α β = μ β * O α β := fun α β => by
    by_cases h : O α β = 0
    · rw [h, mul_zero, mul_zero]
    · rw [hblk α β h]
  have hS : ∀ β γ, ∑ α, μ α * (O α β * O α γ) = diagonal μ β γ := fun β γ => by
    have h1 : ∑ α, μ α * (O α β * O α γ) = μ β * (Oᵀ * O) β γ := by
      rw [mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by rw [transpose_apply, ← mul_assoc, hmu]; ring
    rw [h1, hOtO, one_apply, diagonal_apply]
    split_ifs <;> simp
  simp only [jfam, comb_mulVec]
  refine (sum_smul_vecMulVec_comb μ (fun α β => O α β) (fun β => Jα β *ᵥ x)).trans ?_
  simp only [hS, diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-! ### The reduced eigenspaces of a Clifford form -/

section Eig

variable {ν : ℕ} {J : Fin ν → Matrix (Fin n) (Fin n) ℝ} {R : CurvTensor n} {x : Vec n} {l0 : ℝ} {η : Fin ν → ℝ}

/-- `W(x) = x^⊥ ∩ ⋂_α (J_αx)^⊥`. -/
def Wsub (J : Fin ν → Matrix (Fin n) (Fin n) ℝ) (x : Vec n) : Submodule ℝ (Vec n) :=
  perp x ⊓ ⨅ α, perp (J α *ᵥ x)

lemma mem_Wsub {y : Vec n} : y ∈ Wsub J x ↔ x ⬝ᵥ y = 0 ∧ ∀ α, (J α *ᵥ x) ⬝ᵥ y = 0 := by
  simp only [Wsub, Submodule.mem_inf, Submodule.mem_iInf]
  rfl

/-- A Clifford form on `x^⊥`, `x` a unit vector. -/
lemma jac_apply_perp (hM : R.jacobi x = l0 • Pi x + ∑ α, η α • jfam (J α) x) (hx : x ⬝ᵥ x = 1) {y : Vec n}
    (hy : x ⬝ᵥ y = 0) : R.jacobiMap x y = l0 • y + ∑ α, (η α * ((J α *ᵥ x) ⬝ᵥ y)) • (J α *ᵥ x) := by
  rw [jacobiMap_eq_mulVec, hM, add_mulVec, smul_mulVec, Spectral.Pi_mulVec, hx, one_smul, dotProduct_comm y x, hy,
    zero_smul, sub_zero, sum_mulVec]
  congr 1
  exact Finset.sum_congr rfl fun α _ => by rw [smul_mulVec, jfam_mulVec, smul_smul]

lemma sum_cliff_dot (hJ : IsCliffordStr J) (hx : x ⬝ᵥ x = 1) (f : Fin ν → ℝ) (β : Fin ν) :
    (J β *ᵥ x) ⬝ᵥ ∑ α, f α • (J α *ᵥ x) = f β := by
  simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, cliff_dot hJ, hx, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The reduced eigenspaces of a Clifford form: `E_ℓ(x) = span{J_αx : λ_0 + η_α = ℓ}`, plus `W(x)` when `ℓ = λ_0`. -/
theorem eig_clifford (hJ : IsCliffordStr J) (hM : R.jacobi x = l0 • Pi x + ∑ α, η α • jfam (J α) x)
    (hx : x ⬝ᵥ x = 1) (ℓ : ℝ) :
    Module.End.eigenspace (R.jacobiMap x) ℓ ⊓ perp x =
      Submodule.span ℝ ((fun α => J α *ᵥ x) '' {α | l0 + η α = ℓ}) ⊔ (if ℓ = l0 then Wsub J x else ⊥) := by
  apply le_antisymm
  · rintro y ⟨hyE, hyx⟩
    have hyx' : x ⬝ᵥ y = 0 := hyx
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, jac_apply_perp hM hx hyx'] at hyE
    have hc : ∀ β, (l0 + η β - ℓ) * ((J β *ᵥ x) ⬝ᵥ y) = 0 := by
      intro β
      have e := congrArg (fun z => (J β *ᵥ x) ⬝ᵥ z) hyE
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, sum_cliff_dot hJ hx] at e
      linarith
    by_cases hℓ : ℓ = l0
    · rw [ite_eq_left hℓ]
      have hcT : ∀ α, η α ≠ 0 → (J α *ᵥ x) ⬝ᵥ y = 0 := fun α hα => by
        have e := hc α
        rw [hℓ, add_sub_cancel_left] at e
        exact (mul_eq_zero.1 e).resolve_left hα
      refine Submodule.mem_sup.2 ⟨∑ α, ((J α *ᵥ x) ⬝ᵥ y) • (J α *ᵥ x), ?_,
        y - ∑ α, ((J α *ᵥ x) ⬝ᵥ y) • (J α *ᵥ x), ?_, by abel⟩
      · refine Submodule.sum_mem _ fun α _ => ?_
        by_cases hα : η α = 0
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, by simp [hα, hℓ], rfl⟩)
        · rw [hcT α hα, zero_smul]
          exact Submodule.zero_mem _
      · rw [mem_Wsub]
        refine ⟨?_, fun β => ?_⟩
        · simp only [dotProduct_sub, dotProduct_sum, dotProduct_smul, smul_eq_mul, skew_dot_self (hJ.1 _),
            mul_zero, Finset.sum_const_zero, hyx', sub_zero]
        · rw [dotProduct_sub, sum_cliff_dot hJ hx, sub_self]
    · rw [ite_eq_right hℓ, sup_bot_eq]
      have hy : y = ∑ α, ((ℓ - l0)⁻¹ * (η α * ((J α *ᵥ x) ⬝ᵥ y))) • (J α *ᵥ x) := by
        have e : (ℓ - l0) • y = ∑ α, (η α * ((J α *ᵥ x) ⬝ᵥ y)) • (J α *ᵥ x) := by
          rw [sub_smul, ← hyE]
          abel
        calc y = (ℓ - l0)⁻¹ • ((ℓ - l0) • y) := by
              rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hℓ), one_smul]
          _ = _ := by rw [e, Finset.smul_sum]; simp only [smul_smul]
      rw [hy]
      refine Submodule.sum_mem _ fun α _ => ?_
      by_cases hα : l0 + η α = ℓ
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, hα, rfl⟩)
      · have e : (J α *ᵥ x) ⬝ᵥ y = 0 := (mul_eq_zero.1 (hc α)).resolve_left (sub_ne_zero.2 hα)
        rw [e, mul_zero, mul_zero, zero_smul]
        exact Submodule.zero_mem _
  · apply sup_le
    · rw [Submodule.span_le]
      rintro _ ⟨β, hβ, rfl⟩
      have hvx : x ⬝ᵥ (J β *ᵥ x) = 0 := skew_dot_self (hJ.1 β) x
      rw [SetLike.mem_coe, Submodule.mem_inf, Module.End.mem_eigenspace_iff, jac_apply_perp hM hx hvx]
      refine ⟨?_, hvx⟩
      have e : ∑ α, (η α * ((J α *ᵥ x) ⬝ᵥ (J β *ᵥ x))) • (J α *ᵥ x) = η β • (J β *ᵥ x) := by
        simp only [cliff_dot hJ, hx, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte]
      rw [e, ← add_smul, hβ]
    · split_ifs with hℓ
      · intro y hy
        rw [mem_Wsub] at hy
        rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, jac_apply_perp hM hx hy.1]
        refine ⟨?_, hy.1⟩
        simp only [hy.2, mul_zero, zero_smul, Finset.sum_const_zero, add_zero, hℓ]
      · exact bot_le

end Eig

/-- **Row rem_7_2_eigenspaces.** -/
theorem rem_7_2_eigenspaces_proved (R' : CurvTensor 16) {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ)
    (μ : Fin ν → ℝ) (hJ : IsCliffordStr Jα) (hμ : ∀ α, μ α ≠ 0)
    (hjac : ∀ x, R'.jacobi x = ∑ α, μ α • jfam (Jα α) x) :
    (∀ (x : Vec 16) α β, (Jα α *ᵥ x) ⬝ᵥ (Jα β *ᵥ x) = if α = β then x ⬝ᵥ x else 0) ∧
      (∀ (x : Vec 16) α, x ⬝ᵥ (Jα α *ᵥ x) = 0) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 →
        (∀ ℓ : ℝ, ℓ ≠ 0 → Module.End.eigenspace (R'.jacobiMap x) ℓ ⊓ perp x =
          Submodule.span ℝ ((fun α => Jα α *ᵥ x) '' {α | μ α = ℓ})) ∧
        Module.End.eigenspace (R'.jacobiMap x) 0 ⊓ perp x = perp x ⊓ ⨅ α, perp (Jα α *ᵥ x) := by
  refine ⟨fun x α β => cliff_dot hJ x α β, fun x α => skew_dot_self (hJ.1 α) x, fun x hx => ?_⟩
  have hM : R'.jacobi x = (0 : ℝ) • Pi x + ∑ α, μ α • jfam (Jα α) x := by rw [zero_smul, zero_add, hjac]
  refine ⟨fun ℓ hℓ => ?_, ?_⟩
  · rw [eig_clifford hJ hM hx ℓ, ite_eq_right hℓ, sup_bot_eq]
    simp only [zero_add]
  · rw [eig_clifford hJ hM hx 0, ite_eq_left rfl]
    have e : {α | (0 : ℝ) + μ α = 0} = ∅ := by
      ext α
      simp [hμ α]
    rw [e, Set.image_empty, Submodule.span_empty, bot_sup_eq]
    rfl

end Osserman.Proofs.Rem72a

