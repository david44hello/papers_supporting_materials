/-
Osserman/Proofs/Rem72b.lean — Remark 7.2 of paper 013, second part: the determinant ratio, the constants `c_i`, the
sums of squares and Nikolayevsky's Lemma 3.11 (rows rem_7_2_det_ratio, rem_7_2_const, rem_7_2_sum_squares,
rem_7_2_inner_const; statements copied verbatim from Osserman/Paper/Statements7.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof. (1) At a unit `x`, with `v_α = J_αx` orthonormal and `u = Jx`, the vector
`z = ∑_α ⟨v_α,u⟩/(t - μ_α) v_α + t⁻¹w`, `w = u - ∑_α ⟨v_α,u⟩v_α`, solves `(tI - J_x(R'))z = u`; hence
`tI - J_x(R) = (tI - J_x(R'))(I - c zuᵀ)` and the matrix determinant lemma gives the factor `1 - c⟨u,z⟩`.
(2) An Osserman tensor has the same `det(tI - J_x)` at every unit `x`: by the spectral theorem it is `∏_i (t - λ_i)`,
and the number of `i` with `λ_i = s` is `dim ker(J_x - s)` (the rank of a unitary conjugate of a diagonal matrix),
which is `redMult x s`, plus one for `s = 0` (the line `ℝx`). (3) Partial fractions: if
`∑_{ℓ∈L} a_ℓ/(t - ℓ) + a_0/t = 0` off the poles, the function `t∏(t - ℓ)·(…)` is continuous and vanishes on a dense
set, hence everywhere; its values at the poles give `a = 0`. (4) Homogeneity gives `blockSq = c_ℓ²|x|⁴`, an identity of
polynomials; Lemma 3.11 gives `⟨J_αx, Jx⟩ = sqP·q`, and `q` has degree `0`.
-/
import Osserman.Proofs.Rem72a
import Osserman.Proofs.OssTop
import Osserman.Proofs.Poly
import Osserman.Proofs.HurwitzRadon
import Osserman.Cited.Nik2006

namespace Osserman.Proofs.Rem72b

open Osserman Osserman.Cited Matrix MvPolynomial
open Osserman.Proofs.Rem72a

/-! ### (1) The determinant ratio -/

section Ratio

variable {ν : ℕ} {Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ} {μ : Fin ν → ℝ} {x : Vec 16}

lemma comb_jfam_mulVec (y : Vec 16) :
    (∑ α, μ α • jfam (Jα α) x) *ᵥ y = ∑ α, (μ α * ((Jα α *ᵥ x) ⬝ᵥ y)) • (Jα α *ᵥ x) := by
  rw [sum_mulVec]
  exact Finset.sum_congr rfl fun α _ => by rw [smul_mulVec, jfam_mulVec, smul_smul]

/-- `w = u - ∑_α ⟨J_αx, u⟩ J_αx`. -/
noncomputable def wres (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (x u : Vec 16) : Vec 16 :=
  u - ∑ α, ((Jα α *ᵥ x) ⬝ᵥ u) • (Jα α *ᵥ x)

/-- `z = ∑_α ⟨J_αx, u⟩/(t - μ_α) J_αx + t⁻¹w`. -/
noncomputable def zvec (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (x u : Vec 16) (t : ℝ) : Vec 16 :=
  ∑ α, (((Jα α *ᵥ x) ⬝ᵥ u) / (t - μ α)) • (Jα α *ᵥ x) + t⁻¹ • wres Jα x u

lemma dot_wres (hJ : IsCliffordStr Jα) (hx : x ⬝ᵥ x = 1) (u : Vec 16) (β : Fin ν) :
    (Jα β *ᵥ x) ⬝ᵥ wres Jα x u = 0 := by
  rw [wres, dotProduct_sub, sum_cliff_dot hJ hx, sub_self]

lemma wres_dot (hJ : IsCliffordStr Jα) (hx : x ⬝ᵥ x = 1) (u : Vec 16) (β : Fin ν) :
    wres Jα x u ⬝ᵥ (Jα β *ᵥ x) = 0 := by
  rw [dotProduct_comm, dot_wres hJ hx]

lemma A_zvec (hJ : IsCliffordStr Jα) (hx : x ⬝ᵥ x = 1) {t : ℝ} (ht0 : t ≠ 0) (htμ : ∀ α, t ≠ μ α) (u : Vec 16) :
    (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - ∑ α, μ α • jfam (Jα α) x) *ᵥ zvec Jα μ x u t = u := by
  have hvz : ∀ β, (Jα β *ᵥ x) ⬝ᵥ zvec Jα μ x u t = ((Jα β *ᵥ x) ⬝ᵥ u) / (t - μ β) := fun β => by
    rw [zvec, dotProduct_add, sum_cliff_dot hJ hx, dotProduct_smul, dot_wres hJ hx, smul_zero, add_zero]
  have key : ∀ α, t * (((Jα α *ᵥ x) ⬝ᵥ u) / (t - μ α)) - μ α * (((Jα α *ᵥ x) ⬝ᵥ u) / (t - μ α)) =
      (Jα α *ᵥ x) ⬝ᵥ u := fun α => by
    have h := sub_ne_zero.2 (htμ α)
    field_simp
  rw [sub_mulVec, smul_mulVec, one_mulVec, comb_jfam_mulVec]
  simp only [hvz]
  calc t • zvec Jα μ x u t - ∑ α, (μ α * (((Jα α *ᵥ x) ⬝ᵥ u) / (t - μ α))) • (Jα α *ᵥ x)
      = ∑ α, (t * (((Jα α *ᵥ x) ⬝ᵥ u) / (t - μ α)) - μ α * (((Jα α *ᵥ x) ⬝ᵥ u) / (t - μ α))) •
          (Jα α *ᵥ x) + wres Jα x u := by
        rw [zvec, smul_add, smul_smul, mul_inv_cancel₀ ht0, one_smul, Finset.smul_sum]
        simp only [smul_smul, sub_smul, Finset.sum_sub_distrib]
        abel
    _ = u := by
        simp only [key]
        rw [wres]
        abel

lemma det_A_ne_zero (hJ : IsCliffordStr Jα) (hx : x ⬝ᵥ x = 1) {t : ℝ} (ht0 : t ≠ 0) (htμ : ∀ α, t ≠ μ α) :
    (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - ∑ α, μ α • jfam (Jα α) x).det ≠ 0 := by
  have hsurj : Function.Surjective (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - ∑ α, μ α • jfam (Jα α) x).mulVec :=
    fun u => ⟨zvec Jα μ x u t, A_zvec hJ hx ht0 htμ u⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_surjective_iff_isUnit.1 hsurj)).ne_zero

lemma vecMulVec_smul_left (r : ℝ) (a b : Vec 16) : vecMulVec (r • a) b = r • vecMulVec a b := by
  ext i j
  simp [vecMulVec, mul_assoc]

/-- The matrix determinant lemma, in the form used here. -/
lemma det_sub_rank_one {A : Matrix (Fin 16) (Fin 16) ℝ} {z u : Vec 16} (hAz : A *ᵥ z = u) (c : ℝ) :
    (A - c • vecMulVec u u).det = A.det * (1 - c * (u ⬝ᵥ z)) := by
  have h : A - c • vecMulVec u u = A * (1 + vecMulVec (-c • z) u) := by
    rw [mul_add, mul_one, mul_vecMulVec, mulVec_smul, hAz, vecMulVec_smul_left, neg_smul, sub_eq_add_neg]
  rw [h, det_mul, vecMulVec_eq (ι := Unit), det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul]
  ring

lemma blockSq_sum (μ : Fin ν → ℝ) (K : Matrix (Fin 16) (Fin 16) ℝ) (t : ℝ) :
    ∑ ℓ ∈ Finset.univ.image μ, blockSq Jα μ K x ℓ / (t - ℓ) =
      ∑ α, ((Jα α *ᵥ x) ⬝ᵥ (K *ᵥ x)) ^ 2 / (t - μ α) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := μ) (t := Finset.univ.image μ)
    (fun α _ => Finset.mem_image_of_mem μ (Finset.mem_univ α))]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [blockSq, Finset.sum_div]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [(Finset.mem_filter.1 hα).2]

lemma dot_zvec (K : Matrix (Fin 16) (Fin 16) ℝ) (t : ℝ) :
    (K *ᵥ x) ⬝ᵥ zvec Jα μ x (K *ᵥ x) t =
      ∑ ℓ ∈ Finset.univ.image μ, blockSq Jα μ K x ℓ / (t - ℓ) + zeroSq Jα K x / t := by
  have hc : ∀ α, (K *ᵥ x) ⬝ᵥ (Jα α *ᵥ x) = (Jα α *ᵥ x) ⬝ᵥ (K *ᵥ x) := fun α => dotProduct_comm _ _
  rw [blockSq_sum]
  simp only [zvec, wres, dotProduct_add, dotProduct_sub, dotProduct_sum, dotProduct_smul, smul_eq_mul, zeroSq, hc]
  congr 1
  · exact Finset.sum_congr rfl fun α _ => by ring
  · rw [div_eq_inv_mul]
    congr 2
    exact Finset.sum_congr rfl fun α _ => (sq _).symm

end Ratio

/-- **Row rem_7_2_det_ratio.** -/
theorem rem_7_2_det_ratio_proved (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) (x : Vec 16)
    (hx : x ⬝ᵥ x = 1) (t : ℝ) (ht0 : t ≠ 0) (htμ : ∀ α, t ≠ μ α) :
    (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R.jacobi x).det =
      (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R'.jacobi x).det *
        (1 - c * (∑ ℓ ∈ Finset.univ.image μ, blockSq Jα μ J x ℓ / (t - ℓ) + zeroSq Jα J x / t)) := by
  obtain ⟨hJs, -, -, hR', -, -, hJ, -, hjac⟩ := h
  have hsplit := (rem_7_2_jac_split_proved R R' J hJs c hR' x).1
  have e1 : t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R.jacobi x =
      (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R'.jacobi x) - c • vecMulVec (J *ᵥ x) (J *ᵥ x) := by
    rw [hsplit, jfam]
    abel
  rw [e1, hjac x, det_sub_rank_one (A_zvec hJ hx ht0 htμ (J *ᵥ x)) c, dot_zvec]

/-! ### (2) An Osserman tensor has the same `det(tI - J_x)` at every unit `x` -/

section DetConst

variable {n : ℕ}

/-- `aM + b = U diag(aλ_i + b) U*` for a Hermitian `M`. -/
lemma spec_affine {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) (a b : ℝ) :
    a • M + b • (1 : Matrix (Fin n) (Fin n) ℝ) =
      (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) * diagonal (fun i => a * hM.eigenvalues i + b) *
        star (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
  set U : Matrix (Fin n) (Fin n) ℝ := ↑hM.eigenvectorUnitary
  have hspec : M = U * diagonal (RCLike.ofReal ∘ hM.eigenvalues) * star U := by
    have h := hM.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.2
  have hd : diagonal (fun i => a * hM.eigenvalues i + b) =
      a • diagonal (RCLike.ofReal ∘ hM.eigenvalues) + b • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, diagonal_apply, diagonal_apply, one_apply]
    split_ifs <;> simp
  rw [hd, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, ← hspec, mul_smul_comm, mul_one, smul_mul_assoc, hUU]

lemma isUnit_det_eigenvectorUnitary {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) :
    IsUnit (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).det ∧
      IsUnit (star (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)).det := by
  have h1 := Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.2
  have h2 := Unitary.star_mul_self_of_mem hM.eigenvectorUnitary.2
  exact ⟨IsUnit.of_mul_eq_one _ (by rw [← det_mul, h1, det_one]),
    IsUnit.of_mul_eq_one _ (by rw [← det_mul, h2, det_one])⟩

/-- `det(tI - M) = ∏_i (t - λ_i)` for a Hermitian `M`. -/
lemma det_sub_eq_prod {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) (t : ℝ) :
    (t • (1 : Matrix (Fin n) (Fin n) ℝ) - M).det = ∏ i, (t - hM.eigenvalues i) := by
  have e := spec_affine hM (-1) t
  rw [neg_one_smul, neg_add_eq_sub] at e
  have hUU := Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.2
  rw [e, det_mul, det_mul, mul_right_comm, ← det_mul, hUU, det_one, one_mul, det_diagonal]
  exact Finset.prod_congr rfl fun i _ => by ring

/-- The number of eigenvalues equal to `s` is the dimension of the `s`-eigenspace. -/
lemma card_eig_eq {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) (s : ℝ) :
    (Finset.univ.filter fun i => hM.eigenvalues i = s).card =
      Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' M) s) := by
  have hU := isUnit_det_eigenvectorUnitary hM
  have hrank : (M - s • (1 : Matrix (Fin n) (Fin n) ℝ)).rank =
      Fintype.card {i // hM.eigenvalues i - s ≠ 0} := by
    have e := spec_affine hM 1 (-s)
    rw [one_smul, neg_smul, ← sub_eq_add_neg] at e
    rw [e, rank_mul_eq_left_of_isUnit_det _ _ hU.2, rank_mul_eq_right_of_isUnit_det _ _ hU.1]
    simp only [one_mul, ← sub_eq_add_neg]
    exact rank_diagonal _
  have hker : Module.End.eigenspace (Matrix.toLin' M) s =
      LinearMap.ker (M - s • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVecLin := by
    ext y
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, mulVecLin_apply, sub_mulVec, smul_mulVec, one_mulVec,
      toLin'_apply, sub_eq_zero]
  have hrn := (M - s • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fin_fun] at hrn
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => hM.eigenvalues i = s)
  rw [Finset.card_univ, Fintype.card_fin] at hc
  have hc' : Fintype.card {i // hM.eigenvalues i - s ≠ 0} =
      (Finset.univ.filter fun i => ¬ hM.eigenvalues i = s).card := by
    rw [Fintype.card_subtype]
    simp only [sub_ne_zero]
  rw [hker]
  change (M - s • (1 : Matrix (Fin n) (Fin n) ℝ)).rank + _ = n at hrn
  omega

lemma eig_le_perp (R : CurvTensor n) (x : Vec n) {s : ℝ} (hs : s ≠ 0) :
    Module.End.eigenspace (R.jacobiMap x) s ≤ perp x := by
  intro y hy
  rw [Module.End.mem_eigenspace_iff, jacobiMap_eq_mulVec] at hy
  have h1 : x ⬝ᵥ (R.jacobi x *ᵥ y) = 0 := by
    rw [dotProduct_comm, Curv.symm_dot (Spectral.jacobi_transpose R x), Spectral.jacobi_self, zero_dotProduct]
  rw [hy, dotProduct_smul, smul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left hs

lemma finrank_eig_zero (R : CurvTensor n) {x : Vec n} (hx : x ⬝ᵥ x = 1) :
    Module.finrank ℝ (Module.End.eigenspace (R.jacobiMap x) 0) = R.redMult x 0 + 1 := by
  set E := Module.End.eigenspace (R.jacobiMap x) 0
  have hxE : x ∈ E := by
    rw [Module.End.mem_eigenspace_iff, zero_smul, jacobiMap_eq_mulVec]
    exact Spectral.jacobi_self R x
  have hsup : (E ⊓ perp x) ⊔ Submodule.span ℝ {x} = E := by
    refine le_antisymm (sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).2 hxE)) fun y hy => ?_
    refine Submodule.mem_sup.2 ⟨y - (x ⬝ᵥ y) • x, ⟨E.sub_mem hy (E.smul_mem _ hxE), ?_⟩, (x ⬝ᵥ y) • x,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x), sub_add_cancel _ _⟩
    show x ⬝ᵥ (y - (x ⬝ᵥ y) • x) = 0
    rw [dotProduct_sub, dotProduct_smul, hx, smul_eq_mul, mul_one, sub_self]
  have hinf : (E ⊓ perp x) ⊓ Submodule.span ℝ {x} = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨-, hy⟩, hyx⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hyx
    have e : x ⬝ᵥ (r • x) = 0 := hy
    rw [dotProduct_smul, hx, smul_eq_mul, mul_one] at e
    rw [e, zero_smul]
    exact Submodule.zero_mem _
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h := Submodule.finrank_sup_add_finrank_inf_eq (E ⊓ perp x) (Submodule.span ℝ {x})
  rw [hsup, hinf, finrank_bot, add_zero, finrank_span_singleton hx0] at h
  rw [h]
  rfl

/-- At a unit `x`: the number of eigenvalues of `J_x` equal to `s` is `redMult x s`, plus one for `s = 0`. -/
lemma card_eig_jacobi (R : CurvTensor n) {x : Vec n} (hx : x ⬝ᵥ x = 1) (s : ℝ) :
    (Finset.univ.filter fun i => (OssTop.jacobi_isHermitian R x).eigenvalues i = s).card =
      R.redMult x s + if s = 0 then 1 else 0 := by
  rw [card_eig_eq, CurvTensor.jacobi, Matrix.toLin'_toMatrix']
  by_cases hs : s = 0
  · rw [ite_eq_left hs, hs, finrank_eig_zero R hx]
  · rw [ite_eq_right hs, add_zero, CurvTensor.redMult, inf_eq_left.2 (eig_le_perp R x hs)]

lemma count_map_univ (e : Fin n → ℝ) (s : ℝ) :
    Multiset.count s (Finset.univ.val.map e) = (Finset.univ.filter fun i => e i = s).card := by
  rw [Multiset.count_map]
  simp_rw [eq_comm (a := s)]
  rfl

/-- **An Osserman tensor has the same `det(tI - J_x)` at all unit `x`.** -/
lemma det_eq_of_osserman {R : CurvTensor n} (hO : R.IsOsserman) {x y : Vec n} (hx : x ⬝ᵥ x = 1)
    (hy : y ⬝ᵥ y = 1) (t : ℝ) :
    (t • (1 : Matrix (Fin n) (Fin n) ℝ) - R.jacobi x).det = (t • (1 : Matrix (Fin n) (Fin n) ℝ) - R.jacobi y).det := by
  set hX := OssTop.jacobi_isHermitian R x
  set hY := OssTop.jacobi_isHermitian R y
  rw [det_sub_eq_prod hX, det_sub_eq_prod hY]
  have hms : Finset.univ.val.map hX.eigenvalues = Finset.univ.val.map hY.eigenvalues := by
    ext s
    rw [count_map_univ, count_map_univ, card_eig_jacobi R hx, card_eig_jacobi R hy, hO x y hx hy s]
  rw [Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod]
  have e : ∀ hh : Fin n → ℝ, Finset.univ.val.map (fun i => t - hh i) = (Finset.univ.val.map hh).map (t - ·) :=
    fun hh => by rw [Multiset.map_map]; rfl
  rw [e, e, hms]

end DetConst

/-! ### (3) Partial fractions -/

/-- `Q(t) = a_0∏_{k∈L}(t - k) + ∑_{ℓ∈L} a_ℓ t ∏_{k∈L, k≠ℓ}(t - k)`, i.e. `t∏(t - k)` times the partial fractions. -/
noncomputable def resPoly (L : Finset ℝ) (a : ℝ → ℝ) (a0 t : ℝ) : ℝ :=
  a0 * ∏ k ∈ L, (t - k) + ∑ ℓ ∈ L, a ℓ * t * ∏ k ∈ L.erase ℓ, (t - k)

lemma resPoly_continuous (L : Finset ℝ) (a : ℝ → ℝ) (a0 : ℝ) : Continuous (resPoly L a a0) := by
  unfold resPoly
  exact (continuous_const.mul (continuous_finsetProd _ fun k _ => continuous_id.sub continuous_const)).add
    (continuous_finsetSum _ fun ℓ _ => (continuous_const.mul continuous_id).mul
      (continuous_finsetProd _ fun k _ => continuous_id.sub continuous_const))

/-- If `∑_{ℓ∈L} a_ℓ/(t - ℓ) + a_0/t = 0` for every `t` off the poles, all the residues vanish. -/
lemma residues_zero (L : Finset ℝ) (h0 : (0 : ℝ) ∉ L) (a : ℝ → ℝ) (a0 : ℝ)
    (h : ∀ t : ℝ, t ≠ 0 → t ∉ L → ∑ ℓ ∈ L, a ℓ / (t - ℓ) + a0 / t = 0) :
    (∀ ℓ ∈ L, a ℓ = 0) ∧ a0 = 0 := by
  have hQ0 : ∀ t, t ≠ 0 → t ∉ L → resPoly L a a0 t = 0 := by
    intro t ht0 htL
    have hne : ∀ k ∈ L, t - k ≠ 0 := fun k hk => sub_ne_zero.2 fun e => htL (e ▸ hk)
    have e : resPoly L a a0 t = t * (∏ k ∈ L, (t - k)) * (∑ ℓ ∈ L, a ℓ / (t - ℓ) + a0 / t) := by
      simp only [resPoly, mul_add, Finset.mul_sum]
      rw [add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
        rw [← Finset.mul_prod_erase L (fun k => t - k) hℓ]
        field_simp [hne ℓ hℓ]
      · field_simp
    rw [e, h t ht0 htL, mul_zero]
  have hQ : ∀ t, resPoly L a a0 t = 0 := by
    have hd : Dense (Set.univ \ (↑(insert 0 L) : Set ℝ)) := dense_univ.sdiff_finite (Finset.finite_toSet _)
    have hfun := Continuous.ext_on hd (resPoly_continuous L a a0) continuous_const fun t ht => by
      have ht' : t ∉ insert 0 L := ht.2
      rw [Finset.mem_insert, not_or] at ht'
      exact hQ0 t ht'.1 ht'.2
    exact fun t => congrFun hfun t
  refine ⟨fun ℓ0 hℓ0 => ?_, ?_⟩
  · have e := hQ ℓ0
    have hp0 : ∏ k ∈ L, (ℓ0 - k) = 0 := Finset.prod_eq_zero hℓ0 (sub_self ℓ0)
    have hsum : ∑ ℓ ∈ L, a ℓ * ℓ0 * ∏ k ∈ L.erase ℓ, (ℓ0 - k) = a ℓ0 * ℓ0 * ∏ k ∈ L.erase ℓ0, (ℓ0 - k) := by
      refine Finset.sum_eq_single ℓ0 (fun ℓ _ hne => ?_) (fun hn => absurd hℓ0 hn)
      rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hne, hℓ0⟩) (sub_self ℓ0), mul_zero]
    rw [resPoly, hp0, mul_zero, zero_add, hsum] at e
    have hl0 : ℓ0 ≠ 0 := fun hz => h0 (hz ▸ hℓ0)
    have hpe : ∏ k ∈ L.erase ℓ0, (ℓ0 - k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k hk => sub_ne_zero.2 (Finset.ne_of_mem_erase hk).symm
    rcases mul_eq_zero.1 e with h1 | h1
    · exact (mul_eq_zero.1 h1).resolve_right hl0
    · exact absurd h1 hpe
  · have e := hQ 0
    simp only [resPoly, mul_zero, zero_mul, Finset.sum_const_zero, add_zero] at e
    have hp : ∏ k ∈ L, ((0 : ℝ) - k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k hk => sub_ne_zero.2 fun hz => h0 (hz ▸ hk)
    exact (mul_eq_zero.1 e).resolve_right hp

/-! ### (4) The constants `c_i` -/

lemma blockSq_nonneg {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ)
    (K : Matrix (Fin 16) (Fin 16) ℝ) (x : Vec 16) (ℓ : ℝ) : 0 ≤ blockSq Jα μ K x ℓ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Bessel: `‖π_0(Kx)‖² = |w|² ≥ 0` at a unit `x`. -/
lemma zeroSq_nonneg {ν : ℕ} {Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ} (hJ : IsCliffordStr Jα) {x : Vec 16}
    (hx : x ⬝ᵥ x = 1) (K : Matrix (Fin 16) (Fin 16) ℝ) : 0 ≤ zeroSq Jα K x := by
  have hc : ∀ α, (K *ᵥ x) ⬝ᵥ (Jα α *ᵥ x) = (Jα α *ᵥ x) ⬝ᵥ (K *ᵥ x) := fun α => dotProduct_comm _ _
  have h1 : wres Jα x (K *ᵥ x) ⬝ᵥ wres Jα x (K *ᵥ x) = wres Jα x (K *ᵥ x) ⬝ᵥ (K *ᵥ x) := by
    conv_lhs => arg 2; rw [wres]
    simp only [dotProduct_sub, dotProduct_sum, dotProduct_smul, wres_dot hJ hx, smul_zero, Finset.sum_const_zero,
      sub_zero]
  have e : zeroSq Jα K x = wres Jα x (K *ᵥ x) ⬝ᵥ wres Jα x (K *ᵥ x) := by
    rw [h1, dotProduct_comm, wres, zeroSq]
    simp only [dotProduct_sub, dotProduct_sum, dotProduct_smul, smul_eq_mul, hc, sq]
  rw [e]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

lemma same_at_units (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) {e0 x : Vec 16}
    (he0 : e0 ⬝ᵥ e0 = 1) (hx : x ⬝ᵥ x = 1) :
    (∀ ℓ ∈ Finset.univ.image μ, blockSq Jα μ J x ℓ = blockSq Jα μ J e0 ℓ) ∧ zeroSq Jα J x = zeroSq Jα J e0 := by
  obtain ⟨-, -, hc, -, hO, hO', hJ, hμ, hjac⟩ := id h
  have h0L : (0 : ℝ) ∉ Finset.univ.image μ := by
    rw [Finset.mem_image]
    rintro ⟨α, -, hα⟩
    exact hμ α hα
  have key := residues_zero (Finset.univ.image μ) h0L (fun ℓ => blockSq Jα μ J x ℓ - blockSq Jα μ J e0 ℓ)
    (zeroSq Jα J x - zeroSq Jα J e0) fun t ht0 htL => by
      have htμ : ∀ α, t ≠ μ α := fun α e => htL (e ▸ Finset.mem_image_of_mem μ (Finset.mem_univ α))
      have d1 := rem_7_2_det_ratio_proved R R' J c Jα μ h x hx t ht0 htμ
      have d2 := rem_7_2_det_ratio_proved R R' J c Jα μ h e0 he0 t ht0 htμ
      have hne : (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R'.jacobi e0).det ≠ 0 := by
        rw [hjac e0]
        exact det_A_ne_zero hJ he0 ht0 htμ
      rw [det_eq_of_osserman hO hx he0 t, d2, det_eq_of_osserman hO' hx he0 t] at d1
      have hF := mul_left_cancel₀ hne d1
      have hF' : c * ((∑ ℓ ∈ Finset.univ.image μ, blockSq Jα μ J x ℓ / (t - ℓ) + zeroSq Jα J x / t) -
          (∑ ℓ ∈ Finset.univ.image μ, blockSq Jα μ J e0 ℓ / (t - ℓ) + zeroSq Jα J e0 / t)) = 0 := by
        linear_combination hF
      have hF'' := (mul_eq_zero.1 hF').resolve_left hc
      calc ∑ ℓ ∈ Finset.univ.image μ, (blockSq Jα μ J x ℓ - blockSq Jα μ J e0 ℓ) / (t - ℓ) +
            (zeroSq Jα J x - zeroSq Jα J e0) / t
          = (∑ ℓ ∈ Finset.univ.image μ, blockSq Jα μ J x ℓ / (t - ℓ) + zeroSq Jα J x / t) -
            (∑ ℓ ∈ Finset.univ.image μ, blockSq Jα μ J e0 ℓ / (t - ℓ) + zeroSq Jα J e0 / t) := by
            simp only [sub_div, Finset.sum_sub_distrib]
            ring
        _ = 0 := hF''
  exact ⟨fun ℓ hℓ => sub_eq_zero.1 (key.1 ℓ hℓ), sub_eq_zero.1 key.2⟩

/-- **Row rem_7_2_const.** -/
theorem rem_7_2_const_proved (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) :
    (∀ ℓ ∈ Finset.univ.image μ, ∃ cℓ : ℝ, 0 ≤ cℓ ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → blockSq Jα μ J x ℓ = cℓ ^ 2) ∧
      ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → zeroSq Jα J x = c0 ^ 2 := by
  obtain ⟨-, e0, he0, -⟩ := Spectral.exists_unit_scale 0
  refine ⟨fun ℓ hℓ => ⟨Real.sqrt (blockSq Jα μ J e0 ℓ), Real.sqrt_nonneg _, fun x hx => ?_⟩,
    ⟨Real.sqrt (zeroSq Jα J e0), Real.sqrt_nonneg _, fun x hx => ?_⟩⟩
  · rw [Real.sq_sqrt (blockSq_nonneg _ _ _ _ _), (same_at_units R R' J c Jα μ h he0 hx).1 ℓ hℓ]
  · rw [Real.sq_sqrt (zeroSq_nonneg h.2.2.2.2.2.2.1 he0 J), (same_at_units R R' J c Jα μ h he0 hx).2]

/-! ### (5) Sums of squares and Nikolayevsky's Lemma 3.11 -/

lemma blockSq_smul {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ)
    (K : Matrix (Fin 16) (Fin 16) ℝ) (s : ℝ) (u : Vec 16) (ℓ : ℝ) :
    blockSq Jα μ K (s • u) ℓ = s ^ 4 * blockSq Jα μ K u ℓ := by
  simp only [blockSq, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by ring

lemma dot_transpose_mul (A B : Matrix (Fin 16) (Fin 16) ℝ) (x : Vec 16) :
    x ⬝ᵥ ((Aᵀ * B) *ᵥ x) = (A *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- **Row rem_7_2_sum_squares.** -/
theorem rem_7_2_sum_squares_proved (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) :
    ∀ ℓ ∈ Finset.univ.image μ, (Finset.univ.filter fun α => μ α = ℓ).card ≤ 8 ∧
      (∃ cℓ : ℝ, ∀ x : Vec 16, blockSq Jα μ J x ℓ = cℓ ^ 2 * (x ⬝ᵥ x) ^ 2) ∧
      sqP 16 ∣ ∑ α ∈ Finset.univ.filter (fun α => μ α = ℓ), quadP ((Jα α)ᵀ * J) ^ 2 := by
  intro ℓ hℓ
  obtain ⟨cℓ, -, hcℓ⟩ := (rem_7_2_const_proved R R' J c Jα μ h).1 ℓ hℓ
  have hhom : ∀ x : Vec 16, blockSq Jα μ J x ℓ = cℓ ^ 2 * (x ⬝ᵥ x) ^ 2 := fun x => by
    obtain ⟨s, u, hu, rfl⟩ := Spectral.exists_unit_scale x
    rw [blockSq_smul, hcℓ u hu, smul_dotProduct, dotProduct_smul, hu, smul_eq_mul, smul_eq_mul]
    ring
  have hν : (Finset.univ : Finset (Fin ν)).card ≤ 8 := by
    simpa using HurwitzRadon.rem_7_2_nu_le_8_proved Jα h.2.2.2.2.2.2.1
  refine ⟨(Finset.card_filter_le _ _).trans hν, ⟨cℓ, hhom⟩, ⟨C (cℓ ^ 2) * sqP 16, MvPolynomial.funext fun x => ?_⟩⟩
  have hb := hhom x
  unfold blockSq at hb
  simp only [map_sum, map_pow, map_mul, eval_C, Poly.eval_sqP, Poly.eval_quadP, dot_transpose_mul]
  rw [hb]
  ring

/-- A quadratic polynomial divisible by `sqP 16` is a constant multiple of it. -/
lemma eval_eq_const_mul {p q : MvPolynomial (Fin 16) ℝ} (hp : p.IsHomogeneous 2) (hq : p = sqP 16 * q) :
    ∃ d : ℝ, ∀ x : Vec 16, eval x p = d * (x ⬝ᵥ x) := by
  by_cases hq0 : q = 0
  · exact ⟨0, fun x => by rw [hq, hq0, mul_zero, map_zero, zero_mul]⟩
  have hs0 : sqP 16 ≠ 0 := fun hz => by
    obtain ⟨-, e0, he0, -⟩ := Spectral.exists_unit_scale 0
    have e := congrArg (eval e0) hz
    rw [Poly.eval_sqP, map_zero, he0] at e
    exact one_ne_zero e
  have hp0 : p ≠ 0 := by
    rw [hq]
    exact mul_ne_zero hs0 hq0
  have h2 := MvPolynomial.totalDegree_mul_of_isDomain hs0 hq0
  rw [← hq, hp.totalDegree hp0, Poly.sqP_isHomogeneous.totalDegree hs0] at h2
  have hqC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (by omega : q.totalDegree = 0)
  set d := q.coeff 0
  refine ⟨d, fun x => ?_⟩
  rw [hq, hqC, map_mul, eval_C, Poly.eval_sqP, mul_comm]

/-- **Row rem_7_2_inner_const.** -/
theorem rem_7_2_inner_const_proved (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) :
    ∀ α, ∃ d : ℝ, ∀ x : Vec 16, (Jα α *ᵥ x) ⬝ᵥ (J *ᵥ x) = d * (x ⬝ᵥ x) := by
  intro α
  have hℓ : μ α ∈ Finset.univ.image μ := Finset.mem_image_of_mem μ (Finset.mem_univ α)
  obtain ⟨hcard, -, hdvd⟩ := rem_7_2_sum_squares_proved R R' J c Jα μ h (μ α) hℓ
  set F := Finset.univ.filter fun β => μ β = μ α
  have hαF : α ∈ F := Finset.mem_filter.2 ⟨Finset.mem_univ α, rfl⟩
  let e : Fin F.card ≃ F := F.equivFin.symm
  have hdvd' : sqP 16 ∣ ∑ i, quadP ((Jα (e i).1)ᵀ * J) ^ 2 := by
    rwa [Equiv.sum_comp e (fun b : F => quadP ((Jα b.1)ᵀ * J) ^ 2),
      Finset.sum_coe_sort F (fun β => quadP ((Jα β)ᵀ * J) ^ 2)]
  obtain ⟨q, hq⟩ := nik2006_lemma_3_11 F.card hcard _ hdvd' (e.symm ⟨α, hαF⟩)
  simp only [Equiv.apply_symm_apply] at hq
  obtain ⟨d, hd⟩ := eval_eq_const_mul (Poly.quadP_isHomogeneous _) hq
  exact ⟨d, fun x => by rw [← dot_transpose_mul, ← Poly.eval_quadP, hd]⟩

end Osserman.Proofs.Rem72b

