/-
Six3.lean — proofs of the rows of Setting (T) and Lemma 12.5 of paper 013 (sec_common_lemmas.tex l. 10-25, 96-131;
Osserman/Paper/StatementsSix.lean v0.41): setting_T_change, setting_T_ker_Kt, settingT_nonvacuous, lem_12_5_1,
lem_12_5_2, lem_12_5_radial, lem_12_5_dim_W, lem_12_5_image_W, lem_12_5_1_W, lem_12_5_skew_facts, lem_12_5_1_r_even,
lem_12_5_skew_supported, lem_12_5_1_restrict, lem_12_5_1_r_ne_2, lem_12_5_1_r_ne_4, lem_12_5_1_r_zero, lem_12_5_2_W,
lem_12_5_2_a0, lem_12_5_2_zero. Each `<row>_proved` has the row's type verbatim. Lemma 12.4 is used through
`Six1.lem_12_4_proved`. The general skew-map lemmas (first part) come from an earlier draft,
checked here.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.SixPieces
import Osserman.Proofs.Six1
import Osserman.Proofs.OctonionFacts

namespace Osserman.Proofs.Six3

open Osserman Matrix Osserman.Proofs.OctonionLinear Osserman.Proofs.OctonionFacts

/-! ## General linear algebra on `Vec n` -/

lemma mem_orthSub {n : ℕ} (W : Submodule ℝ (Vec n)) (v : Vec n) :
    v ∈ orthSub W ↔ ∀ w ∈ W, w ⬝ᵥ v = 0 := Iff.rfl

lemma dot_mulVec_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (u : Vec n) (v : Vec m) :
    (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Aᵀ *ᵥ v) := by
  rw [dotProduct_mulVec, vecMul_transpose]

lemma skew_dot {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S) (u v : Vec n) :
    (S *ᵥ u) ⬝ᵥ v = -(u ⬝ᵥ (S *ᵥ v)) := by
  rw [dot_mulVec_transpose, hS, neg_mulVec, dotProduct_neg]

lemma range_le_iff {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (W : Submodule ℝ (Vec m)) :
    LinearMap.range (Matrix.toLin' M) ≤ W ↔ ∀ v, M *ᵥ v ∈ W := by
  constructor
  · intro h v
    exact h ⟨v, rfl⟩
  · rintro h _ ⟨v, rfl⟩
    exact h v

lemma mem_range_toLin' {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (v : Vec n) :
    M *ᵥ v ∈ LinearMap.range (Matrix.toLin' M) := ⟨v, rfl⟩

lemma finrank_range_eq_rank {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' M)) = M.rank := by
  rw [Matrix.toLin'_apply']
  rfl

/-- A matrix whose columns are orthonormal (`WmᵀWm = 1`) is injective. -/
lemma ker_eq_bot_of_orth {n r : ℕ} (Wm : Matrix (Fin n) (Fin r) ℝ) (hWm : Wmᵀ * Wm = 1) :
    LinearMap.ker (Matrix.toLin' Wm) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro y hy
  rw [Matrix.toLin'_apply] at hy
  have h1 : (Wmᵀ * Wm) *ᵥ y = 0 := by rw [← mulVec_mulVec, hy, mulVec_zero]
  rwa [hWm, one_mulVec] at h1

lemma finrank_range_of_ker_bot {n r : ℕ} (Wm : Matrix (Fin n) (Fin r) ℝ)
    (hker : LinearMap.ker (Matrix.toLin' Wm) = ⊥) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' Wm)) = r := by
  rw [LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hker), Module.finrank_fin_fun]

/-! ## Skew maps -/

/-- A skew map vanishes exactly on the orthogonal complement of its image. -/
lemma skew_ker_eq {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S) :
    LinearMap.ker (Matrix.toLin' S) = orthSub (LinearMap.range (Matrix.toLin' S)) := by
  ext v
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, mem_orthSub]
  constructor
  · rintro hv _ ⟨u, rfl⟩
    rw [Matrix.toLin'_apply, skew_dot S hS, hv, dotProduct_zero, neg_zero]
  · intro hv
    have h1 := hv (S *ᵥ (S *ᵥ v)) (mem_range_toLin' S _)
    rw [skew_dot S hS, neg_eq_zero] at h1
    exact dotProduct_self_eq_zero.mp h1

/-- A skew map is injective on its image. -/
lemma skew_inj_on_range {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S) (v : Vec n)
    (hv : v ∈ LinearMap.range (Matrix.toLin' S)) (h0 : S *ᵥ v = 0) : v = 0 := by
  obtain ⟨u, rfl⟩ := hv
  rw [Matrix.toLin'_apply] at h0 ⊢
  have h1 : (S *ᵥ u) ⬝ᵥ (S *ᵥ u) = 0 := by rw [skew_dot S hS, h0, dotProduct_zero, neg_zero]
  exact dotProduct_self_eq_zero.mp h1

lemma restrict_skew {n r : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S) (Wm : Matrix (Fin n) (Fin r) ℝ) :
    (Wmᵀ * S * Wm)ᵀ = -(Wmᵀ * S * Wm) := by
  rw [transpose_mul, transpose_mul, hS, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

/-- The restriction `Wmᵀ S Wm` of a skew map to its image, written through an injective `Wm` with the same image,
is invertible. -/
lemma restrict_det_ne_zero {n r : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S) (Wm : Matrix (Fin n) (Fin r) ℝ)
    (hker : LinearMap.ker (Matrix.toLin' Wm) = ⊥)
    (hR : LinearMap.range (Matrix.toLin' S) = LinearMap.range (Matrix.toLin' Wm)) :
    (Wmᵀ * S * Wm).det ≠ 0 := by
  intro hdet
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 : Wmᵀ *ᵥ (S *ᵥ (Wm *ᵥ y)) = 0 := by
    rw [mulVec_mulVec, mulVec_mulVec]
    exact hy
  have hv : S *ᵥ (Wm *ᵥ y) ∈ LinearMap.range (Matrix.toLin' Wm) := hR ▸ mem_range_toLin' S _
  obtain ⟨z, hz⟩ := hv
  rw [Matrix.toLin'_apply] at hz
  have h2 : (S *ᵥ (Wm *ᵥ y)) ⬝ᵥ (S *ᵥ (Wm *ᵥ y)) = 0 := by
    calc (S *ᵥ (Wm *ᵥ y)) ⬝ᵥ (S *ᵥ (Wm *ᵥ y)) = (Wm *ᵥ z) ⬝ᵥ (S *ᵥ (Wm *ᵥ y)) := by rw [hz]
      _ = 0 := by rw [dot_mulVec_transpose, h1, dotProduct_zero]
  have h3 := dotProduct_self_eq_zero.mp h2
  have h4 : Wm *ᵥ y ∈ LinearMap.range (Matrix.toLin' S) := hR.symm ▸ mem_range_toLin' Wm y
  have h5 := skew_inj_on_range S hS _ h4 h3
  apply hy0
  exact LinearMap.ker_eq_bot'.mp hker y (by rw [Matrix.toLin'_apply]; exact h5)

/-- Every subspace is the image of an injective matrix with `finrank` columns. -/
lemma exists_inj_matrix {n : ℕ} (W : Submodule ℝ (Vec n)) :
    ∃ Wm : Matrix (Fin n) (Fin (Module.finrank ℝ W)) ℝ,
      LinearMap.ker (Matrix.toLin' Wm) = ⊥ ∧ LinearMap.range (Matrix.toLin' Wm) = W := by
  let b := Module.finBasis ℝ W
  refine ⟨LinearMap.toMatrix' (W.subtype ∘ₗ b.equivFun.symm.toLinearMap), ?_, ?_⟩
  · rw [Matrix.toLin'_toMatrix', LinearMap.ker_eq_bot]
    exact (Submodule.injective_subtype W).comp b.equivFun.symm.injective
  · rw [Matrix.toLin'_toMatrix', LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      Submodule.range_subtype]

/-- An invertible real skew `r × r` matrix has even size. -/
lemma even_of_skew_det {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (hA : Aᵀ = -A) (hdet : A.det ≠ 0) : Even r := by
  have h1 : A.det = (-1) ^ r * A.det := by
    have h0 := Matrix.det_neg A
    rw [Fintype.card_fin, ← hA, Matrix.det_transpose] at h0
    exact h0
  have h2 : (-1 : ℝ) ^ r = 1 := by
    have h3 : ((-1 : ℝ) ^ r - 1) * A.det = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · exact absurd h4 hdet
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h2

/-- A real skew matrix has even rank. -/
lemma skew_even {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S) :
    Even (Module.finrank ℝ (LinearMap.range (Matrix.toLin' S))) := by
  obtain ⟨Wm, hker, hR⟩ := exists_inj_matrix (LinearMap.range (Matrix.toLin' S))
  exact even_of_skew_det _ (restrict_skew S hS Wm) (restrict_det_ne_zero S hS Wm hker hR.symm)

lemma skew_zero_of_rank_le_one {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S)
    (h1 : Module.finrank ℝ (LinearMap.range (Matrix.toLin' S)) ≤ 1) : S = 0 := by
  obtain ⟨k, hk⟩ := skew_even S hS
  have h0 : Module.finrank ℝ (LinearMap.range (Matrix.toLin' S)) = 0 := by omega
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  exact Matrix.toLin'.injective (by rw [h0, map_zero])

/-! ## Orthonormal bases as matrices -/

/-- Every subspace of dimension `r` is the image of a matrix with `r` orthonormal columns. -/
lemma exists_onb_matrix {n : ℕ} (W : Submodule ℝ (Vec n)) (r : ℕ) (hr : Module.finrank ℝ W = r) :
    ∃ Wm : Matrix (Fin n) (Fin r) ℝ, Wmᵀ * Wm = 1 ∧ LinearMap.range (Matrix.toLin' Wm) = W := by
  let e : Vec n ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  let W' : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := W.map e.toLinearMap
  have hW' : Module.finrank ℝ W' = r := by
    rw [LinearEquiv.finrank_map_eq]
    exact hr
  let b : OrthonormalBasis (Fin r) ℝ W' := (stdOrthonormalBasis ℝ W').reindex (finCongr hW')
  let Wm : Matrix (Fin n) (Fin r) ℝ := Matrix.of fun i k => (b k : EuclideanSpace ℝ (Fin n)).ofLp i
  have horth : Wmᵀ * Wm = 1 := by
    ext k l
    have h := b.inner_eq_ite k l
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    simp only [dotProduct, Wm, Matrix.transpose_apply, Matrix.of_apply, star_trivial]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  refine ⟨Wm, horth, ?_⟩
  have hle : LinearMap.range (Matrix.toLin' Wm) ≤ W := by
    rw [Matrix.toLin'_apply', Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨w, hw, hwk⟩ := Submodule.mem_map.mp (b k).2
    have hcol : Wm.col k = w := by
      ext i
      change (b k : EuclideanSpace ℝ (Fin n)).ofLp i = w i
      rw [← hwk]
      rfl
    rw [SetLike.mem_coe, hcol]
    exact hw
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_range_of_ker_bot Wm (ker_eq_bot_of_orth Wm horth), hr]

/-! ## Skew maps supported on a subspace, and their dimension -/

/-- The skew `n × n` matrices with image in `W`. -/
def skewSupp {n : ℕ} (W : Submodule ℝ (Vec n)) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {M | Mᵀ = -M ∧ LinearMap.range (Matrix.toLin' M) ≤ W}
  add_mem' := by
    rintro M N ⟨hM, hM'⟩ ⟨hN, hN'⟩
    refine ⟨by rw [transpose_add, hM, hN, neg_add], ?_⟩
    rw [range_le_iff] at hM' hN' ⊢
    intro v
    rw [add_mulVec]
    exact W.add_mem (hM' v) (hN' v)
  zero_mem' := by
    refine ⟨by simp, ?_⟩
    rw [range_le_iff]
    intro v
    rw [zero_mulVec]
    exact W.zero_mem
  smul_mem' := by
    rintro c M ⟨hM, hM'⟩
    refine ⟨by rw [transpose_smul, hM, smul_neg], ?_⟩
    rw [range_le_iff] at hM' ⊢
    intro v
    rw [smul_mulVec]
    exact W.smul_mem c (hM' v)

lemma mem_skewSupp {n : ℕ} (W : Submodule ℝ (Vec n)) (M : Matrix (Fin n) (Fin n) ℝ) :
    M ∈ skewSupp W ↔ Mᵀ = -M ∧ LinearMap.range (Matrix.toLin' M) ≤ W := Iff.rfl

/-- The skew `r × r` matrices. -/
def skewSub (r : ℕ) : Submodule ℝ (Matrix (Fin r) (Fin r) ℝ) where
  carrier := {A | Aᵀ = -A}
  add_mem' := by
    rintro A B hA hB
    change (A + B)ᵀ = -(A + B)
    rw [transpose_add, hA, hB, neg_add]
  zero_mem' := by
    change (0 : Matrix (Fin r) (Fin r) ℝ)ᵀ = -0
    simp
  smul_mem' := by
    rintro c A hA
    change (c • A)ᵀ = -(c • A)
    rw [transpose_smul, hA, smul_neg]

lemma mem_skewSub (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) : A ∈ skewSub r ↔ Aᵀ = -A := Iff.rfl

lemma proj_mul_of_range {n r : ℕ} (Wm : Matrix (Fin n) (Fin r) ℝ) (hWm : Wmᵀ * Wm = 1)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : LinearMap.range (Matrix.toLin' M) ≤ LinearMap.range (Matrix.toLin' Wm)) :
    Wm * Wmᵀ * M = M := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  obtain ⟨z, hz⟩ := hM (mem_range_toLin' M v)
  rw [Matrix.toLin'_apply] at hz
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mulVec_mulVec, ← hz, mulVec_mulVec, Matrix.mul_assoc, hWm,
    Matrix.mul_one]

lemma mul_proj_of_skew {n r : ℕ} (Wm : Matrix (Fin n) (Fin r) ℝ) (hWm : Wmᵀ * Wm = 1)
    (M : Matrix (Fin n) (Fin n) ℝ) (hS : Mᵀ = -M)
    (hM : LinearMap.range (Matrix.toLin' M) ≤ LinearMap.range (Matrix.toLin' Wm)) :
    M * (Wm * Wmᵀ) = M := by
  have h := congrArg Matrix.transpose (proj_mul_of_range Wm hWm M hM)
  rw [transpose_mul, transpose_mul, transpose_transpose, hS, Matrix.neg_mul] at h
  exact neg_injective h

/-- Skew maps supported on `W` correspond to skew maps of `ℝ^r`, through an orthonormal basis `Wm` of `W`. -/
noncomputable def suppEquiv {n r : ℕ} (W : Submodule ℝ (Vec n)) (Wm : Matrix (Fin n) (Fin r) ℝ)
    (hWm : Wmᵀ * Wm = 1) (hWr : LinearMap.range (Matrix.toLin' Wm) = W) : skewSupp W ≃ₗ[ℝ] skewSub r where
  toFun M := ⟨Wmᵀ * M.1 * Wm, restrict_skew M.1 ((mem_skewSupp W M.1).mp M.2).1 Wm⟩
  invFun A := ⟨Wm * A.1 * Wmᵀ, by
    refine ⟨?_, ?_⟩
    · rw [transpose_mul, transpose_mul, transpose_transpose, (mem_skewSub r A.1).mp A.2, Matrix.neg_mul,
        Matrix.mul_neg, Matrix.mul_assoc]
    · rw [range_le_iff]
      intro v
      rw [Matrix.mul_assoc, ← mulVec_mulVec, ← hWr]
      exact mem_range_toLin' Wm _⟩
  map_add' M N := by
    apply Subtype.ext
    change Wmᵀ * (M.1 + N.1) * Wm = Wmᵀ * M.1 * Wm + Wmᵀ * N.1 * Wm
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by
    apply Subtype.ext
    change Wmᵀ * (c • M.1) * Wm = c • (Wmᵀ * M.1 * Wm)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  left_inv M := by
    apply Subtype.ext
    change Wm * (Wmᵀ * M.1 * Wm) * Wmᵀ = M.1
    have hM := (mem_skewSupp W M.1).mp M.2
    have h1 := proj_mul_of_range Wm hWm M.1 (hWr ▸ hM.2)
    have h2 := mul_proj_of_skew Wm hWm M.1 hM.1 (hWr ▸ hM.2)
    calc Wm * (Wmᵀ * M.1 * Wm) * Wmᵀ = (Wm * Wmᵀ * M.1) * (Wm * Wmᵀ) := by simp only [Matrix.mul_assoc]
      _ = M.1 := by rw [h1, h2]
  right_inv A := by
    apply Subtype.ext
    change Wmᵀ * (Wm * A.1 * Wmᵀ) * Wm = A.1
    calc Wmᵀ * (Wm * A.1 * Wmᵀ) * Wm = (Wmᵀ * Wm) * A.1 * (Wmᵀ * Wm) := by simp only [Matrix.mul_assoc]
      _ = A.1 := by rw [hWm, Matrix.one_mul, Matrix.mul_one]

/-- The skew matrix with lower-left... upper entries `A_{ij} = f(j, i)` for `i < j`. -/
def skewOf {r : ℕ} (f : (Σ j : Fin r, Fin j.val) → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun a b => if h : a.val < b.val then f ⟨b, ⟨a.val, h⟩⟩
    else if h' : b.val < a.val then -f ⟨a, ⟨b.val, h'⟩⟩ else 0

lemma skewOf_skew {r : ℕ} (f : (Σ j : Fin r, Fin j.val) → ℝ) : (skewOf f)ᵀ = -(skewOf f) := by
  ext a b
  rw [transpose_apply, neg_apply]
  unfold skewOf
  rw [of_apply, of_apply]
  split_ifs <;> first | rfl | (rw [neg_neg]) | simp | omega

lemma skew_entry {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (hA : Aᵀ = -A) (a b : Fin r) : A b a = -A a b := by
  have h := congrFun (congrFun hA a) b
  simpa using h

/-- Coordinates on the skew `r × r` matrices: the entries above the diagonal. -/
noncomputable def skewCoord (r : ℕ) : skewSub r ≃ₗ[ℝ] ((Σ j : Fin r, Fin j.val) → ℝ) where
  toFun A := fun s => A.1 ⟨s.2.val, s.2.isLt.trans s.1.isLt⟩ s.1
  invFun f := ⟨skewOf f, skewOf_skew f⟩
  map_add' A B := rfl
  map_smul' c A := rfl
  left_inv A := by
    apply Subtype.ext
    have hA := (mem_skewSub r A.1).mp A.2
    ext a b
    dsimp only
    unfold skewOf
    rw [of_apply]
    split_ifs with h1 h2
    · rfl
    · change -A.1 b a = A.1 a b
      rw [skew_entry A.1 hA a b, neg_neg]
    · have hab : a = b := Fin.ext (by omega)
      subst hab
      have h3 := skew_entry A.1 hA a a
      linarith
  right_inv f := by
    funext s
    obtain ⟨j, i⟩ := s
    change skewOf f ⟨i.val, _⟩ j = f ⟨j, i⟩
    unfold skewOf
    rw [of_apply]
    split_ifs with h1
    · rfl
    all_goals exact absurd i.isLt h1

lemma card_upper (r : ℕ) : Fintype.card (Σ j : Fin r, Fin j.val) = r * (r - 1) / 2 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

lemma finrank_skewSupp {n : ℕ} (W : Submodule ℝ (Vec n)) :
    Module.finrank ℝ (skewSupp W) = Module.finrank ℝ W * (Module.finrank ℝ W - 1) / 2 := by
  obtain ⟨Wm, hWm, hWr⟩ := exists_onb_matrix W _ rfl
  rw [LinearEquiv.finrank_eq (suppEquiv W Wm hWm hWr), LinearEquiv.finrank_eq (skewCoord _),
    Module.finrank_fintype_fun_eq_card, card_upper]

/-- A linear map from a space `U` into a space of smaller dimension has a nonzero kernel vector. -/
lemma exists_ker {V M : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [AddCommGroup M]
    [Module ℝ M] [FiniteDimensional ℝ M] (U : Submodule ℝ V) (f : V →ₗ[ℝ] M) (S : Submodule ℝ M)
    (hS : ∀ a ∈ U, f a ∈ S) (h : Module.finrank ℝ S < Module.finrank ℝ U) : ∃ a ∈ U, a ≠ 0 ∧ f a = 0 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  have h2 : Module.finrank ℝ (LinearMap.range (f.domRestrict U)) ≤ Module.finrank ℝ S := by
    apply Submodule.finrank_mono
    rw [LinearMap.range_domRestrict, Submodule.map_le_iff_le_comap]
    exact fun a ha => hS a ha
  have h3 : LinearMap.ker (f.domRestrict U) ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h1
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h3
  refine ⟨x, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  simpa using hx

/-! ## Small facts used by the rows -/

lemma finrank_map_inj {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (hf : Function.Injective f) (U : Submodule ℝ V) :
    Module.finrank ℝ (U.map f) = Module.finrank ℝ U :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf U)).symm

lemma range_toLin'_mul {l m n : ℕ} (A : Matrix (Fin l) (Fin m) ℝ) (M : Matrix (Fin m) (Fin n) ℝ) :
    LinearMap.range (Matrix.toLin' (A * M)) = (LinearMap.range (Matrix.toLin' M)).map (Matrix.toLin' A) := by
  rw [Matrix.toLin'_mul, LinearMap.range_comp]

/-- `a ↦ KᵀB(a)` as a linear map. -/
def KBlin (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (K : Matrix (Fin 16) (Fin 8) ℝ) (hlin : IsLinearMap ℝ B) :
    Vec 8 →ₗ[ℝ] Matrix (Fin 8) (Fin 8) ℝ where
  toFun a := Kᵀ * B a
  map_add' a b := by rw [hlin.map_add, Matrix.mul_add]
  map_smul' c a := by rw [hlin.map_smul, Matrix.mul_smul]; rfl

section SettingT

variable {B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ} {E : Submodule ℝ (Vec 16)} {L K : Matrix (Fin 16) (Fin 8) ℝ}
  {g0 : Vec 8}

lemma skewKB (h : SettingT B E L K g0) (a : Vec 8) : (Kᵀ * B a)ᵀ = -(Kᵀ * B a) := (h.2.2.2.2.2.2.2.2 a).2

lemma exists_ne_zero_of_pos {U : Submodule ℝ (Vec 8)} (hU : 0 < Module.finrank ℝ U) : ∃ a ∈ U, a ≠ 0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  intro hb
  rw [hb, finrank_bot] at hU
  exact lt_irrefl 0 hU

/-- If `KᵀB(a) = 0` and `a ≠ 0`, then `Im B(a) = E` ("by rank eight"); `hker` is `ker Kᵀ = E`. -/
lemma range_eq_E (h : SettingT B E L K g0) (hker : LinearMap.ker (Matrix.toLin' Kᵀ) = E) {a : Vec 8} (ha0 : a ≠ 0)
    (hz : Kᵀ * B a = 0) : LinearMap.range (Matrix.toLin' (B a)) = E := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨w, rfl⟩
    rw [← hker, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, hz, zero_mulVec]
  · rw [finrank_range_eq_rank, h.2.2.1 a ha0, h.1]

end SettingT

/-! ## Setting (T) -/

/-- Row `setting_T_change` (StatementsSix.lean v0.41). -/
theorem setting_T_change_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (Cm : Matrix (Fin 8) (Fin 8) ℝ)
    (hC : IsUnit Cm.det) : SettingT (fun a => B (Cm *ᵥ a)) E (L * Cm) K g0 := by
  obtain ⟨hE8, hlin, hrank, hLker, hLran, hKK, hKran, hg0, hrad⟩ := h
  have hCinj : Function.Injective (Matrix.toLin' Cm) := by
    intro u v huv
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at huv
    exact Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det Cm).mpr hC) huv
  have hCsurj : LinearMap.range (Matrix.toLin' Cm) = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hCinj)
  refine ⟨hE8, ⟨fun a b => ?_, fun c a => ?_⟩, fun a ha => ?_, ?_, ?_, hKK, hKran, hg0, fun a => ⟨?_, hrad _ |>.2⟩⟩
  · simp only [mulVec_add, hlin.map_add]
  · simp only [mulVec_smul, hlin.map_smul]
  · refine hrank _ fun h0 => ha (hCinj ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h0, mulVec_zero]
  · rw [Matrix.toLin'_mul, LinearMap.ker_comp, hLker, Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.mpr hCinj
  · rw [Matrix.toLin'_mul, LinearMap.range_comp, hCsurj, Submodule.map_top, hLran]
  · change B (Cm *ᵥ a) *ᵥ g0 = -((L * Cm) *ᵥ a)
    rw [(hrad _).1, mulVec_mulVec]

/-- Row `setting_T_ker_Kt` (StatementsSix.lean v0.41). -/
theorem setting_T_ker_Kt_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) :
    LinearMap.ker (Matrix.toLin' Kᵀ) = E := by
  obtain ⟨hE8, -, -, -, -, hKK, hKran, -, -⟩ := h
  have hle : E ≤ LinearMap.ker (Matrix.toLin' Kᵀ) := by
    intro y hy
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    have hdot : ∀ v, (Kᵀ *ᵥ y) ⬝ᵥ v = 0 := by
      intro v
      rw [dot_mulVec_transpose, transpose_transpose]
      have hKv : K *ᵥ v ∈ orthSub E := hKran ▸ mem_range_toLin' K v
      exact hKv y hy
    exact dotProduct_self_eq_zero.mp (hdot _)
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' Kᵀ)
  have hr : Module.finrank ℝ (LinearMap.range (Matrix.toLin' Kᵀ)) = 8 := by
    rw [finrank_range_eq_rank, Matrix.rank_transpose, ← finrank_range_eq_rank,
      finrank_range_of_ker_bot K (ker_eq_bot_of_orth K hKK)]
  rw [Module.finrank_fin_fun, hr] at hrn
  have hk : Module.finrank ℝ (LinearMap.ker (Matrix.toLin' Kᵀ)) = 8 :=
    Nat.add_left_cancel (hrn.trans (by norm_num : (16 : ℕ) = 8 + 8))
  rw [hE8]
  exact hk.symm

/-! ## Lemma 12.5 -/

/-- Row `lem_12_5_radial` (StatementsSix.lean v0.41). -/
theorem lem_12_5_radial_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1) :
    U.map (Matrix.toLin' L) ≤ V1 ⊓ E := by
  obtain ⟨-, -, -, -, hLran, -, -, -, hrad⟩ := h
  rintro _ ⟨a, ha, rfl⟩
  rw [Submodule.mem_inf]
  refine ⟨?_, hLran ▸ LinearMap.mem_range_self _ a⟩
  by_cases ha0 : a = 0
  · rw [ha0, map_zero]
    exact V1.zero_mem
  · have hLa : L *ᵥ a = B a *ᵥ (-g0) := by rw [mulVec_neg, (hrad a).1, neg_neg]
    rw [Matrix.toLin'_apply, hLa]
    exact hIm a ha ha0 (mem_range_toLin' _ _)

/-- Row `lem_12_5_dim_W` (StatementsSix.lean v0.41). -/
theorem lem_12_5_dim_W_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1) :
    Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) + Module.finrank ℝ ↥(V1 ⊓ E) = Module.finrank ℝ V1 ∧
      Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) + Module.finrank ℝ U ≤ Module.finrank ℝ V1 := by
  have hker := setting_T_ker_Kt_proved B E L K g0 h
  have hrad := lem_12_5_radial_proved B E L K g0 h U V1 hIm
  have hLinj : Function.Injective (Matrix.toLin' L) := LinearMap.ker_eq_bot.mp h.2.2.2.1
  have h1 : Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) + Module.finrank ℝ ↥(V1 ⊓ E) = Module.finrank ℝ V1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker ((Matrix.toLin' Kᵀ).comp V1.subtype)
    have hrange : LinearMap.range ((Matrix.toLin' Kᵀ).comp V1.subtype) = V1.map (Matrix.toLin' Kᵀ) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hmap : (LinearMap.ker ((Matrix.toLin' Kᵀ).comp V1.subtype)).map V1.subtype = V1 ⊓ E := by
      rw [LinearMap.ker_comp, hker, Submodule.map_comap_subtype]
    have hkerg : Module.finrank ℝ (LinearMap.ker ((Matrix.toLin' Kᵀ).comp V1.subtype)) =
        Module.finrank ℝ ↥(V1 ⊓ E) := by
      rw [← hmap, finrank_map_inj V1.subtype (Submodule.injective_subtype V1)]
    rw [hrange, hkerg] at hrn
    exact hrn
  have h2 : Module.finrank ℝ U ≤ Module.finrank ℝ ↥(V1 ⊓ E) := by
    rw [← finrank_map_inj _ hLinj U]
    exact Submodule.finrank_mono hrad
  exact ⟨h1, by omega⟩

/-- Row `lem_12_5_image_W` (StatementsSix.lean v0.41). -/
theorem lem_12_5_image_W_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1) :
    ∀ a ∈ U, LinearMap.range (Matrix.toLin' (Kᵀ * B a)) ≤ V1.map (Matrix.toLin' Kᵀ) ∧
      (Kᵀ * B a)ᵀ = -(Kᵀ * B a) := by
  intro a ha
  refine ⟨?_, skewKB h a⟩
  rw [range_toLin'_mul]
  by_cases ha0 : a = 0
  · rw [ha0, h.2.1.map_zero, map_zero, LinearMap.range_zero, Submodule.map_bot]
    exact bot_le
  · exact Submodule.map_mono (hIm a ha ha0)

/-- Row `lem_12_5_1_W` (StatementsSix.lean v0.41). -/
theorem lem_12_5_1_W_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) :
    Module.finrank ℝ V1 = 8 ∧ Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) ≤ 4 ∧
      ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (Kᵀ * B a)) = V1.map (Matrix.toLin' Kᵀ) := by
  have hdim := lem_12_5_dim_W_proved B E L K g0 h U V1 (fun a ha ha0 => (hIm a ha ha0).le)
  obtain ⟨a0, ha0U, ha00⟩ := exists_ne_zero_of_pos (U := U) (by omega)
  have hV8 : Module.finrank ℝ V1 = 8 := by
    rw [← hIm a0 ha0U ha00, finrank_range_eq_rank, h.2.2.1 a0 ha00]
  refine ⟨hV8, by omega, fun a ha ha0 => ?_⟩
  rw [range_toLin'_mul, hIm a ha ha0]

/-- Row `lem_12_5_skew_facts` (StatementsSix.lean v0.41). -/
theorem lem_12_5_skew_facts_proved {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S) :
    LinearMap.ker (Matrix.toLin' S) = orthSub (LinearMap.range (Matrix.toLin' S)) ∧
      (∀ v ∈ LinearMap.range (Matrix.toLin' S), S *ᵥ v = 0 → v = 0) ∧
      Even (Module.finrank ℝ (LinearMap.range (Matrix.toLin' S))) ∧
      (Module.finrank ℝ (LinearMap.range (Matrix.toLin' S)) ≤ 1 → S = 0) :=
  ⟨skew_ker_eq S hS, fun v hv h0 => skew_inj_on_range S hS v hv h0, skew_even S hS, skew_zero_of_rank_le_one S hS⟩

/-- Row `lem_12_5_1_r_even` (StatementsSix.lean v0.41). -/
theorem lem_12_5_1_r_even_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) :
    Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) = 0 ∨ Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) = 2 ∨
      Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) = 4 := by
  have hW := lem_12_5_1_W_proved B E L K g0 h U V1 hIm hU
  obtain ⟨a0, ha0U, ha00⟩ := exists_ne_zero_of_pos (U := U) (by omega)
  have heven := skew_even _ (skewKB h a0)
  rw [hW.2.2 a0 ha0U ha00] at heven
  obtain ⟨k, hk⟩ := heven
  have h4 := hW.2.1
  omega

/-- Row `lem_12_5_skew_supported` (StatementsSix.lean v0.41). -/
theorem lem_12_5_skew_supported_proved {n : ℕ} (W : Submodule ℝ (Vec n)) :
    ∃ S : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ),
      (∀ M, M ∈ S ↔ Mᵀ = -M ∧ LinearMap.range (Matrix.toLin' M) ≤ W) ∧
      Module.finrank ℝ S = Module.finrank ℝ W * (Module.finrank ℝ W - 1) / 2 :=
  ⟨skewSupp W, mem_skewSupp W, finrank_skewSupp W⟩

/-- Row `lem_12_5_1_restrict` (StatementsSix.lean v0.41). -/
theorem lem_12_5_1_restrict_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) {r : ℕ} (Wm : Matrix (Fin 8) (Fin r) ℝ) (hWm : Wmᵀ * Wm = 1)
    (hWr : LinearMap.range (Matrix.toLin' Wm) = V1.map (Matrix.toLin' Kᵀ)) :
    Module.finrank ℝ U + r ≤ 8 ∧ (0 < r → ∀ a ∈ U, Kᵀ * B a = 0 → a = 0) ∧
      (∀ a ∈ U, (Wmᵀ * (Kᵀ * B a) * Wm)ᵀ = -(Wmᵀ * (Kᵀ * B a) * Wm)) ∧
      ∀ a ∈ U, a ≠ 0 → (Wmᵀ * (Kᵀ * B a) * Wm).det ≠ 0 := by
  have hW := lem_12_5_1_W_proved B E L K g0 h U V1 hIm hU
  have hdim := lem_12_5_dim_W_proved B E L K g0 h U V1 (fun a ha ha0 => (hIm a ha ha0).le)
  have hr : Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) = r := by
    rw [← hWr, finrank_range_of_ker_bot Wm (ker_eq_bot_of_orth Wm hWm)]
  refine ⟨by have := hdim.2; have := hW.1; omega, fun hr0 a ha hz => ?_, fun a _ => restrict_skew _ (skewKB h a) Wm,
    fun a ha ha0 => restrict_det_ne_zero _ (skewKB h a) Wm (ker_eq_bot_of_orth Wm hWm) (by rw [hW.2.2 a ha ha0, hWr])⟩
  by_contra ha0
  have h1 := hW.2.2 a ha ha0
  rw [hz, map_zero, LinearMap.range_zero] at h1
  rw [← h1, finrank_bot] at hr
  omega

/-- Row `lem_12_5_1_r_ne_2` (StatementsSix.lean v0.41). -/
theorem lem_12_5_1_r_ne_2_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) :
    Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) ≠ 2 := by
  intro h2
  have hW := lem_12_5_1_W_proved B E L K g0 h U V1 hIm hU
  have himg := lem_12_5_image_W_proved B E L K g0 h U V1 (fun a ha ha0 => (hIm a ha ha0).le)
  obtain ⟨a, ha, ha0, hfa⟩ := exists_ker U (KBlin B K h.2.1) (skewSupp (V1.map (Matrix.toLin' Kᵀ)))
    (fun a ha => ⟨skewKB h a, (himg a ha).1⟩) (by rw [finrank_skewSupp, h2]; omega)
  have h1 := hW.2.2 a ha ha0
  rw [show Kᵀ * B a = 0 from hfa, map_zero, LinearMap.range_zero] at h1
  rw [← h1, finrank_bot] at h2
  omega

/-- `a ↦ Wmᵀ(KᵀB(a))Wm` as a linear map. -/
def restrictLin (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (K : Matrix (Fin 16) (Fin 8) ℝ) (hlin : IsLinearMap ℝ B)
    {r : ℕ} (Wm : Matrix (Fin 8) (Fin r) ℝ) : Vec 8 →ₗ[ℝ] Matrix (Fin r) (Fin r) ℝ where
  toFun a := Wmᵀ * (Kᵀ * B a) * Wm
  map_add' a b := by rw [hlin.map_add, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c a := by rw [hlin.map_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul]; rfl

/-- Row `lem_12_5_1_r_ne_4` (StatementsSix.lean v0.41). -/
theorem lem_12_5_1_r_ne_4_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) :
    Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) ≠ 4 := by
  intro h4
  obtain ⟨Wm, hWm, hWr⟩ := exists_onb_matrix (V1.map (Matrix.toLin' Kᵀ)) 4 h4
  have hres := lem_12_5_1_restrict_proved B E L K g0 h U V1 hIm hU Wm hWm hWr
  let g := (restrictLin B K h.2.1 Wm).domRestrict U
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a hga
    by_contra ha0
    have hne : (a : Vec 8) ≠ 0 := fun h0 => ha0 (Subtype.ext h0)
    apply hres.2.2.2 a a.2 hne
    have hz : Wmᵀ * (Kᵀ * B a) * Wm = 0 := hga
    rw [hz, Matrix.det_zero]
  have hfr : Module.finrank ℝ (LinearMap.range g) = Module.finrank ℝ U := LinearMap.finrank_range_of_inj hinj
  obtain ⟨A, hA, hA0, hdet⟩ := Osserman.Proofs.Six1.lem_12_4_proved (LinearMap.range g)
    (by rintro _ ⟨a, rfl⟩; exact hres.2.2.1 a a.2) (by rw [hfr]; exact hU)
  obtain ⟨a, rfl⟩ := hA
  have ha0 : (a : Vec 8) ≠ 0 := by
    intro h0
    apply hA0
    change restrictLin B K h.2.1 Wm a = 0
    rw [h0, map_zero]
  exact hres.2.2.2 a a.2 ha0 hdet

/-- Row `lem_12_5_1_r_zero` (StatementsSix.lean v0.41). -/
theorem lem_12_5_1_r_zero_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) :
    Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) = 0 ∧ V1 ≤ E ∧ V1 = E := by
  have hker := setting_T_ker_Kt_proved B E L K g0 h
  have hW := lem_12_5_1_W_proved B E L K g0 h U V1 hIm hU
  have h0 : Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) = 0 := by
    rcases lem_12_5_1_r_even_proved B E L K g0 h U V1 hIm hU with h0 | h2 | h4
    · exact h0
    · exact absurd h2 (lem_12_5_1_r_ne_2_proved B E L K g0 h U V1 hIm hU)
    · exact absurd h4 (lem_12_5_1_r_ne_4_proved B E L K g0 h U V1 hIm hU)
  have hle : V1 ≤ E := by
    intro v hv
    rw [← hker, LinearMap.mem_ker]
    have hmem : Matrix.toLin' Kᵀ v ∈ V1.map (Matrix.toLin' Kᵀ) := Submodule.mem_map_of_mem hv
    rw [Submodule.finrank_eq_zero.mp h0] at hmem
    exact (Submodule.mem_bot ℝ).mp hmem
  exact ⟨h0, hle, Submodule.eq_of_le_of_finrank_eq hle (by rw [hW.1, h.1])⟩

/-- Row `lem_12_5_1` (StatementsSix.lean v0.41). -/
theorem lem_12_5_1_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) : V1 = E :=
  (lem_12_5_1_r_zero_proved B E L K g0 h U V1 hIm hU).2.2

/-- Row `lem_12_5_2_W` (StatementsSix.lean v0.41). -/
theorem lem_12_5_2_W_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1)
    (hV : Module.finrank ℝ V1 ≤ 9) (hU : 7 ≤ Module.finrank ℝ U) :
    Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) ≤ 2 ∧
      ∃ S : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℝ), Module.finrank ℝ S ≤ 1 ∧ (∀ M ∈ S, Mᵀ = -M) ∧
        ∀ a ∈ U, Kᵀ * B a ∈ S := by
  have hdim := lem_12_5_dim_W_proved B E L K g0 h U V1 hIm
  have himg := lem_12_5_image_W_proved B E L K g0 h U V1 hIm
  have hr : Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) ≤ 2 := by have := hdim.2; omega
  refine ⟨hr, skewSupp (V1.map (Matrix.toLin' Kᵀ)), ?_, fun M hM => hM.1, fun a ha => ⟨skewKB h a, (himg a ha).1⟩⟩
  rw [finrank_skewSupp]
  generalize Module.finrank ℝ ↥(V1.map (Matrix.toLin' Kᵀ)) = r at hr ⊢
  interval_cases r <;> norm_num

/-- Row `lem_12_5_2_a0` (StatementsSix.lean v0.41). -/
theorem lem_12_5_2_a0_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1)
    (hV : Module.finrank ℝ V1 ≤ 9) (hU : 7 ≤ Module.finrank ℝ U) :
    ∃ a0 ∈ U, a0 ≠ 0 ∧ Kᵀ * B a0 = 0 ∧ LinearMap.range (Matrix.toLin' (B a0)) = E ∧ E ≤ V1 ∧
      Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) ≤ 1 := by
  have hker := setting_T_ker_Kt_proved B E L K g0 h
  have hdim := lem_12_5_dim_W_proved B E L K g0 h U V1 hIm
  obtain ⟨-, S, hS1, -, hSmem⟩ := lem_12_5_2_W_proved B E L K g0 h U V1 hIm hV hU
  obtain ⟨a0, ha0, ha00, hfa⟩ := exists_ker U (KBlin B K h.2.1) S hSmem (by omega)
  have hKB : Kᵀ * B a0 = 0 := hfa
  have hrE := range_eq_E h hker ha00 hKB
  have hEV : E ≤ V1 := hrE ▸ hIm a0 ha0 ha00
  refine ⟨a0, ha0, ha00, hKB, hrE, hEV, ?_⟩
  have h1 := hdim.1
  rw [inf_eq_right.mpr hEV, h.1] at h1
  omega

/-- Row `lem_12_5_2_zero` (StatementsSix.lean v0.41). -/
theorem lem_12_5_2_zero_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1)
    (hV : Module.finrank ℝ V1 ≤ 9) (hU : 7 ≤ Module.finrank ℝ U) :
    ∀ a ∈ U, Kᵀ * B a = 0 ∧ (a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = E) := by
  have hker := setting_T_ker_Kt_proved B E L K g0 h
  have himg := lem_12_5_image_W_proved B E L K g0 h U V1 hIm
  obtain ⟨-, -, -, -, -, -, hW1⟩ := lem_12_5_2_a0_proved B E L K g0 h U V1 hIm hV hU
  intro a ha
  have hz : Kᵀ * B a = 0 :=
    skew_zero_of_rank_le_one _ (skewKB h a) ((Submodule.finrank_mono (himg a ha).1).trans hW1)
  exact ⟨hz, fun ha0 => range_eq_E h hker ha0 hz⟩

/-- Row `lem_12_5_2` (StatementsSix.lean v0.41). -/
theorem lem_12_5_2_proved (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1)
    (hV : Module.finrank ℝ V1 ≤ 9) (hU : 7 ≤ Module.finrank ℝ U) :
    ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = E :=
  fun a ha ha0 => (lem_12_5_2_zero_proved B E L K g0 h U V1 hIm hV hU a ha).2 ha0

/-! ## Setting (T) is met: `E` = the first octonion coordinate, `B(a)g = (-(a·g), 0)`, `g₀ = 1` -/

section NonVacuous

/-- Two vectors with the same dot product against every vector are equal. -/
lemma vec_eq_of_dot {n : ℕ} {u v : Vec n} (h : ∀ w, u ⬝ᵥ w = v ⬝ᵥ w) : u = v :=
  funext fun i => by simpa [dotProduct_single] using h (Pi.single i 1)

/-- `g ↦ (-(a·g), 0)`. -/
def nvBlin (a : Vec 8) : Vec 8 →ₗ[ℝ] Vec 16 where
  toFun g := octPair (-(omul a g)) 0
  map_add' g g' := by rw [omul_add_right, neg_add, pair_add, add_zero]
  map_smul' c g := by rw [omul_smul_right, RingHom.id_apply, pair_smul, smul_neg, smul_zero]

/-- `a ↦ (a, 0)`. -/
def nvLlin : Vec 8 →ₗ[ℝ] Vec 16 where
  toFun a := octPair a 0
  map_add' a a' := by rw [pair_add, add_zero]
  map_smul' c a := by rw [RingHom.id_apply, pair_smul, smul_zero]

/-- `b ↦ (0, b)`. -/
def nvKlin : Vec 8 →ₗ[ℝ] Vec 16 where
  toFun b := octPair 0 b
  map_add' b b' := by rw [pair_add, add_zero]
  map_smul' c b := by rw [RingHom.id_apply, pair_smul, smul_zero]

noncomputable def nvB (a : Vec 8) : Matrix (Fin 16) (Fin 8) ℝ := LinearMap.toMatrix' (nvBlin a)
noncomputable def nvL : Matrix (Fin 16) (Fin 8) ℝ := LinearMap.toMatrix' nvLlin
noncomputable def nvK : Matrix (Fin 16) (Fin 8) ℝ := LinearMap.toMatrix' nvKlin

lemma toMatrix'_mulVec' {m n : ℕ} (f : Vec n →ₗ[ℝ] Vec m) (v : Vec n) : LinearMap.toMatrix' f *ᵥ v = f v := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

lemma nvB_mulVec (a g : Vec 8) : nvB a *ᵥ g = octPair (-(omul a g)) 0 := toMatrix'_mulVec' _ g
lemma nvL_mulVec (a : Vec 8) : nvL *ᵥ a = octPair a 0 := toMatrix'_mulVec' _ a
lemma nvK_mulVec (b : Vec 8) : nvK *ᵥ b = octPair 0 b := toMatrix'_mulVec' _ b

lemma pair_eq_zero {a b : Vec 8} (h : octPair a b = 0) : a = 0 ∧ b = 0 := by
  have h1 := congrArg oct1 h
  have h2 := congrArg oct2 h
  rw [first_pair] at h1
  rw [second_pair] at h2
  refine ⟨h1.trans ?_, h2.trans ?_⟩ <;> rfl

lemma ker_bot_of_inj {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (h : ∀ v, M *ᵥ v = 0 → v = 0) :
    LinearMap.ker (Matrix.toLin' M) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv
  exact h v (by rw [← Matrix.toLin'_apply]; exact hv)

lemma nvKt_mulVec (y : Vec 16) (w : Vec 8) : (nvKᵀ *ᵥ y) ⬝ᵥ w = oct2 y ⬝ᵥ w := by
  rw [dot_mulVec_transpose, transpose_transpose, nvK_mulVec, ← pair_parts y, pair_dot, dotProduct_zero, zero_add,
    second_pair]

lemma nvK_orth : nvKᵀ * nvK = 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← mulVec_mulVec, one_mulVec]
  exact vec_eq_of_dot fun w => by rw [nvKt_mulVec, nvK_mulVec, second_pair]

lemma nvKt_nvB (a : Vec 8) : nvKᵀ * nvB a = 0 := by
  rw [Matrix.ext_iff_mulVec]
  intro g
  rw [← mulVec_mulVec, zero_mulVec]
  exact vec_eq_of_dot fun w => by rw [nvKt_mulVec, nvB_mulVec, second_pair, zero_dotProduct]

lemma nvE_finrank : Module.finrank ℝ (LinearMap.range (Matrix.toLin' nvL)) = 8 := by
  apply finrank_range_of_ker_bot
  refine ker_bot_of_inj _ fun a ha => ?_
  rw [nvL_mulVec] at ha
  exact (pair_eq_zero ha).1

lemma nvK_range : LinearMap.range (Matrix.toLin' nvK) = orthSub (LinearMap.range (Matrix.toLin' nvL)) := by
  ext y
  rw [mem_orthSub]
  constructor
  · rintro ⟨b, rfl⟩ _ ⟨a, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, nvL_mulVec, nvK_mulVec, pair_dot, dotProduct_zero,
      zero_dotProduct, add_zero]
  · intro hy
    have h1 : oct1 y = 0 := by
      have h := hy (nvL *ᵥ oct1 y) (mem_range_toLin' _ _)
      rw [nvL_mulVec, ← pair_parts y, pair_dot, zero_dotProduct, add_zero, first_pair] at h
      exact dotProduct_self_eq_zero.mp h
    refine ⟨oct2 y, ?_⟩
    rw [Matrix.toLin'_apply, nvK_mulVec, ← h1, pair_parts]

lemma nvB_rank (a : Vec 8) (ha : a ≠ 0) : (nvB a).rank = 8 := by
  rw [← finrank_range_eq_rank]
  apply finrank_range_of_ker_bot
  refine ker_bot_of_inj _ fun g hg => ?_
  rw [nvB_mulVec] at hg
  have h1 := neg_eq_zero.mp (pair_eq_zero hg).1
  have h2 := oct_norm_mul_proved a g
  rw [h1, dotProduct_zero] at h2
  have ha2 : a ⬝ᵥ a ≠ 0 := fun h => ha (dotProduct_self_eq_zero.mp h)
  exact dotProduct_self_eq_zero.mp ((mul_eq_zero.mp h2.symm).resolve_left ha2)

lemma nvB_linear : IsLinearMap ℝ nvB := by
  refine ⟨fun a b => ?_, fun c a => ?_⟩
  · rw [Matrix.ext_iff_mulVec]
    intro g
    rw [add_mulVec, nvB_mulVec, nvB_mulVec, nvB_mulVec, omul_add_left, neg_add, pair_add, add_zero]
  · rw [Matrix.ext_iff_mulVec]
    intro g
    rw [smul_mulVec, nvB_mulVec, nvB_mulVec, omul_smul_left, pair_smul, smul_neg, smul_zero]

/-- Row `settingT_nonvacuous` (StatementsSix.lean v0.41). -/
theorem settingT_nonvacuous_proved :
    ∃ (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16)) (L K : Matrix (Fin 16) (Fin 8) ℝ)
      (g0 : Vec 8), SettingT B E L K g0 := by
  refine ⟨nvB, LinearMap.range (Matrix.toLin' nvL), nvL, nvK, oone, nvE_finrank, nvB_linear, nvB_rank, ?_, rfl,
    nvK_orth, nvK_range, ?_, fun a => ⟨?_, ?_⟩⟩
  · refine ker_bot_of_inj _ fun a ha => ?_
    rw [nvL_mulVec] at ha
    exact (pair_eq_zero ha).1
  · intro h0
    have h1 := congrFun h0 0
    simp [oone] at h1
  · rw [nvB_mulVec, omul_one, nvL_mulVec, ← neg_one_smul ℝ (octPair a 0), pair_smul, neg_one_smul, smul_zero]
  · rw [nvKt_nvB, transpose_zero, neg_zero]

end NonVacuous

end Osserman.Proofs.Six3
