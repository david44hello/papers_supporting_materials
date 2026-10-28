/-
Osserman/Proofs/Six1.lean — proofs of the rows of Lemmas 12.1, 12.4 and 12.6 of paper 013 (sec_common_lemmas.tex
l. 29-47, 83-95, 133-143), statements in Osserman/Paper/StatementsSix.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.SixPieces
namespace Osserman.Proofs.Six1
open Osserman Matrix

/-
Six1.lean — proofs of the rows of Lemmas 12.1, 12.4, 12.6 of paper 013 (sec_common_lemmas.tex), rows of
Osserman/Paper/StatementsSix.lean copied verbatim with suffix `_proved`.
-/

/-! ## Lemma 12.1 -/

lemma mem_ker_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Vec n) :
    v ∈ LinearMap.ker (Matrix.toLin' M) ↔ M *ᵥ v = 0 := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply]

lemma quad_pencil {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (v : Vec n) :
    v ⬝ᵥ ((D1 + s • D0) *ᵥ v) = v ⬝ᵥ (D1 *ᵥ v) + s * v ⬝ᵥ (D0 *ᵥ v) := by
  rw [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]

lemma psd_nonneg {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) (v : Vec n) :
    0 ≤ v ⬝ᵥ (P *ᵥ v) := by
  simpa using hP.dotProduct_mulVec_nonneg v

theorem lem_12_1_psd_null_proved {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) (v : Vec n)
    (hv : v ⬝ᵥ (P *ᵥ v) = 0) : P *ᵥ v = 0 := by
  have h := hP.dotProduct_mulVec_zero_iff (x := v)
  simp only [star_trivial] at h
  exact h.mp hv

theorem lem_12_1_psd_sum_ker_proved {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) :
    LinearMap.ker (Matrix.toLin' (P + Q)) = LinearMap.ker (Matrix.toLin' P) ⊓ LinearMap.ker (Matrix.toLin' Q) := by
  ext v
  simp only [Submodule.mem_inf, mem_ker_iff]
  constructor
  · intro h
    have hP0 := psd_nonneg P hP v
    have hQ0 := psd_nonneg Q hQ v
    have hsum : v ⬝ᵥ (P *ᵥ v) + v ⬝ᵥ (Q *ᵥ v) = 0 := by
      rw [← dotProduct_add, ← add_mulVec, h, dotProduct_zero]
    exact ⟨lem_12_1_psd_null_proved P hP v (by linarith),
      lem_12_1_psd_null_proved Q hQ v (by linarith)⟩
  · rintro ⟨h1, h2⟩
    rw [add_mulVec, h1, h2, add_zero]

theorem lem_12_1_two_points_proved {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (t1 t2 : ℝ) (h : t1 ≠ t2) :
    LinearMap.ker (Matrix.toLin' (D1 + t1 • D0)) ⊓ LinearMap.ker (Matrix.toLin' (D1 + t2 • D0)) =
      LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) := by
  ext v
  simp only [Submodule.mem_inf, mem_ker_iff, add_mulVec, smul_mulVec]
  constructor
  · rintro ⟨h1, h2⟩
    have e : (t1 - t2) • (D0 *ᵥ v) = (D1 *ᵥ v + t1 • D0 *ᵥ v) - (D1 *ᵥ v + t2 • D0 *ᵥ v) := by
      rw [sub_smul]; abel
    rw [h1, h2, sub_zero] at e
    have hD0 : D0 *ᵥ v = 0 := (smul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr h)
    rw [hD0, smul_zero, add_zero] at h1
    exact ⟨hD0, h1⟩
  · rintro ⟨h0, h1⟩
    simp [h0, h1]

/-- The scalar core of the interior step: an affine function, nonnegative at `t1 < t < t2` and zero at `t`, vanishes
at `t1` and `t2`. -/
lemma affine_zero {a b t t1 t2 : ℝ} (h1 : t1 < t) (h2 : t < t2) (h : a + t * b = 0) (g1 : 0 ≤ a + t1 * b)
    (g2 : 0 ≤ a + t2 * b) : a + t1 * b = 0 ∧ a + t2 * b = 0 := by
  have hb1 : b ≤ 0 := by nlinarith
  have hb2 : 0 ≤ b := by nlinarith
  have hb : b = 0 := le_antisymm hb1 hb2
  subst hb
  constructor <;> linarith

theorem lem_12_1_interior_split_proved {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (h0 : D0ᵀ = D0) (h1 : D1ᵀ = D1)
    (I : Set ℝ) (hI : I.OrdConnected) (hint : (interior I).Nonempty) (hpsd : ∀ t ∈ I, (D1 + t • D0).PosSemidef) :
    ∀ t ∈ interior I, (∃ t1 ∈ I, ∃ t2 ∈ I, t1 < t ∧ t < t2) ∧
      ∀ t1 ∈ I, ∀ t2 ∈ I, t1 < t → t < t2 →
        LinearMap.ker (Matrix.toLin' (D1 + t • D0)) =
          LinearMap.ker (Matrix.toLin' (D1 + t1 • D0)) ⊓ LinearMap.ker (Matrix.toLin' (D1 + t2 • D0)) := by
  intro t ht
  refine ⟨?_, ?_⟩
  · obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (mem_interior_iff_mem_nhds.mp ht)
    refine ⟨(l + t) / 2, hsub ⟨by linarith, by linarith⟩, (t + u) / 2, hsub ⟨by linarith, by linarith⟩,
      by linarith, by linarith⟩
  · intro t1 ht1 t2 ht2 hlt1 hlt2
    have htI : t ∈ I := interior_subset ht
    apply le_antisymm
    · intro v hv
      rw [mem_ker_iff] at hv
      have hq : v ⬝ᵥ ((D1 + t • D0) *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
      have g1 := psd_nonneg _ (hpsd t1 ht1) v
      have g2 := psd_nonneg _ (hpsd t2 ht2) v
      rw [quad_pencil] at hq g1 g2
      obtain ⟨z1, z2⟩ := affine_zero hlt1 hlt2 hq g1 g2
      rw [← quad_pencil] at z1 z2
      exact ⟨(mem_ker_iff _ v).mpr (lem_12_1_psd_null_proved _ (hpsd t1 ht1) v z1),
        (mem_ker_iff _ v).mpr (lem_12_1_psd_null_proved _ (hpsd t2 ht2) v z2)⟩
    · intro v hv
      rw [lem_12_1_two_points_proved D0 D1 t1 t2 (by linarith)] at hv
      have hv' := hv
      simp only [Submodule.mem_inf, mem_ker_iff] at hv' ⊢
      rw [add_mulVec, smul_mulVec, hv'.1, hv'.2, smul_zero, add_zero]

theorem lem_12_1_proved {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (h0 : D0ᵀ = D0) (h1 : D1ᵀ = D1) (I : Set ℝ)
    (hI : I.OrdConnected) (hint : (interior I).Nonempty) (hpsd : ∀ t ∈ I, (D1 + t • D0).PosSemidef) :
    ∀ t ∈ interior I, LinearMap.ker (Matrix.toLin' (D1 + t • D0)) =
      LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) := by
  intro t ht
  obtain ⟨⟨t1, ht1, t2, ht2, hlt1, hlt2⟩, hsplit⟩ :=
    lem_12_1_interior_split_proved D0 D1 h0 h1 I hI hint hpsd t ht
  rw [hsplit t1 ht1 t2 ht2 hlt1 hlt2, lem_12_1_two_points_proved D0 D1 t1 t2 (by linarith)]

lemma finrank_ker_add_rank {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' M)) + M.rank = n := by
  rw [Matrix.rank, Matrix.toLin'_apply', add_comm, LinearMap.finrank_range_add_finrank_ker,
    Module.finrank_fin_fun]

lemma finrank_range_eq_rank {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' M)) = M.rank := by
  rw [Matrix.rank, Matrix.toLin'_apply']

theorem lem_12_1_rank_eq_proved {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) :
    (∀ t : ℝ, LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) ≤
      LinearMap.ker (Matrix.toLin' (D1 + t • D0))) ∧
    ∀ t t' : ℝ, LinearMap.ker (Matrix.toLin' (D1 + t' • D0)) =
        LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) →
      (D1 + t • D0).rank = (D1 + t' • D0).rank →
      LinearMap.ker (Matrix.toLin' (D1 + t • D0)) =
        LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) := by
  have hle : ∀ t : ℝ, LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) ≤
      LinearMap.ker (Matrix.toLin' (D1 + t • D0)) := by
    intro t v hv
    simp only [Submodule.mem_inf, mem_ker_iff] at hv ⊢
    rw [add_mulVec, smul_mulVec, hv.1, hv.2, smul_zero, add_zero]
  refine ⟨hle, ?_⟩
  intro t t' hker hrank
  symm
  apply Submodule.eq_of_le_of_finrank_eq (hle t)
  have e1 := finrank_ker_add_rank (D1 + t • D0)
  have e2 := finrank_ker_add_rank (D1 + t' • D0)
  rw [hker] at e2
  omega

theorem lem_12_1_endpoint_proved {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (h0 : D0ᵀ = D0) (h1 : D1ᵀ = D1)
    (I : Set ℝ) (hI : I.OrdConnected) (hint : (interior I).Nonempty) (hpsd : ∀ t ∈ I, (D1 + t • D0).PosSemidef) :
    ∀ t t' : ℝ, t' ∈ interior I → (D1 + t • D0).rank = (D1 + t' • D0).rank →
      LinearMap.ker (Matrix.toLin' (D1 + t • D0)) =
        LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) := by
  intro t t' ht' hrank
  exact (lem_12_1_rank_eq_proved D0 D1).2 t t' (lem_12_1_proved D0 D1 h0 h1 I hI hint hpsd t' ht') hrank

/-- `orthSub` is the orthogonal complement for the dot-product bilinear form. -/
lemma orthSub_eq_orthogonal {n : ℕ} (W : Submodule ℝ (Vec n)) :
    orthSub W = LinearMap.BilinForm.orthogonal (dotProductBilin ℝ ℝ : LinearMap.BilinForm ℝ (Vec n)) W := by
  ext y
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  rfl

lemma finrank_orthSub {n : ℕ} (W : Submodule ℝ (Vec n)) :
    Module.finrank ℝ W + Module.finrank ℝ (orthSub W) = n := by
  have hker : LinearMap.ker (dotProductBilin ℝ ℝ : LinearMap.BilinForm ℝ (Vec n)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact dotProduct_eq_zero v (fun w => by simpa using LinearMap.congr_fun hv w)
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal'
    (B := (dotProductBilin ℝ ℝ : LinearMap.BilinForm ℝ (Vec n))) W
  rw [hker, inf_bot_eq, finrank_bot, add_zero, Module.finrank_fin_fun] at h
  rw [orthSub_eq_orthogonal]
  exact h

lemma orthSub_orthSub {n : ℕ} (W : Submodule ℝ (Vec n)) : orthSub (orthSub W) = W := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro w hw y hy
    rw [dotProduct_comm]
    exact hy w hw
  · have e1 := finrank_orthSub W
    have e2 := finrank_orthSub (orthSub W)
    omega

lemma dot_sym {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (a y : Vec n) :
    (M *ᵥ a) ⬝ᵥ y = a ⬝ᵥ (M *ᵥ y) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]

lemma orthSub_range_sup {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (h0 : D0ᵀ = D0) (h1 : D1ᵀ = D1) :
    orthSub (LinearMap.range (Matrix.toLin' D0) ⊔ LinearMap.range (Matrix.toLin' D1)) =
      LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) := by
  ext y
  simp only [Submodule.mem_inf, mem_ker_iff]
  constructor
  · intro hy
    have hy' : ∀ r ∈ LinearMap.range (Matrix.toLin' D0) ⊔ LinearMap.range (Matrix.toLin' D1), r ⬝ᵥ y = 0 := hy
    constructor
    · apply dotProduct_eq_zero
      intro a
      rw [dotProduct_comm, ← dot_sym D0 h0]
      exact hy' _ (Submodule.mem_sup_left (LinearMap.mem_range_self _ a))
    · apply dotProduct_eq_zero
      intro a
      rw [dotProduct_comm, ← dot_sym D1 h1]
      exact hy' _ (Submodule.mem_sup_right (LinearMap.mem_range_self _ a))
  · rintro ⟨hy0, hy1⟩
    show ∀ r ∈ LinearMap.range (Matrix.toLin' D0) ⊔ LinearMap.range (Matrix.toLin' D1), r ⬝ᵥ y = 0
    intro r hr
    obtain ⟨r0, hr0, r1, hr1, rfl⟩ := Submodule.mem_sup.mp hr
    obtain ⟨a, rfl⟩ := hr0
    obtain ⟨b, rfl⟩ := hr1
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, add_dotProduct, dot_sym D0 h0, dot_sym D1 h1, hy0, hy1,
      dotProduct_zero, dotProduct_zero, add_zero]

theorem lem_12_1_orth_proved {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (h0 : D0ᵀ = D0) (h1 : D1ᵀ = D1) :
    orthSub (LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1)) =
      LinearMap.range (Matrix.toLin' D0) ⊔ LinearMap.range (Matrix.toLin' D1) := by
  rw [← orthSub_range_sup D0 D1 h0 h1, orthSub_orthSub]

theorem lem_12_1_image_proved {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (h0 : D0ᵀ = D0) (h1 : D1ᵀ = D1)
    (I : Set ℝ) (hI : I.OrdConnected) (hint : (interior I).Nonempty) (hpsd : ∀ t ∈ I, (D1 + t • D0).PosSemidef) :
    ∀ t ∈ interior I, LinearMap.range (Matrix.toLin' (D1 + t • D0)) =
      LinearMap.range (Matrix.toLin' D0) ⊔ LinearMap.range (Matrix.toLin' D1) := by
  intro t ht
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, rfl⟩
    rw [Matrix.toLin'_apply, add_mulVec, smul_mulVec, add_comm, ← mulVec_smul]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self (Matrix.toLin' D0) (t • x))
      (LinearMap.mem_range_self (Matrix.toLin' D1) x)
  · have e1 := finrank_ker_add_rank (D1 + t • D0)
    rw [lem_12_1_proved D0 D1 h0 h1 I hI hint hpsd t ht] at e1
    have e2 := finrank_orthSub (LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1))
    rw [lem_12_1_orth_proved D0 D1 h0 h1] at e2
    rw [finrank_range_eq_rank]
    exact Nat.add_left_cancel (e1.trans e2.symm)

/-! ## Lemma 12.4 -/

/-- The change of variables of the hint: `z = (y₀+y₃, y₁+y₄, y₂+y₅, y₂−y₅, −(y₁−y₄), y₀−y₃)`. -/
def Pm : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, -1; 0, -1, 0, 0, 1, 0;
    1, 0, 0, -1, 0, 0]

/-- Its inverse. -/
noncomputable def Pinv : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1/2, 0, 0, 0, 0, 1/2; 0, 1/2, 0, 0, -1/2, 0; 0, 0, 1/2, 1/2, 0, 0; 1/2, 0, 0, 0, 0, -1/2;
    0, 1/2, 0, 0, 1/2, 0; 0, 0, 1/2, -1/2, 0, 0]

lemma Pm_mul_Pinv : Pm * Pinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pm, Pinv, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

lemma isUnit_det_Pm : IsUnit Pm.det := Matrix.isUnit_det_of_right_inverse Pm_mul_Pinv

lemma pf4_skew4_Pm (y : Fin 6 → ℝ) : pf4 (skew4 (Pm *ᵥ y)) = sig33 y := by
  simp [pf4, skew4, sig33, Pm, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

lemma skew_eq_skew4 (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : Aᵀ = -A) :
    A = skew4 ![A 0 1, A 0 2, A 0 3, A 1 2, A 1 3, A 2 3] := by
  have h : ∀ i j, A j i = -A i j := fun i j => by
    have := congrFun (congrFun hA i) j
    simpa [transpose_apply] using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew4] <;>
    linarith [h 0 0, h 1 1, h 2 2, h 3 3, h 0 1, h 0 2, h 0 3, h 1 2, h 1 3, h 2 3]

theorem lem_12_4_signature_proved :
    (∀ A : Matrix (Fin 4) (Fin 4) ℝ, Aᵀ = -A → A = skew4 ![A 0 1, A 0 2, A 0 3, A 1 2, A 1 3, A 2 3]) ∧
      ∃ P : Matrix (Fin 6) (Fin 6) ℝ, IsUnit P.det ∧ ∀ y : Fin 6 → ℝ, pf4 (skew4 (P *ᵥ y)) = sig33 y :=
  ⟨skew_eq_skew4, Pm, isUnit_det_Pm, pf4_skew4_Pm⟩

theorem lem_12_4_hyperbolic_planes_proved (A : Matrix (Fin 4) (Fin 4) ℝ) :
    pf4 A = (((A 0 1 + A 2 3) / 2) ^ 2 - ((A 0 1 - A 2 3) / 2) ^ 2) +
      (((A 0 2 - A 1 3) / 2) ^ 2 - ((A 0 2 + A 1 3) / 2) ^ 2) +
      (((A 0 3 + A 1 2) / 2) ^ 2 - ((A 0 3 - A 1 2) / 2) ^ 2) := by
  unfold pf4
  ring

lemma det_skew4 (y : Fin 6 → ℝ) : (skew4 y).det = pf4 (skew4 y) ^ 2 := by
  simp (config := {decide := true}) [skew4, pf4, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem lem_12_4_det_pf_proved (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : Aᵀ = -A) : A.det = pf4 A ^ 2 := by
  have h := det_skew4 ![A 0 1, A 0 2, A 0 3, A 1 2, A 1 3, A 2 3]
  rwa [← skew_eq_skew4 A hA] at h

theorem lem_12_4_nonvanishing_proved (W : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ)) (hW : ∀ A ∈ W, Aᵀ = -A)
    (h4 : Module.finrank ℝ W = 4) (hinv : ∀ A ∈ W, A ≠ 0 → A.det ≠ 0) : ∀ A ∈ W, A ≠ 0 → pf4 A ≠ 0 := by
  intro A hA hne hpf
  apply hinv A hA hne
  rw [lem_12_4_det_pf_proved A (hW A hA), hpf]
  ring

lemma pf4_add_smul (A B : Matrix (Fin 4) (Fin 4) ℝ) (s : ℝ) :
    pf4 (A + s • B) = pf4 B * (s * s) + (A 0 1 * B 2 3 + B 0 1 * A 2 3 - A 0 2 * B 1 3 - B 0 2 * A 1 3 +
      A 0 3 * B 1 2 + B 0 3 * A 1 2) * s + pf4 A := by
  simp only [pf4, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

lemma pf4_smul (c : ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) : pf4 (c • B) = c ^ 2 * pf4 B := by
  simp only [pf4, Matrix.smul_apply, smul_eq_mul]
  ring

/-- A real quadratic form taking both signs on a space has a nontrivial zero there (here for the Pfaffian). -/
lemma exists_pf4_zero (W : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ)) (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : A ∈ W) (hB : B ∈ W) (hneg : pf4 A < 0) (hpos : 0 < pf4 B) : ∃ C ∈ W, C ≠ 0 ∧ pf4 C = 0 := by
  set β := A 0 1 * B 2 3 + B 0 1 * A 2 3 - A 0 2 * B 1 3 - B 0 2 * A 1 3 + A 0 3 * B 1 2 + B 0 3 * A 1 2
  have hdisc : 0 ≤ discrim (pf4 B) β (pf4 A) := by
    unfold discrim
    nlinarith [sq_nonneg β]
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero hpos.ne'
    ⟨Real.sqrt (discrim (pf4 B) β (pf4 A)), (Real.mul_self_sqrt hdisc).symm⟩
  refine ⟨A + x • B, W.add_mem hA (W.smul_mem x hB), ?_, ?_⟩
  · intro h0
    have hAeq : A = (-x) • B := by
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      exact h0
    rw [hAeq, pf4_smul] at hneg
    nlinarith [sq_nonneg x]
  · rw [pf4_add_smul]
    linarith [hx]

theorem lem_12_4_definite_proved (W : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ)) (hW : ∀ A ∈ W, Aᵀ = -A)
    (h4 : Module.finrank ℝ W = 4) (hnz : ∀ A ∈ W, A ≠ 0 → pf4 A ≠ 0) :
    (∀ A ∈ W, A ≠ 0 → 0 < pf4 A) ∨ ∀ A ∈ W, A ≠ 0 → pf4 A < 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨A, hAW, hA0, hA⟩, ⟨B, hBW, hB0, hB⟩⟩ := hcon
  have hA' : pf4 A < 0 := lt_of_le_of_ne hA (hnz A hAW hA0)
  have hB' : 0 < pf4 B := lt_of_le_of_ne hB (hnz B hBW hB0).symm
  obtain ⟨C, hCW, hC0, hC⟩ := exists_pf4_zero W A B hAW hBW hA' hB'
  exact hnz C hCW hC0 hC

/-- Dimension count: a subspace of dimension `≥ 4` and an injective image of `ℝ³`, both inside a space of dimension
`≤ 6`, meet nontrivially. -/
lemma exists_ne_zero_mem {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (S W : Submodule ℝ V) (hS : Module.finrank ℝ S ≤ 6) (hWS : W ≤ S) (hW : 4 ≤ Module.finrank ℝ W)
    (f : (Fin 3 → ℝ) →ₗ[ℝ] V) (hf : Function.Injective f) (hfS : LinearMap.range f ≤ S) :
    ∃ x, x ≠ 0 ∧ f x ∈ W := by
  have hR : Module.finrank ℝ (LinearMap.range f) = 3 := by
    rw [LinearMap.finrank_range_of_inj hf, Module.finrank_fin_fun]
  have hsup : Module.finrank ℝ ↥(W ⊔ LinearMap.range f) ≤ 6 :=
    (Submodule.finrank_mono (sup_le hWS hfS)).trans hS
  have key := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.range f)
  have hne : W ⊓ LinearMap.range f ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at key
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hzW, x, rfl⟩ := hz
  refine ⟨x, ?_, hzW⟩
  rintro rfl
  exact hz0 (map_zero f)

/-- `x ↦ (x₀, x₁, x₂, 0, 0, 0)`. -/
def EL : Matrix (Fin 6) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, 0, 1; 0, 0, 0; 0, 0, 0; 0, 0, 0]

/-- `x ↦ (0, 0, 0, x₀, x₁, x₂)`. -/
def EH : Matrix (Fin 6) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 0; 0, 0, 0; 1, 0, 0; 0, 1, 0; 0, 0, 1]

lemma EL_inj : Function.Injective EL.mulVec := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [EL, mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
  funext i
  fin_cases i <;> simp [h0, h1, h2]

lemma EH_inj : Function.Injective EH.mulVec := by
  intro x y h
  have h0 := congrFun h 3
  have h1 := congrFun h 4
  have h2 := congrFun h 5
  simp [EH, mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
  funext i
  fin_cases i <;> simp [h0, h1, h2]

lemma sig33_EL (x : Fin 3 → ℝ) : sig33 (EL *ᵥ x) = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  simp [sig33, EL, mulVec, dotProduct, Fin.sum_univ_succ]

lemma sig33_EH (x : Fin 3 → ℝ) : sig33 (EH *ᵥ x) = -(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  simp [sig33, EH, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

lemma sum_sq_pos (x : Fin 3 → ℝ) (hx : x ≠ 0) : 0 < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  by_contra h
  apply hx
  have e0 : x 0 ^ 2 = 0 := by linarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have e1 : x 1 ^ 2 = 0 := by linarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have e2 : x 2 ^ 2 = 0 := by linarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  rw [pow_eq_zero_iff two_ne_zero] at e0 e1 e2
  funext i
  fin_cases i <;> simp [e0, e1, e2]

lemma toLin'_comp_inj {k : ℕ} (P : Matrix (Fin 6) (Fin 6) ℝ) (hP : IsUnit P.det) (E : Matrix (Fin 6) (Fin k) ℝ)
    (hE : Function.Injective E.mulVec) : Function.Injective (Matrix.toLin' (P * E)) := by
  have hPinj : Function.Injective P.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det P).mpr hP)
  intro x y h
  simp only [Matrix.toLin'_apply, ← mulVec_mulVec] at h
  exact hE (hPinj h)

theorem lem_12_4_sylvester_proved (Q : (Fin 6 → ℝ) → ℝ)
    (hQ : ∃ P : Matrix (Fin 6) (Fin 6) ℝ, IsUnit P.det ∧ ∀ y : Fin 6 → ℝ, Q (P *ᵥ y) = sig33 y) :
    ¬ ∃ W : Submodule ℝ (Fin 6 → ℝ), Module.finrank ℝ W = 4 ∧
      ((∀ y ∈ W, y ≠ 0 → 0 < Q y) ∨ ∀ y ∈ W, y ≠ 0 → Q y < 0) := by
  rintro ⟨W, hW4, hdef⟩
  obtain ⟨P, hP, hQP⟩ := hQ
  have htop : Module.finrank ℝ (⊤ : Submodule ℝ (Fin 6 → ℝ)) ≤ 6 := by
    rw [finrank_top, Module.finrank_fin_fun]
  rcases hdef with hpos | hneg
  · obtain ⟨x, hx0, hxW⟩ := exists_ne_zero_mem ⊤ W htop le_top hW4.ge (Matrix.toLin' (P * EH))
      (toLin'_comp_inj P hP EH EH_inj) le_top
    have hne : Matrix.toLin' (P * EH) x ≠ 0 := by
      intro h
      apply hx0
      apply toLin'_comp_inj P hP EH EH_inj
      rw [h, map_zero]
    have h1 := hpos _ hxW hne
    rw [Matrix.toLin'_apply, ← mulVec_mulVec, hQP, sig33_EH] at h1
    linarith [sum_sq_pos x hx0]
  · obtain ⟨x, hx0, hxW⟩ := exists_ne_zero_mem ⊤ W htop le_top hW4.ge (Matrix.toLin' (P * EL))
      (toLin'_comp_inj P hP EL EL_inj) le_top
    have hne : Matrix.toLin' (P * EL) x ≠ 0 := by
      intro h
      apply hx0
      apply toLin'_comp_inj P hP EL EL_inj
      rw [h, map_zero]
    have h1 := hneg _ hxW hne
    rw [Matrix.toLin'_apply, ← mulVec_mulVec, hQP, sig33_EL] at h1
    linarith [sum_sq_pos x hx0]

/-- `skew4` as a linear map. -/
def skew4L : (Fin 6 → ℝ) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ where
  toFun := skew4
  map_add' y z := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skew4] <;> ring
  map_smul' c y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skew4]

lemma skew4_inj : Function.Injective skew4 := by
  intro y z h
  have e0 := congrFun (congrFun h 0) 1
  have e1 := congrFun (congrFun h 0) 2
  have e2 := congrFun (congrFun h 0) 3
  have e3 := congrFun (congrFun h 1) 2
  have e4 := congrFun (congrFun h 1) 3
  have e5 := congrFun (congrFun h 2) 3
  simp [skew4] at e0 e1 e2 e3 e4 e5
  funext i
  fin_cases i <;> simp [e0, e1, e2, e3, e4, e5]

/-- In the space of skew matrices, a subspace of dimension `≥ 4` contains `skew4 (Pm (E x))` for some `x ≠ 0`. -/
lemma exists_skew_mem (W : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ)) (hW : ∀ A ∈ W, Aᵀ = -A)
    (h4 : 4 ≤ Module.finrank ℝ W) (E : Matrix (Fin 6) (Fin 3) ℝ) (hE : Function.Injective E.mulVec) :
    ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ skew4 (Pm *ᵥ (E *ᵥ x)) ∈ W := by
  have hS : Module.finrank ℝ (LinearMap.range skew4L) ≤ 6 := by
    have := LinearMap.finrank_range_le skew4L
    rwa [Module.finrank_fin_fun] at this
  have hWS : W ≤ LinearMap.range skew4L := by
    intro A hA
    exact ⟨_, (skew_eq_skew4 A (hW A hA)).symm⟩
  have hinj : Function.Injective (skew4L ∘ₗ Matrix.toLin' (Pm * E)) := by
    intro x y h
    exact toLin'_comp_inj Pm isUnit_det_Pm E hE (skew4_inj h)
  obtain ⟨x, hx0, hxW⟩ := exists_ne_zero_mem (LinearMap.range skew4L) W hS hWS h4
    (skew4L ∘ₗ Matrix.toLin' (Pm * E)) hinj (LinearMap.range_comp_le_range _ _)
  refine ⟨x, hx0, ?_⟩
  simpa [skew4L, Matrix.toLin'_apply, mulVec_mulVec] using hxW

theorem lem_12_4_proved (W : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ)) (hW : ∀ A ∈ W, Aᵀ = -A)
    (h4 : 4 ≤ Module.finrank ℝ W) : ∃ A ∈ W, A ≠ 0 ∧ A.det = 0 := by
  obtain ⟨x, hx0, hxW⟩ := exists_skew_mem W hW h4 EH EH_inj
  obtain ⟨y, hy0, hyW⟩ := exists_skew_mem W hW h4 EL EL_inj
  have hneg : pf4 (skew4 (Pm *ᵥ (EH *ᵥ x))) < 0 := by
    rw [pf4_skew4_Pm, sig33_EH]
    linarith [sum_sq_pos x hx0]
  have hpos : 0 < pf4 (skew4 (Pm *ᵥ (EL *ᵥ y))) := by
    rw [pf4_skew4_Pm, sig33_EL]
    exact sum_sq_pos y hy0
  obtain ⟨C, hCW, hC0, hC⟩ := exists_pf4_zero W _ _ hxW hyW hneg hpos
  refine ⟨C, hCW, hC0, ?_⟩
  rw [lem_12_4_det_pf_proved C (hW C hCW), hC]
  ring

/-! ## Lemma 12.6 -/

theorem lem_12_6_rank_one_proved {𝕜 : Type*} [Field 𝕜] {m n : ℕ} (M : Matrix (Fin m) (Fin n) 𝕜)
    (hM : M.rank ≤ 1) : ∃ (w : Fin m → 𝕜) (e : Fin n → 𝕜), M = vecMulVec w e := by
  rw [Matrix.rank] at hM
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hM
  choose c hc using fun j : Fin n => hv ⟨M.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
  refine ⟨(v : Fin m → 𝕜), c, ?_⟩
  ext i j
  have h := congrArg (fun z : LinearMap.range M.mulVecLin => (z : Fin m → 𝕜) i) (hc j)
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVecLin_apply, mulVec_single_one,
    Matrix.col_apply] at h
  rw [vecMulVec_apply, ← h, mul_comm]

lemma minor_of_rank_le_one {𝕜 : Type*} [Field 𝕜] {m n : ℕ} (M : Matrix (Fin m) (Fin n) 𝕜) (hM : M.rank ≤ 1)
    (i j : Fin m) (k l : Fin n) : M i k * M j l = M i l * M j k := by
  obtain ⟨w, e, rfl⟩ := lem_12_6_rank_one_proved M hM
  simp only [vecMulVec_apply]
  ring

/-- Rank at most one of `abᵀ + cdᵀ` forces `a ∥ c` or `b ∥ d` (all 2 × 2 minors). -/
lemma minor_sum {𝕜 : Type*} [Field 𝕜] {m n : ℕ} (a c : Fin m → 𝕜) (b d : Fin n → 𝕜)
    (h : (vecMulVec a b + vecMulVec c d).rank ≤ 1) :
    (∀ i j, a i * c j = c i * a j) ∨ (∀ k l, b k * d l = d k * b l) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨i, j, hij⟩, ⟨k, l, hkl⟩⟩ := hcon
  have hm := minor_of_rank_le_one _ h i j k l
  simp only [Matrix.add_apply, vecMulVec_apply] at hm
  apply mul_ne_zero (sub_ne_zero.mpr hij) (sub_ne_zero.mpr hkl)
  linear_combination hm

lemma prop_of_minors {𝕜 : Type*} [Field 𝕜] {m : ℕ} (a c : Fin m → 𝕜) (ha : a ≠ 0)
    (h : ∀ i j, a i * c j = c i * a j) : ∃ t : 𝕜, c = t • a := by
  obtain ⟨i0, hi0⟩ : ∃ i, a i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact ha (funext hh)
  refine ⟨c i0 / a i0, funext fun j => ?_⟩
  have hj := h i0 j
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination hj

lemma row_vecMulVec {𝕜 : Type*} [Field 𝕜] {m n : ℕ} (w : Fin m → 𝕜) (e : Fin n → 𝕜) (i : Fin m) :
    (vecMulVec w e) i = w i • e := by
  ext k
  simp [vecMulVec_apply]

theorem lem_12_6_pair_proved {𝕜 : Type*} [Field 𝕜] {m n : ℕ} (S : Submodule 𝕜 (Matrix (Fin m) (Fin n) 𝕜))
    (hS : ∀ M ∈ S, M.rank ≤ 1) :
    ∀ (w1 w2 : Fin m → 𝕜) (e1 e2 : Fin n → 𝕜), vecMulVec w1 e1 ∈ S → vecMulVec w2 e2 ∈ S →
      LinearIndependent 𝕜 ![w1, w2] → e1 ≠ 0 → e2 ≠ 0 →
      e2 ∈ Submodule.span 𝕜 {e1} ∧ ∀ M ∈ S, ∀ i, M i ∈ Submodule.span 𝕜 {e1} := by
  intro w1 w2 e1 e2 h1 h2 hli he1 he2
  have hli' := LinearIndependent.pair_iff.mp hli
  have hw1 : w1 ≠ 0 := by
    intro h
    have := hli' 1 0 (by simp [h])
    simp at this
  have hnot : ¬ ∀ i j, w1 i * w2 j = w2 i * w1 j := by
    intro h
    obtain ⟨t, ht⟩ := prop_of_minors w1 w2 hw1 h
    have := hli' t (-1) (by rw [ht]; simp)
    simp at this
  have he12 : ∀ k l, e1 k * e2 l = e2 k * e1 l :=
    (minor_sum w1 w2 e1 e2 (hS _ (S.add_mem h1 h2))).resolve_left hnot
  obtain ⟨t2, ht2⟩ := prop_of_minors e1 e2 he1 he12
  have ht2ne : t2 ≠ 0 := by
    rintro rfl
    apply he2
    rw [ht2, zero_smul]
  refine ⟨Submodule.mem_span_singleton.mpr ⟨t2, ht2.symm⟩, ?_⟩
  intro M hM i
  obtain ⟨w, e, rfl⟩ := lem_12_6_rank_one_proved M (hS M hM)
  rw [row_vecMulVec]
  by_cases hee : ∀ k l, e1 k * e l = e k * e1 l
  · obtain ⟨t, ht⟩ := prop_of_minors e1 e he1 hee
    rw [ht, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e1)
  · have hww1 : ∀ i j, w i * w1 j = w1 i * w j := by
      rcases minor_sum w w1 e e1 (hS _ (S.add_mem hM h1)) with h | h
      · exact h
      · exact absurd (fun k l => (h k l).symm) hee
    have hww2 : ∀ i j, w i * w2 j = w2 i * w j := by
      rcases minor_sum w w2 e e2 (hS _ (S.add_mem hM h2)) with h | h
      · exact h
      · refine absurd (fun k l => ?_) hee
        have hkl := h k l
        rw [ht2] at hkl
        simp only [Pi.smul_apply, smul_eq_mul] at hkl
        have : t2 * (e k * e1 l - e1 k * e l) = 0 := by linear_combination hkl
        have := (mul_eq_zero.mp this).resolve_left ht2ne
        linear_combination -this
    by_cases hw : w = 0
    · rw [hw]
      simp
    · exfalso
      obtain ⟨s1, hs1⟩ := prop_of_minors w w1 hw hww1
      obtain ⟨s2, hs2⟩ := prop_of_minors w w2 hw hww2
      have := hli' s2 (-s1) (by rw [hs1, hs2, smul_smul, smul_smul, neg_mul, neg_smul, mul_comm]; simp)
      apply hw1
      rw [hs1, neg_eq_zero.mp this.2, zero_smul]

lemma range_le_span_of_finrank_le_one {𝕜 : Type*} [Field 𝕜] {m : ℕ} (N : Submodule 𝕜 (Fin m → 𝕜))
    (hN : Module.finrank 𝕜 N ≤ 1) : ∃ w : Fin m → 𝕜, N ≤ Submodule.span 𝕜 {w} := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hN
  refine ⟨(v : Fin m → 𝕜), fun y hy => ?_⟩
  obtain ⟨c, hc⟩ := hv ⟨y, hy⟩
  rw [Submodule.mem_span_singleton]
  exact ⟨c, by simpa using congrArg Subtype.val hc⟩

theorem lem_12_6_common_image_proved {𝕜 : Type*} [Field 𝕜] {m n : ℕ}
    (S : Submodule 𝕜 (Matrix (Fin m) (Fin n) 𝕜))
    (hS : ∀ M ∈ S, M.rank ≤ 1)
    (hno : ∀ M1 ∈ S, ∀ M2 ∈ S,
      Module.finrank 𝕜 ↥(LinearMap.range (Matrix.toLin' M1) ⊔ LinearMap.range (Matrix.toLin' M2)) ≤ 1) :
    ∃ w : Fin m → 𝕜, ∀ M ∈ S, LinearMap.range (Matrix.toLin' M) ≤ Submodule.span 𝕜 {w} := by
  by_cases hall : ∀ M ∈ S, M = 0
  · refine ⟨0, fun M hM => ?_⟩
    rw [hall M hM, map_zero, LinearMap.range_zero]
    exact bot_le
  push Not at hall
  obtain ⟨M0, hM0, hM0ne⟩ := hall
  have hle1 : Module.finrank 𝕜 (LinearMap.range (Matrix.toLin' M0)) ≤ 1 := by
    have := hno M0 hM0 M0 hM0
    rwa [sup_idem] at this
  have hpos : 1 ≤ Module.finrank 𝕜 (LinearMap.range (Matrix.toLin' M0)) := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
    exact hM0ne (by simpa using h0)
  obtain ⟨w, hw⟩ := range_le_span_of_finrank_le_one _ hle1
  refine ⟨w, fun M hM => ?_⟩
  have heq : LinearMap.range (Matrix.toLin' M0) =
      LinearMap.range (Matrix.toLin' M0) ⊔ LinearMap.range (Matrix.toLin' M) :=
    Submodule.eq_of_le_of_finrank_le le_sup_left (by have := hno M0 hM0 M hM; omega)
  calc LinearMap.range (Matrix.toLin' M) ≤ LinearMap.range (Matrix.toLin' M0) := by
        rw [heq]; exact le_sup_right
    _ ≤ Submodule.span 𝕜 {w} := hw

theorem lem_12_6_proved {𝕜 : Type*} [Field 𝕜] {m n : ℕ} (S : Submodule 𝕜 (Matrix (Fin m) (Fin n) 𝕜))
    (hS : ∀ M ∈ S, M.rank ≤ 1) :
    (∃ w : Fin m → 𝕜, ∀ M ∈ S, LinearMap.range (Matrix.toLin' M) ≤ Submodule.span 𝕜 {w}) ∨
      ∃ e : Fin n → 𝕜, ∀ M ∈ S, ∀ i, M i ∈ Submodule.span 𝕜 {e} := by
  by_cases hpair : ∃ (w1 w2 : Fin m → 𝕜) (e1 e2 : Fin n → 𝕜), vecMulVec w1 e1 ∈ S ∧ vecMulVec w2 e2 ∈ S ∧
      LinearIndependent 𝕜 ![w1, w2] ∧ e1 ≠ 0 ∧ e2 ≠ 0
  · obtain ⟨w1, w2, e1, e2, h1, h2, hli, he1, he2⟩ := hpair
    exact Or.inr ⟨e1, (lem_12_6_pair_proved S hS w1 w2 e1 e2 h1 h2 hli he1 he2).2⟩
  left
  by_cases hall : ∀ M ∈ S, M = 0
  · refine ⟨0, fun M hM => ?_⟩
    rw [hall M hM, map_zero, LinearMap.range_zero]
    exact bot_le
  push Not at hall
  obtain ⟨M0, hM0, hne⟩ := hall
  obtain ⟨w0, e0, rfl⟩ := lem_12_6_rank_one_proved M0 (hS _ hM0)
  have hw0 : w0 ≠ 0 := by
    rintro rfl
    apply hne
    ext i j
    simp [vecMulVec_apply]
  have he0 : e0 ≠ 0 := by
    rintro rfl
    apply hne
    ext i j
    simp [vecMulVec_apply]
  refine ⟨w0, fun M hM => ?_⟩
  obtain ⟨w, e, rfl⟩ := lem_12_6_rank_one_proved M (hS _ hM)
  rintro _ ⟨x, rfl⟩
  rw [Matrix.toLin'_apply, Submodule.mem_span_singleton]
  by_cases he : e = 0
  · refine ⟨0, ?_⟩
    rw [he, zero_smul]
    ext i
    simp [mulVec, dotProduct, vecMulVec_apply]
  have hdep : ¬ LinearIndependent 𝕜 ![w0, w] := fun hli => hpair ⟨w0, w, e0, e, hM0, hM, hli, he0, he⟩
  rw [LinearIndependent.pair_iff] at hdep
  push Not at hdep
  obtain ⟨s, t, hst, hne'⟩ := hdep
  have ht : t ≠ 0 := by
    rintro rfl
    have hs : s ≠ 0 := fun h => hne' h rfl
    rw [zero_smul, add_zero] at hst
    exact hw0 ((smul_eq_zero.mp hst).resolve_left hs)
  have hw : w = (-s / t) • w0 := by
    funext i
    have hi := congrFun hst i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination hi
  refine ⟨(e ⬝ᵥ x) * (-s / t), ?_⟩
  rw [hw]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, vecMulVec_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Osserman.Proofs.Six1
