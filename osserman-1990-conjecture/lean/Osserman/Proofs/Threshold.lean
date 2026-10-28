/-
Osserman/Proofs/Threshold.lean — Lemma 4.1 (lem:threshold, paper 013 l. 491-533) and its named proof steps, by an
algebraic route (AUDIT.md, "route differences": the image of `h` is shown onto by eigenvectors of `H(a)`, not by the
paper's open-and-compact image argument).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.Threshold

namespace Osserman.Proofs.Threshold

open Osserman Matrix

lemma quadratic_combination {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (a : Fin (m + 1) → ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (Hcomb H a *ᵥ x) = a ⬝ᵥ hvec H x := by
  rw [Hcomb, Matrix.sum_mulVec, dotProduct_sum]
  change (∑ i, x ⬝ᵥ ((a i • H i) *ᵥ x)) = ∑ i, a i * hvec H x i
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.smul_mulVec, dotProduct_smul]
  rfl

lemma unit_dot_bound_eq {k : ℕ} (a b : Fin k → ℝ) (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) :
    a ⬝ᵥ b ≤ 1 ∧ (a ⬝ᵥ b = 1 ↔ b = a) := by
  have ha' : ∑ i, a i ^ 2 = 1 := by simpa only [dotProduct, pow_two] using ha
  have hb' : ∑ i, b i ^ 2 = 1 := by simpa only [dotProduct, pow_two] using hb
  have expansion : ∑ i, (a i - b i) ^ 2 =
      (∑ i, a i ^ 2) + (∑ i, b i ^ 2) - 2 * ∑ i, a i * b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [ha', hb'] at expansion
  have nonnegative : 0 ≤ ∑ i, (a i - b i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have bound : a ⬝ᵥ b ≤ 1 := by
    change (∑ i, a i * b i) ≤ 1
    linarith
  refine ⟨bound, ?_⟩
  constructor
  · intro equal
    have zero : ∑ i, (a i - b i) ^ 2 = 0 := by
      change (∑ i, a i * b i) = 1 at equal
      linarith
    have each := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
      sq_nonneg (a i - b i))).mp zero
    funext i
    exact (sub_eq_zero.mp (sq_eq_zero_iff.mp (each i (Finset.mem_univ i)))).symm
  · rintro rfl
    exact ha

theorem threshold_le_one {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (_hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (a : Fin (m + 1) → ℝ) (x : Fin n → ℝ) (ha : a ⬝ᵥ a = 1) (hx : x ⬝ᵥ x = 1) :
    x ⬝ᵥ (Hcomb H a *ᵥ x) ≤ 1 ∧ (x ⬝ᵥ (Hcomb H a *ᵥ x) = 1 ↔ hvec H x = a) := by
  rw [quadratic_combination]
  apply unit_dot_bound_eq a (hvec H x) ha
  have h := hnorm x
  rw [hx, one_pow] at h
  simpa only [dotProduct, pow_two] using h

lemma quadratic_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hsym : A.IsSymm)
    (x y : Fin n → ℝ) :
    (x + y) ⬝ᵥ (A *ᵥ (x + y)) =
      x ⬝ᵥ (A *ᵥ x) + 2 * (x ⬝ᵥ (A *ᵥ y)) + y ⬝ᵥ (A *ᵥ y) := by
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  have cross := hsym.dotProduct_mulVec_comm (x := y) (y := x)
  linarith

lemma quadratic_sub {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hsym : A.IsSymm)
    (x y : Fin n → ℝ) :
    (x - y) ⬝ᵥ (A *ᵥ (x - y)) =
      x ⬝ᵥ (A *ᵥ x) - 2 * (x ⬝ᵥ (A *ᵥ y)) + y ⬝ᵥ (A *ᵥ y) := by
  simpa only [sub_eq_add_neg, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct,
    neg_neg, mul_neg] using quadratic_add A hsym x (-y)

lemma normsq_add {n : ℕ} (x y : Fin n → ℝ) :
    (x + y) ⬝ᵥ (x + y) = x ⬝ᵥ x + 2 * (x ⬝ᵥ y) + y ⬝ᵥ y := by
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_comm y x]
  ring

lemma normsq_sub {n : ℕ} (x y : Fin n → ℝ) :
    (x - y) ⬝ᵥ (x - y) = x ⬝ᵥ x - 2 * (x ⬝ᵥ y) + y ⬝ᵥ y := by
  simpa only [sub_eq_add_neg, dotProduct_neg, neg_dotProduct, neg_neg, mul_neg] using normsq_add x (-y)

lemma mixed_coefficient_identity {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (x y : Fin n → ℝ) :
    (x ⬝ᵥ x) * (y ⬝ᵥ y) - ∑ i, hvec H x i * hvec H y i =
      2 * ∑ i, (x ⬝ᵥ (H i *ᵥ y)) ^ 2 - 2 * (x ⬝ᵥ y) ^ 2 := by
  have even : (∑ i, hvec H (x + y) i ^ 2) + (∑ i, hvec H (x - y) i ^ 2) =
      2 * (∑ i, hvec H x i ^ 2) + 8 * (∑ i, (x ⬝ᵥ (H i *ᵥ y)) ^ 2) +
        2 * (∑ i, hvec H y i ^ 2) + 4 * ∑ i, hvec H x i * hvec H y i := by
    calc
      _ = ∑ i, (hvec H (x + y) i ^ 2 + hvec H (x - y) i ^ 2) :=
        (Finset.sum_add_distrib).symm
      _ = ∑ i, (2 * hvec H x i ^ 2 + 8 * (x ⬝ᵥ (H i *ᵥ y)) ^ 2 +
          2 * hvec H y i ^ 2 + 4 * (hvec H x i * hvec H y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        change ((x + y) ⬝ᵥ (H i *ᵥ (x + y))) ^ 2 +
          ((x - y) ⬝ᵥ (H i *ᵥ (x - y))) ^ 2 = _
        rw [quadratic_add _ (hsym i), quadratic_sub _ (hsym i)]
        dsimp only [hvec]
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hnorm (x + y), hnorm (x - y), hnorm x, hnorm y, normsq_add, normsq_sub] at even
  nlinarith only [even]

@[simp] lemma hvec_zero {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) :
    hvec H 0 = 0 := by ext i; simp [hvec]

lemma hvec_smul {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ) (x : Fin n → ℝ) : hvec H (c • x) = c ^ 2 • hvec H x := by
  ext i
  simp only [hvec, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma Hcomb_symm {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i, (H i).IsSymm) (a : Fin (m + 1) → ℝ) : (Hcomb H a).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [Hcomb, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [(hsym k).apply i j]

lemma quadratic_bound {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (a : Fin (m + 1) → ℝ) (ha : a ⬝ᵥ a = 1) (x : Fin n → ℝ) :
    x ⬝ᵥ (Hcomb H a *ᵥ x) ≤ x ⬝ᵥ x := by
  rw [quadratic_combination]
  have ha' : ∑ i, a i ^ 2 = 1 := by simpa only [dotProduct, pow_two] using ha
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (hvec H x)
  rw [ha', hnorm x, one_mul] at cs
  have cs' : (a ⬝ᵥ hvec H x) ^ 2 ≤ (x ⬝ᵥ x) ^ 2 := cs
  have nonnegative : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  by_cases positive : 0 ≤ a ⬝ᵥ hvec H x
  · exact (sq_le_sq₀ positive nonnegative).mp cs'
  · exact (le_of_not_ge positive).trans nonnegative

lemma comb_posSemidef {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (a : Fin (m + 1) → ℝ) (ha : a ⬝ᵥ a = 1) : (1 - Hcomb H a).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (Matrix.isSymm_one.sub (Hcomb_symm H hsym a)))
  intro x
  simpa only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] using
    sub_nonneg.mpr (quadratic_bound H hnorm a ha x)

theorem threshold_fibre {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (a : Fin (m + 1) → ℝ) (ha : a ⬝ᵥ a = 1) (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1) :
    hvec H x = a ↔ (1 - Hcomb H a) *ᵥ x = 0 := by
  have bound := threshold_le_one H hsym hnorm a x ha hx
  have zero := (comb_posSemidef H hsym hnorm a ha).dotProduct_mulVec_zero_iff (x := x)
  calc
    hvec H x = a ↔ x ⬝ᵥ (Hcomb H a *ᵥ x) = 1 := bound.2.symm
    _ ↔ 1 - x ⬝ᵥ (Hcomb H a *ᵥ x) = 0 := by constructor <;> intro h <;> linarith
    _ ↔ (1 - Hcomb H a) *ᵥ x = 0 := by
      simpa only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hx] using zero

lemma Hcomb_hvec_mulVec {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1) : Hcomb H (hvec H x) *ᵥ x = x := by
  have ha : hvec H x ⬝ᵥ hvec H x = 1 := by
    have h := hnorm x
    rw [hx, one_pow] at h
    simpa only [dotProduct, pow_two] using h
  have kernel := (threshold_fibre H hsym hnorm (hvec H x) ha x hx).mp rfl
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at kernel
  exact (sub_eq_zero.mp kernel).symm

lemma symm_eq_of_quadratic {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hsA : A.IsSymm) (hsB : B.IsSymm)
    (equal : ∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (B *ᵥ x)) : A = B := by
  have bilinear (x y : Fin n → ℝ) : x ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ (B *ᵥ y) := by
    have h := equal (x + y)
    rw [quadratic_add A hsA, quadratic_add B hsB, equal x, equal y] at h
    linarith
  ext i j
  have h := bilinear (Pi.single i 1) (Pi.single j 1)
  simpa only [Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col_apply] using h

lemma outer_symm {n : ℕ} (v : Fin n → ℝ) : (vecMulVec v v).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [Matrix.vecMulVec_apply]
  ring

lemma quadratic_outer {n : ℕ} (v y : Fin n → ℝ) :
    y ⬝ᵥ (vecMulVec v v *ᵥ y) = (v ⬝ᵥ y) ^ 2 := by
  rw [dotProduct_mulVec, vecMul_vecMulVec, smul_dotProduct]
  change (y ⬝ᵥ v) * (v ⬝ᵥ y) = (v ⬝ᵥ y) ^ 2
  rw [dotProduct_comm y v, pow_two]

theorem rank_identity {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1) :
    1 - Hcomb H (hvec H x) =
      (2 : ℝ) • (∑ i, vecMulVec (H i *ᵥ x) (H i *ᵥ x)) - (2 : ℝ) • vecMulVec x x := by
  have sumSymm : (∑ i, vecMulVec (H i *ᵥ x) (H i *ᵥ x)).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
    apply Finset.sum_congr rfl
    intro k _
    ring
  apply symm_eq_of_quadratic _ _ (Matrix.isSymm_one.sub (Hcomb_symm H hsym _))
    ((sumSymm.smul (2 : ℝ)).sub ((outer_symm x).smul (2 : ℝ)))
  intro y
  have cross (i : Fin (m + 1)) : (H i *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (H i *ᵥ y) :=
    (dotProduct_comm _ _).trans ((hsym i).dotProduct_mulVec_comm (x := y) (y := x))
  have left : y ⬝ᵥ ((1 - Hcomb H (hvec H x)) *ᵥ y) =
      y ⬝ᵥ y - ∑ i, hvec H x i * hvec H y i := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, quadratic_combination]
    rfl
  have right : y ⬝ᵥ (((2 : ℝ) • (∑ i, vecMulVec (H i *ᵥ x) (H i *ᵥ x)) -
      (2 : ℝ) • vecMulVec x x) *ᵥ y) =
      2 * ∑ i, (x ⬝ᵥ (H i *ᵥ y)) ^ 2 - 2 * (x ⬝ᵥ y) ^ 2 := by
    simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      Matrix.sum_mulVec, dotProduct_sum, smul_eq_mul]
    simp_rw [quadratic_outer, cross]
  have coefficient := mixed_coefficient_identity H hsym hnorm x y
  rw [hx, one_mul] at coefficient
  exact left.trans (coefficient.trans right.symm)

lemma unit_rescale {n : ℕ} (z : Fin n → ℝ) (nonzero : z ≠ 0) :
    ∃ c : ℝ, (c • z) ⬝ᵥ (c • z) = 1 := by
  have nonnegative : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg fun i _ => mul_self_nonneg (z i)
  have positive : 0 < z ⬝ᵥ z := lt_of_le_of_ne nonnegative
    (fun equal => nonzero (dotProduct_self_eq_zero.mp equal.symm))
  have sqrtPositive := Real.sqrt_pos.mpr positive
  have sqrtNonzero := ne_of_gt sqrtPositive
  have sqrtSquare := Real.sq_sqrt nonnegative
  refine ⟨(Real.sqrt (z ⬝ᵥ z))⁻¹, ?_⟩
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  nlinarith only [sqrtSquare]

theorem fibres_meet_only_zero {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (a b : Fin (m + 1) → ℝ) (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) (distinct : a ≠ b)
    (z : Fin n → ℝ) (left : (1 - Hcomb H a) *ᵥ z = 0)
    (right : (1 - Hcomb H b) *ᵥ z = 0) : z = 0 := by
  by_contra nonzero
  obtain ⟨c, unit⟩ := unit_rescale z nonzero
  have leftScaled : (1 - Hcomb H a) *ᵥ (c • z) = 0 := by
    rw [Matrix.mulVec_smul, left, smul_zero]
  have rightScaled : (1 - Hcomb H b) *ᵥ (c • z) = 0 := by
    rw [Matrix.mulVec_smul, right, smul_zero]
  have imageLeft := (threshold_fibre H hsym hnorm a ha (c • z) unit).mpr leftScaled
  have imageRight := (threshold_fibre H hsym hnorm b hb (c • z) unit).mpr rightScaled
  exact distinct (imageLeft.symm.trans imageRight)

def columnMap {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin (m + 1)) ℝ := fun j i => (H i *ᵥ x) j

lemma columnMap_mulVec {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (a : Fin (m + 1) → ℝ) :
    columnMap H x *ᵥ a = Hcomb H a *ᵥ x := by
  rw [Hcomb, Matrix.sum_mulVec]
  ext j
  simp only [Matrix.smul_mulVec, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, columnMap]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem threshold_rank_bound {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1) :
    (1 - Hcomb H (hvec H x)).rank ≤ m := by
  let a := hvec H x
  let V := columnMap H x
  let W : Matrix (Fin n) (Fin (m + 1)) ℝ := V - vecMulVec x a
  have ha : a ⬝ᵥ a = 1 := by
    have h := hnorm x
    rw [hx, one_pow] at h
    simpa only [dotProduct, pow_two] using h
  have va : V *ᵥ a = x := (columnMap_mulVec H x a).trans
    (Hcomb_hvec_mulVec H hsym hnorm x hx)
  have wa : W *ᵥ a = 0 := by
    change (V - vecMulVec x a) *ᵥ a = 0
    rw [Matrix.sub_mulVec, va]
    ext j
    simp only [Pi.sub_apply, Pi.zero_apply, Matrix.mulVec, dotProduct,
      Matrix.vecMulVec_apply]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    change x j - x j * (a ⬝ᵥ a) = 0
    rw [ha, mul_one, sub_self]
  have an : a ≠ 0 := by intro h; simp [h] at ha
  have kn : LinearMap.ker W.mulVecLin ≠ ⊥ := by
    intro equal
    have member : a ∈ LinearMap.ker W.mulVecLin := wa
    rw [equal, Submodule.mem_bot] at member
    exact an member
  have kp : 0 < Module.finrank ℝ (LinearMap.ker W.mulVecLin) := by
    exact Nat.pos_of_ne_zero (fun h => kn (Submodule.finrank_eq_zero.mp h))
  have wn := W.mulVecLin.finrank_range_add_finrank_ker
  have wr : W.rank ≤ m := by
    rw [Module.finrank_pi, Fintype.card_fin] at wn
    change W.rank + _ = m + 1 at wn
    omega
  have factor : 1 - Hcomb H a = W * ((2 : ℝ) • Vᵀ) := by
    rw [rank_identity H hsym hnorm x hx]
    ext j k
    have vk := congrFun va k
    change (∑ i, V k i * a i) = x k at vk
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply]
    change 2 * (∑ i, V j i * V k i) - 2 * (x j * x k) =
      ∑ i, (V j i - x j * a i) * (2 * V k i)
    calc
      _ = ∑ i, (2 * (V j i * V k i) - 2 * x j * (V k i * a i)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, vk]
        ring
      _ = _ := by apply Finset.sum_congr rfl; intro i _; ring
  rw [factor]
  exact (Matrix.rank_mul_le_left _ _).trans wr

theorem threshold_dimension {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1) :
    n - m ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (1 - Hcomb H (hvec H x)))) := by
  have bound := threshold_rank_bound H hsym hnorm x hx
  have rn := (1 - Hcomb H (hvec H x)).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin] at rn
  rw [Matrix.toLin'_apply']
  change (1 - Hcomb H (hvec H x)).rank + _ = n at rn
  omega

theorem threshold_a {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (a : Fin (m + 1) → ℝ)
    (attained : ∃ x : Fin n → ℝ, x ⬝ᵥ x = 1 ∧ hvec H x = a) :
    (1 - Hcomb H a).PosSemidef ∧
    (∀ x : Fin n → ℝ, x ⬝ᵥ x = 1 → (hvec H x = a ↔ (1 - Hcomb H a) *ᵥ x = 0)) ∧
    n - m ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (1 - Hcomb H a))) := by
  obtain ⟨x, hx, rfl⟩ := attained
  have ha : hvec H x ⬝ᵥ hvec H x = 1 := by
    have h := hnorm x
    rw [hx, one_pow] at h
    simpa only [dotProduct, pow_two] using h
  exact ⟨comb_posSemidef H hsym hnorm (hvec H x) ha,
    fun y hy => threshold_fibre H hsym hnorm (hvec H x) ha y hy,
    threshold_dimension H hsym hnorm x hx⟩

lemma fibre_kernels_disjoint {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (a b : Fin (m + 1) → ℝ) (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) (distinct : a ≠ b) :
    Disjoint (LinearMap.ker (Matrix.toLin' (1 - Hcomb H a)))
      (LinearMap.ker (Matrix.toLin' (1 - Hcomb H b))) := by
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  intro z hz
  change z = 0
  exact fibres_meet_only_zero H hsym hnorm a b ha hb distinct z hz.1 hz.2

lemma hvec_unit {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1) : hvec H x ⬝ᵥ hvec H x = 1 := by
  have h := hnorm x
  rw [hx, one_pow] at h
  simpa only [dotProduct, pow_two] using h

theorem threshold_b {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (dimension : 2 * m < n) (x y : Fin n → ℝ)
    (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1) : hvec H x = hvec H y := by
  by_contra distinct
  have dx := threshold_dimension H hsym hnorm x hx
  have dy := threshold_dimension H hsym hnorm y hy
  have disj := fibre_kernels_disjoint H hsym hnorm (hvec H x) (hvec H y)
    (hvec_unit H hnorm x hx) (hvec_unit H hnorm y hy) distinct
  have sum := Submodule.finrank_add_finrank_le_of_disjoint disj
  rw [Module.finrank_pi, Fintype.card_fin] at sum
  omega

def NonconstantOnUnit {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ u v : Fin n → ℝ, u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ hvec H u ≠ hvec H v

lemma exists_other_image {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (nonconstant : NonconstantOnUnit H) (a : Fin (m + 1) → ℝ) :
    ∃ y : Fin n → ℝ, y ⬝ᵥ y = 1 ∧ a ≠ hvec H y := by
  obtain ⟨u, v, hu, hv, distinct⟩ := nonconstant
  by_cases equal : a = hvec H u
  · exact ⟨v, hv, fun h => distinct (equal.symm.trans h)⟩
  · exact ⟨u, hu, equal⟩

theorem threshold_dimension_eq {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (dimension : n = 2 * m) (nonconstant : NonconstantOnUnit H)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (1 - Hcomb H (hvec H x)))) = m := by
  obtain ⟨y, hy, distinct⟩ := exists_other_image H nonconstant (hvec H x)
  have dx := threshold_dimension H hsym hnorm x hx
  have dy := threshold_dimension H hsym hnorm y hy
  have disj := fibre_kernels_disjoint H hsym hnorm (hvec H x) (hvec H y)
    (hvec_unit H hnorm x hx) (hvec_unit H hnorm y hy) distinct
  have sum := Submodule.finrank_add_finrank_le_of_disjoint disj
  rw [Module.finrank_pi, Fintype.card_fin] at sum
  omega

lemma rank_identity_columns {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1) :
    1 - Hcomb H (hvec H x) =
      (2 : ℝ) • (columnMap H x * (columnMap H x)ᵀ) - (2 : ℝ) • vecMulVec x x := by
  rw [rank_identity H hsym hnorm x hx]
  congr 2
  ext j k
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.transpose_apply, columnMap]

lemma outer_mulVec_real {r s : ℕ} (u : Fin r → ℝ) (v y : Fin s → ℝ) :
    vecMulVec u v *ᵥ y = (v ⬝ᵥ y) • u := by
  ext j
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma threshold_range_le {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1) :
    LinearMap.range (1 - Hcomb H (hvec H x)).mulVecLin ≤
      LinearMap.range (columnMap H x).mulVecLin := by
  rintro y ⟨z, rfl⟩
  refine ⟨(2 : ℝ) • ((columnMap H x)ᵀ *ᵥ z) - (2 * (x ⬝ᵥ z)) • hvec H x, ?_⟩
  change columnMap H x *ᵥ _ = (1 - Hcomb H (hvec H x)) *ᵥ z
  rw [rank_identity_columns H hsym hnorm x hx, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    outer_mulVec_real, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
    columnMap_mulVec H x (hvec H x), Hcomb_hvec_mulVec H hsym hnorm x hx, smul_smul]

theorem columnMap_injective {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (dimension : n = 2 * m) (nonconstant : NonconstantOnUnit H)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1) :
    Function.Injective (columnMap H x).mulVecLin := by
  let B := 1 - Hcomb H (hvec H x)
  let V := columnMap H x
  have dk := threshold_dimension_eq H hsym hnorm dimension nonconstant x hx
  rw [Matrix.toLin'_apply'] at dk
  have bn := B.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin] at bn
  have br : B.rank = m := by change B.rank + _ = n at bn; change Module.finrank ℝ B.mulVecLin.ker = m at dk; omega
  have bx : B *ᵥ x = 0 := by
    dsimp only [B]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Hcomb_hvec_mulVec H hsym hnorm x hx, sub_self]
  have bs : B.IsSymm := Matrix.isSymm_one.sub (Hcomb_symm H hsym _)
  have outside : x ∉ LinearMap.range B.mulVecLin := by
    rintro ⟨z, hz⟩
    have orthogonal := bs.dotProduct_mulVec_comm (x := x) (y := z)
    change B *ᵥ z = x at hz
    rw [hz, bx, dotProduct_zero] at orthogonal
    linarith
  have inside : x ∈ LinearMap.range V.mulVecLin :=
    ⟨hvec H x, (columnMap_mulVec H x _).trans (Hcomb_hvec_mulVec H hsym hnorm x hx)⟩
  have strict : LinearMap.range B.mulVecLin < LinearMap.range V.mulVecLin := by
    refine lt_iff_le_and_ne.mpr ⟨threshold_range_le H hsym hnorm x hx, ?_⟩
    intro equal
    exact outside (equal.symm ▸ inside)
  have vr := Submodule.finrank_lt_finrank_of_lt strict
  change B.rank < V.rank at vr
  have vn := V.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin] at vn
  change V.rank + _ = m + 1 at vn
  have zero : Module.finrank ℝ V.mulVecLin.ker = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp zero)

lemma eigen_coefficient_eq {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (dimension : n = 2 * m) (nonconstant : NonconstantOnUnit H)
    (a : Fin (m + 1) → ℝ) (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1)
    (value : ℝ) (eigen : Hcomb H a *ᵥ x = value • x) : a = value • hvec H x := by
  apply columnMap_injective H hsym hnorm dimension nonconstant x hx
  change columnMap H x *ᵥ a = columnMap H x *ᵥ (value • hvec H x)
  rw [columnMap_mulVec, eigen, Matrix.mulVec_smul, columnMap_mulVec,
    Hcomb_hvec_mulVec H hsym hnorm x hx]

lemma eigenvalue_sq {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (dimension : n = 2 * m) (nonconstant : NonconstantOnUnit H)
    (a : Fin (m + 1) → ℝ) (ha : a ⬝ᵥ a = 1)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1)
    (value : ℝ) (eigen : Hcomb H a *ᵥ x = value • x) : value ^ 2 = 1 := by
  have equal := eigen_coefficient_eq H hsym hnorm dimension nonconstant a x hx value eigen
  have imageUnit := hvec_unit H hnorm x hx
  rw [equal, smul_dotProduct, dotProduct_smul, imageUnit, smul_eq_mul, smul_eq_mul, mul_one] at ha
  nlinarith only [ha]

lemma eigenvector_unit {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hermitian : A.IsHermitian) (i : Fin n) :
    (⇑(hermitian.eigenvectorBasis i)) ⬝ᵥ (⇑(hermitian.eigenvectorBasis i)) = 1 := by
  have unit := hermitian.eigenvectorBasis.orthonormal.1 i
  have inner : inner ℝ (hermitian.eigenvectorBasis i) (hermitian.eigenvectorBasis i) = 1 := by
    rw [real_inner_self_eq_norm_sq, unit]
    norm_num
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using inner

theorem threshold_sq {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (dimension : n = 2 * m) (_positive : 1 ≤ m) (nonconstant : NonconstantOnUnit H)
    (a : Fin (m + 1) → ℝ) (ha : a ⬝ᵥ a = 1) : Hcomb H a * Hcomb H a = 1 := by
  let hermitian := Matrix.isHermitian_iff_isSymm.mpr (Hcomb_symm H hsym a)
  have values (i : Fin n) : hermitian.eigenvalues i ^ 2 = 1 :=
    eigenvalue_sq H hsym hnorm dimension nonconstant a ha
      (⇑(hermitian.eigenvectorBasis i)) (eigenvector_unit hermitian i)
      (hermitian.eigenvalues i) (hermitian.mulVec_eigenvectorBasis i)
  have dsq : diagonal (RCLike.ofReal ∘ hermitian.eigenvalues : Fin n → ℝ) *
      diagonal (RCLike.ofReal ∘ hermitian.eigenvalues : Fin n → ℝ) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases equal : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.mul_apply,
        Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, ← pow_two] using values i
    · simp [Matrix.diagonal_apply_ne _ equal, Matrix.one_apply_ne equal]
  have conjugated := congrArg (Unitary.conjStarAlgAut ℝ _ hermitian.eigenvectorUnitary) dsq
  simpa only [map_mul, map_one, ← hermitian.spectral_theorem] using conjugated

theorem threshold_onto {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (dimension : n = 2 * m) (positive : 1 ≤ m) (nonconstant : NonconstantOnUnit H)
    (a : Fin (m + 1) → ℝ) (ha : a ⬝ᵥ a = 1) :
    ∃ x : Fin n → ℝ, x ⬝ᵥ x = 1 ∧ hvec H x = a := by
  let A := Hcomb H a
  have square : A * A = 1 := threshold_sq H hsym hnorm dimension positive nonconstant a ha
  have notMinus : A ≠ -1 := by
    intro equal
    obtain ⟨u, v, hu, hv, distinct⟩ := nonconstant
    have eu : A *ᵥ u = (-1 : ℝ) • u := by
      rw [equal, Matrix.neg_mulVec, Matrix.one_mulVec, neg_one_smul]
    have ev : A *ᵥ v = (-1 : ℝ) • v := by
      rw [equal, Matrix.neg_mulVec, Matrix.one_mulVec, neg_one_smul]
    have cu := eigen_coefficient_eq H hsym hnorm dimension ⟨u, v, hu, hv, distinct⟩ a u hu (-1) eu
    have cv := eigen_coefficient_eq H hsym hnorm dimension ⟨u, v, hu, hv, distinct⟩ a v hv (-1) ev
    apply distinct
    apply neg_injective
    simpa only [neg_one_smul] using cu.symm.trans cv
  have notZero : A + 1 ≠ 0 := by
    intro equal
    exact notMinus (eq_neg_of_add_eq_zero_left equal)
  have existsVector : ∃ y : Fin n → ℝ, (A + 1) *ᵥ y ≠ 0 := by
    by_contra absent
    push Not at absent
    apply notZero
    apply Matrix.mulVec_injective
    funext y
    rw [absent y, Matrix.zero_mulVec]
  obtain ⟨y, hy⟩ := existsVector
  let z := (A + 1) *ᵥ y
  have eigen : A *ᵥ z = z := by
    dsimp only [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_add, square, Matrix.mul_one, add_comm]
  obtain ⟨c, unit⟩ := unit_rescale z hy
  refine ⟨c • z, unit, ?_⟩
  apply (threshold_fibre H hsym hnorm a ha (c • z) unit).mpr
  change (1 - A) *ᵥ (c • z) = 0
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul, eigen, sub_self]

lemma Hcomb_add {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (a b : Fin (m + 1) → ℝ) : Hcomb H (a + b) = Hcomb H a + Hcomb H b := by
  simp only [Hcomb, Pi.add_apply, add_smul, Finset.sum_add_distrib]

lemma Hcomb_smul {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ) (a : Fin (m + 1) → ℝ) : Hcomb H (c • a) = c • Hcomb H a := by
  simp only [Hcomb, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

lemma Hcomb_single {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (i : Fin (m + 1)) : Hcomb H (Pi.single i 1) = H i := by
  simp [Hcomb, Pi.single_apply]

theorem threshold_c {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (dimension : n = 2 * m) (positive : 1 ≤ m) (nonconstant : NonconstantOnUnit H)
    (i j : Fin (m + 1)) : H i * H j + H j * H i = if i = j then 2 else 0 := by
  have each (k : Fin (m + 1)) : H k * H k = 1 := by
    have unit : (Pi.single k 1 : Fin (m + 1) → ℝ) ⬝ᵥ Pi.single k 1 = 1 := by simp
    simpa only [Hcomb_single] using
      threshold_sq H hsym hnorm dimension positive nonconstant (Pi.single k 1) unit
  by_cases equal : i = j
  · subst j
    rw [ite_eq_left rfl, each]
    norm_num
  · rw [ite_eq_right equal]
    let a : Fin (m + 1) → ℝ := (3 / 5 : ℝ) • Pi.single i 1 + (4 / 5 : ℝ) • Pi.single j 1
    have unit : a ⬝ᵥ a = 1 := by
      dsimp only [a]
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul]
      norm_num [equal, Ne.symm equal]
    have square := threshold_sq H hsym hnorm dimension positive nonconstant a unit
    dsimp only [a] at square
    rw [Hcomb_add, Hcomb_smul, Hcomb_smul, Hcomb_single, Hcomb_single] at square
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, each] at square
    ext r s
    have entry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M r s) square
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at entry
    change (H i * H j) r s + (H j * H i) r s = 0
    linarith only [entry]

def perpendicular {n : ℕ} (x : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (dotProductBilin ℝ ℝ x)

def differential {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : perpendicular x →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
  ((columnMap H x)ᵀ).mulVecLin.comp (perpendicular x).subtype

lemma differential_apply {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (y : perpendicular x) (i : Fin (m + 1)) :
    differential H x y i = (H i *ᵥ x) ⬝ᵥ (y : Fin n → ℝ) := rfl

lemma perpendicular_finrank {k : ℕ} (a : Fin (k + 1) → ℝ) (ha : a ⬝ᵥ a = 1) :
    Module.finrank ℝ (perpendicular a) = k := by
  have nonzero : (dotProductBilin ℝ ℝ a : (Fin (k + 1) → ℝ) →ₗ[ℝ] ℝ) ≠ 0 := by
    intro equal
    have evaluated := congrArg (fun f : (Fin (k + 1) → ℝ) →ₗ[ℝ] ℝ => f a) equal
    change a ⬝ᵥ a = 0 at evaluated
    linarith
  have dimension := Module.Dual.finrank_ker_add_one_of_ne_zero nonzero
  rw [Module.finrank_pi, Fintype.card_fin] at dimension
  change Module.finrank ℝ (perpendicular a) + 1 = k + 1 at dimension
  omega

lemma differential_range {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (dimension : n = 2 * m) (nonconstant : NonconstantOnUnit H)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1) :
    LinearMap.range (differential H x) = perpendicular (hvec H x) := by
  have rankT : ((columnMap H x)ᵀ).rank = m + 1 := by
    rw [Matrix.rank_transpose]
    change Module.finrank ℝ (LinearMap.range (columnMap H x).mulVecLin) = m + 1
    rw [LinearMap.finrank_range_of_inj (columnMap_injective H hsym hnorm dimension nonconstant x hx),
      Module.finrank_pi, Fintype.card_fin]
  have top : LinearMap.range ((columnMap H x)ᵀ).mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by simpa only [Matrix.rank, Module.finrank_pi, Fintype.card_fin] using rankT)
  have surjective := LinearMap.range_eq_top.mp top
  have orthogonal (y : Fin n → ℝ) :
      hvec H x ⬝ᵥ ((columnMap H x)ᵀ *ᵥ y) = x ⬝ᵥ y := by
    rw [Matrix.dotProduct_transpose_mulVec, columnMap_mulVec, Hcomb_hvec_mulVec H hsym hnorm x hx]
    exact dotProduct_comm y x
  apply le_antisymm
  · rintro b ⟨y, rfl⟩
    change hvec H x ⬝ᵥ ((columnMap H x)ᵀ *ᵥ (y : Fin n → ℝ)) = 0
    rw [orthogonal]
    exact y.property
  · intro b hb
    obtain ⟨y, hy⟩ := surjective b
    have member : y ∈ perpendicular x := by
      change x ⬝ᵥ y = 0
      rw [← orthogonal y]
      change ((columnMap H x)ᵀ *ᵥ y) = b at hy
      rw [hy]
      exact hb
    exact ⟨⟨y, member⟩, hy⟩

theorem threshold_dh_rank {n m : ℕ}
    (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Fin n → ℝ, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (dimension : n = 2 * m) (_positive : 1 ≤ m) (nonconstant : NonconstantOnUnit H)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1) :
    Module.finrank ℝ (LinearMap.range (differential H x)) = m := by
  rw [differential_range H hsym hnorm dimension nonconstant x hx]
  exact perpendicular_finrank (hvec H x) (hvec_unit H hnorm x hx)

/-! ### The statement forms of `Osserman/Paper/Statements.lean` -/

theorem lem_4_1_le_one_proved {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) :
    ∀ (a : Fin (m + 1) → ℝ) (x : Vec n), a ⬝ᵥ a = 1 → x ⬝ᵥ x = 1 →
      x ⬝ᵥ (Hcomb H a *ᵥ x) ≤ 1 ∧ (x ⬝ᵥ (Hcomb H a *ᵥ x) = 1 ↔ hvec H x = a) :=
  fun a x ha hx => threshold_le_one H hsym hnorm a x ha hx

theorem lem_4_1_a_proved {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) :
    ∀ a : Fin (m + 1) → ℝ, (∃ x, x ⬝ᵥ x = 1 ∧ hvec H x = a) →
      (1 - Hcomb H a).PosSemidef ∧ (∀ x, x ⬝ᵥ x = 1 → (hvec H x = a ↔ (1 - Hcomb H a) *ᵥ x = 0)) ∧
        n - m ≤ Module.finrank ℝ ↥(LinearMap.ker (Matrix.toLin' (1 - Hcomb H a))) :=
  fun a ha => threshold_a H hsym hnorm a ha

theorem lem_4_1_fibres_disjoint_proved {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i, (H i).IsSymm) (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (a b : Fin (m + 1) → ℝ)
    (ha : ∃ x, x ⬝ᵥ x = 1 ∧ hvec H x = a) (hb : ∃ x, x ⬝ᵥ x = 1 ∧ hvec H x = b) (hab : a ≠ b) :
    LinearMap.ker (Matrix.toLin' (1 - Hcomb H a)) ⊓ LinearMap.ker (Matrix.toLin' (1 - Hcomb H b)) = ⊥ := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact disjoint_iff.mp
    (fibre_kernels_disjoint H hsym hnorm _ _ (hvec_unit H hnorm x hx) (hvec_unit H hnorm y hy) hab)

theorem lem_4_1_b_proved {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : 2 * m < n) :
    ∀ x y : Vec n, x ⬝ᵥ x = 1 → y ⬝ᵥ y = 1 → hvec H x = hvec H y :=
  fun x y hx hy => threshold_b H hsym hnorm hn x y hx hy

/-- `x^⊥` of Defs/Basic.lean is `perpendicular x`. -/
lemma perp_eq_perpendicular {n : ℕ} (x : Vec n) : perp x = perpendicular x := by
  ext y
  exact Iff.rfl

theorem lem_4_1_dh_rank_proved {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) (x : Vec n) (hx : x ⬝ᵥ x = 1) :
    Module.finrank ℝ ↥((perp x).map (Matrix.toLin' (Matrix.of fun i j => (H i *ᵥ x) j))) = m := by
  have hM : Matrix.toLin' (Matrix.of fun i j => (H i *ᵥ x) j) = ((columnMap H x)ᵀ).mulVecLin := rfl
  have hr : (perp x).map (Matrix.toLin' (Matrix.of fun i j => (H i *ᵥ x) j)) =
      LinearMap.range (differential H x) := by
    rw [differential, LinearMap.range_comp, Submodule.range_subtype, perp_eq_perpendicular, hM]
  rw [hr]
  exact threshold_dh_rank H hsym hnorm hn hm hnc x hx

theorem lem_4_1_onto_proved {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) :
    ∀ a : Fin (m + 1) → ℝ, a ⬝ᵥ a = 1 → ∃ x, x ⬝ᵥ x = 1 ∧ hvec H x = a :=
  fun a ha => threshold_onto H hsym hnorm hn hm hnc a ha

theorem lem_4_1_sq_proved {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) :
    ∀ a : Fin (m + 1) → ℝ, a ⬝ᵥ a = 1 → Hcomb H a * Hcomb H a = 1 :=
  fun a ha => threshold_sq H hsym hnorm hn hm hnc a ha

theorem lem_4_1_c_proved {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) :
    ∀ i j, H i * H j + H j * H i = if i = j then 2 else 0 :=
  fun i j => threshold_c H hsym hnorm hn hm hnc i j

end Osserman.Proofs.Threshold
