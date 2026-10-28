/-
Osserman/Proofs/Threshold2.lean — four more named steps of Lemma 4.1 (paper 013 l. 523-533; review a1 M-3): dim U_a = m,
the independence of the H_ix, the image of h is open and compact, and the ±1 eigenspaces of H(a).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Threshold

namespace Osserman.Proofs.Threshold2

open Osserman Osserman.Proofs.Threshold Matrix

theorem lem_4_1_dim_eq_proved {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) (a : Fin (m + 1) → ℝ)
    (ha : ∃ x, x ⬝ᵥ x = 1 ∧ hvec H x = a) :
    Module.finrank ℝ ↥(LinearMap.ker (Matrix.toLin' (1 - Hcomb H a))) = m := by
  obtain ⟨x, hx, rfl⟩ := ha
  exact threshold_dimension_eq H hsym hnorm hn hnc x hx

theorem lem_4_1_indep_proved {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) (x : Vec n) (hx : x ⬝ᵥ x = 1) :
    ∀ u : Fin (m + 1) → ℝ, u ⬝ᵥ hvec H x = 0 →
      x ⬝ᵥ (Hcomb H u *ᵥ x) = 0 ∧ (Hcomb H u *ᵥ x = 0 → u = 0) := by
  intro u hu
  refine ⟨(quadratic_combination H u x).trans hu, ?_⟩
  intro zero
  apply columnMap_injective H hsym hnorm hn hnc x hx
  change columnMap H x *ᵥ u = columnMap H x *ᵥ 0
  rw [columnMap_mulVec, zero, Matrix.mulVec_zero]

lemma unit_set_compact {k : ℕ} : IsCompact {a : Fin k → ℝ | a ⬝ᵥ a = 1} := by
  have closed : IsClosed {a : Fin k → ℝ | a ⬝ᵥ a = 1} := by
    apply isClosed_eq _ continuous_const
    unfold dotProduct
    fun_prop
  have bounds (a : Fin k → ℝ) (ha : a ⬝ᵥ a = 1) (i : Fin k) : -1 ≤ a i ∧ a i ≤ 1 := by
    have total : ∑ j, a j ^ 2 = 1 := by simpa only [dotProduct, pow_two] using ha
    have square : a i ^ 2 ≤ 1 := by
      rw [← total]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
    constructor <;> nlinarith
  apply (isCompact_Icc : IsCompact (Set.Icc (-1 : Fin k → ℝ) 1)).of_isClosed_subset closed
  intro a ha
  exact ⟨fun i => (bounds a ha i).1, fun i => (bounds a ha i).2⟩

theorem lem_4_1_image_open_proved {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) :
    IsOpen {a : {a : Fin (m + 1) → ℝ // a ⬝ᵥ a = 1} | ∃ x : Vec n, x ⬝ᵥ x = 1 ∧ hvec H x = a.1} ∧
      IsCompact {a : Fin (m + 1) → ℝ | ∃ x : Vec n, x ⬝ᵥ x = 1 ∧ hvec H x = a} := by
  have onto := threshold_onto H hsym hnorm hn hm hnc
  constructor
  · have equal : {a : {a : Fin (m + 1) → ℝ // a ⬝ᵥ a = 1} | ∃ x : Vec n, x ⬝ᵥ x = 1 ∧ hvec H x = a.1} =
        Set.univ := by
      ext a
      exact iff_true_intro (onto a.1 a.2)
    rw [equal]
    exact isOpen_univ
  · have equal : {a : Fin (m + 1) → ℝ | ∃ x : Vec n, x ⬝ᵥ x = 1 ∧ hvec H x = a} =
        {a : Fin (m + 1) → ℝ | a ⬝ᵥ a = 1} := by
      ext a
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hvec_unit H hnorm x hx
      · exact onto a
    rw [equal]
    exact unit_set_compact

theorem lem_4_1_pm_eigenspaces_proved {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) :
    ∀ a : Fin (m + 1) → ℝ, a ⬝ᵥ a = 1 →
      (∃ x, x ⬝ᵥ x = 1 ∧ hvec H x = -a) ∧
      Module.finrank ℝ ↥(LinearMap.ker (Matrix.toLin' (1 - Hcomb H a))) = m ∧
      Module.finrank ℝ ↥(LinearMap.ker (Matrix.toLin' (1 + Hcomb H a))) = m := by
  intro a ha
  have negUnit : (-a) ⬝ᵥ (-a) = 1 := by simpa only [neg_dotProduct, dotProduct_neg, neg_neg] using ha
  have attained := threshold_onto H hsym hnorm hn hm hnc a ha
  have attainedNeg := threshold_onto H hsym hnorm hn hm hnc (-a) negUnit
  refine ⟨attainedNeg, lem_4_1_dim_eq_proved H hsym hnorm hn hnc a attained, ?_⟩
  have negative := lem_4_1_dim_eq_proved H hsym hnorm hn hnc (-a) attainedNeg
  have combination : Hcomb H (-a) = -Hcomb H a := by
    simpa only [neg_one_smul] using Hcomb_smul H (-1) a
  rw [combination, sub_neg_eq_add] at negative
  exact negative

end Osserman.Proofs.Threshold2
