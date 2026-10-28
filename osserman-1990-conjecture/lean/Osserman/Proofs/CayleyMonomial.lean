/-
helpers/CayleyMonomial.lean — products of two monomials in the generators of a symmetric Clifford system on ℝ^16
(paper 013, §6): `sec6_monomial_product`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.CayleyProducts

namespace Osserman.Proofs.CayleyMonomial

open Osserman Matrix
open Osserman.Proofs.CayleyProducts

/-- `A = ±B`. -/
def PlusMinus {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Prop := A = B ∨ A = -B

lemma PlusMinus.refl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : PlusMinus A A := Or.inl rfl

lemma PlusMinus.symm {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (h : PlusMinus A B) : PlusMinus B A := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

lemma PlusMinus.trans {n : ℕ} {A B C : Matrix (Fin n) (Fin n) ℝ} (hab : PlusMinus A B)
    (hbc : PlusMinus B C) : PlusMinus A C := by
  rcases hab with h | h <;> rcases hbc with g | g
  · exact Or.inl (h.trans g)
  · exact Or.inr (h.trans g)
  · exact Or.inr (by rw [h, g])
  · exact Or.inl (by rw [h, g, neg_neg])

lemma PlusMinus.mul_left {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (C : Matrix (Fin n) (Fin n) ℝ)
    (h : PlusMinus A B) : PlusMinus (C * A) (C * B) := by
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h, mul_neg])

lemma PlusMinus.mul_right {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (C : Matrix (Fin n) (Fin n) ℝ)
    (h : PlusMinus A B) : PlusMinus (A * C) (B * C) := by
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h, neg_mul])

lemma word_cons {n k : ℕ} (S : Fin k → Matrix (Fin n) (Fin n) ℝ) (i : Fin k) (l : List (Fin k)) :
    word S (i :: l) = S i * word S l := by
  simp [word]

/-- Reordering the factors of a word changes it at most by a sign. -/
lemma word_perm {n k : ℕ} (S : Fin k → Matrix (Fin n) (Fin n) ℝ) (hS : IsSymmCliffordSystem S)
    {l₁ l₂ : List (Fin k)} (h : l₁.Perm l₂) : PlusMinus (word S l₁) (word S l₂) := by
  induction h with
  | nil => exact PlusMinus.refl _
  | cons x _ ih =>
    rw [word_cons, word_cons]
    exact ih.mul_left (S x)
  | swap x y l =>
    rw [word_cons, word_cons, word_cons, word_cons, ← mul_assoc, ← mul_assoc, generator_swap S hS y x]
    by_cases same : y = x
    · rw [ite_eq_left same, one_smul]
      exact PlusMinus.refl _
    · rw [ite_eq_right same, neg_one_zsmul, neg_mul]
      exact Or.inr rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- One generator times a sorted monomial is ± the sorted monomial over `{i} Δ t`. -/
lemma generator_times_sorted {n k : ℕ} (S : Fin k → Matrix (Fin n) (Fin n) ℝ)
    (hS : IsSymmCliffordSystem S) (i : Fin k) (t : Finset (Fin k)) :
    PlusMinus (S i * word S (t.sort (· ≤ ·))) (word S ((symmDiff {i} t).sort (· ≤ ·))) := by
  by_cases member : i ∈ t
  · have distinct : (i :: (symmDiff {i} t).sort (· ≤ ·)).Nodup := by
      refine List.nodup_cons.mpr ⟨?_, Finset.sort_nodup _ _⟩
      simp [Finset.mem_sort, Finset.mem_symmDiff, member]
    have perm : (t.sort (· ≤ ·)).Perm (i :: (symmDiff {i} t).sort (· ≤ ·)) := by
      refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) distinct).mpr ?_
      intro a
      simp only [List.mem_cons, Finset.mem_sort, Finset.mem_symmDiff, Finset.mem_singleton]
      by_cases equal : a = i
      · subst equal
        simp [member]
      · simp [equal]
    have moved := (word_perm S hS perm).mul_left (S i)
    rw [word_cons, ← mul_assoc, system_square S hS, one_mul] at moved
    exact moved
  · have distinct : (i :: t.sort (· ≤ ·)).Nodup :=
      List.nodup_cons.mpr ⟨by simpa [Finset.mem_sort] using member, Finset.sort_nodup _ _⟩
    have perm : (i :: t.sort (· ≤ ·)).Perm ((symmDiff {i} t).sort (· ≤ ·)) := by
      refine (List.perm_ext_iff_of_nodup distinct (Finset.sort_nodup _ _)).mpr ?_
      intro a
      simp only [List.mem_cons, Finset.mem_sort, Finset.mem_symmDiff, Finset.mem_singleton]
      by_cases equal : a = i
      · subst equal
        simp [member]
      · simp [equal]
    have moved := word_perm S hS perm
    rw [word_cons] at moved
    exact moved

/-- The product of two sorted monomials is ± the sorted monomial over the symmetric difference. -/
lemma sorted_product {n k : ℕ} (S : Fin k → Matrix (Fin n) (Fin n) ℝ) (hS : IsSymmCliffordSystem S)
    (s t : Finset (Fin k)) :
    PlusMinus (word S (s.sort (· ≤ ·)) * word S (t.sort (· ≤ ·)))
      (word S ((symmDiff s t).sort (· ≤ ·))) := by
  induction s using Finset.induction_on with
  | empty =>
    have base : symmDiff (∅ : Finset (Fin k)) t = t := by
      ext a
      simp [Finset.mem_symmDiff]
    rw [base, Finset.sort_empty]
    simp only [word, List.map_nil, List.prod_nil, one_mul]
    exact PlusMinus.refl _
  | insert a s absent ih =>
    have single : symmDiff {a} s = insert a s := by
      ext x
      by_cases equal : x = a
      · subst equal
        simp [Finset.mem_symmDiff, absent]
      · simp [Finset.mem_symmDiff, equal]
    have regroup : symmDiff {a} (symmDiff s t) = symmDiff (insert a s) t := by
      rw [← single, symmDiff_assoc]
    have head := generator_times_sorted S hS a s
    rw [single] at head
    have first := head.symm.mul_right (word S (t.sort (· ≤ ·)))
    rw [mul_assoc] at first
    have last := generator_times_sorted S hS a (symmDiff s t)
    rw [regroup] at last
    exact first.trans ((ih.mul_left (S a)).trans last)

lemma symmDiff_card_pos {k : ℕ} (s t : Finset (Fin k)) (distinct : s ≠ t) : 1 ≤ (symmDiff s t).card := by
  obtain ⟨i, differ⟩ := differing_membership s t distinct
  have positive : 0 < (symmDiff s t).card :=
    Finset.card_pos.mpr ⟨i, by rw [Finset.mem_symmDiff]; tauto⟩
  omega

lemma symmDiff_card_le {k : ℕ} (s t : Finset (Fin k)) (cs : s.card = 0 ∨ s.card = 1 ∨ s.card = 4)
    (ct : t.card = 0 ∨ t.card = 1 ∨ t.card = 4) : (symmDiff s t).card ≤ 8 := by
  have contained : symmDiff s t ⊆ s ∪ t := by
    intro x member
    rw [Finset.mem_symmDiff] at member
    rw [Finset.mem_union]
    tauto
  have subsetBound := Finset.card_le_card contained
  have unionBound := Finset.card_union_le s t
  omega

lemma anticommute_of_sign {n k : ℕ} (S : Fin k → Matrix (Fin n) (Fin n) ℝ) (hS : IsSymmCliffordSystem S)
    (i : Fin k) (l : List (Fin k)) (sign : wordSign i l = -1) :
    S i * word S l = -(word S l * S i) := by
  rw [word_commute S hS, sign, neg_one_zsmul]

lemma anticommute_of_plusMinus {n : ℕ} {A B M : Matrix (Fin n) (Fin n) ℝ} (h : PlusMinus A B)
    (anti : M * B = -(B * M)) : M * A = -(A * M) := by
  rcases h with h | h <;> rw [h]
  · exact anti
  · rw [mul_neg, neg_mul, anti]

theorem sec6_monomial_product_proved (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) :
    let prod := fun s : Finset (Fin 9) => ((s.sort (· ≤ ·)).map S).prod
    let idx := (Finset.univ : Finset (Finset (Fin 9))).filter fun s => s.card = 0 ∨ s.card = 1 ∨ s.card = 4
    ∀ s ∈ idx, ∀ t ∈ idx, s ≠ t →
      (prod s * prod t = prod (symmDiff s t) ∨ prod s * prod t = -prod (symmDiff s t)) ∧
      1 ≤ (symmDiff s t).card ∧ (symmDiff s t).card ≤ 8 ∧
      (Odd (symmDiff s t).card →
        ∃ i, i ∉ symmDiff s t ∧ S i * (prod s * prod t) = -((prod s * prod t) * S i)) ∧
      (Even (symmDiff s t).card →
        ∃ i, i ∈ symmDiff s t ∧ S i * (prod s * prod t) = -((prod s * prod t) * S i)) := by
  dsimp only
  intro s hs t ht distinct
  have cs := (Finset.mem_filter.mp hs).2
  have ct := (Finset.mem_filter.mp ht).2
  have pm := sorted_product S hS s t
  have lower := symmDiff_card_pos s t distinct
  have upper := symmDiff_card_le s t cs ct
  refine ⟨pm, lower, upper, ?_, ?_⟩
  · intro odd
    have bound : (symmDiff s t).card < (Finset.univ : Finset (Fin 9)).card := by
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨i, _, outside⟩ := Finset.exists_mem_notMem_of_card_lt_card bound
    have absent : i ∉ (symmDiff s t).sort (· ≤ ·) := by simpa [Finset.mem_sort] using outside
    have sign : wordSign i ((symmDiff s t).sort (· ≤ ·)) = -1 := by
      rw [wordSign_of_not_mem i ((symmDiff s t).sort (· ≤ ·)) absent, Finset.length_sort]
      exact odd.neg_one_pow
    exact ⟨i, outside, anticommute_of_plusMinus pm (anticommute_of_sign S hS i _ sign)⟩
  · intro even
    obtain ⟨i, inside⟩ := Finset.card_pos.mp (by omega : 0 < (symmDiff s t).card)
    have present : i ∈ (symmDiff s t).sort (· ≤ ·) := by simpa [Finset.mem_sort] using inside
    have sign : wordSign i ((symmDiff s t).sort (· ≤ ·)) = -1 := by
      rw [wordSign_nodup i _ (Finset.sort_nodup _ _), ite_eq_left present, Finset.length_sort, even.neg_one_pow]
    exact ⟨i, inside, anticommute_of_plusMinus pm (anticommute_of_sign S hS i _ sign)⟩

end Osserman.Proofs.CayleyMonomial

