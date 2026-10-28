/-
Osserman/Proofs/CayleyProducts.lean — products of generators of a symmetric Clifford system on ℝ^16 and the 136-basis
of the symmetric matrices (paper 013, §6, l. 611-626): `sec6_basis_136`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.Basic

namespace Osserman.Proofs.CayleyProducts

open Osserman Matrix

lemma system_square {n k : ℕ} (S : Fin k → Matrix (Fin n) (Fin n) ℝ)
    (hS : IsSymmCliffordSystem S) (i : Fin k) : S i * S i = 1 := by
  have equal := hS.2 i i
  rw [ite_eq_left rfl] at equal
  ext r c
  have entry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M r c) equal
  simp only [Matrix.add_apply] at entry
  have two : (2 : Matrix (Fin n) (Fin n) ℝ) = 1 + 1 := by norm_num
  rw [two, Matrix.add_apply] at entry
  linarith

def word {n k : ℕ} (S : Fin k → Matrix (Fin n) (Fin n) ℝ) (indices : List (Fin k)) :
    Matrix (Fin n) (Fin n) ℝ := (indices.map S).prod

def wordSign {k : ℕ} (i : Fin k) (indices : List (Fin k)) : ℤ :=
  (indices.map (fun j => if i = j then (1 : ℤ) else -1)).prod

lemma generator_swap {n k : ℕ} (S : Fin k → Matrix (Fin n) (Fin n) ℝ)
    (hS : IsSymmCliffordSystem S) (i j : Fin k) :
    S i * S j = (if i = j then (1 : ℤ) else -1) • (S j * S i) := by
  by_cases same : i = j
  · subst j
    simp
  · rw [ite_eq_right same, neg_one_zsmul]
    exact eq_neg_of_add_eq_zero_left (by simpa only [ite_eq_right same] using hS.2 i j)

lemma word_commute {n k : ℕ} (S : Fin k → Matrix (Fin n) (Fin n) ℝ)
    (hS : IsSymmCliffordSystem S) (i : Fin k) (indices : List (Fin k)) :
    S i * word S indices = wordSign i indices • (word S indices * S i) := by
  induction indices with
  | nil => simp [word, wordSign]
  | cons j rest ih =>
    simp only [word, List.map_cons, List.prod_cons, wordSign] at ih ⊢
    rw [← mul_assoc, generator_swap S hS i j, smul_mul_assoc, mul_assoc, ih,
      mul_smul_comm, smul_smul, ← mul_assoc]

lemma word_conjugate {n k : ℕ} (S : Fin k → Matrix (Fin n) (Fin n) ℝ)
    (hS : IsSymmCliffordSystem S) (i : Fin k) (indices : List (Fin k)) :
    S i * word S indices * S i = wordSign i indices • word S indices := by
  rw [word_commute S hS, smul_mul_assoc, mul_assoc, system_square S hS, mul_one]

lemma wordSign_of_not_mem {k : ℕ} (i : Fin k) (indices : List (Fin k)) (absent : i ∉ indices) :
    wordSign i indices = (-1 : ℤ) ^ indices.length := by
  induction indices with
  | nil => simp [wordSign]
  | cons j rest ih =>
    have different : i ≠ j := fun equal => absent (by simp [equal])
    have absentRest : i ∉ rest := fun member => absent (by simp [member])
    simp only [wordSign, List.map_cons, List.prod_cons, ite_eq_right different,
      List.length_cons, pow_succ]
    rw [← wordSign, ih absentRest]
    ring

def reversalSign : ℕ → ℤ
  | 0 => 1
  | d + 1 => (-1 : ℤ) ^ d * reversalSign d

lemma word_transpose {n k : ℕ} (S : Fin k → Matrix (Fin n) (Fin n) ℝ)
    (hS : IsSymmCliffordSystem S) (indices : List (Fin k)) (distinct : indices.Nodup) :
    (word S indices)ᵀ = reversalSign indices.length • word S indices := by
  induction indices with
  | nil => simp [word, reversalSign]
  | cons i rest ih =>
    obtain ⟨absent, distinctRest⟩ := List.nodup_cons.mp distinct
    have commute := word_commute S hS i rest
    rw [wordSign_of_not_mem i rest absent] at commute
    have signSquare : ((-1 : ℤ) ^ rest.length) * ((-1 : ℤ) ^ rest.length) = 1 := by
      rw [← mul_pow]
      norm_num
    have reversed : word S rest * S i = (-1 : ℤ) ^ rest.length • (S i * word S rest) := by
      rw [commute, smul_smul, signSquare, one_smul]
    change (S i * word S rest)ᵀ = reversalSign (rest.length + 1) • (S i * word S rest)
    rw [Matrix.transpose_mul, hS.1 i, ih distinctRest, smul_mul_assoc, reversed,
      smul_smul, reversalSign]
    congr 1
    ring

lemma word_orthogonal {n k : ℕ} (S : Fin k → Matrix (Fin n) (Fin n) ℝ)
    (hS : IsSymmCliffordSystem S) (indices : List (Fin k)) :
    (word S indices)ᵀ * word S indices = 1 := by
  induction indices with
  | nil => simp [word]
  | cons i rest ih =>
    change (S i * word S rest)ᵀ * (S i * word S rest) = 1
    rw [Matrix.transpose_mul, hS.1 i]
    calc
      _ = (word S rest)ᵀ * (S i * S i) * word S rest := by simp only [mul_assoc]
      _ = 1 := by rw [system_square S hS, mul_one, ih]

lemma word_symmetric_014 {n : ℕ} (S : Fin 9 → Matrix (Fin n) (Fin n) ℝ)
    (hS : IsSymmCliffordSystem S) (s : Finset (Fin 9)) (card : s.card = 0 ∨ s.card = 1 ∨ s.card = 4) :
    (word S (s.sort (· ≤ ·)))ᵀ = word S (s.sort (· ≤ ·)) := by
  rw [word_transpose S hS _ (Finset.sort_nodup _ _), Finset.length_sort]
  rcases card with card | card | card <;> rw [card] <;> norm_num [reversalSign]

lemma wordSign_nodup {k : ℕ} (i : Fin k) (indices : List (Fin k)) (distinct : indices.Nodup) :
    wordSign i indices = if i ∈ indices then -((-1 : ℤ) ^ indices.length) else (-1 : ℤ) ^ indices.length := by
  induction indices with
  | nil => simp [wordSign]
  | cons j rest ih =>
    obtain ⟨absent, nd⟩ := List.nodup_cons.mp distinct
    by_cases same : i = j
    · subst i
      simp only [wordSign, List.map_cons, List.prod_cons, ite_eq_left rfl, one_mul]
      rw [← wordSign, wordSign_of_not_mem j rest absent]
      simp [pow_succ]
    · have inductionEquation := ih nd
      change (if i = j then (1 : ℤ) else -1) * wordSign i rest = _
      rw [ite_eq_right same, inductionEquation]
      by_cases member : i ∈ rest <;> simp [same, member, pow_succ] <;> ring

lemma wordSign_014 {k : ℕ} (s : Finset (Fin k)) (card : s.card = 0 ∨ s.card = 1 ∨ s.card = 4) (i : Fin k) :
    wordSign i (s.sort (· ≤ ·)) =
      if s.card = 1 then (if i ∈ s then 1 else -1) else (if i ∈ s then -1 else 1) := by
  rw [wordSign_nodup i _ (Finset.sort_nodup _ _)]
  simp only [Finset.mem_sort, Finset.length_sort]
  rcases card with card | card | card <;> rw [card] <;> split_ifs <;> norm_num at *

lemma differing_membership {k : ℕ} (s t : Finset (Fin k)) (distinct : s ≠ t) :
    ∃ i, (i ∈ s ∧ i ∉ t) ∨ (i ∉ s ∧ i ∈ t) := by
  by_contra absent
  push Not at absent
  apply distinct
  ext i
  specialize absent i
  tauto

lemma signs_distinguish (s t : Finset (Fin 9))
    (cs : s.card = 0 ∨ s.card = 1 ∨ s.card = 4)
    (ct : t.card = 0 ∨ t.card = 1 ∨ t.card = 4) (distinct : s ≠ t) :
    ∃ i, wordSign i (s.sort (· ≤ ·)) * wordSign i (t.sort (· ≤ ·)) = -1 := by
  by_cases same : (s.card = 1 ↔ t.card = 1)
  · obtain ⟨i, h | h⟩ := differing_membership s t distinct
    · refine ⟨i, ?_⟩
      rw [wordSign_014 s cs, wordSign_014 t ct]
      by_cases sc : s.card = 1
      · simp [sc, same.mp sc, h.1, h.2]
      · have tc : t.card ≠ 1 := fun equal => sc (same.mpr equal)
        simp [sc, tc, h.1, h.2]
    · refine ⟨i, ?_⟩
      rw [wordSign_014 s cs, wordSign_014 t ct]
      by_cases sc : s.card = 1
      · simp [sc, same.mp sc, h.1, h.2]
      · have tc : t.card ≠ 1 := fun equal => sc (same.mpr equal)
        simp [sc, tc, h.1, h.2]
  · have total : s.card + t.card ≤ 5 := by omega
    have bound : (s ∪ t).card < (Finset.univ : Finset (Fin 9)).card := by
      have unionBound := Finset.card_union_le s t
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨i, _, outside⟩ := Finset.exists_mem_notMem_of_card_lt_card bound
    have nots : i ∉ s := fun member => outside (Finset.mem_union_left t member)
    have nott : i ∉ t := fun member => outside (Finset.mem_union_right s member)
    refine ⟨i, ?_⟩
    rw [wordSign_014 s cs, wordSign_014 t ct]
    by_cases sc : s.card = 1
    · have tc : t.card ≠ 1 := fun equal => same (by simp [sc, equal])
      simp [sc, tc, nots, nott]
    · have tc : t.card = 1 := by tauto
      simp [sc, tc, nots, nott]

lemma conjugate_trace {n : ℕ} (S : Fin 9 → Matrix (Fin n) (Fin n) ℝ)
    (hS : IsSymmCliffordSystem S) (i : Fin 9) (M : Matrix (Fin n) (Fin n) ℝ) :
    (S i * M * S i).trace = M.trace := by
  rw [Matrix.trace_mul_cycle, system_square S hS, one_mul]

lemma word_pair_trace_zero {n : ℕ} (S : Fin 9 → Matrix (Fin n) (Fin n) ℝ)
    (hS : IsSymmCliffordSystem S) (s t : Finset (Fin 9))
    (cs : s.card = 0 ∨ s.card = 1 ∨ s.card = 4)
    (ct : t.card = 0 ∨ t.card = 1 ∨ t.card = 4) (distinct : s ≠ t) :
    (word S (s.sort (· ≤ ·)) * word S (t.sort (· ≤ ·))).trace = 0 := by
  obtain ⟨i, opposite⟩ := signs_distinguish s t cs ct distinct
  let A := word S (s.sort (· ≤ ·))
  let B := word S (t.sort (· ≤ ·))
  have factor : S i * (A * B) * S i = (S i * A * S i) * (S i * B * S i) := by
    simp only [mul_assoc]
    rw [← mul_assoc (S i) (S i), system_square S hS, one_mul]
  have conjugate : S i * (A * B) * S i = -(A * B) := by
    rw [factor, word_conjugate S hS i (s.sort (· ≤ ·)), word_conjugate S hS i (t.sort (· ≤ ·)),
      smul_mul_assoc, mul_smul_comm, smul_smul, opposite, neg_one_zsmul]
  have trace := conjugate_trace S hS i (A * B)
  rw [conjugate, Matrix.trace_neg] at trace
  change (A * B).trace = 0
  linarith

def productIndices : Finset (Finset (Fin 9)) :=
  Finset.univ.filter fun s => s.card = 0 ∨ s.card = 1 ∨ s.card = 4

lemma productIndices_card : productIndices.card = 136 := by decide +kernel

lemma productIndices_valid (s : productIndices) : s.1.card = 0 ∨ s.1.card = 1 ∨ s.1.card = 4 :=
  (Finset.mem_filter.mp s.2).2

lemma word_trace_pair (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S)
    (s t : productIndices) :
    (word S (s.1.sort (· ≤ ·)) * word S (t.1.sort (· ≤ ·))).trace = if s = t then 16 else 0 := by
  by_cases same : s = t
  · subst t
    rw [ite_eq_left rfl]
    have ortho := word_orthogonal S hS (s.1.sort (· ≤ ·))
    rw [word_symmetric_014 S hS s.1 (productIndices_valid s)] at ortho
    rw [ortho, Matrix.trace_one]
    norm_num
  · rw [ite_eq_right same]
    exact word_pair_trace_zero S hS s.1 t.1 (productIndices_valid s) (productIndices_valid t)
      (fun equal => same (Subtype.ext equal))

lemma words_independent (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) :
    LinearIndependent ℝ (fun s : productIndices => word S (s.1.sort (· ≤ ·))) := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients zero t
  have traced := congrArg (fun M : Matrix (Fin 16) (Fin 16) ℝ =>
    (M * word S (t.1.sort (· ≤ ·))).trace) zero
  rw [Matrix.sum_mul, Matrix.trace_sum] at traced
  simp only [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, Matrix.zero_mul, Matrix.trace_zero] at traced
  have coefficientZero : coefficients t * 16 = 0 := by
    simpa [word_trace_pair S hS] using traced
  linarith

def symmetricSpace (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {M | Mᵀ = M}
  zero_mem' := by simp
  add_mem' := by
    intro A B ha hb
    change Aᵀ = A at ha
    change Bᵀ = B at hb
    change (A + B)ᵀ = A + B
    rw [Matrix.transpose_add, ha, hb]
  smul_mem' := by
    intro c A ha
    change Aᵀ = A at ha
    change (c • A)ᵀ = c • A
    rw [Matrix.transpose_smul, ha]

def upperCoordinates (n : ℕ) : symmetricSpace n →ₗ[ℝ] ({p : Fin n × Fin n // p.1 ≤ p.2} → ℝ) where
  toFun M p := M.1 p.1.1 p.1.2
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma upperCoordinates_injective (n : ℕ) : Function.Injective (upperCoordinates n) := by
  intro A B equal
  apply Subtype.ext
  ext i j
  by_cases ordered : i ≤ j
  · exact congrFun equal ⟨(i, j), ordered⟩
  · have reverse := congrFun equal ⟨(j, i), le_of_not_ge ordered⟩
    have sa := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) A.property
    have sb := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) B.property
    change A.1 j i = A.1 i j at sa
    change B.1 j i = B.1 i j at sb
    exact sa.symm.trans (reverse.trans sb)

lemma symmetricSpace_finrank_le : Module.finrank ℝ (symmetricSpace 16) ≤ 136 := by
  have bound := LinearMap.finrank_le_finrank_of_injective (upperCoordinates_injective 16)
  rw [Module.finrank_pi] at bound
  have count : Fintype.card {p : Fin 16 × Fin 16 // p.1 ≤ p.2} = 136 := by decide +kernel
  rwa [count] at bound

lemma words_span (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) :
    Submodule.span ℝ (Set.range (fun s : productIndices => word S (s.1.sort (· ≤ ·)))) = symmetricSpace 16 := by
  have contained : Submodule.span ℝ (Set.range (fun s : productIndices => word S (s.1.sort (· ≤ ·)))) ≤
      symmetricSpace 16 := by
    apply Submodule.span_le.mpr
    rintro M ⟨s, rfl⟩
    exact word_symmetric_014 S hS s.1 (productIndices_valid s)
  have dimension : Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun s : productIndices => word S (s.1.sort (· ≤ ·))))) = 136 := by
    rw [finrank_span_eq_card (words_independent S hS), Fintype.card_coe]
    exact productIndices_card
  apply Submodule.eq_of_le_of_finrank_le contained
  rw [dimension]
  exact symmetricSpace_finrank_le

lemma wordSign_sum (s : Finset (Fin 9)) :
    (∑ i : Fin 9, wordSign i (s.sort (· ≤ ·))) = (-1 : ℤ) ^ s.card * (9 - 2 * (s.card : ℤ)) := by
  let parity := (-1 : ℤ) ^ s.card
  have shape (i : Fin 9) : wordSign i (s.sort (· ≤ ·)) = parity - if i ∈ s then 2 * parity else 0 := by
    rw [wordSign_nodup i _ (Finset.sort_nodup _ _)]
    simp only [Finset.mem_sort, Finset.length_sort]
    by_cases member : i ∈ s <;> simp [member, parity] <;> ring
  have correction : (∑ i : Fin 9, if i ∈ s then 2 * parity else 0) = (s.card : ℤ) * (2 * parity) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_ite_mem_eq s (fun _ => 2 * parity)
  simp_rw [shape]
  rw [Finset.sum_sub_distrib, correction]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp only [parity]
  ring

lemma word_T_action {n : ℕ} (S : Fin 9 → Matrix (Fin n) (Fin n) ℝ) (hS : IsSymmCliffordSystem S)
    (s : Finset (Fin 9)) :
    ∑ i, S i * word S (s.sort (· ≤ ·)) * S i =
      ((-1 : ℝ) ^ s.card * (9 - 2 * (s.card : ℝ))) • word S (s.sort (· ≤ ·)) := by
  simp_rw [word_conjugate S hS]
  rw [← Finset.sum_smul, wordSign_sum, ← Int.cast_smul_eq_zsmul ℝ]
  push_cast
  rfl

theorem sec6_basis_136_proved (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) :
    let prod := fun s : Finset (Fin 9) => ((s.sort (· ≤ ·)).map S).prod
    let idx := (Finset.univ : Finset (Finset (Fin 9))).filter fun s => s.card = 0 ∨ s.card = 1 ∨ s.card = 4
    idx.card = 136 ∧ (∀ s ∈ idx, (prod s)ᵀ = prod s) ∧
      (∀ s ∈ idx, ∀ t ∈ idx, s ≠ t → (prod s * prod t).trace = 0) ∧
      LinearIndependent ℝ (fun s : ↥idx => prod s.1) ∧
      Submodule.span ℝ ((fun s => prod s) '' (idx : Set (Finset (Fin 9)))) =
        {M : Matrix (Fin 16) (Fin 16) ℝ | Mᵀ = M} ∧
      ∀ s ∈ idx, ∑ i, S i * prod s * S i = ((-1 : ℝ) ^ s.card * (9 - 2 * (s.card : ℝ))) • prod s := by
  dsimp only
  refine ⟨productIndices_card, ?_, ?_, words_independent S hS, ?_, ?_⟩
  · intro s member
    exact word_symmetric_014 S hS s (Finset.mem_filter.mp member).2
  · intro s hs t ht distinct
    exact word_pair_trace_zero S hS s t (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp ht).2 distinct
  · have ranges : ((fun s => word S (s.sort (· ≤ ·))) '' (productIndices : Set (Finset (Fin 9)))) =
        Set.range (fun s : productIndices => word S (s.1.sort (· ≤ ·))) := by
      ext M
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, hs⟩, rfl⟩
      · rintro ⟨s, rfl⟩
        exact ⟨s.1, s.2, rfl⟩
    change SetLike.coe (Submodule.span ℝ ((fun s => word S (s.sort (· ≤ ·))) ''
      (productIndices : Set (Finset (Fin 9))))) = {M : Matrix (Fin 16) (Fin 16) ℝ | Mᵀ = M}
    rw [ranges, words_span S hS]
    rfl
  · intro s _
    exact word_T_action S hS s

end Osserman.Proofs.CayleyProducts
