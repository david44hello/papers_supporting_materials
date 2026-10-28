/-
Osserman/Proofs/Hopf.lean — the expansion of xxᵀ in the 136-basis and (eq:HopfM) for a symmetric Clifford system of
nine matrices on ℝ^16 (paper 013, §6, l. 627-634): `sec6_xxT_expansion`, `sec6_hopf`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.CayleyProducts
import Osserman.Proofs.Cayley

namespace Osserman.Proofs.Hopf

open Osserman Matrix Osserman.Proofs.CayleyProducts Osserman.Proofs.Cayley

def fourIndices : Finset (Finset (Fin 9)) := Finset.univ.filter fun s => s.card = 4

lemma productIndices_split {A : Type*} [AddCommMonoid A] (f : Finset (Fin 9) → A) :
    ∑ s ∈ productIndices, f s = f ∅ + (∑ i : Fin 9, f {i}) + ∑ s ∈ fourIndices, f s := by
  let singles : Finset (Finset (Fin 9)) := Finset.univ.image (fun i : Fin 9 => {i})
  have single_card (s : Finset (Fin 9)) : s ∈ singles ↔ s.card = 1 := by
    simp only [singles, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, equal⟩ => by rw [← equal]; simp,
      fun card => by obtain ⟨i, equal⟩ := Finset.card_eq_one.mp card; exact ⟨i, equal.symm⟩⟩
  have split : productIndices = ({∅} ∪ singles) ∪ fourIndices := by
    ext s
    simp only [productIndices, fourIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_singleton, single_card]
    rw [Finset.card_eq_zero]
    tauto
  have disjoint01 : Disjoint ({∅} : Finset (Finset (Fin 9))) singles := by
    apply Finset.disjoint_left.mpr
    intro s hs ht
    have empty := Finset.mem_singleton.mp hs
    have card := (single_card s).mp ht
    subst s
    simp at card
  have disjoint4 : Disjoint (({∅} : Finset (Finset (Fin 9))) ∪ singles) fourIndices := by
    apply Finset.disjoint_left.mpr
    intro s hs ht
    have card4 := (Finset.mem_filter.mp ht).2
    rcases Finset.mem_union.mp hs with empty | one
    · have equal := Finset.mem_singleton.mp empty
      subst s
      simp at card4
    · have card1 := (single_card s).mp one
      omega
  rw [split, Finset.sum_union disjoint4, Finset.sum_union disjoint01, Finset.sum_singleton]
  have singles_sum : ∑ s ∈ singles, f s = ∑ i : Fin 9, f {i} := by
    dsimp only [singles]
    rw [Finset.sum_image]
    intro i _ j _ equal
    exact Finset.singleton_injective equal
  rw [singles_sum]

lemma symmetric_expansion (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S)
    (M : Matrix (Fin 16) (Fin 16) ℝ) (hsym : Mᵀ = M) :
    M = ∑ s : productIndices, ((M * word S (s.1.sort (· ≤ ·))).trace / 16) • word S (s.1.sort (· ≤ ·)) := by
  have member : M ∈ Submodule.span ℝ (Set.range (fun s : productIndices => word S (s.1.sort (· ≤ ·)))) := by
    rw [words_span S hS]
    exact hsym
  obtain ⟨coefficients, expansion⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp member
  have coefficient (t : productIndices) : coefficients t = (M * word S (t.1.sort (· ≤ ·))).trace / 16 := by
    have traced := congrArg (fun N : Matrix (Fin 16) (Fin 16) ℝ => (N * word S (t.1.sort (· ≤ ·))).trace) expansion
    rw [Matrix.sum_mul, Matrix.trace_sum] at traced
    simp only [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul] at traced
    have equal : coefficients t * 16 = (M * word S (t.1.sort (· ≤ ·))).trace := by
      simpa [word_trace_pair S hS] using traced
    linarith
  calc
    M = ∑ s, coefficients s • word S (s.1.sort (· ≤ ·)) := expansion.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [coefficient]

lemma trace_outer_mul (x : Vec 16) (M : Matrix (Fin 16) (Fin 16) ℝ) :
    (vecMulVec x x * M).trace = x ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem sec6_xxT_expansion_proved (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) (x : Vec 16) :
    let prod := fun s : Finset (Fin 9) => ((s.sort (· ≤ ·)).map S).prod
    ∃ c : Finset (Fin 9) → ℝ, vecMulVec x x = (1 / 16 : ℝ) • ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) +
      ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i) + ∑ s ∈ (Finset.univ.filter fun s : Finset (Fin 9) => s.card = 4), c s • prod s := by
  dsimp only
  let c := fun s : Finset (Fin 9) => (vecMulVec x x * word S (s.sort (· ≤ ·))).trace / 16
  refine ⟨c, ?_⟩
  have expansion := symmetric_expansion S hS (vecMulVec x x) (by ext i j; simp [Matrix.vecMulVec_apply, mul_comm])
  have expanded : vecMulVec x x = ∑ s ∈ productIndices, c s • word S (s.sort (· ≤ ·)) := by
    rw [← Finset.sum_coe_sort]
    exact expansion
  have empty : c ∅ = (x ⬝ᵥ x) / 16 := by simp [c, word, Matrix.trace_vecMulVec]
  have single (i : Fin 9) : c {i} = (x ⬝ᵥ (S i *ᵥ x)) / 16 := by
    simp only [c, word, Finset.sort_singleton, List.map_singleton, List.prod_singleton, trace_outer_mul]
  rw [productIndices_split] at expanded
  simp only [empty, single, word, Finset.sort_empty, List.map_nil, List.prod_nil,
    Finset.sort_singleton, List.map_singleton, List.prod_singleton] at expanded
  rw [expanded]
  congr 1
  simp only [smul_add, Finset.smul_sum, smul_smul]
  congr 1
  · congr 1
    ring
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring

def conjugationOperator (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) :
    Matrix (Fin 16) (Fin 16) ℝ →ₗ[ℝ] Matrix (Fin 16) (Fin 16) ℝ where
  toFun M := ∑ i, S i * M * S i
  map_add' := by intro A B; simp only [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' := by intro c M; simp only [mul_smul_comm, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

lemma conjugation_one (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) :
    conjugationOperator S 1 = (9 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  change (∑ i, S i * 1 * S i) = _
  simp only [mul_one, system_square S hS, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_cast

lemma conjugation_generator (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) (j : Fin 9) :
    conjugationOperator S (S j) = (-7 : ℝ) • S j := by
  have action := word_T_action S hS {j}
  norm_num [word, conjugationOperator] at action ⊢
  exact action

lemma conjugation_four (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S)
    (s : Finset (Fin 9)) (hs : s.card = 4) :
    conjugationOperator S (word S (s.sort (· ≤ ·))) = word S (s.sort (· ≤ ·)) := by
  have action := word_T_action S hS s
  norm_num [hs, conjugationOperator] at action ⊢
  exact action

theorem sec6_hopf_proved (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) (x : Vec 16) :
    ∑ i, vecMulVec (S i *ᵥ x) (S i *ᵥ x) = vecMulVec x x + (1 / 2 : ℝ) •
        ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i) ∧
      ∑ i, (x ⬝ᵥ (S i *ᵥ x)) ^ 2 = (x ⬝ᵥ x) ^ 2 := by
  obtain ⟨c, expansion⟩ := sec6_xxT_expansion_proved S hS x
  change vecMulVec x x = (1 / 16 : ℝ) • ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) +
    ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i) + ∑ s ∈ fourIndices, c s • word S (s.sort (· ≤ ·)) at expansion
  have conjugated := congrArg (conjugationOperator S) expansion
  have four_fixed : conjugationOperator S (∑ s ∈ fourIndices, c s • word S (s.sort (· ≤ ·))) =
      ∑ s ∈ fourIndices, c s • word S (s.sort (· ≤ ·)) := by
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro s hs
    rw [conjugation_four S hS s (Finset.mem_filter.mp hs).2]
  have outer_image : conjugationOperator S (vecMulVec x x) =
      ∑ i, vecMulVec (S i *ᵥ x) (S i *ᵥ x) := by
    change (∑ i, S i * vecMulVec x x * S i) = _
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose, hS.1 i]
  change conjugationOperator S (vecMulVec x x) = conjugationOperator S
    ((1 / 16 : ℝ) • ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) +
      ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i) + ∑ s ∈ fourIndices, c s • word S (s.sort (· ≤ ·))) at conjugated
  rw [map_add, four_fixed, map_smul, map_add, map_smul, conjugation_one S hS, outer_image] at conjugated
  simp only [map_sum, map_smul, conjugation_generator S hS] at conjugated
  have scale_sum : (∑ i, (x ⬝ᵥ (S i *ᵥ x)) • (-7 : ℝ) • S i) =
      (-7 : ℝ) • ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  rw [scale_sum] at conjugated
  have identity : ∑ i, vecMulVec (S i *ᵥ x) (S i *ᵥ x) = vecMulVec x x + (1 / 2 : ℝ) •
      ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i) := by
    rw [conjugated, expansion]
    module
  refine ⟨identity, ?_⟩
  have contraction := sec6_hopf_contraction_proved S hS x
  have dotted := congrArg (fun M : Matrix (Fin 16) (Fin 16) ℝ => x ⬝ᵥ (M *ᵥ x)) identity
  rw [contraction.1, contraction.2] at dotted
  linarith

end Osserman.Proofs.Hopf
