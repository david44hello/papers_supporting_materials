/-
NagataHigman/Proofs/Examples.lean — the worked examples of short paper v1.10 (steps (1), (6) of Proposition 2.1; Section 4.1).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Defs.WordCycle
import NagataHigman.Defs.FirstReturn
import NagataHigman.Defs.Spanning
import NagataHigman.Defs.Young
import NagataHigman.Proofs.Shapes
import NagataHigman.Proofs.Surfaced

noncomputable section

namespace NagataHigman.Proofs.Examples

open NagataHigman Equiv Finset NagataHigman.FirstReturn

variable (F : Type*) [Field F]

/-- The example `N`-cycle of step (6): `τ = Φ(x_0 x_1 x_2 x_3)`, i.e. `4 → 0 → 1 → 2 → 3 → 4`. -/
local notation "τ₅" => wordCycle (1 : Equiv.Perm (Fin 4))

/-- The second word `x_0 x_3 x_1 x_2` of step (6), as a permutation of `Fin 4`. -/
local notation "w₅" => (⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩ : Equiv.Perm (Fin 4))

/-! ## Step (1) -/

-- l. 320-322: Φ(x2x3x1) is the 4-cycle 4→2→3→1→4.
theorem ex_step1 :
    multilinWord F (finRotate 3) = letter F 1 * letter F 2 * letter F 0 ∧
      wordCycle (finRotate 3) 3 = 1 ∧ wordCycle (finRotate 3) 1 = 2 ∧ wordCycle (finRotate 3) 2 = 0 ∧
      wordCycle (finRotate 3) 0 = 3 :=
  ⟨rfl, by decide⟩

/-! ## Step (6): the first-return map and the arcs -/

theorem ex_step6_tau :
    (wordCycle (1 : Equiv.Perm (Fin 4))) 4 = 0 ∧ (wordCycle (1 : Equiv.Perm (Fin 4))) 0 = 1 ∧
      (wordCycle (1 : Equiv.Perm (Fin 4))) 1 = 2 ∧ (wordCycle (1 : Equiv.Perm (Fin 4))) 2 = 3 ∧
      (wordCycle (1 : Equiv.Perm (Fin 4))) 3 = 4 := by
  decide

/-- The return time is the `k` that returns to `X` first. -/
theorem returnTime_eq_of {N : ℕ} {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} {k : ℕ} (hk : 0 < k)
    (hmem : (τ ^ k) x ∈ X) (hmin : ∀ j, 0 < j → j < k → (τ ^ j) x ∉ X) : returnTime τ X x = k := by
  have hex : ∃ k, 0 < k ∧ (τ ^ k) x ∈ X := ⟨k, hk, hmem⟩
  obtain ⟨h0, h1⟩ := returnTime_spec hex
  refine le_antisymm ?_ ?_
  · by_contra hlt
    exact returnTime_min hex hk (by omega) hmem
  · by_contra hlt
    exact hmin _ h0 (by omega) h1

theorem returnTime_ex0 : returnTime τ₅ {0, 2, 3} 0 = 2 :=
  returnTime_eq_of (by norm_num) (by decide) fun j hj0 hj2 => by
    obtain rfl : j = 1 := by omega
    decide

theorem returnTime_ex2 : returnTime τ₅ {0, 2, 3} 2 = 1 :=
  returnTime_eq_of (by norm_num) (by decide) fun j hj0 hj1 => by omega

theorem returnTime_ex3 : returnTime τ₅ {0, 2, 3} 3 = 2 :=
  returnTime_eq_of (by norm_num) (by decide) fun j hj0 hj2 => by
    obtain rfl : j = 1 := by omega
    decide

theorem firstReturn_apply_of_mem {N : ℕ} {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} {k : ℕ}
    (hx : x ∈ X) (hk : returnTime τ X x = k) : firstReturn τ X x = (τ ^ k) x := by
  show firstReturnFun τ X x = _
  rw [firstReturnFun, ite_eq_left hx, hk]

theorem firstReturn_apply_of_not_mem {N : ℕ} {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N}
    (hx : x ∉ X) : firstReturn τ X x = x := by
  show firstReturnFun τ X x = _
  rw [firstReturnFun, ite_eq_right hx]

-- l. 343: τ̄ = (1 3 4) (Lean: 0 → 2 → 3 → 0).
theorem ex_step6_return :
    firstReturn (wordCycle (1 : Equiv.Perm (Fin 4))) {0, 2, 3} = List.formPerm [0, 2, 3] := by
  ext x : 1
  obtain rfl | rfl | rfl | rfl | rfl : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by revert x; decide
  · rw [firstReturn_apply_of_mem (by decide) returnTime_ex0]; decide
  · rw [firstReturn_apply_of_not_mem (by decide)]; decide
  · rw [firstReturn_apply_of_mem (by decide) returnTime_ex2]; decide
  · rw [firstReturn_apply_of_mem (by decide) returnTime_ex3]; decide
  · rw [firstReturn_apply_of_not_mem (by decide)]; decide

-- l. 343: the arcs (2,3), (4) and Arc_0 = (5,1).
theorem ex_step6_arcs :
    arc (wordCycle (1 : Equiv.Perm (Fin 4))) {0, 2, 3} 0 = [1, 2] ∧
      arc (wordCycle (1 : Equiv.Perm (Fin 4))) {0, 2, 3} 2 = [3] ∧
      arc (wordCycle (1 : Equiv.Perm (Fin 4))) {0, 2, 3} 3 = [4, 0] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [arc, returnTime_ex0]; decide
  · rw [arc, returnTime_ex2]; decide
  · rw [arc, returnTime_ex3]; decide

/-! ## Step (6): the set `Π` -/

/-- On `Fin 5`, a full cycle is a permutation whose orbit of `0` (exponents `0, …, 4`) is everything. -/
theorem isFullCycle_five_iff (σ : Perm (Fin 5)) :
    IsFullCycle σ ↔ ∀ y : Fin 5, ∃ k : Fin 5, (σ ^ (k : ℕ)) 0 = y := by
  constructor
  · intro h y
    have hmove : ∀ z, σ z ≠ z := fun z => by rw [← Perm.mem_support, h.2]; exact mem_univ z
    obtain ⟨i, hi, hiy⟩ := (h.1.sameCycle (hmove 0) (hmove y)).exists_pow_eq'
    rw [h.1.orderOf, h.2, card_univ, Fintype.card_fin] at hi
    exact ⟨⟨i, hi⟩, hiy⟩
  · intro h
    have hmove : ∀ z, σ z ≠ z := by
      intro z hz
      obtain ⟨k, hk⟩ := h z
      have h0 : σ 0 = 0 := by
        apply (σ ^ (k : ℕ)).injective
        rw [← Perm.mul_apply, ← pow_succ, pow_succ', Perm.mul_apply, hk, hz]
      obtain ⟨j, hj⟩ := h 1
      rw [Perm.pow_apply_eq_self_of_apply_eq_self h0] at hj
      exact absurd hj (by decide)
    refine ⟨⟨0, hmove 0, fun y _ => ?_⟩, ?_⟩
    · obtain ⟨k, hk⟩ := h y
      exact ⟨(k : ℕ), by rw [zpow_natCast]; exact hk⟩
    · ext z
      simp only [Perm.mem_support, mem_univ, iff_true]
      exact hmove z

/-- Membership in `Π`, pointwise. -/
theorem mem_Pi_iff (π : Perm (Fin 5)) :
    (π.support ⊆ {0, 2, 3} ∧ IsFullCycle (wordCycle (1 : Equiv.Perm (Fin 4)) * π)) ↔
      (π = 1 ∨ π = List.formPerm [0, 2, 3]) := by
  rw [isFullCycle_five_iff]
  revert π
  decide +kernel

open Classical in
-- l. 372: Π = {1, τ̄}.
theorem ex_step6_Pi :
    Finset.univ.filter (fun π : Equiv.Perm (Fin 5) =>
        π.support ⊆ {0, 2, 3} ∧ IsFullCycle (wordCycle (1 : Equiv.Perm (Fin 4)) * π)) =
      {1, firstReturn (wordCycle (1 : Equiv.Perm (Fin 4))) {0, 2, 3}} := by
  rw [ex_step6_return]
  ext π
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  exact mem_Pi_iff π

/-! ## Step (6): the sum `P(τ E_K)` -/

theorem perm_mul_perm' {N : ℕ} (σ τ : Perm (Fin N)) : perm F σ * perm F τ = perm F (σ * τ) := by
  simp [perm, MonoidAlgebra.single_mul_single]

open Classical in
theorem cycleProj_perm {N : ℕ} (σ : Perm (Fin N)) :
    cycleProj F N (perm F σ) = if IsFullCycle σ then perm F σ else 0 := by
  show ∑ ρ ∈ univ.filter (fun ρ : Perm (Fin N) => IsFullCycle ρ), (perm F σ).coeff ρ • perm F ρ = _
  simp only [perm, MonoidAlgebra.coeff_single, Finsupp.single_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq]
  simp [mem_filter]

theorem perm_mul_altSum_eq {N : ℕ} (τ : Perm (Fin N)) (X : Finset (Fin N)) :
    perm F τ * altSum F X =
      ∑ π ∈ univ.filter (fun π : Perm (Fin N) => π.support ⊆ X), ((Perm.sign π : ℤ) : F) • perm F (τ * π) := by
  unfold altSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [mul_smul_comm, perm_mul_perm']

-- l. 372: Φ⁻¹P(τE_K) = x1x2x3x4 + x1x4x2x3, i.e. P(τE_K) = τ + Φ(x1x4x2x3).
theorem ex_step6_sum :
    cycleProj F 5 (perm F (wordCycle (1 : Equiv.Perm (Fin 4))) * altSum F {0, 2, 3}) =
      perm F (wordCycle (1 : Equiv.Perm (Fin 4))) +
        perm F (wordCycle (⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩ : Equiv.Perm (Fin 4))) := by
  classical
  rw [perm_mul_altSum_eq, map_sum]
  simp only [map_smul, cycleProj_perm, smul_ite, smul_zero]
  rw [← Finset.sum_filter, Finset.filter_filter]
  have hset : univ.filter (fun π : Perm (Fin 5) => π.support ⊆ {0, 2, 3} ∧ IsFullCycle (τ₅ * π)) =
      {1, List.formPerm [0, 2, 3]} := by
    ext π
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    exact mem_Pi_iff π
  rw [hset, Finset.sum_pair (by decide)]
  have hsign : Perm.sign (List.formPerm ([0, 2, 3] : List (Fin 5))) = 1 := by decide
  have hmul : τ₅ * List.formPerm [0, 2, 3] = wordCycle w₅ := by decide
  rw [Perm.sign_one, hsign, mul_one, hmul]
  simp

/-! ## Step (6): the word side -/

theorem symSum_two {R : Type*} [NonUnitalRing R] (y : Fin 2 → R) : symSum 2 y = y 0 * y 1 + y 1 * y 0 := by
  unfold symSum
  rw [show (Finset.univ : Finset (Perm (Fin 2))) = {1, swap 0 1} by decide, Finset.sum_pair (by decide)]
  rfl

-- l. 372: x1x2x3x4 + x1x4x2x3 = x1 · L(x2x3, x4).
theorem ex_step6_word :
    multilinWord F (1 : Equiv.Perm (Fin 4)) +
        multilinWord F (⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩ : Equiv.Perm (Fin 4)) =
      sandwichElem F [0] ![[1, 2], [3]] [] := by
  have h1 : multilinWord F (1 : Perm (Fin 4)) = letter F 0 * letter F 1 * letter F 2 * letter F 3 := rfl
  have h2 : multilinWord F w₅ = letter F 0 * letter F 3 * letter F 1 * letter F 2 := rfl
  have h3 : sandwichElem F [0] ![[1, 2], [3]] [] =
      letter F 0 * (letter F 1 * letter F 2 * letter F 3 + letter F 3 * (letter F 1 * letter F 2)) := by
    simp only [sandwichElem, sandwich, symSum_two]
    rfl
  rw [h1, h2, h3]
  simp only [mul_add, mul_assoc]

/-! ## Section 4.1: `ν` for `n = 3` -/

-- l. 446-448 and l. 602: ν = (3,3,2), its cells, its two corners, and h(ν) = (5,3).
theorem ex_nu_three (lam : Shape 8) (h : lam.InBox 3) :
    lam.parts = {3, 3, 2} ∧
      (∀ i j : ℕ, (i, j) ∈ lam.diagram ↔ (i, j) ∈ ({(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1)} :
        Finset (ℕ × ℕ))) ∧
      (∀ T : SYT lam, (T.pos 7 = (1, 2) ∧ T.content 7 = 1) ∨ (T.pos 7 = (2, 1) ∧ T.content 7 = -1)) ∧
      lam.diagonalHooks = {5, 3} := by
  have hparts := sec_4_1_nu_proved 3 (by norm_num) lam h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hparts]; decide
  · intro i j
    rw [mem_nu_iff 3 (by norm_num) lam hparts]
    simp only [mem_insert, mem_singleton, Prod.mk.injEq]
    omega
  · intro T
    have := nu_top_corner 3 (by norm_num) lam h T (7 : Fin 8) (by norm_num)
    simpa using this
  · rw [thm_4_4_hooks_proved 3 (by norm_num) lam h]
    decide

end NagataHigman.Proofs.Examples

end
