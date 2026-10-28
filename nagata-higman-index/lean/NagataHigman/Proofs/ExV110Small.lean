/-
NagataHigman/Proofs/ExV110Small.lean — two small worked examples that are new in short paper v1.10 of project 011
(Nagata–Higman index; FINAL tex md5 23b0bd3e): N8 (v1.10 l. 369-372, Proposition 2.1, step (6)) and N13 (v1.10 l. 576-578,
Lemma 4.2(d)). Proofs in
`NagataHigman.Proofs.ExV110Small`, statements in `NagataHigman.Paper`. Lean is 0-indexed (paper: 1-indexed).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Proofs.ExV110

noncomputable section

namespace NagataHigman.Proofs.ExV110Small

open NagataHigman Equiv Finset NagataHigman.FirstReturn

/-! ## N8: Proposition 2.1, step (6), example (`τ = (4 0 1 2 3)`, `K = {0, 2, 3}`, `τ̄ = (0 2 3)`) -/

/-- On `Fin 5`, a permutation supported in `{0, 2, 3}` that moves `0`, `2` and `3` is `(0 2 3)` or `(0 3 2)`. -/
theorem moves_K_iff (θ : Perm (Fin 5)) :
    (θ.support ⊆ {0, 2, 3} ∧ θ 0 ≠ 0 ∧ θ 2 ≠ 2 ∧ θ 3 ≠ 3) ↔
      (θ = List.formPerm [0, 2, 3] ∨ θ = List.formPerm [0, 3, 2]) := by
  revert θ
  decide +kernel

theorem sq_formPerm_K : (List.formPerm ([0, 2, 3] : List (Fin 5))) ^ 2 = List.formPerm [0, 3, 2] := by
  decide

theorem support_formPerm_K : (List.formPerm ([0, 2, 3] : List (Fin 5))).support ⊆ {0, 2, 3} := by
  decide

theorem support_one_K : (1 : Perm (Fin 5)).support ⊆ {0, 2, 3} := by
  decide

/-- `{a | a ∈ l}` is `K` for both orders of the `3`-cycle. -/
theorem setOf_mem_K (l : List (Fin 5)) (hl : l = [0, 2, 3] ∨ l = [0, 3, 2]) :
    {a | a ∈ l} = ((({0, 2, 3} : Finset (Fin 5))) : Set (Fin 5)) := by
  ext x
  rcases hl with rfl | rfl
  · simp
  · simp
    tauto

/-- The `3`-cycles on `K` (permutations supported in `K` that are cyclic on `K`) are exactly `τ̄` and `τ̄²`. -/
theorem threeCycles_K (θ : Perm (Fin 5)) :
    (θ.support ⊆ {0, 2, 3} ∧ θ.IsCycleOn ((({0, 2, 3} : Finset (Fin 5))) : Set (Fin 5))) ↔
      (θ = List.formPerm [0, 2, 3] ∨ θ = List.formPerm [0, 2, 3] ^ 2) := by
  have hK : ((({0, 2, 3} : Finset (Fin 5))) : Set (Fin 5)).Nontrivial := ⟨0, by simp, 2, by simp, by decide⟩
  rw [sq_formPerm_K]
  constructor
  · rintro ⟨hs, hc⟩
    exact (moves_K_iff θ).1 ⟨hs, hc.apply_ne hK (by simp), hc.apply_ne hK (by simp), hc.apply_ne hK (by simp)⟩
  · intro h
    refine ⟨((moves_K_iff θ).2 h).1, ?_⟩
    rcases h with rfl | rfl
    · rw [← setOf_mem_K [0, 2, 3] (Or.inl rfl)]
      exact (show ([0, 2, 3] : List (Fin 5)).Nodup by decide).isCycleOn_formPerm
    · rw [← setOf_mem_K [0, 3, 2] (Or.inr rfl)]
      exact (show ([0, 3, 2] : List (Fin 5)).Nodup by decide).isCycleOn_formPerm

open Classical in
/-- `Π = {π ∈ Sym(K) : τ̄π is a 3-cycle on K} = {1, τ̄}`: `τ̄π` is `τ̄` or `τ̄²`. -/
theorem Pi_bar_K :
    Finset.univ.filter (fun π : Perm (Fin 5) => π.support ⊆ {0, 2, 3} ∧
        (List.formPerm [0, 2, 3] * π).IsCycleOn ((({0, 2, 3} : Finset (Fin 5))) : Set (Fin 5))) =
      {1, List.formPerm [0, 2, 3]} := by
  ext π
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hπ, hc⟩
    have hs : (List.formPerm [0, 2, 3] * π).support ⊆ {0, 2, 3} :=
      (Perm.support_mul_le _ _).trans (sup_le support_formPerm_K hπ)
    rcases (threeCycles_K _).1 ⟨hs, hc⟩ with h | h
    · exact Or.inl (mul_left_cancel (h.trans (mul_one _).symm))
    · rw [pow_two] at h
      exact Or.inr (mul_left_cancel h)
  · rintro (rfl | rfl)
    · refine ⟨support_one_K, ?_⟩
      rw [mul_one]
      exact ((threeCycles_K _).2 (Or.inl rfl)).2
    · refine ⟨support_formPerm_K, ?_⟩
      rw [← pow_two]
      exact ((threeCycles_K _).2 (Or.inr rfl)).2

open Classical in
/-- N8 (v1.10 l. 369-372), with `τ̄` the first-return map of `τ` to `K`: the `3`-cycles on `K` are `τ̄`, `τ̄²`;
`Π = {1, τ̄}`; and `ττ̄ = (4 0 3 1 2) = Φ(x_0 x_3 x_1 x_2)`. -/
theorem ex_step6_bar :
    (∀ θ : Perm (Fin 5), (θ.support ⊆ {0, 2, 3} ∧ θ.IsCycleOn ((({0, 2, 3} : Finset (Fin 5))) : Set (Fin 5))) ↔
        (θ = firstReturn (wordCycle (1 : Perm (Fin 4))) {0, 2, 3} ∨
          θ = firstReturn (wordCycle (1 : Perm (Fin 4))) {0, 2, 3} ^ 2)) ∧
    Finset.univ.filter (fun π : Perm (Fin 5) => π.support ⊆ {0, 2, 3} ∧
        (firstReturn (wordCycle (1 : Perm (Fin 4))) {0, 2, 3} * π).IsCycleOn
          ((({0, 2, 3} : Finset (Fin 5))) : Set (Fin 5))) =
      {1, firstReturn (wordCycle (1 : Perm (Fin 4))) {0, 2, 3}} ∧
    wordCycle (1 : Perm (Fin 4)) * firstReturn (wordCycle (1 : Perm (Fin 4))) {0, 2, 3} =
      List.formPerm [4, 0, 3, 1, 2] ∧
    wordCycle (1 : Perm (Fin 4)) * firstReturn (wordCycle (1 : Perm (Fin 4))) {0, 2, 3} =
      wordCycle (⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩ : Perm (Fin 4)) := by
  rw [NagataHigman.Proofs.Examples.ex_step6_return]
  exact ⟨threeCycles_K, Pi_bar_K, by decide, by decide⟩

/-! ## N13: Lemma 4.2(d), example (`n = 3`, `ν = (3, 3, 2)`, `N = 8`) -/

/-- The cells of `ν = (3, 3, 2)` (0-indexed). -/
abbrev nuCells : Finset (ℕ × ℕ) := {(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1)}

/-- In `ν = (3, 3, 2)`: a cell other than `(1, 2)` whose lower and right neighbours, when they are cells, are `(1, 2)`
is `(0, 2)` or `(2, 1)`. -/
theorem nu_second_cells (a b : ℕ) (hmem : (a, b) ∈ nuCells) (hne : (a, b) ≠ (1, 2))
    (hdown : (a + 1, b) ∈ nuCells → (a + 1, b) = (1, 2)) (hright : (a, b + 1) ∈ nuCells → (a, b + 1) = (1, 2)) :
    (a, b) = (0, 2) ∨ (a, b) = (2, 1) := by
  simp only [nuCells, mem_insert, mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact absurd rfl hne
    | exact absurd (hright (by decide)) (by decide)
    | exact absurd (hdown (by decide)) (by decide)

/-- N13 (v1.10 l. 576-578): for `ν = (3, 3, 2)`, if the largest entry `7` is at `a₊ = (1, 2)`, then `6` is at
`(0, 2)` (content `2`) or at `a₋ = (2, 1)` (content `-1`), and `c_T(6)(c_T(7) - c_T(6)) = -2`. -/
theorem ex_lem_4_2_d (lam : Shape 8) (h : lam.InBox 3) (T : SYT lam) (h7 : T.pos 7 = (1, 2)) :
    ((T.pos 6 = (0, 2) ∧ T.content 6 = 2) ∨ (T.pos 6 = (2, 1) ∧ T.content 6 = -1)) ∧
      T.content 6 * (T.content 7 - T.content 6) = -2 := by
  have hcells : ∀ c : ℕ × ℕ, c ∈ lam.diagram.cells ↔ c ∈ nuCells := fun c => by
    rw [YoungDiagram.mem_cells]
    exact (NagataHigman.Proofs.Examples.ex_nu_three lam h).2.1 c.1 c.2
  obtain ⟨hne, hdown, hright⟩ := NagataHigman.Proofs.second_corner T 7 6 (by decide) (by decide)
  rw [h7] at hne hdown hright
  have hc7 : T.content 7 = 1 := by norm_num [SYT.content, h7]
  rcases nu_second_cells (T.pos 6).1 (T.pos 6).2 ((hcells _).1 (T.pos_mem 6)) hne
      (fun hm => hdown ((hcells _).2 hm)) (fun hm => hright ((hcells _).2 hm)) with hp | hp
  · have hp' : T.pos 6 = (0, 2) := hp
    have hc6 : T.content 6 = 2 := by norm_num [SYT.content, hp']
    exact ⟨Or.inl ⟨hp', hc6⟩, by norm_num [hc6, hc7]⟩
  · have hp' : T.pos 6 = (2, 1) := hp
    have hc6 : T.content 6 = -1 := by norm_num [SYT.content, hp']
    exact ⟨Or.inr ⟨hp', hc6⟩, by norm_num [hc6, hc7]⟩

end NagataHigman.Proofs.ExV110Small

end
