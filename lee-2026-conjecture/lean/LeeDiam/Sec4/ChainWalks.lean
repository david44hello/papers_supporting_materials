/-
LeeDiam/Sec4/ChainWalks.lean — Section 4: the walk statement of Theorem 4.1 (sec_chain.tex v1.50 l. 165-182): every
split of an antichain of `B_k` has a walk of length at most `g(k) = ⌊3(k+1)/4⌋`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

Induction on `k`. A word without empty columns: Proposition 4.13 (`overview_fullword`; for `k = 1` one move). An
empty column `e`: the columns `< e` and `> e` are translated copies of `B_e` and `B_{k-e-1}` (`shift_walk`), their walks
are performed one after the other (`walk_sequential`), and `g(e) + g(k-e-1) ≤ g(k)` (Lemma 4.14 (i)).
-/
import LeeDiam.Defs.Chain
import LeeDiam.Sec4.FullWord

namespace LeeDiam.S4

open Band

section ChainWalks

/-- A walk bound on `B_n` transfers to the antichains of `B_K` that lie in the columns `d, …, d + n - 1`. -/
theorem shift_walk {n K d : ℕ} (hd : n + d ≤ K) {g : ℕ}
    (hP : ∀ U' A' B' : Set (Band n), IsSplit A' B' U' → ∃ W', IsWalkFromTo W' A' B' ∧ W'.length - 1 ≤ g)
    {U A B : Set (Band K)} (hAB : IsSplit A B U) (hU : ∀ x ∈ U, d ≤ x.1.val ∧ x.1.val < d + n) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 ≤ g ∧ ∀ X ∈ W, ∀ x ∈ X, d ≤ x.1.val ∧ x.1.val < d + n := by
  set f : Band n → Band K := colShift d hd with hf
  have himg : ∀ C ⊆ U, f '' (f ⁻¹' C) = C := fun C hC => by
    apply Set.image_preimage_eq_of_subset
    intro x hx
    obtain ⟨h1, h2⟩ := hU x (hC hx)
    exact ⟨((⟨x.1.val - d, by omega⟩ : Fin n), x.2),
      Prod.ext (Fin.ext (by show x.1.val - d + d = x.1.val; omega)) rfl⟩
  have hAU : A ⊆ U := fun x hx => hAB.2.1 ▸ Or.inl hx
  have hBU : B ⊆ U := fun x hx => hAB.2.1 ▸ Or.inr hx
  have hanti : IsAntichainSet (f ⁻¹' U) := by
    rw [(translation d hd).2.1, himg U subset_rfl]
    exact hAB.2.2
  have hsplit : IsSplit (f ⁻¹' A) (f ⁻¹' B) (f ⁻¹' U) :=
    ⟨hAB.1.preimage f, by rw [← Set.preimage_union, hAB.2.1], hanti⟩
  obtain ⟨W', hW', hlen⟩ := hP _ _ _ hsplit
  refine ⟨W'.map (f '' ·), ⟨(translation d hd).2.2.2 W' hW'.1, ?_, ?_⟩, by rw [List.length_map]; exact hlen, ?_⟩
  · rw [List.head?_map, hW'.2.1, Option.map_some, himg A hAU]
  · rw [List.getLast?_map, hW'.2.2, Option.map_some, himg B hBU]
  · intro X hX x hx
    obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hX
    obtain ⟨y, -, rfl⟩ := hx
    have := y.1.isLt
    show d ≤ y.1.val + d ∧ y.1.val + d < d + n
    omega

/-- The one-move walk `(A, B)` when `A ∪ B` is connected. -/
theorem walk_two {k : ℕ} {A B U : Set (Band k)} (hAB : IsSplit A B U) (hU : IsConnSet U) :
    IsWalkFromTo [A, B] A B := by
  have hAU : A ⊆ U := fun x hx => hAB.2.1 ▸ Or.inl hx
  have hBU : B ⊆ U := fun x hx => hAB.2.1 ▸ Or.inr hx
  refine ⟨⟨by simp, ?_, ?_⟩, rfl, rfl⟩
  · intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl
    · exact hAB.2.2.subset hAU
    · exact hAB.2.2.subset hBU
  · rw [List.isChain_cons_cons]
    refine ⟨?_, List.isChain_singleton _⟩
    rw [symmDiff_of_disjoint hAB.1, hAB.2.1]
    exact hU

/-- Theorem 4.1, the walk statement: every split of an antichain of `B_k` has a walk of length at most
`⌊3(k+1)/4⌋`. -/
theorem chain_walks (k : ℕ) : ∀ U A B : Set (Band k), IsSplit A B U →
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 ≤ 3 * (k + 1) / 4 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U A B hAB
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · -- `B_0` is empty
    subst hk0
    have hA : A = ∅ := by ext x; exact x.1.elim0
    have hB : B = ∅ := by ext x; exact x.1.elim0
    subst hA hB
    exact ⟨[∅], ⟨⟨by simp, by simp [isAntichainSet_row 0 (∅ : Set (Band 0)) (by simp)],
      List.isChain_singleton _⟩, rfl, rfl⟩, by simp⟩
  by_cases hfull : ∀ l : Fin k, ∃ x ∈ U, x.1 = l
  · rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · -- `k = 1`: `U` is one element
      obtain ⟨u, hu, -⟩ := hfull ⟨0, hk1⟩
      have hUu : U = {u} := by
        ext x
        constructor
        · intro hx
          have h1 := x.1.isLt
          have h2 := u.1.isLt
          exact Set.mem_singleton_iff.2 (antichain_col hAB.2.2 hx hu (Fin.ext (by omega)))
        · intro hx
          rw [Set.mem_singleton_iff.1 hx]
          exact hu
      refine ⟨[A, B], walk_two hAB (hUu ▸ isConnSet_singleton u), ?_⟩
      simp only [List.length_cons, List.length_nil]
      omega
    · obtain ⟨W, hW, hlen⟩ := overview_fullword hk2 U hAB.2.2 hfull A B hAB
      exact ⟨W, hW, by omega⟩
  · obtain ⟨e, he⟩ : ∃ e : Fin k, ∀ x ∈ U, x.1 ≠ e := by
      by_contra hne
      apply hfull
      intro l
      by_contra hl
      exact hne ⟨l, fun x hx hxl => hl ⟨x, hx, hxl⟩⟩
    set V₁ : Set (Band k) := U ∩ {x | x.1.val < e.val} with hV₁
    set V₂ : Set (Band k) := U ∩ {x | e.val < x.1.val} with hV₂
    have hUV : ∀ x, x ∈ U ↔ x ∈ V₁ ∨ x ∈ V₂ := fun x => by
      constructor
      · intro hx
        have hne : x.1.val ≠ e.val := fun h => he x hx (Fin.ext h)
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro (h | h)
        · exact h.1
        · exact h.1
    obtain ⟨hs1, hs2, hrA, hrB⟩ := split_parts hAB hUV
    have he1 := e.isLt
    obtain ⟨W₁, hW₁, hlen₁, hcols₁⟩ := shift_walk (n := e.val) (d := 0) (by omega) (ih e.val e.isLt) hs1
      (fun x hx => ⟨Nat.zero_le _, by have h' : x.1.val < e.val := hx.2; show x.1.val < 0 + e.val; omega⟩)
    obtain ⟨W₂, hW₂, hlen₂, hcols₂⟩ := shift_walk (n := k - e.val - 1) (d := e.val + 1) (by omega)
      (ih (k - e.val - 1) (by omega)) hs2
      (fun x hx => ⟨by have h' : e.val < x.1.val := hx.2; show e.val + 1 ≤ x.1.val; omega,
        by have := x.1.isLt; omega⟩)
    obtain ⟨hW, hlen⟩ := walk_sequential W₁ W₂ _ _ _ _ hW₁ hW₂ (fun X hX Y hY x hx y hy => by
      have := (hcols₁ X hX x hx).2
      have := (hcols₂ Y hY y hy).1
      omega)
    rw [hrA, hrB] at hW
    refine ⟨_, hW, ?_⟩
    rw [hlen]
    have : k - e.val - 1 + 1 = k - e.val := by omega
    rw [this] at hlen₂
    omega

end ChainWalks

end LeeDiam.S4

