/-
LeeDiam/Sec4/Lem411Step.lean — the step of the paper's proof of Lemma 4.11 (Junction, sec_chain.tex v1.50 l. 133-135)
that the Lean route for `lem_4_11` does not use: the paper's comb walk `Q`, its first phase ordered so that `K` comes
last; "the element a_{i+1} is present exactly before K, and c_i is absent then".
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

Lean columns are 0-based: the paper's `a_{i+1}` is `a ⟨i, _⟩`, `c_i` is `c ⟨i - 1, _⟩`, the segment `{a_{i+1}, …, a_L}`
is `rowSeg 0 i (i + j - 1)`, the even helper positions `i + 2, i + 4, …` are `helperSet 1 i (i + j - 1)`.
`Q = L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff C).tail` is the walk of Lemma 4.5: `L₁` lists the components of
`A'' ∪ C` (first phase), `L₂` those of `C ∪ B''` (second phase). Move `L₁.length` of `Q` (from state `L₁.length - 1` to
state `L₁.length`) is `K`: the last move of the first phase, the one that exchanges the component of `a_{i+1}`.
The paper's merged order ("the moves of the first phase of Q before K; then the moves of W, where K is performed
together with the move of W at which c_i first appears; then the second phase of Q") is `mergeIndexW`, `mergeIndexQ`
(Defs/MergeSchedule.lean; the same functions as `jW`, `jV` of Sec4/Junction.lean, by `rfl` below) with
`κ = L₁.length - 1`: state `α` of the merged walk is `W_{mergeIndexW α} ∪ Q_{mergeIndexQ α}`.
-/
import LeeDiam.Defs.MergeSchedule
import LeeDiam.Sec4.Junction
import LeeDiam.Sec4.Chain

namespace LeeDiam.S4

open Band

/-- "`c_i` is absent then", for any walk `Q` in which `a_{i+1}` occurs only in states `≤ κ` and `c_i` never: in the merged
walk `Z_α = W_{jW α} ∪ Q_{jV α}` (Q's move `κ` performed together with W's move into state `μ`), a state that contains
`a_{i+1}` does not contain `c_i`, if `c_i` is in no state of `W` before `μ` and `W` starts at middle elements. -/
theorem junction_absent_then {k : ℕ} {Q W : List (Set (Band k))} {A' B' : Set (Band k)} {aa cc : Band k}
    {κ μ : ℕ} (hQa : ∀ m, aa ∈ Q.getD m ∅ → m ≤ κ) (hQc : ∀ m, cc ∉ Q.getD m ∅) (hWa : ∀ m, aa ∉ W.getD m ∅)
    (hW : IsWalkFromTo W A' B') (hmid : ∀ x ∈ A' ∪ B', x.2 = 1) (hc2 : cc.2 ≠ 1)
    (hμ : ∀ t < μ, cc ∉ W.getD t ∅) (α : ℕ)
    (hα : aa ∈ W.getD (jW κ (W.length - 1) α) ∅ ∪ Q.getD (jV κ μ (W.length - 1) α) ∅) :
    cc ∉ W.getD (jW κ (W.length - 1) α) ∅ ∪ Q.getD (jV κ μ (W.length - 1) α) ∅ := by
  have hjV : jV κ μ (W.length - 1) α ≤ κ := by
    rcases hα with h | h
    · exact absurd h (hWa _)
    · exact hQa _ h
  have hjW : jW κ (W.length - 1) α = 0 ∨ jW κ (W.length - 1) α < μ := by
    unfold jV at hjV
    unfold jW
    split_ifs at hjV ⊢ <;> omega
  rintro (h | h)
  · rcases hjW with h0 | hlt
    · rw [h0, headD_of_head? hW.2.1] at h
      exact hc2 (hmid cc (Or.inl h))
    · exact hμ _ hlt h
  · exact hQc _ h

/-- The junction's schedule of `W` is the paper's merged order `mergeIndexW` (Defs). -/
theorem jW_eq_mergeIndexW : jW = mergeIndexW := rfl

/-- The junction's schedule of `Q` is the paper's merged order `mergeIndexQ` (Defs). -/
theorem jV_eq_mergeIndexQ : jV = mergeIndexQ := rfl

end LeeDiam.S4

namespace LeeDiam

open Band S4

/-- **Proof of Lemma 4.11** (Junction), sec_chain l. 133-135, `j ≥ 2`, row `a` (`a_{i+1}` initial, by reversal): the
paper's walk `Q` exists (Lemma 4.5, even helper positions, first phase ordered so that `K` comes last; it is a walk of
Corollary 4.6: length `⌊j/2⌋ + 1`, no middle element, columns `i+1, …, L`, `a_{i+1}` the only element of column `i+1`);
"the element `a_{i+1}` is present exactly before `K`" (in state `t` of `Q` iff `t < L₁.length`); "and `c_i` is absent
then": for every walk `W` from middle elements `A'` to `B'` in the columns `≤ i` and every `μ` before which `c_i` is in no
state of `W` (the move at which `c_i` first appears), no state of the merged walk contains both `a_{i+1}` and `c_i`. -/
theorem lem_4_11_step_proved {k : ℕ} (i j : ℕ) (hi : 1 ≤ i) (hj : 2 ≤ j) (hL : i + j ≤ k)
    (A'' B'' : Set (Band k)) (hAB : IsSplit A'' B'' (rowSeg 0 i (i + j - 1)))
    (ha : a ⟨i, by omega⟩ ∈ A'') :
    ∃ L₁ L₂ : List (Set (Band k)),
      L₁.Nodup ∧ (∀ D, D ∈ L₁ ↔ IsComponent D (A'' ∪ helperSet 1 i (i + j - 1))) ∧
      L₂.Nodup ∧ (∀ D, D ∈ L₂ ↔ IsComponent D (helperSet 1 i (i + j - 1) ∪ B'')) ∧
      a ⟨i, by omega⟩ ∈ L₁.getLastD ∅ ∧
      IsWalkFromTo (L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff (helperSet 1 i (i + j - 1))).tail) A'' B'' ∧
      (L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff (helperSet 1 i (i + j - 1))).tail).length - 1 = j / 2 + 1 ∧
      (∀ X ∈ L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff (helperSet 1 i (i + j - 1))).tail, ∀ x ∈ X,
        x.2 ≠ 1 ∧ i ≤ x.1.val ∧ x.1.val ≤ i + j - 1 ∧ (x.1.val = i → x.2 = 0)) ∧
      (∀ t, (a ⟨i, by omega⟩ ∈
          (L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff (helperSet 1 i (i + j - 1))).tail).getD t ∅ ↔
        t < L₁.length)) ∧
      ∀ (W : List (Set (Band k))) (A' B' : Set (Band k)), IsWalkFromTo W A' B' → (∀ x ∈ A' ∪ B', x.2 = 1) →
        (∀ X ∈ W, ∀ x ∈ X, x.1.val < i) → ∀ μ : ℕ, (∀ t < μ, c ⟨i - 1, by omega⟩ ∉ W.getD t ∅) →
        ∀ α : ℕ, a ⟨i, by omega⟩ ∈ W.getD (mergeIndexW (L₁.length - 1) (W.length - 1) α) ∅ ∪
            (L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff (helperSet 1 i (i + j - 1))).tail).getD
              (mergeIndexQ (L₁.length - 1) μ (W.length - 1) α) ∅ →
          c ⟨i - 1, by omega⟩ ∉ W.getD (mergeIndexW (L₁.length - 1) (W.length - 1) α) ∅ ∪
            (L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff (helperSet 1 i (i + j - 1))).tail).getD
              (mergeIndexQ (L₁.length - 1) μ (W.length - 1) α) ∅ := by
  classical
  set aa : Band k := a ⟨i, by omega⟩ with haa
  set cc : Band k := c ⟨i - 1, by omega⟩ with hcc
  set C : Set (Band k) := helperSet 1 i (i + j - 1) with hC
  -- the first phase, ordered so that the component `Da` of `a_{i+1}` comes last
  obtain ⟨L, hLnd, hLc⟩ := exists_comps_list (A'' ∪ C)
  obtain ⟨Da, hDa, haDa⟩ := comp_exists (S := A'' ∪ C) (Or.inl ha)
  have hDaL : Da ∈ L := (hLc Da).2 hDa
  have hperm : (L.erase Da ++ [Da]).Perm L :=
    (List.perm_append_singleton Da (L.erase Da)).trans (List.perm_cons_erase hDaL).symm
  have hL₁nd : (L.erase Da ++ [Da]).Nodup := hperm.nodup_iff.2 hLnd
  have hL₁c : ∀ D, D ∈ L.erase Da ++ [Da] ↔ IsComponent D (A'' ∪ C) := fun D => hperm.mem_iff.trans (hLc D)
  have hDa_erase : Da ∉ L.erase Da := fun h => ((hLnd.mem_erase_iff).1 h).1 rfl
  obtain ⟨L₂, hL₂nd, hL₂c⟩ := exists_comps_list (C ∪ B'')
  obtain ⟨-, hQw, hQlen, hQsub, -⟩ := comb i (i + j - 1) (by omega) (by omega) 1 (Or.inr ⟨rfl, by omega⟩) A'' B'' hAB
    (L.erase Da ++ [Da]) L₂ hL₁nd hL₁c hL₂nd hL₂c
  set L₁ := L.erase Da ++ [Da] with hL₁
  set Q := L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff C).tail with hQ
  have hL₁len : L₁.length = (L.erase Da).length + 1 := by rw [hL₁, List.length_append, List.length_singleton]
  have hcount : C.ncard = j / 2 := by
    rw [hC, (lem_4_5_count_proved i (i + j - 1) (by omega) (by omega)).1]
    congr 1
    omega
  have hstate : ∀ X ∈ Q, ∀ x ∈ X, x.2 ≠ 1 ∧ i ≤ x.1.val ∧ x.1.val ≤ i + j - 1 ∧ (x.1.val = i → x.2 = 0) := by
    intro X hX x hx
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := comb_state_prop (hQsub X hX hx)
    exact ⟨h1, h2, h3, h4⟩
  -- `a_{i+1}` is in no state of the second phase
  have haC : aa ∉ C := fun h => by
    have h02 : (0 : Fin 3) = 2 := h.1
    exact absurd h02 (by decide)
  have haB : aa ∉ B'' := fun h => Set.disjoint_left.1 hAB.1 ha h
  have hsecond : ∀ X ∈ L₂.scanl symmDiff C, aa ∉ X := by
    intro X hX hxX
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hX
    rw [mem_scanl_symmDiff C L₂ (comps_pairwise hL₂nd hL₂c) hm] at hxX
    have hex : ∃ D ∈ L₂.take m, aa ∈ D := by
      by_contra hno
      exact haC (hxX.2 hno)
    obtain ⟨D, hD, haD⟩ := hex
    rcases ((hL₂c D).1 (List.mem_of_mem_take hD)).2.1 haD with h | h
    · exact haC h
    · exact haB h
  -- "a_{i+1} is present exactly before K"
  have hpresent : ∀ t, aa ∈ Q.getD t ∅ ↔ t < L₁.length := by
    intro t
    by_cases ht : t ≤ L₁.length
    · have hlen : t < (L₁.scanl symmDiff A'').length := by rw [List.length_scanl]; omega
      rw [hQ, List.getD_append _ _ _ _ hlen, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen,
        Option.getD_some, mem_scanl_symmDiff A'' L₁ (comps_pairwise hL₁nd hL₁c) hlen]
      have hiff : (∃ D ∈ L₁.take t, aa ∈ D) ↔ t = L₁.length := by
        constructor
        · rintro ⟨D, hD, haD⟩
          have hDeq : D = Da := comp_eq_of_mem ((hL₁c D).1 (List.mem_of_mem_take hD)) hDa haD haDa
          by_contra hne
          have hle : t ≤ (L.erase Da).length := by omega
          rw [hL₁, List.take_append_of_le_length hle] at hD
          have hmem : D ∈ L.erase Da := List.mem_of_mem_take hD
          rw [hDeq] at hmem
          exact hDa_erase hmem
        · intro h
          exact ⟨Da, by rw [h, List.take_length]; exact (hL₁c Da).2 hDa, haDa⟩
      rw [hiff]
      constructor
      · intro h
        have h' := h.1 ha
        omega
      · intro h
        exact ⟨fun _ hne => by omega, fun _ => ha⟩
    · constructor
      · intro hmem
        exfalso
        have hle : (L₁.scanl symmDiff A'').length ≤ t := by rw [List.length_scanl]; omega
        rw [hQ, List.getD_append_right _ _ _ _ hle] at hmem
        obtain ⟨X, hX, hxX⟩ := mem_of_mem_getD hmem
        exact hsecond X (List.mem_of_mem_tail hX) hxX
      · intro h
        omega
  refine ⟨L₁, L₂, hL₁nd, hL₁c, hL₂nd, hL₂c, ?_, hQw, by rw [hQlen, hcount], hstate, hpresent, ?_⟩
  · rw [hL₁, List.getLastD_concat]
    exact haDa
  -- "and c_i is absent then"
  intro W A' B' hW hmid hcols μ hμ α hα
  rw [← jW_eq_mergeIndexW, ← jV_eq_mergeIndexQ] at hα ⊢
  refine junction_absent_then (fun m hm => ?_) (fun m h => ?_) (fun m h => ?_) hW hmid (by simp [hcc, c]) hμ α hα
  · have := (hpresent m).1 hm
    omega
  · obtain ⟨X, hX, hxX⟩ := mem_of_mem_getD h
    have h2 : i ≤ i - 1 := (hstate X hX cc hxX).2.1
    omega
  · obtain ⟨X, hX, hxX⟩ := mem_of_mem_getD h
    have h2 : i < i := hcols X hX aa hxX
    omega

/-- **Proof of Lemma 4.11** (Junction), sec_chain l. 133-135, `j = 1`: "If `j = 1`, let `K` be the only move of `Q`; then
the first phase consists of `K`": `Q = (A'', B'')` (here `A'' = {a_{i+1}}`, `B'' = ∅`) is a walk of Corollary 4.6
(length `⌊1/2⌋ + 1`, no middle element, column `i+1` only); `a_{i+1}` is present exactly before `K` (in state `t` iff
`t < 1`); and `c_i` is absent then, in the merged walk with `κ = 0`. -/
theorem lem_4_11_step_one_proved {k : ℕ} (i : ℕ) (hi : 1 ≤ i) (hL : i + 1 ≤ k)
    (A'' B'' : Set (Band k)) (hAB : IsSplit A'' B'' (rowSeg 0 i i)) (ha : a ⟨i, by omega⟩ ∈ A'') :
    IsWalkFromTo [A'', B''] A'' B'' ∧ ([A'', B''] : List (Set (Band k))).length - 1 = 1 / 2 + 1 ∧
      (∀ X ∈ ([A'', B''] : List (Set (Band k))), ∀ x ∈ X,
        x.2 ≠ 1 ∧ i ≤ x.1.val ∧ x.1.val ≤ i ∧ (x.1.val = i → x.2 = 0)) ∧
      (∀ t, (a ⟨i, by omega⟩ ∈ ([A'', B''] : List (Set (Band k))).getD t ∅ ↔ t < 1)) ∧
      ∀ (W : List (Set (Band k))) (A' B' : Set (Band k)), IsWalkFromTo W A' B' → (∀ x ∈ A' ∪ B', x.2 = 1) →
        (∀ X ∈ W, ∀ x ∈ X, x.1.val < i) → ∀ μ : ℕ, (∀ t < μ, c ⟨i - 1, by omega⟩ ∉ W.getD t ∅) →
        ∀ α : ℕ, a ⟨i, by omega⟩ ∈ W.getD (mergeIndexW 0 (W.length - 1) α) ∅ ∪
            ([A'', B''] : List (Set (Band k))).getD (mergeIndexQ 0 μ (W.length - 1) α) ∅ →
          c ⟨i - 1, by omega⟩ ∉ W.getD (mergeIndexW 0 (W.length - 1) α) ∅ ∪
            ([A'', B''] : List (Set (Band k))).getD (mergeIndexQ 0 μ (W.length - 1) α) ∅ := by
  set aa : Band k := a ⟨i, by omega⟩ with haa
  obtain ⟨hdis, hU, hanti⟩ := hAB
  have hseg : ∀ x : Band k, x ∈ (rowSeg 0 i i : Set (Band k)) ↔ x = aa := by
    intro x
    constructor
    · rintro ⟨h0, h1, h2⟩
      exact Prod.ext (Fin.ext (by simp [haa, a]; omega)) (by simp [haa, a, h0])
    · rintro rfl
      exact ⟨rfl, le_rfl, le_rfl⟩
  have hsub : ∀ X ∈ ([A'', B''] : List (Set (Band k))), X ⊆ rowSeg 0 i i := by
    intro X hX
    simp at hX
    rcases hX with rfl | rfl
    · rw [← hU]
      exact Set.subset_union_left
    · rw [← hU]
      exact Set.subset_union_right
  have haB : aa ∉ B'' := fun h => Set.disjoint_left.1 hdis ha h
  have hdiff : symmDiff A'' B'' = {aa} := by
    ext x
    rw [Set.mem_symmDiff, Set.mem_singleton_iff, ← hseg, ← hU]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl ⟨h, fun h' => Set.disjoint_left.1 hdis h h'⟩
      · exact Or.inr ⟨h, fun h' => Set.disjoint_left.1 hdis h' h⟩
  have hwalk : IsWalkFromTo [A'', B''] A'' B'' := by
    refine ⟨⟨List.cons_ne_nil _ _, fun X hX => hanti.subset (hsub X hX), ?_⟩, rfl, rfl⟩
    refine List.isChain_pair.2 ?_
    rw [hdiff]
    exact isConnSet_singleton aa
  have hstate : ∀ X ∈ ([A'', B''] : List (Set (Band k))), ∀ x ∈ X,
      x.2 ≠ 1 ∧ i ≤ x.1.val ∧ x.1.val ≤ i ∧ (x.1.val = i → x.2 = 0) := by
    intro X hX x hx
    obtain ⟨h0, h1, h2⟩ := hsub X hX hx
    exact ⟨by rw [h0]; decide, h1, h2, fun _ => h0⟩
  have hpresent : ∀ t, aa ∈ ([A'', B''] : List (Set (Band k))).getD t ∅ ↔ t < 1 := by
    intro t
    rcases t with _ | _ | t
    · simpa using ha
    · simpa using haB
    · simp
  refine ⟨hwalk, rfl, hstate, hpresent, ?_⟩
  intro W A' B' hW hmid hcols μ hμ α hα
  rw [← jW_eq_mergeIndexW, ← jV_eq_mergeIndexQ] at hα ⊢
  refine junction_absent_then (fun m hm => ?_) (fun m h => ?_) (fun m h => ?_) hW hmid (by simp [c]) hμ α hα
  · have := (hpresent m).1 hm
    omega
  · obtain ⟨X, hX, hxX⟩ := mem_of_mem_getD h
    have h2 : i ≤ i - 1 := (hstate X hX _ hxX).2.1
    omega
  · obtain ⟨X, hX, hxX⟩ := mem_of_mem_getD h
    have h2 : i < i := hcols X hX aa hxX
    omega

end LeeDiam
