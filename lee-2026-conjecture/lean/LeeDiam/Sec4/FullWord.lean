/-
LeeDiam/Sec4/FullWord.lean — Section 4 helper: antichains without empty columns (Proposition 4.13, sec_chain.tex v1.50
l. 152-164) and the overview statement of Section 4 for them.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

The word of `U` is `b^m x^(L-m)`: the middle elements fill the columns `< m`, the row `r` of `x` fills the others
(`run_form`). The proof splits on `m`: `m = 0` (Corollary 4.6); `m` odd (Corollary 4.10, then Lemma 4.11 if `m < L`);
`m` even (Corollary 4.10 on the columns `< m - 1`, then Lemma 4.12 if `m < L`, or Lemma 4.4 for `b_{m-1}` if `m = L`).
-/
import LeeDiam.Defs.Chain
import LeeDiam.Sec4.HalfJunction

namespace LeeDiam.S4

open Band

section FullWord

variable {k : ℕ}

/-- A split of `U = V₁ ∪ V₂` restricts to splits of `V₁` and `V₂`, and the parts recover `A` and `B`. -/
theorem split_parts {U V₁ V₂ A B : Set (Band k)} (hAB : IsSplit A B U) (hU : ∀ x, x ∈ U ↔ x ∈ V₁ ∨ x ∈ V₂) :
    IsSplit (A ∩ V₁) (B ∩ V₁) V₁ ∧ IsSplit (A ∩ V₂) (B ∩ V₂) V₂ ∧ A ∩ V₁ ∪ A ∩ V₂ = A ∧
      B ∩ V₁ ∪ B ∩ V₂ = B := by
  obtain ⟨hdis, hAB', hanti⟩ := hAB
  have hsub : ∀ x, x ∈ A ∨ x ∈ B ↔ x ∈ V₁ ∨ x ∈ V₂ := fun x => by rw [← hU, ← hAB']; rfl
  have hV₁ : V₁ ⊆ U := fun x hx => (hU x).2 (Or.inl hx)
  have hV₂ : V₂ ⊆ U := fun x hx => (hU x).2 (Or.inr hx)
  have hdis' : ∀ V : Set (Band k), Disjoint (A ∩ V) (B ∩ V) := fun V =>
    Set.disjoint_of_subset (fun x hx => hx.1) (fun x hx => hx.1) hdis
  have hun : ∀ V : Set (Band k), V ⊆ U → A ∩ V ∪ B ∩ V = V := fun V hV => by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.2
      · exact hx.2
    · intro hx
      rcases (hsub x).2 (by rw [← hU]; exact hV hx) with h | h
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨h, hx⟩
  have hrec : ∀ C : Set (Band k), C ⊆ U → C ∩ V₁ ∪ C ∩ V₂ = C := fun C hC => by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact hx.1
    · intro hx
      rcases (hU x).1 (hC hx) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hAU : A ⊆ U := fun x hx => hAB' ▸ Or.inl hx
  have hBU : B ⊆ U := fun x hx => hAB' ▸ Or.inr hx
  exact ⟨⟨hdis' V₁, hun V₁ hV₁, hanti.subset hV₁⟩, ⟨hdis' V₂, hun V₂ hV₂, hanti.subset hV₂⟩, hrec A hAU,
    hrec B hBU⟩

theorem mem_mids_iff {x : Band k} {m : ℕ} : x ∈ {x : Band k | x.2 = 1 ∧ x.1.val < m} ↔ x.2.val = 1 ∧ x.1.val < m :=
  ⟨fun h => ⟨by rw [h.1]; rfl, h.2⟩, fun h => ⟨Fin.ext h.1, h.2⟩⟩

theorem mem_rowSeg_iff {x : Band k} {r : Fin 3} {s e : ℕ} :
    x ∈ (rowSeg r s e : Set (Band k)) ↔ x.2.val = r.val ∧ s ≤ x.1.val ∧ x.1.val ≤ e :=
  ⟨fun h => ⟨by rw [h.1], h.2.1, h.2.2⟩, fun h => ⟨Fin.ext h.1, h.2.1, h.2.2⟩⟩

theorem eq_b_iff {x : Band k} {q : Fin k} : x = b q ↔ x.1.val = q.val ∧ x.2.val = 1 := band_ext_iff x (b q)

/-- In a walk tame at `i`, some state contains the outer element `h`. -/
theorem tame_mem {W : List (Set (Band k))} {i : Fin k} {h : Band k} (hW : IsWalk W) (hT : IsTameAt W i h) :
    ∃ X ∈ W, h ∈ X := by
  obtain ⟨μ, ν, hμ1, hμν, hνn, hmem⟩ := tame_arrive_depart W i h hT
  exact ⟨W.getD μ ∅, getD_mem_of_le hW.1 (by omega), (hmem μ (by omega)).2 ⟨le_rfl, hμν⟩⟩

/-- Lemma 4.4 for `b_q` and a walk tame at `p = q - 1`: `b_q` rides along, initial or final, at no extra length. -/
theorem ride_b {p q : Fin k} (hpq : q.val = p.val + 1) {W : List (Set (Band k))} {A' B' : Set (Band k)}
    {h : Band k} (hW : IsWalkFromTo W A' B') (hT : IsTameAt W p h) :
    (∃ W', IsWalkFromTo W' (A' ∪ {b q}) B' ∧ W'.length = W.length) ∧
      ∃ W', IsWalkFromTo W' A' (B' ∪ {b q}) ∧ W'.length = W.length := by
  obtain ⟨μ, ν, hμ1, hμν, hνn, hmem⟩ := tame_arrive_depart W p h hT
  have hcolW : ∀ X ∈ W, ∀ x ∈ X, x.1.val ≤ p.val := tame_cols_le hT
  have hy : ∀ X ∈ W, b q ∉ X := not_mem_of_cols hpq hcolW rfl
  have hb1 : (b q).1.val = q.val := rfl
  have hb2 : (b q).2.val = 1 := rfl
  have honly : ∀ t, ∀ z ∈ W.getD t ∅, Comp (b q) z → z = h := by
    intro t z hz hcz
    obtain ⟨X, hX, hzX⟩ := mem_of_mem_getD hz
    have hzc := hcolW X hX z hzX
    rw [comp_iff_val] at hcz
    have hz2 := z.2.isLt
    have key : z.1.val = p.val ∧ z.2.val ≠ 1 := by omega
    exact tame_only_h hW.1 hT hX hzX (Fin.ext key.1) (fun h' => key.2 (by rw [h']; rfl))
  have hbh : Comp (b q) h := by
    rw [comp_iff_val]
    have h1 : h.1.val = p.val := by rw [hT.2.1]
    have h2 : h.2.val ≠ 1 := fun h' => hT.2.2.1 (Fin.ext h')
    omega
  have hn : ¬ (W.length - 1 < μ) := by omega
  constructor
  · obtain ⟨hw, hlen⟩ := ride_prefix W hW.1 (b q) hy μ ⟨h, (hmem μ (by omega)).2 ⟨le_rfl, hμν⟩, hbh⟩
      (fun t ht z hz hcz => by
        rw [honly t z hz hcz] at hz
        have htl : t < W.length := by omega
        exact absurd ((hmem t htl).1 hz).1 (by omega))
    refine ⟨_, ⟨hw, ?_, ?_⟩, hlen⟩
    · rw [List.head?_eq_getElem?, List.getElem?_mapIdx, ← List.head?_eq_getElem?, hW.2.1]
      simp [show 0 < μ by omega, Set.union_singleton]
    · rw [List.getLast?_eq_getElem?, List.length_mapIdx, List.getElem?_mapIdx, ← List.getLast?_eq_getElem?, hW.2.2]
      simp [hn]
  · obtain ⟨hw, hlen⟩ := ride_suffix W hW.1 (b q) hy ν (by omega)
      ⟨h, (hmem (ν - 1) (by omega)).2 ⟨by omega, by omega⟩, hbh⟩
      (fun t ht z hz hcz => by
        rw [honly t z hz hcz] at hz
        by_cases htl : t < W.length
        · exact absurd ((hmem t htl).1 hz).2 (by omega)
        · rw [getD_eq_empty (by omega)] at hz
          exact hz)
    refine ⟨_, ⟨hw, ?_, ?_⟩, hlen⟩
    · rw [List.head?_eq_getElem?, List.getElem?_mapIdx, ← List.head?_eq_getElem?, hW.2.1]
      simp [show ¬ ν ≤ 0 by omega]
    · rw [List.getLast?_eq_getElem?, List.length_mapIdx, List.getElem?_mapIdx, ← List.getLast?_eq_getElem?, hW.2.2]
      simp [show ν ≤ W.length - 1 by omega, Set.union_singleton]

theorem rev_ne_one {r : Fin 3} (hr : r ≠ 1) : Fin.rev r ≠ 1 := fun h => hr (by rw [← Fin.rev_rev r, h]; rfl)

/-- Proposition 4.13 with the number `m ≤ L` of middle elements. -/
theorem full_word_m (L : ℕ) (hL : 2 ≤ L) (U : Set (Band L)) (m : ℕ) (hmL : m ≤ L) (r : Fin 3) (hr : r ≠ 1)
    (hmemU : ∀ x, x ∈ U ↔ (x.2.val = 1 ∧ x.1.val < m) ∨ (x.2.val = r.val ∧ m ≤ x.1.val))
    (A B : Set (Band L)) (hAB : IsSplit A B U) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 ≤ (if 1 ≤ m then (L + 1) / 2 + 1 else L / 2 + 1) := by
  have hrv : r.val ≠ 1 := fun h => hr (Fin.ext h)
  have hrl := r.isLt
  have hcol : ∀ x : Band L, x.1.val < L := fun x => x.1.isLt
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · -- no middle elements: Corollary 4.6
    subst hm0
    have hUS : U = rowSeg r 0 (L - 1) := by
      ext x
      rw [hmemU, mem_rowSeg_iff]
      have := hcol x
      omega
    obtain ⟨W, hW, hlen, -, -⟩ := comb_cor r hr 0 (L - 1) (by omega) (by omega) A B (hUS ▸ hAB)
    exact ⟨W, hW, by rw [hlen]; split_ifs <;> omega⟩
  rcases Nat.even_or_odd m with ⟨m2, hm2⟩ | ⟨m2, hm2⟩
  · -- `m` even: Corollary 4.10 on the columns `< m - 1`
    have hm2' : 2 ≤ m := by omega
    set M' : Set (Band L) := {x | x.2 = 1 ∧ x.1.val < m - 1} with hM'
    set q : Fin L := ⟨m - 1, by omega⟩ with hq
    obtain ⟨W, h, hW, hWlen, hT, -, hWcols⟩ :=
      tame_cor (m - 1) (by omega) (by omega) r hr (A ∩ M') (B ∩ M')
        (split_parts hAB (V₂ := (U \ M')) (fun x => by
          constructor
          · intro hx
            by_cases h : x ∈ M'
            · exact Or.inl h
            · exact Or.inr ⟨hx, h⟩
          · rintro (h | h)
            · rw [hmemU]; rw [mem_mids_iff] at h; omega
            · exact h.1)).1
    have hT' : IsTameAt W ⟨m - 2, by omega⟩ h := by
      have : (⟨m - 1 - 1, by omega⟩ : Fin L) = ⟨m - 2, by omega⟩ := Fin.ext (by show m - 1 - 1 = m - 2; omega)
      rw [← this]
      exact hT
    have hmid : ∀ x ∈ A ∩ M' ∪ B ∩ M', x.2 = 1 := by
      rintro x (hx | hx)
      · exact hx.2.1
      · exact hx.2.1
    rcases Nat.lt_or_ge m L with hmL' | hmL'
    · -- Lemma 4.12
      set N : Set (Band L) := insert (b ⟨m - 1, by omega⟩) (rowSeg r m (m + (L - m) - 1)) with hN
      have hUN : ∀ x, x ∈ U ↔ x ∈ M' ∨ x ∈ N := fun x => by
        rw [hmemU, mem_mids_iff, hN, Set.mem_insert_iff, eq_b_iff, mem_rowSeg_iff]
        have := hcol x
        show _ ↔ _ ∨ (x.1.val = m - 1 ∧ x.2.val = 1) ∨ _
        omega
      obtain ⟨hs1, hs2, hrA, hrB⟩ := split_parts hAB hUN
      obtain ⟨W', hW', hlen, -⟩ := half_junction m (L - m) hm2' (by omega) (by omega) r hr W (A ∩ M') (B ∩ M') h hW
        hT' hmid (A ∩ N) (B ∩ N) hs2
      rw [hrA, hrB] at hW'
      exact ⟨W', hW', by rw [hlen, hWlen]; split_ifs <;> omega⟩
    · -- `m = L`: Lemma 4.4 for `b_{m-1}`
      have hmeq : m = L := le_antisymm hmL hmL'
      have hUb : ∀ x, x ∈ U ↔ x ∈ M' ∨ x ∈ ({b q} : Set (Band L)) := fun x => by
        rw [hmemU, mem_mids_iff, Set.mem_singleton_iff, eq_b_iff]
        have := hcol x
        show _ ↔ _ ∨ (x.1.val = m - 1 ∧ x.2.val = 1)
        omega
      obtain ⟨-, -, hrA, hrB⟩ := split_parts hAB hUb
      have hpq : q.val = (⟨m - 1 - 1, by omega⟩ : Fin L).val + 1 := by show m - 1 = m - 1 - 1 + 1; omega
      obtain ⟨hini, hfin⟩ := ride_b hpq hW hT
      have hbU : b q ∈ A ∨ b q ∈ B := by
        rw [← Set.mem_union, hAB.2.1, hUb]
        exact Or.inr rfl
      rcases hbU with hbA | hbB
      · have hbB : b q ∉ B := fun h' => Set.disjoint_left.1 hAB.1 hbA h'
        have e1 : A ∩ {b q} = {b q} := Set.inter_eq_right.2 (Set.singleton_subset_iff.2 hbA)
        have e2 : B ∩ {b q} = ∅ := Set.inter_singleton_eq_empty.2 hbB
        obtain ⟨W', hW', hlen⟩ := hini
        rw [← e1, hrA] at hW'
        rw [← Set.union_empty (B ∩ M'), ← e2, hrB] at hW'
        exact ⟨W', hW', by rw [hlen]; split_ifs <;> omega⟩
      · have hbA : b q ∉ A := fun h' => Set.disjoint_left.1 hAB.1 h' hbB
        have e1 : B ∩ {b q} = {b q} := Set.inter_eq_right.2 (Set.singleton_subset_iff.2 hbB)
        have e2 : A ∩ {b q} = ∅ := Set.inter_singleton_eq_empty.2 hbA
        obtain ⟨W', hW', hlen⟩ := hfin
        rw [← e1, hrB] at hW'
        rw [← Set.union_empty (A ∩ M'), ← e2, hrA] at hW'
        exact ⟨W', hW', by rw [hlen]; split_ifs <;> omega⟩
  · -- `m` odd: Corollary 4.10 on the columns `< m`
    set M : Set (Band L) := {x | x.2 = 1 ∧ x.1.val < m} with hM
    set S : Set (Band L) := rowSeg r m (m + (L - m) - 1) with hS
    have hUMS : ∀ x, x ∈ U ↔ x ∈ M ∨ x ∈ S := fun x => by
      rw [hmemU, mem_mids_iff, hS, mem_rowSeg_iff]
      have := hcol x
      omega
    obtain ⟨hs1, hs2, hrA, hrB⟩ := split_parts hAB hUMS
    obtain ⟨W, h, hW, hWlen, hT, hh2, hWcols⟩ := tame_cor m hm1 hmL (Fin.rev r) (rev_ne_one hr) (A ∩ M) (B ∩ M) hs1
    rcases Nat.lt_or_ge m L with hmL' | hmL'
    · -- Lemma 4.11
      have hmid : ∀ x ∈ A ∩ M ∪ B ∩ M, x.2 = 1 := by
        rintro x (hx | hx)
        · exact hx.2.1
        · exact hx.2.1
      have hc : ∃ X ∈ W, ((⟨m - 1, by omega⟩ : Fin L), Fin.rev r) ∈ X := by
        obtain ⟨X, hX, hhX⟩ := tame_mem hW.1 hT
        have hhe : h = ((⟨m - 1, by omega⟩ : Fin L), Fin.rev r) := Prod.ext hT.2.1 hh2
        exact ⟨X, hX, by rw [← hhe]; exact hhX⟩
      obtain ⟨W', hW', hlen, -⟩ := junction m (L - m) hm1 (by omega) (by omega) r hr W (A ∩ M) (B ∩ M) hW hmid
        hWcols hc (A ∩ S) (B ∩ S) hs2
      rw [hrA, hrB] at hW'
      exact ⟨W', hW', by rw [hlen, hWlen]; split_ifs <;> omega⟩
    · -- `m = L`: the tame walk itself
      have hS0 : ∀ C : Set (Band L), C ∩ S = ∅ := fun C => by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hx
        rw [hS, mem_rowSeg_iff] at hx
        have := hcol x
        omega
      rw [hS0, Set.union_empty] at hrA hrB
      rw [hrA, hrB] at hW
      exact ⟨W, hW, by rw [hWlen]; split_ifs <;> omega⟩

/-- Proposition 4.13, in the statement form of Sec4/Chain.lean `prop_4_13`. -/
theorem full_word (L : ℕ) (hL : 2 ≤ L) (U : Set (Band L)) (hU : IsAntichainSet U)
    (hfull : ∀ l : Fin L, ∃ x ∈ U, x.1 = l) (i : ℕ) (hi : ∀ x ∈ U, x.2 = 1 ↔ x.1.val < i)
    (A B : Set (Band L)) (hAB : IsSplit A B U) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 ≤ (if 1 ≤ i then (L + 1) / 2 + 1 else L / 2 + 1) := by
  obtain ⟨i₀, r, hr, hrow⟩ := run_form U hU 0 (L - 1) (fun l _ _ => hfull l)
  have hrv : r.val ≠ 1 := fun h => hr (Fin.ext h)
  obtain ⟨m, hmL, hi', him⟩ : ∃ m, m ≤ L ∧ (∀ x ∈ U, x.2 = 1 ↔ x.1.val < m) ∧ (1 ≤ i ↔ 1 ≤ m) := by
    by_cases h : i ≤ L
    · exact ⟨i, h, hi, Iff.rfl⟩
    · exact ⟨L, le_rfl, fun x hx => by rw [hi x hx]; have := x.1.isLt; omega, by omega⟩
  have hmemU : ∀ x, x ∈ U ↔ (x.2.val = 1 ∧ x.1.val < m) ∨ (x.2.val = r.val ∧ m ≤ x.1.val) := by
    intro x
    constructor
    · intro hx
      by_cases h1 : x.2 = 1
      · exact Or.inl ⟨by rw [h1]; rfl, (hi' x hx).1 h1⟩
      · have h2 : ¬ x.1.val < m := fun h => h1 ((hi' x hx).2 h)
        exact Or.inr ⟨by rw [(hrow x hx (Nat.zero_le _) (by have := x.1.isLt; omega)).2 h1], by omega⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · obtain ⟨y, hy, hyx⟩ := hfull x.1
        have hy1 : y.2 = 1 := (hi' y hy).2 (by rw [hyx]; exact h2)
        have : y = x := Prod.ext hyx (Fin.ext (by rw [hy1, h1]; rfl))
        exact this ▸ hy
      · obtain ⟨y, hy, hyx⟩ := hfull x.1
        have hy1 : y.2 ≠ 1 := fun h => by
          have := (hi' y hy).1 h
          rw [hyx] at this
          omega
        have : y = x :=
          Prod.ext hyx (Fin.ext (by rw [(hrow y hy (Nat.zero_le _) (by have := y.1.isLt; omega)).2 hy1, h1]))
        exact this ▸ hy
  obtain ⟨W, hW, hlen⟩ := full_word_m L hL U m hmL r hr hmemU A B hAB
  refine ⟨W, hW, ?_⟩
  split_ifs at hlen ⊢ <;> omega

/-- The Section 4 overview for antichains without empty columns: every split has a walk of length at most
`⌈k/2⌉ + 1`. -/
theorem overview_fullword (hk : 2 ≤ k) (U : Set (Band k)) (hU : IsAntichainSet U)
    (hfull : ∀ l : Fin k, ∃ x ∈ U, x.1 = l) (A B : Set (Band k)) (hAB : IsSplit A B U) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 ≤ (k + 1) / 2 + 1 := by
  obtain ⟨i, r, -, hrow⟩ := run_form U hU 0 (k - 1) (fun l _ _ => hfull l)
  have hi : ∀ x ∈ U, x.2 = 1 ↔ x.1.val < i := fun x hx => by
    have := (hrow x hx (Nat.zero_le _) (by have := x.1.isLt; omega)).1
    rw [Nat.zero_add] at this
    exact this
  obtain ⟨W, hW, hlen⟩ := full_word k hk U hU hfull i hi A B hAB
  refine ⟨W, hW, ?_⟩
  split_ifs at hlen <;> omega

end FullWord

end LeeDiam.S4

