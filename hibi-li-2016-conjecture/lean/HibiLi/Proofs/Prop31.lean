/-
HibiLi/Proofs/Prop31.lean — proof of Proposition 3.1 (Fourier Prop. 3.1): O_I(P) and O_{I∪{q}}(P) as fibres over B.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Proofs.LU

namespace HibiLi.Proofs

open HibiLi Finset

section Prop31

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-! ### Moving finsets between `P' = P \ {q}` and `P` -/

/-- A finset of `P'` seen as a finset of `P`. -/
def liftK (K : Finset s.P') : Finset P := K.map (Function.Embedding.subtype _)

lemma forall_mem_liftK {K : Finset s.P'} {Φ : P → Prop} : (∀ p ∈ liftK s K, Φ p) ↔ ∀ p ∈ K, Φ p.1 := by
  simp [liftK]

lemma q_notMem_liftK (K : Finset s.P') : s.q ∉ liftK s K := by
  simp [liftK]

lemma sum_liftK (K : Finset s.P') (x : P → ℝ) : ∑ p ∈ liftK s K, x p = s.chainSum K (fun p => x p.1) := by
  simp [liftK, Switch.chainSum]

lemma liftK_subset_iff {K : Finset s.P'} {S : Set P} : (↑(liftK s K) : Set P) ⊆ S ↔ ∀ p ∈ K, p.1 ∈ S :=
  forall_mem_liftK s (Φ := (· ∈ S))

lemma isChainSet_liftK {K : Finset s.P'} : IsChainSet P (liftK s K) ↔ IsChainSet s.P' K := by
  simp only [IsChainSet, liftK, coe_map, Function.Embedding.coe_subtype]
  refine ⟨fun h a ha b hb hab => ?_, fun h => h.image_of_map_rel _ _ Subtype.val fun _ _ hab => hab⟩
  exact h (Set.mem_image_of_mem _ ha) (Set.mem_image_of_mem _ hb) (Subtype.coe_injective.ne hab)

/-- Every finset of `P` avoiding `q` comes from `P'`. -/
lemma exists_liftK {K : Finset P} (hq : s.q ∉ K) : ∃ K' : Finset s.P', liftK s K' = K := by
  classical
  exact ⟨K.subtype (· ≠ s.q), subtype_map_of_mem fun p hp => ne_of_mem_of_not_mem hp hq⟩

/-! ### Branches of `L` and `U` -/

lemma mem_lowBranches {K : Finset s.P'} :
    K ∈ s.lowBranches ↔ (∀ p ∈ K, p.1 ∈ s.I) ∧ IsChainSet s.P' K ∧ ∀ p ∈ K, p.1 < s.q := by
  simp only [Switch.lowBranches, mem_filter, mem_univ, true_and]
  exact Iff.rfl

lemma none_mem_upBranches : (none : Option s.P') ∈ s.upBranches := by
  simp [Switch.upBranches]

lemma some_mem_upBranches {r : s.P'} (hr : s.q < r.1) : some r ∈ s.upBranches := by
  simp [Switch.upBranches, hr]

lemma mem_upBranches {j : Option s.P'} (hj : j ∈ s.upBranches) : j = none ∨ ∃ r : s.P', s.q < r.1 ∧ j = some r := by
  cases j with
  | none => exact Or.inl rfl
  | some r => exact Or.inr ⟨r, by simpa [Switch.upBranches] using hj, rfl⟩

/-- `z ≤ U − L` iff `ℓ_K + z ≤` every upper branch, for every lower branch `K`. -/
lemma le_U_sub_L_iff (u : s.P' → ℝ) (z : ℝ) :
    z ≤ s.U u - s.L u ↔ ∀ K ∈ s.lowBranches, ∀ j ∈ s.upBranches, s.chainSum K u + z ≤ s.upVal j u := by
  rw [le_sub_comm, Switch.L, sup'_le_iff]
  refine forall₂_congr fun K _ => ?_
  rw [le_sub_iff_add_le, Switch.U, le_inf'_iff]

/-! ### The inequalities of `B`, read in `P` -/

/-- If `x` lies in `O_J(P)` with `J = I` off `q`, its restriction to `P'` lies in `B`. -/
lemma restrict_mem_B {J : Set P} (hJ : ∀ p, p ≠ s.q → (p ∈ J ↔ p ∈ s.I)) {x : P → ℝ}
    (hx : x ∈ chainOrderPolytope P J) : (fun p : s.P' => x p.1) ∈ s.B := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  have hI' : ∀ p : s.P', p ∈ s.I' ↔ p.1 ∈ J := fun p => (hJ p.1 p.2).symm
  have hK : ∀ K : Finset s.P', ↑K ⊆ s.I' → (↑(liftK s K) : Set P) ⊆ J := fun K hK =>
    (liftK_subset_iff s).2 fun p hp => (hI' p).1 (hK hp)
  refine ⟨fun p hp => h1 _ ((hI' p).1 hp), fun r hr => h2 _ (mt (hI' r).2 hr),
    fun r r' hr hr' hrr' => h3 _ _ (mt (hI' r).2 hr) (mt (hI' r').2 hr') hrr', ?_, ?_⟩
  · intro r hr K hKI hKc hKr
    have := h4 _ (mt (hI' r).2 hr) (liftK s K) (hK K hKI) ((isChainSet_liftK s).2 hKc) ((forall_mem_liftK s).2 hKr)
    rwa [sum_liftK] at this
  · intro K hKI hKc
    have := h5 (liftK s K) (hK K hKI) ((isChainSet_liftK s).2 hKc)
    rwa [sum_liftK] at this

/-- The inequalities of `B`, transported to the coordinates of `P` (elements and chains avoiding `q`). -/
lemma of_restrict_mem_B {x : P → ℝ} (hu : (fun p : s.P' => x p.1) ∈ s.B) :
    (∀ p ∈ s.I, 0 ≤ x p) ∧
    (∀ r ∉ s.I, r ≠ s.q → 0 ≤ x r ∧ x r ≤ 1) ∧
    (∀ r r', r ∉ s.I → r' ∉ s.I → r ≠ s.q → r' ≠ s.q → r ≤ r' → x r ≤ x r') ∧
    (∀ r ∉ s.I, r ≠ s.q → ∀ K : Finset P, (↑K ⊆ s.I) → IsChainSet P K → (∀ p ∈ K, p < r) → ∑ p ∈ K, x p ≤ x r) ∧
    (∀ K : Finset P, (↑K ⊆ s.I) → IsChainSet P K → ∑ p ∈ K, x p ≤ 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hu
  have hlift : ∀ K : Finset P, (↑K ⊆ s.I) → ∃ K', liftK s K' = K := fun K hK =>
    exists_liftK s fun hq => s.q_notMem (hK hq)
  refine ⟨fun p hp => h1 ⟨p, ne_of_mem_of_not_mem hp s.q_notMem⟩ hp, fun r hr hrq => h2 ⟨r, hrq⟩ hr,
    fun r r' hr hr' hrq hr'q hrr' => h3 ⟨r, hrq⟩ ⟨r', hr'q⟩ hr hr' hrr', ?_, ?_⟩
  · intro r hr hrq K hKI hKc hKr
    obtain ⟨K, rfl⟩ := hlift K hKI
    rw [sum_liftK]
    exact h4 ⟨r, hrq⟩ hr K ((liftK_subset_iff s).1 hKI) ((isChainSet_liftK s).1 hKc) ((forall_mem_liftK s).1 hKr)
  · intro K hKI hKc
    obtain ⟨K, rfl⟩ := hlift K hKI
    rw [sum_liftK]
    exact h5 K ((liftK_subset_iff s).1 hKI) ((isChainSet_liftK s).1 hKc)

/-! ### The two fibre descriptions -/

/-- `O_I(P) = {(u, z) : u ∈ B, L(u) ≤ z ≤ U(u)}`. -/
lemma fibre_I (x : P → ℝ) :
    x ∈ chainOrderPolytope P s.I ↔
      (fun p : s.P' => x p.1) ∈ s.B ∧ s.L (fun p => x p.1) ≤ x s.q ∧ x s.q ≤ s.U (fun p => x p.1) := by
  constructor
  · intro hx
    obtain ⟨-, h2, h3, h4, -⟩ := id hx
    refine ⟨restrict_mem_B s (fun _ _ => Iff.rfl) hx, sup'_le _ _ fun K hK => ?_, le_inf' _ _ fun j hj => ?_⟩
    · obtain ⟨hKI, hKc, hKq⟩ := (mem_lowBranches s).1 hK
      have := h4 s.q s.q_notMem (liftK s K) ((liftK_subset_iff s).2 hKI) ((isChainSet_liftK s).2 hKc)
        ((forall_mem_liftK s).2 hKq)
      rwa [sum_liftK] at this
    · rcases mem_upBranches s hj with rfl | ⟨r, hr, rfl⟩
      · exact (h2 s.q s.q_notMem).2
      · exact h3 s.q r.1 s.q_notMem (not_mem_I_of_gt s hr) hr.le
  · rintro ⟨hu, hL, hU⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := of_restrict_mem_B s hu
    obtain ⟨hL0, -, hU1⟩ := L_U_bounds s hu
    refine ⟨h1, fun r hr => ?_, fun r r' hr hr' hrr' => ?_, fun r hr K hKI hKc hKr => ?_, h5⟩
    · by_cases hrq : r = s.q
      · subst hrq; exact ⟨hL0.trans hL, hU.trans hU1⟩
      · exact h2 r hr hrq
    · by_cases hrq : r = s.q <;> by_cases hr'q : r' = s.q
      · rw [hrq, hr'q]
      · subst hrq
        exact hU.trans (U_le_upVal s (some_mem_upBranches s (r := ⟨r', hr'q⟩) (lt_of_le_of_ne hrr' (Ne.symm hr'q))) _)
      · subst hr'q; exact absurd (s.q_minimal r (lt_of_le_of_ne hrr' hrq)) hr
      · exact h3 r r' hr hr' hrq hr'q hrr'
    · by_cases hrq : r = s.q
      · subst hrq
        obtain ⟨K, rfl⟩ := exists_liftK s fun hq => s.q_notMem (hKI hq)
        rw [sum_liftK]
        refine (chainSum_le_L s ((mem_lowBranches s).2 ⟨(liftK_subset_iff s).1 hKI, (isChainSet_liftK s).1 hKc,
          (forall_mem_liftK s).1 hKr⟩) _).trans hL
      · exact h4 r hr hrq K hKI hKc hKr

/-- A chain of `I ∪ {q}` through `q` is a lower branch `K'` of `L` followed by `q` (`q` is maximal in `I ∪ {q}`). -/
lemma split_chain_through_q (x : P → ℝ) {K : Finset P} (hKI : ↑K ⊆ insert s.q s.I) (hKc : IsChainSet P K)
    (hqK : s.q ∈ K) : ∃ K' ∈ s.lowBranches, ∑ p ∈ K, x p = s.chainSum K' (fun p => x p.1) + x s.q := by
  classical
  obtain ⟨K', hK'⟩ := exists_liftK s (notMem_erase s.q K)
  have hmem : ∀ p ∈ K', p.1 ∈ K := (forall_mem_liftK s).1 fun p hp => mem_of_mem_erase (hK' ▸ hp)
  have hI : ∀ p ∈ K', p.1 ∈ s.I := fun p hp => (Set.mem_insert_iff.1 (hKI (hmem p hp))).resolve_left p.2
  refine ⟨K', (mem_lowBranches s).2 ⟨hI, (isChainSet_liftK s).1 (hKc.mono ?_), fun p hp => ?_⟩, ?_⟩
  · rw [hK', coe_erase]; exact Set.sdiff_subset
  · rcases hKc (hmem p hp) hqK p.2 with h | h
    · exact lt_of_le_of_ne h p.2
    · exact absurd (s.isLowerSet h (hI p hp)) s.q_notMem
  · rw [← sum_erase_add K _ hqK, ← hK', sum_liftK]

/-- `O_{I∪{q}}(P) = {(u, w) : u ∈ B, 0 ≤ w ≤ U(u) − L(u)}`. -/
lemma fibre_insert (x : P → ℝ) :
    x ∈ chainOrderPolytope P (insert s.q s.I) ↔
      (fun p : s.P' => x p.1) ∈ s.B ∧ 0 ≤ x s.q ∧ x s.q ≤ s.U (fun p => x p.1) - s.L (fun p => x p.1) := by
  classical
  rw [le_U_sub_L_iff]
  constructor
  · intro hx
    obtain ⟨h1, -, -, h4, h5⟩ := id hx
    refine ⟨restrict_mem_B s (fun p hp => by simp [hp]) hx, h1 s.q (Set.mem_insert _ _), fun K hK j hj => ?_⟩
    obtain ⟨hKI, hKc, hKq⟩ := (mem_lowBranches s).1 hK
    have hsub : (↑(insert s.q (liftK s K)) : Set P) ⊆ insert s.q s.I := by
      rw [coe_insert]; exact Set.insert_subset_insert ((liftK_subset_iff s).2 hKI)
    have hchain : IsChainSet P (insert s.q (liftK s K)) := by
      unfold IsChainSet; rw [coe_insert]
      exact ((isChainSet_liftK s).2 hKc).insert fun b hb _ =>
        Or.inr ((forall_mem_liftK s (Φ := (· ≤ s.q))).2 (fun p hp => (hKq p hp).le) b hb)
    have hsum : ∑ p ∈ insert s.q (liftK s K), x p = s.chainSum K (fun p => x p.1) + x s.q := by
      rw [sum_insert (q_notMem_liftK s K), sum_liftK, add_comm]
    rw [← hsum]
    rcases mem_upBranches s hj with rfl | ⟨r, hr, rfl⟩
    · exact h5 _ hsub hchain
    · refine h4 r.1 (by simp [r.2, not_mem_I_of_gt s hr]) _ hsub hchain fun p hp => ?_
      rcases mem_insert.1 hp with rfl | hp
      · exact hr
      · exact ((forall_mem_liftK s (Φ := (· < s.q))).2 hKq p hp).trans hr
  · rintro ⟨hu, hq0, hLU⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := of_restrict_mem_B s hu
    have hnot : ∀ r, r ∉ insert s.q s.I → r ∉ s.I ∧ r ≠ s.q := fun r hr =>
      ⟨fun h => hr (Or.inr h), fun h => hr (Or.inl h)⟩
    have hnoq : ∀ K : Finset P, (↑K ⊆ insert s.q s.I) → s.q ∉ K → (↑K : Set P) ⊆ s.I :=
      fun K hKI hqK p hp => (Set.mem_insert_iff.1 (hKI hp)).resolve_left fun h => hqK (h ▸ hp)
    refine ⟨?_, fun r hr => h2 r (hnot r hr).1 (hnot r hr).2,
      fun r r' hr hr' hrr' => h3 r r' (hnot r hr).1 (hnot r' hr').1 (hnot r hr).2 (hnot r' hr').2 hrr', ?_, ?_⟩
    · rintro p (rfl | hp)
      exacts [hq0, h1 p hp]
    · intro r hr K hKI hKc hKr
      by_cases hqK : s.q ∈ K
      · obtain ⟨K', hK', hsum⟩ := split_chain_through_q s x hKI hKc hqK
        rw [hsum]
        exact hLU K' hK' (some ⟨r, (hnot r hr).2⟩) (some_mem_upBranches s (hKr _ hqK))
      · exact h4 r (hnot r hr).1 (hnot r hr).2 K (hnoq K hKI hqK) hKc hKr
    · intro K hKI hKc
      by_cases hqK : s.q ∈ K
      · obtain ⟨K', hK', hsum⟩ := split_chain_through_q s x hKI hKc hqK
        rw [hsum]
        exact hLU K' hK' none (none_mem_upBranches s)
      · exact h5 K (hnoq K hKI hqK) hKc

end Prop31

/-- **Proposition 3.1** (Fourier Prop. 3.1): in coordinates `(u, z)`, `u ∈ B`, `z = x_q`,
`O_I(P) = {L(u) ≤ z ≤ U(u)}` and `O_{I∪{q}}(P) = {0 ≤ z ≤ U(u) − L(u)}`. -/
theorem prop_3_1_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (x : P → ℝ) :
    (x ∈ chainOrderPolytope P s.I ↔
      (fun p : s.P' => x p.1) ∈ s.B ∧ s.L (fun p => x p.1) ≤ x s.q ∧ x s.q ≤ s.U (fun p => x p.1)) ∧
    (x ∈ chainOrderPolytope P (insert s.q s.I) ↔
      (fun p : s.P' => x p.1) ∈ s.B ∧ 0 ≤ x s.q ∧ x s.q ≤ s.U (fun p => x p.1) - s.L (fun p => x p.1)) :=
  ⟨fibre_I s x, fibre_insert s x⟩

end HibiLi.Proofs
