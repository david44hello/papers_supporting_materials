/-
LeeDiam/Sec6/ChainHelp.lean — Section 6.3 of paper 004 (short v1.50, sec_reverse.tex l. 190-274): helpers for the chain
side of `P_n`: the walk `A → M_A → {h} → M_B → B` (Theorem 6.13) and the attachment facts of Lemma 6.10.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Vertices
import LeeDiam.Defs.Walks
import LeeDiam.Defs.Pn
import LeeDiam.Defs.PnSets
import LeeDiam.Sec4.BandOrder
import LeeDiam.Sec6.PnOrder
import LeeDiam.Sec6.Structure

namespace LeeDiam.S6C

open PnSets PnOrder

variable {n : ℕ}

/-- The pair `{i, k}` for `i ≠ k`. -/
def pr (i k : Fin n) (hik : i ≠ k) : Pair n := ⟨{i, k}, Finset.card_pair hik⟩

theorem mem_pr_left (i k : Fin n) (hik : i ≠ k) : i ∈ (pr i k hik).1 := Finset.mem_insert_self _ _

theorem mem_pr_right (i k : Fin n) (hik : i ≠ k) : k ∈ (pr i k hik).1 :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- One step of a path inside `D`. -/
abbrev Step (D : Set (Pn n)) (u v : Pn n) : Prop := u ∈ D ∧ v ∈ D ∧ Comp u v

theorem comp_m_a (E : Pair n) (i : Fin n) (hi : i ∈ E.1) : Comp (PnElem.m E : Pn n) (PnElem.a i) :=
  Or.inl (lt_iff_ple.2 ⟨hi, fun e => by cases e⟩)

theorem comp_m'_b (E : Pair n) (j : Fin n) (hj : j ∈ E.1) : Comp (PnElem.m' E : Pn n) (PnElem.b j) :=
  Or.inl (lt_iff_ple.2 ⟨hj, fun e => by cases e⟩)

/-- `A △ M_A` is connected (`n ≥ 2`): `m_{ik}` joins `a_i` and `a_k`. -/
theorem conn_A_MA (hn : 2 ≤ n) : IsConnSet (symmDiff (tgtA n) (pairMinA n)) := by
  have memA : ∀ i, (PnElem.a i : Pn n) ∈ symmDiff (tgtA n) (pairMinA n) :=
    fun i => Set.mem_symmDiff.2 (Or.inl ⟨⟨i, rfl⟩, fun ⟨E, hE⟩ => by cases hE⟩)
  have memM : ∀ E, (PnElem.m E : Pn n) ∈ symmDiff (tgtA n) (pairMinA n) :=
    fun E => Set.mem_symmDiff.2 (Or.inr ⟨⟨E, rfl⟩, fun ⟨i, hi⟩ => by cases hi⟩)
  let i0 : Fin n := ⟨0, by omega⟩
  have pathA : ∀ i, Relation.ReflTransGen (Step (symmDiff (tgtA n) (pairMinA n))) (PnElem.a i0) (PnElem.a i) := by
    intro i
    by_cases hi : i0 = i
    · rw [hi]
    · exact Relation.ReflTransGen.head ⟨memA i0, memM (pr i0 i hi), Or.symm (comp_m_a _ i0 (mem_pr_left _ _ hi))⟩
        (Relation.ReflTransGen.single ⟨memM _, memA i, comp_m_a _ i (mem_pr_right _ _ hi)⟩)
  refine S4.isConnSet_of_rtg (memA i0) fun y hy => ?_
  rcases Set.mem_symmDiff.1 hy with ⟨⟨i, rfl⟩, -⟩ | ⟨⟨E, rfl⟩, -⟩
  · exact pathA i
  · obtain ⟨i, hi⟩ := pair_nonempty E
    exact (pathA i).tail ⟨memA i, memM E, Or.symm (comp_m_a E i hi)⟩

/-- `M_B △ B` is connected (`n ≥ 2`). -/
theorem conn_MB_B (hn : 2 ≤ n) : IsConnSet (symmDiff (pairMinB n) (tgtB n)) := by
  have memB : ∀ j, (PnElem.b j : Pn n) ∈ symmDiff (pairMinB n) (tgtB n) :=
    fun j => Set.mem_symmDiff.2 (Or.inr ⟨⟨j, rfl⟩, fun ⟨E, hE⟩ => by cases hE⟩)
  have memM : ∀ E, (PnElem.m' E : Pn n) ∈ symmDiff (pairMinB n) (tgtB n) :=
    fun E => Set.mem_symmDiff.2 (Or.inl ⟨⟨E, rfl⟩, fun ⟨j, hj⟩ => by cases hj⟩)
  let j0 : Fin n := ⟨0, by omega⟩
  have pathB : ∀ j, Relation.ReflTransGen (Step (symmDiff (pairMinB n) (tgtB n))) (PnElem.b j0) (PnElem.b j) := by
    intro j
    by_cases hj : j0 = j
    · rw [hj]
    · exact Relation.ReflTransGen.head ⟨memB j0, memM (pr j0 j hj), Or.symm (comp_m'_b _ j0 (mem_pr_left _ _ hj))⟩
        (Relation.ReflTransGen.single ⟨memM _, memB j, comp_m'_b _ j (mem_pr_right _ _ hj)⟩)
  refine S4.isConnSet_of_rtg (memB j0) fun y hy => ?_
  rcases Set.mem_symmDiff.1 hy with ⟨⟨E, rfl⟩, -⟩ | ⟨⟨j, rfl⟩, -⟩
  · obtain ⟨j, hj⟩ := pair_nonempty E
    exact (pathB j).tail ⟨memB j, memM E, Or.symm (comp_m'_b E j hj)⟩
  · exact pathB j

/-- `M_A △ {h}` is connected: every `m_E` lies below `h`. -/
theorem conn_MA_h : IsConnSet (symmDiff (pairMinA n) {PnElem.h}) := by
  have memH : (PnElem.h : Pn n) ∈ symmDiff (pairMinA n) {PnElem.h} :=
    Set.mem_symmDiff.2 (Or.inr ⟨rfl, fun ⟨E, hE⟩ => by cases hE⟩)
  refine S4.isConnSet_of_rtg memH fun y hy => ?_
  rcases Set.mem_symmDiff.1 hy with ⟨⟨E, rfl⟩, hE⟩ | ⟨hyh, -⟩
  · exact Relation.ReflTransGen.single ⟨memH, hy, Or.inr (lt_of_le_of_ne (m_le_h E) (fun e => by cases e))⟩
  · rw [Set.mem_singleton_iff.1 hyh]

/-- `{h} △ M_B` is connected: every `m'_E` lies below `h`. -/
theorem conn_h_MB : IsConnSet (symmDiff {PnElem.h} (pairMinB n)) := by
  have memH : (PnElem.h : Pn n) ∈ symmDiff {PnElem.h} (pairMinB n) :=
    Set.mem_symmDiff.2 (Or.inl ⟨rfl, fun ⟨E, hE⟩ => by cases hE⟩)
  refine S4.isConnSet_of_rtg memH fun y hy => ?_
  rcases Set.mem_symmDiff.1 hy with ⟨hyh, -⟩ | ⟨⟨E, rfl⟩, hE⟩
  · rw [Set.mem_singleton_iff.1 hyh]
  · exact Relation.ReflTransGen.single ⟨memH, hy, Or.inr (lt_of_le_of_ne (m'_le_h E) (fun e => by cases e))⟩

theorem isAntichainSet_singleton (x : Pn n) : IsAntichainSet ({x} : Set (Pn n)) :=
  fun _ hu _ hv hne _ => hne (hu.trans hv.symm)

/-- Proof of Theorem 6.13 (sec_reverse l. 268-272): `A → M_A → {h} → M_B → B` is a walk. -/
theorem walk_6_13 (hn : 2 ≤ n) :
    IsWalkFromTo [tgtA n, pairMinA n, {PnElem.h}, pairMinB n, tgtB n] (tgtA n) (tgtB n) := by
  obtain ⟨hA, hB, -, hMA, hMB⟩ := sec6_antichains_proved n
  refine ⟨⟨by simp, ?_, ?_⟩, rfl, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro X (rfl | rfl | rfl | rfl | rfl)
    exacts [hA, hMA, isAntichainSet_singleton _, hMB, hB]
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨conn_A_MA hn, conn_MA_h, conn_h_MB, conn_MB_B hn⟩

/-! ### Lemma 6.10 (Attached elements) -/

theorem lamA_not_att (z : Pn n) (hz : z ∈ lamA n) (u : Pn n) (hu : u ∈ tgtB n) : ¬ Attached z u := by
  rcases hz with ((⟨E, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) <;> obtain ⟨j, rfl⟩ := hu <;>
    simp [Attached, comp_iff_ple, ple]

theorem lamB_not_att (z : Pn n) (hz : z ∈ lamB n) (u : Pn n) (hu : u ∈ tgtA n) : ¬ Attached z u := by
  rcases hz with ((⟨E, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) <;> obtain ⟨i, rfl⟩ := hu <;>
    simp [Attached, comp_iff_ple, ple]

theorem encard_pair_le (x y : Pn n) : ({x, y} : Set (Pn n)).encard ≤ 2 :=
  (Set.encard_insert_le _ _).trans (by rw [Set.encard_singleton]; rfl)

theorem encard_singleton_le (x : Pn n) : ({x} : Set (Pn n)).encard ≤ 2 := by
  rw [Set.encard_singleton]; norm_num

/-- Lemma 6.10 (ii), `A`-side: an element of `Z_B` is attached to at most two targets of `A`. -/
theorem att_A_le_two (z : Pn n) (hz : z ∈ zB n) : {u | u ∈ tgtA n ∧ Attached z u}.encard ≤ 2 := by
  rw [(sec6_ZA_proved n).2.2.2] at hz
  rcases hz with (((⟨E, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | rfl) | ⟨i, rfl⟩
  · obtain ⟨p, q, -, hE⟩ := Finset.card_eq_two.1 E.2
    refine (Set.encard_le_encard ?_).trans (encard_pair_le (PnElem.a p) (PnElem.a q))
    rintro u ⟨⟨l, rfl⟩, hatt⟩
    simp only [Attached, comp_iff_ple, ple, hE] at hatt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, PnElem.a.injEq]
    simpa using hatt
  · refine (Set.encard_le_encard ?_).trans (encard_singleton_le (PnElem.a i))
    rintro u ⟨⟨l, rfl⟩, hatt⟩
    simp only [Attached, comp_iff_ple, ple] at hatt
    simp only [Set.mem_singleton_iff, PnElem.a.injEq]
    simpa [eq_comm] using hatt
  · refine (Set.encard_le_encard ?_).trans (encard_singleton_le (PnElem.a i))
    rintro u ⟨⟨l, rfl⟩, hatt⟩
    simp only [Attached, comp_iff_ple, ple] at hatt
    simp only [Set.mem_singleton_iff, PnElem.a.injEq]
    simpa [eq_comm] using hatt
  · refine (Set.encard_le_encard ?_).trans (encard_singleton_le (PnElem.h))
    rintro u ⟨⟨l, rfl⟩, hatt⟩
    simp [Attached, comp_iff_ple, ple] at hatt
  · refine (Set.encard_le_encard ?_).trans (encard_singleton_le (PnElem.a i))
    rintro u ⟨⟨l, rfl⟩, hatt⟩
    simp only [Attached, comp_iff_ple, ple] at hatt
    simp only [Set.mem_singleton_iff, PnElem.a.injEq]
    simpa [eq_comm] using hatt

/-- Lemma 6.10 (ii), `B`-side: an element of `Z_A` is attached to at most two targets of `B`. -/
theorem att_B_le_two (z : Pn n) (hz : z ∈ zA n) : {u | u ∈ tgtB n ∧ Attached z u}.encard ≤ 2 := by
  rw [(sec6_ZA_proved n).2.2.1] at hz
  rcases hz with (((⟨E, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) | rfl) | ⟨j, rfl⟩
  · obtain ⟨p, q, -, hE⟩ := Finset.card_eq_two.1 E.2
    refine (Set.encard_le_encard ?_).trans (encard_pair_le (PnElem.b p) (PnElem.b q))
    rintro u ⟨⟨l, rfl⟩, hatt⟩
    simp only [Attached, comp_iff_ple, ple, hE] at hatt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, PnElem.b.injEq]
    simpa using hatt
  · refine (Set.encard_le_encard ?_).trans (encard_singleton_le (PnElem.b j))
    rintro u ⟨⟨l, rfl⟩, hatt⟩
    simp only [Attached, comp_iff_ple, ple] at hatt
    simp only [Set.mem_singleton_iff, PnElem.b.injEq]
    simpa [eq_comm] using hatt
  · refine (Set.encard_le_encard ?_).trans (encard_singleton_le (PnElem.b j))
    rintro u ⟨⟨l, rfl⟩, hatt⟩
    simp only [Attached, comp_iff_ple, ple] at hatt
    simp only [Set.mem_singleton_iff, PnElem.b.injEq]
    simpa [eq_comm] using hatt
  · refine (Set.encard_le_encard ?_).trans (encard_singleton_le (PnElem.h))
    rintro u ⟨⟨l, rfl⟩, hatt⟩
    simp [Attached, comp_iff_ple, ple] at hatt
  · refine (Set.encard_le_encard ?_).trans (encard_singleton_le (PnElem.b j))
    rintro u ⟨⟨l, rfl⟩, hatt⟩
    simp only [Attached, comp_iff_ple, ple] at hatt
    simp only [Set.mem_singleton_iff, PnElem.b.injEq]
    simpa [eq_comm] using hatt

/-- Lemma 6.10 (i), `B`-side: `B` and the sets of types (D'), (L') lie in `Λ_B`. -/
theorem sub_lamB (Y : Set (Pn n)) (hY : Y = tgtB n ∨ IsTypeD' n Y ∨ IsTypeL' n Y) : Y ⊆ lamB n := by
  have hB : tgtB n ⊆ lamB n := Set.subset_union_right
  rcases hY with rfl | ⟨j, rfl⟩ | ⟨R, S, -, -, -, hS, -, rfl⟩
  · exact hB
  · exact Set.sdiff_subset.trans hB
  · exact Set.union_subset (Set.sdiff_subset.trans hB) (hS.trans Set.subset_union_left)

/-- Lemma 6.10 (i), `A`-side. -/
theorem sub_lamA (X : Set (Pn n)) (hX : X = tgtA n ∨ IsTypeD n X ∨ IsTypeL n X) : X ⊆ lamA n := by
  have hA : tgtA n ⊆ lamA n := Set.subset_union_right
  rcases hX with rfl | ⟨i, rfl⟩ | ⟨R, S, -, -, -, hS, -, rfl⟩
  · exact hA
  · exact Set.sdiff_subset.trans hA
  · exact Set.union_subset (Set.sdiff_subset.trans hA) (hS.trans Set.subset_union_left)

theorem lem_6_10 (n : ℕ) :
    (∀ Y : Set (Pn n), (Y = tgtB n ∨ IsTypeD' n Y ∨ IsTypeL' n Y) →
      Y ⊆ lamB n ∧ ∀ z ∈ Y, ∀ u ∈ tgtA n, ¬ Attached z u) ∧
    (∀ z ∈ zB n, (∀ z' ∈ insert z (tgtB n), z' ≠ z → ∀ u ∈ tgtA n, ¬ Attached z' u) ∧
      {u | u ∈ tgtA n ∧ Attached z u}.encard ≤ 2) ∧
    (∀ (j : Fin n) (S : Set (Pn n)), (S = {PnElem.w' j} ∨ (S.Nonempty ∧ S ⊆ {x | ∃ i, x = PnElem.t i j})) →
      ((tgtB n \ {PnElem.b j}) ∪ S) ∩ tgtA n = ∅ ∧
      (∀ z ∈ (tgtB n \ {PnElem.b j}) ∪ S, ∀ u ∈ tgtA n, Comp z u → ∃ p, z = PnElem.t p j ∧ z ∈ S) ∧
      ∀ p : Fin n, ∀ u ∈ tgtA n, Comp (PnElem.t p j : Pn n) u → u = PnElem.a p) := by
  refine ⟨fun Y hY => ⟨sub_lamB Y hY, fun z hz u hu => lamB_not_att z (sub_lamB Y hY hz) u hu⟩,
    fun z hz => ⟨fun z' hz' hne u hu => ?_, att_A_le_two z hz⟩, fun j S hS => ⟨?_, ?_, ?_⟩⟩
  · rcases hz' with rfl | hz'
    · exact absurd rfl hne
    · exact lamB_not_att z' (Set.subset_union_right hz') u hu
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro (⟨⟨l, rfl⟩, -⟩ | hxS) ⟨i, hi⟩
    · cases hi
    · rcases hS with rfl | ⟨-, hS⟩
      · rw [Set.mem_singleton_iff.1 hxS] at hi; cases hi
      · obtain ⟨p, rfl⟩ := hS hxS; cases hi
  · rintro z (⟨⟨l, rfl⟩, -⟩ | hzS) u ⟨i, rfl⟩ hc
    · simp [comp_iff_ple, ple] at hc
    · rcases hS with rfl | ⟨-, hS⟩
      · rw [Set.mem_singleton_iff.1 hzS] at hc; simp [comp_iff_ple, ple] at hc
      · obtain ⟨p, rfl⟩ := hS hzS; exact ⟨p, rfl, hzS⟩
  · rintro p u ⟨i, rfl⟩ hc
    simp only [comp_iff_ple, ple] at hc
    simp only [PnElem.a.injEq]
    simpa [eq_comm] using hc

theorem lem_6_10_swap (n : ℕ) :
    (∀ X : Set (Pn n), (X = tgtA n ∨ IsTypeD n X ∨ IsTypeL n X) →
      X ⊆ lamA n ∧ ∀ z ∈ X, ∀ u ∈ tgtB n, ¬ Attached z u) ∧
    (∀ z ∈ zA n, (∀ z' ∈ insert z (tgtA n), z' ≠ z → ∀ u ∈ tgtB n, ¬ Attached z' u) ∧
      {u | u ∈ tgtB n ∧ Attached z u}.encard ≤ 2) ∧
    (∀ (i : Fin n) (S : Set (Pn n)), (S = {PnElem.w i} ∨ (S.Nonempty ∧ S ⊆ {x | ∃ j, x = PnElem.t i j})) →
      ((tgtA n \ {PnElem.a i}) ∪ S) ∩ tgtB n = ∅ ∧
      (∀ z ∈ (tgtA n \ {PnElem.a i}) ∪ S, ∀ u ∈ tgtB n, Comp z u → ∃ q, z = PnElem.t i q ∧ z ∈ S) ∧
      ∀ q : Fin n, ∀ u ∈ tgtB n, Comp (PnElem.t i q : Pn n) u → u = PnElem.b q) := by
  refine ⟨fun X hX => ⟨sub_lamA X hX, fun z hz u hu => lamA_not_att z (sub_lamA X hX hz) u hu⟩,
    fun z hz => ⟨fun z' hz' hne u hu => ?_, att_B_le_two z hz⟩, fun i S hS => ⟨?_, ?_, ?_⟩⟩
  · rcases hz' with rfl | hz'
    · exact absurd rfl hne
    · exact lamA_not_att z' (Set.subset_union_right hz') u hu
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro (⟨⟨l, rfl⟩, -⟩ | hxS) ⟨j, hj⟩
    · cases hj
    · rcases hS with rfl | ⟨-, hS⟩
      · rw [Set.mem_singleton_iff.1 hxS] at hj; cases hj
      · obtain ⟨q, rfl⟩ := hS hxS; cases hj
  · rintro z (⟨⟨l, rfl⟩, -⟩ | hzS) u ⟨j, rfl⟩ hc
    · simp [comp_iff_ple, ple] at hc
    · rcases hS with rfl | ⟨-, hS⟩
      · rw [Set.mem_singleton_iff.1 hzS] at hc; simp [comp_iff_ple, ple] at hc
      · obtain ⟨q, rfl⟩ := hS hzS; exact ⟨q, rfl, hzS⟩
  · rintro q u ⟨j, rfl⟩ hc
    simp only [comp_iff_ple, ple] at hc
    simp only [PnElem.b.injEq]
    simpa [eq_comm] using hc

end LeeDiam.S6C
