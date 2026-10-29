/-
Cereceda/Bip/Basic.lean — Section 3 of the paper (short v3.90): sequence tools, greedy facts, Lemma 3.2, the kinds of
vertices, Lemma 3.3, Lemma 3.4 (upper middle).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Lemma 3.4 (any order of ties) is proved by one general "sweep" lemma (`Bip.isSeq_sweep`): moving the vertices of a list
in turn to their target colours is a sequence when every earlier neighbour's target and every later neighbour's
current colour differ from the target of the moving vertex.
-/
import Cereceda.Defs.Instance
import Cereceda.Defs.Bipartite

namespace Cereceda

open Finset

namespace Bip

variable {W : Type} [DecidableEq W]

section SeqTools

variable (H : SimpleGraph W) (A : W → Finset (Fin 4))

theorem isSeq_append_iff : ∀ (ms ms' : List (W × Fin 4)) (c c'' : W → Fin 4),
    IsSeq H A c (ms ++ ms') c'' ↔ ∃ c', IsSeq H A c ms c' ∧ IsSeq H A c' ms' c''
  | [], ms', c, c'' => by simp [IsSeq]
  | m :: ms, ms', c, c'' => by
    simp only [List.cons_append, IsSeq]
    rw [isSeq_append_iff ms ms']
    constructor
    · rintro ⟨hm, c', h1, h2⟩
      exact ⟨c', ⟨hm, h1⟩, h2⟩
    · rintro ⟨c', ⟨hm, h1⟩, h2⟩
      exact ⟨hm, c', h1, h2⟩

theorem isSeq_append {ms ms' : List (W × Fin 4)} {c c' c'' : W → Fin 4}
    (h1 : IsSeq H A c ms c') (h2 : IsSeq H A c' ms' c'') : IsSeq H A c (ms ++ ms') c'' :=
  (isSeq_append_iff H A ms ms' c c'').2 ⟨c', h1, h2⟩

/-- The sweep: the vertices of the duplicate-free list `l` move in turn from `c` to their targets `t` (a vertex whose
colour is already its target does not move). It is a sequence if every target is allowed, a neighbour outside `l`
never has the target, and for `a` before `b` in `l` with `a ~ b`: `t a ≠ t b` and `c b ≠ t a`. -/
theorem isSeq_sweep (t : W → Fin 4) :
    ∀ (l : List W) (c : W → Fin 4), l.Nodup →
      (∀ v ∈ l, t v ∈ A v) →
      (∀ v ∈ l, ∀ u, u ∉ l → H.Adj v u → c u ≠ t v) →
      l.Pairwise (fun a b => H.Adj a b → t a ≠ t b ∧ c b ≠ t a) →
      IsSeq H A c ((l.filter fun v => c v ≠ t v).map fun v => (v, t v)) (fun w => if w ∈ l then t w else c w)
  | [], c, _, _, _, _ => by simp [IsSeq]
  | v :: l, c, hnd, hA, hout, hpw => by
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hpw
    have ih := isSeq_sweep t l (Function.update c v (t v)) hnd.2 (fun w hw => hA w (by simp [hw])) ?_ ?_
    · have hfilt : l.filter (fun w => Function.update c v (t v) w ≠ t w) = l.filter (fun w => c w ≠ t w) := by
        apply List.filter_congr
        intro w hw
        have hwv : w ≠ v := fun h => hnd.1 (h ▸ hw)
        simp [Function.update_of_ne hwv]
      have hfin : (fun w => if w ∈ l then t w else Function.update c v (t v) w) =
          (fun w => if w ∈ v :: l then t w else c w) := by
        funext w
        by_cases hw : w = v
        · rw [hw]
          simp [hnd.1]
        · simp [hw]
      rw [hfilt, hfin] at ih
      by_cases hmv : c v = t v
      · rw [List.filter_cons_of_neg (by simpa using hmv)]
        have hc : Function.update c v (t v) = c := by
          rw [← hmv]
          exact Function.update_eq_self v c
        rw [hc] at ih
        exact ih
      · rw [List.filter_cons_of_pos (by simpa using hmv)]
        simp only [List.map_cons, IsSeq]
        refine ⟨⟨fun h => hmv h.symm, hA v (by simp), ?_⟩, ih⟩
        intro u hu
        by_cases hul : u ∈ l
        · exact (hpw.1 u hul hu).2
        · have huv : u ≠ v := by
            rintro rfl
            exact H.irrefl hu
          exact hout v (by simp) u (by simp [huv, hul]) hu
    · intro w hw u hul hadj
      by_cases huv : u = v
      · rw [huv, Function.update_self]
        rw [huv] at hadj
        exact (hpw.1 w hw hadj.symm).1
      · rw [Function.update_of_ne huv]
        exact hout w (by simp [hw]) u (by simp [huv, hul]) hadj
    · refine List.Pairwise.imp_of_mem ?_ hpw.2
      intro a b _ hb hab hadj
      have hbv : b ≠ v := fun h => hnd.1 (h ▸ hb)
      rw [Function.update_of_ne hbv]
      exact hab hadj

theorem movesOf_append (ms ms' : List (W × Fin 4)) (v : W) :
    movesOf (ms ++ ms') v = movesOf ms v + movesOf ms' v := by
  simp [movesOf, List.countP_append]

theorem movesOf_map (t : W → Fin 4) (l : List W) (hnd : l.Nodup) (v : W) :
    movesOf (l.map fun w => (w, t w)) v = if v ∈ l then 1 else 0 := by
  unfold movesOf
  rw [List.countP_map]
  have : List.countP ((fun m : W × Fin 4 => decide (m.1 = v)) ∘ fun w => (w, t w)) l = l.count v := by
    rw [List.count_eq_countP]
    simp only [Function.comp_def]
    congr 1
  rw [this]
  by_cases hv : v ∈ l
  · simp [hv, List.count_eq_one_of_mem hnd hv]
  · simp [hv, List.count_eq_zero.2 hv]

theorem movesOf_filter_map (t : W → Fin 4) (p : W → Bool) (l : List W) (hnd : l.Nodup) (v : W) :
    movesOf ((l.filter p).map fun w => (w, t w)) v = if v ∈ l ∧ p v = true then 1 else 0 := by
  rw [movesOf_map t _ (hnd.filter p) v]
  simp [List.mem_filter]

theorem movesOf_filter_map_le (t : W → Fin 4) (p : W → Bool) (l : List W) (hnd : l.Nodup) (v : W) :
    movesOf ((l.filter p).map fun w => (w, t w)) v ≤ 1 := by
  rw [movesOf_filter_map t p l hnd v]
  split_ifs <;> omega

/-- The length of a list of moves is the sum over all vertices of their numbers of moves. -/
theorem length_eq_sum_movesOf [Fintype W] : ∀ ms : List (W × Fin 4), ms.length = ∑ v, movesOf ms v
  | [] => by simp [movesOf]
  | m :: ms => by
    have ih := length_eq_sum_movesOf ms
    have hcons : ∀ v, movesOf (m :: ms) v = movesOf ms v + if m.1 = v then 1 else 0 := by
      intro v
      simp only [movesOf, List.countP_cons]
      simp
    simp only [hcons, Finset.sum_add_distrib, List.length_cons, ih]
    simp

end SeqTools

variable [Fintype W]

section Greedy

theorem x_ne_zero (I : Instance W) : I.x ≠ 0 :=
  ne_of_gt (lt_of_le_of_lt (Fin.zero_le I.g) I.g_lt_x)

theorem x_mem_L (I : Instance W) : I.x ∈ I.L I.sink := by
  rw [I.L_sink]
  simp

theorem g_mem_L (I : Instance W) : I.g ∈ I.L I.sink := by
  rw [I.L_sink]
  simp

/-- A greedy colouring takes, at every vertex, a colour of its list (the sink colour `c0` is in the sink's list). -/
theorem greedy_mem_L (I : Instance W) {c0 : Fin 4} {c : W → Fin 4} (hc : I.IsGreedy c0 c)
    (h0 : c0 ∈ I.L I.sink) (v : W) : c v ∈ I.L v := by
  by_cases hv : v = I.sink
  · rw [hv, hc.1]
    exact h0
  · exact (hc.2 v hv).1

theorem ne_sink_of_mem_out {I : Instance W} {a b : W} (hb : b ∈ I.out a) : a ≠ I.sink := by
  intro ha
  rw [ha, I.sink_out] at hb
  simp at hb

theorem adj_of_mem_out {I : Instance W} {u v : W} (hu : u ∈ I.out v) : I.graph.Adj v u := by
  simp only [Skeleton.graph, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl hu⟩
  intro h
  rw [h] at hu
  exact absurd (I.out_before u u hu) (lt_irrefl _)

theorem mem_out_of_adj {I : Instance W} {u v : W} (h : I.graph.Adj u v) : v ∈ I.out u ∨ u ∈ I.out v := by
  simp only [Skeleton.graph, SimpleGraph.fromRel_adj] at h
  exact h.2

/-- A greedy colouring is proper on the graph of the instance. -/
theorem greedy_proper (I : Instance W) {c0 : Fin 4} {c : W → Fin 4} (hc : I.IsGreedy c0 c) :
    IsProperFn I.graph c := by
  intro u v huv
  rcases mem_out_of_adj huv with h | h
  · have := (hc.2 u (ne_sink_of_mem_out h)).2.1
    intro heq
    exact this (Finset.mem_image.2 ⟨v, h, heq.symm⟩)
  · have := (hc.2 v (ne_sink_of_mem_out h)).2.1
    intro heq
    exact this (Finset.mem_image.2 ⟨u, h, heq⟩)

/-- A smaller colour of the list than the greedy one is held by an out-neighbour. -/
theorem greedy_below (I : Instance W) {c0 : Fin 4} {c : W → Fin 4} (hc : I.IsGreedy c0 c) {v : W}
    (hv : v ≠ I.sink) {z : Fin 4} (hz : z ∈ I.L v) (hlt : z < c v) : ∃ u ∈ I.out v, c u = z :=
  Finset.mem_image.1 ((hc.2 v hv).2.2 z hz hlt)

/-- No out-neighbour has the greedy colour. -/
theorem greedy_out_ne (I : Instance W) {c0 : Fin 4} {c : W → Fin 4} (hc : I.IsGreedy c0 c) {v u : W}
    (hu : u ∈ I.out v) : c u ≠ c v := by
  intro h
  exact (hc.2 v (ne_sink_of_mem_out hu)).2.1 (Finset.mem_image.2 ⟨u, hu, h⟩)

/-- Lemma 3.2 for one greedy colouring: a vertex other than the sink never gets the colour 3. -/
theorem greedy_ne_three (I : Instance W) {c0 : Fin 4} {c : W → Fin 4} (hc : I.IsGreedy c0 c) {v : W}
    (hv : v ≠ I.sink) : c v ≠ 3 := by
  intro h3
  have hl := hc.2 v hv
  have hsub : I.L v ⊆ insert 3 ((I.out v).image c) := by
    intro z hz
    have hz3 : z = 3 ∨ z < 3 := by
      have key : ∀ z : Fin 4, z = 3 ∨ z < 3 := by decide
      exact key z
    rcases hz3 with heq | hlt
    · rw [heq]
      exact mem_insert_self _ _
    · exact mem_insert_of_mem (hl.2.2 z hz (h3 ▸ hlt))
  have h1 := card_le_card hsub
  have h2 := card_insert_le (3 : Fin 4) ((I.out v).image c)
  have h3' := card_image_le (s := I.out v) (f := c)
  have h4 := I.L_card v
  omega

theorem le_two_of_ne_three {y : Fin 4} (h : y ≠ 3) : y ≤ 2 := by
  revert y
  decide

end Greedy

end Bip

/-- **Lemma 3.2** (lem:s1), v3.90 l. 410-411: for every vertex `v ≠ s`, `α(v), β(v) ∈ {0,1,2}`. -/
theorem lem_3_2_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (v : W) (hv : v ≠ I.sink) : α v ≤ 2 ∧ β v ≤ 2 :=
  ⟨Bip.le_two_of_ne_three (Bip.greedy_ne_three I hα hv), Bip.le_two_of_ne_three (Bip.greedy_ne_three I hβ hv)⟩

/-- Section 3, v3.90 l. 418-421 (with `g = 0`): the kinds of vertices. -/
theorem sec3_kinds_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg0 : I.g = 0)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    (∀ v, v ≠ I.sink →
      (IsFixed α β v ∨ IsLowSwapper α β v ∨ IsHighMover α β v) ∧
      ¬ (IsFixed α β v ∧ IsLowSwapper α β v) ∧ ¬ (IsFixed α β v ∧ IsHighMover α β v) ∧
      ¬ (IsLowSwapper α β v ∧ IsHighMover α β v)) ∧
    (I.x = 1 → IsLowSwapper α β I.sink) ∧ (I.x = 2 → IsHighMover α β I.sink) ∧
    (I.x = 3 → ¬ IsFixed α β I.sink ∧ ¬ IsLowSwapper α β I.sink ∧ ¬ IsHighMover α β I.sink) ∧
    IsJoiner α β I.sink := by
  have hs : α I.sink = I.x ∧ β I.sink = 0 := ⟨hα.1, hβ.1.trans hg0⟩
  have hx0 := Bip.x_ne_zero I
  refine ⟨fun v hv => ?_, ?_⟩
  · have h := lem_3_2_proved I α β hα hβ v hv
    unfold IsFixed IsLowSwapper IsHighMover
    revert h
    generalize α v = a
    generalize β v = b
    revert a b
    decide
  · unfold IsFixed IsLowSwapper IsHighMover IsJoiner
    rw [hs.1, hs.2]
    revert hx0
    generalize I.x = y
    revert y
    decide

/-- **Lemma 3.3** (lem:s3), v3.90 l. 424-425: every leaver has an out-neighbour that is a joiner, and every joiner other
than `s` has an out-neighbour that is a leaver. -/
theorem lem_3_3_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    (∀ v, IsLeaver α β v → ∃ u ∈ I.out v, IsJoiner α β u) ∧
    (∀ v, v ≠ I.sink → IsJoiner α β v → ∃ u ∈ I.out v, IsLeaver α β u) := by
  refine ⟨fun v ⟨h0, hb⟩ => ?_, fun v hv ⟨ha, h0⟩ => ?_⟩
  · have hv : v ≠ I.sink := by
      intro h
      rw [h, hα.1] at h0
      exact Bip.x_ne_zero I h0
    have h0L : (0 : Fin 4) ∈ I.L v := h0 ▸ (hα.2 v hv).1
    obtain ⟨u, hu, hβu⟩ := Bip.greedy_below I hβ hv h0L (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hb))
    refine ⟨u, hu, fun hαu => Bip.greedy_out_ne I hα hu (hαu.trans h0.symm), hβu⟩
  · have h0L : (0 : Fin 4) ∈ I.L v := h0 ▸ (hβ.2 v hv).1
    obtain ⟨u, hu, hαu⟩ := Bip.greedy_below I hα hv h0L (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm ha))
    refine ⟨u, hu, hαu, fun hβu => Bip.greedy_out_ne I hβ hu (hβu.trans h0.symm)⟩

/-- **Lemma 3.4** (lem:um), v3.90 l. 433-438: the upper-middle sequence, for any order of the ties. -/
theorem lem_3_4_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (α β μ : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (hμ : IsProperFn I.graph μ) (hμL : ∀ v, μ v ∈ I.L v)
    (hμα : ∀ v, α v ≤ μ v) (hμβ : ∀ v, β v ≤ μ v) (hμs : μ I.sink = I.x)
    (ord1 ord2 : List W) (h1 : ord1.Nodup ∧ ∀ v, v ∈ ord1) (h2 : ord2.Nodup ∧ ∀ v, v ∈ ord2)
    (hs1 : ord1.Pairwise (fun u v => μ v ≤ μ u)) (hs2 : ord2.Pairwise (fun u v => μ u ≤ μ v)) :
    I.IsSeq α ((ord1.filter (fun v => α v ≠ μ v)).map (fun v => (v, μ v)) ++
        (ord2.filter (fun v => μ v ≠ β v)).map (fun v => (v, β v))) β ∧
      (∀ v, movesOf ((ord1.filter (fun v => α v ≠ μ v)).map (fun v => (v, μ v)) ++
        (ord2.filter (fun v => μ v ≠ β v)).map (fun v => (v, β v))) v ≤ 2) ∧
      movesOf ((ord1.filter (fun v => α v ≠ μ v)).map (fun v => (v, μ v)) ++
        (ord2.filter (fun v => μ v ≠ β v)).map (fun v => (v, β v))) I.sink = 1 := by
  have hβp := Bip.greedy_proper I hβ
  have ph1 := Bip.isSeq_sweep I.graph I.L μ ord1 α h1.1 (fun v _ => hμL v)
    (fun v _ u hu _ => absurd (h1.2 u) hu) (hs1.imp fun {a b} hab hadj => by
      have hne := hμ a b hadj
      have hlt : μ b < μ a := lt_of_le_of_ne hab (Ne.symm hne)
      exact ⟨hne, ne_of_lt (lt_of_le_of_lt (hμα b) hlt)⟩)
  have ph2 := Bip.isSeq_sweep I.graph I.L β ord2 μ h2.1 (fun v _ => Bip.greedy_mem_L I hβ (Bip.g_mem_L I) v)
    (fun v _ u hu _ => absurd (h2.2 u) hu) (hs2.imp fun {a b} hab hadj => by
      have hne := hμ a b hadj
      have hlt : μ a < μ b := lt_of_le_of_ne hab hne
      exact ⟨hβp a b hadj, ne_of_gt (lt_of_le_of_lt (hμβ a) hlt)⟩)
  have e1 : (fun w => if w ∈ ord1 then μ w else α w) = μ := by
    funext w
    simp [h1.2 w]
  have e2 : (fun w => if w ∈ ord2 then β w else μ w) = β := by
    funext w
    simp [h2.2 w]
  rw [e1] at ph1
  rw [e2] at ph2
  refine ⟨Bip.isSeq_append I.graph I.L ph1 ph2, fun v => ?_, ?_⟩
  · rw [Bip.movesOf_append]
    have a1 := Bip.movesOf_filter_map_le μ (fun v => decide (α v ≠ μ v)) ord1 h1.1 v
    have a2 := Bip.movesOf_filter_map_le β (fun v => decide (μ v ≠ β v)) ord2 h2.1 v
    omega
  · rw [Bip.movesOf_append, Bip.movesOf_filter_map μ _ ord1 h1.1, Bip.movesOf_filter_map β _ ord2 h2.1]
    have hne : I.x ≠ I.g := ne_of_gt I.g_lt_x
    simp [h1.2, h2.2, hα.1, hβ.1, hμs, hne]

end Cereceda
