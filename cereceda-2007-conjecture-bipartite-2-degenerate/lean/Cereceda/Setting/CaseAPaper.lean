/-
Cereceda/Setting/CaseAPaper.lean — the paper's own route of Lemma 2.3 (heights on T, |E(v)| <= 4, Lemma 2.4; short v3.90
l. 307-346 and 404).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof plan. For a greedy colouring `c`, the colour heights `hcol`: `1 ↦ 1`, `2 ↦ 2`, `3 ↦ 0` (and `0 ↦ 0`) form a height of
`c` on the forest `F` (only the sink can be on `3`, and its children are on `1`). Every other height differs from it by a
constant on `T` (`Heights.diff_walk`), which gives the offsets; parity along walks gives `E` even. For the sequence we
apply `Heights.main` (Lemma 2.4 on any graph) to the subtype `T` with the lists `L v \ {0}`, and extend by `α` outside `T`
(there `α = β`, and the neighbours of `T` outside `T` are on `0`).
-/
import Cereceda.Defs.Instance
import Cereceda.Setting.CaseA
import Cereceda.Setting.Heights

namespace Cereceda

open Finset

namespace CaseAPaper

open CaseA Heights

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ### Colour heights -/

/-- The colour height: `1 ↦ 1`, `2 ↦ 2`, `3 ↦ 0`, `0 ↦ 0`. -/
def hcol (y : Fin 4) : ℤ := if y = 1 then 1 else if y = 2 then 2 else 0

lemma hcol_dvd (y : Fin 4) : (3 : ℤ) ∣ hcol y - y.val := by
  fin_cases y <;> decide

lemma hcol_one : hcol 1 = 1 := by decide
lemma hcol_two : hcol 2 = 2 := by decide
lemma hcol_three : hcol 3 = 0 := by decide

/-- On an edge between colours `a ≠ b` (both not `0`, and `3` only next to `1`) the colour heights differ by one. -/
lemma hcol_step : ∀ a b : Fin 4, a ≠ b → a ≠ 0 → b ≠ 0 → (a = 3 → b = 1) → (b = 3 → a = 1) →
    hcol a = hcol b + 1 ∨ hcol b = hcol a + 1 := by
  decide

omit [Fintype W] [DecidableEq W] in
lemma isHt_add_const {H : SimpleGraph W} {c : W → Fin 4} {h : W → ℤ} (hh : IsHt H c h) (k : ℤ) :
    IsHt H c (fun v => h v + 3 * k) :=
  ⟨fun v => by have := hh.1 v; show (3 : ℤ) ∣ h v + 3 * k - _; omega,
    fun u v huv => by have := hh.2 u v huv; show h u + 3 * k = h v + 3 * k + 1 ∨ h v + 3 * k = h u + 3 * k + 1; omega⟩

omit [Fintype W] [DecidableEq W] in
lemma isHt_mono {H H' : SimpleGraph W} (hle : H ≤ H') {c : W → Fin 4} {h : W → ℤ} (hh : IsHt H' c h) :
    IsHt H c h :=
  ⟨hh.1, fun u v huv => hh.2 u v (hle huv)⟩

omit [Fintype W] [DecidableEq W] in
/-- Two heights (of possibly different colourings) change by `±1` along every edge: their differences agree mod 2. -/
lemma parity_walk {H : SimpleGraph W} {c c' : W → Fin 4} {h h' : W → ℤ} (hh : IsHt H c h) (hh' : IsHt H c' h')
    {u v : W} (p : H.Walk u v) : (2 : ℤ) ∣ (h' u - h u) - (h' v - h v) := by
  induction p with
  | nil => simp
  | cons hadj p ih =>
    have h1 := hh.2 _ _ hadj
    have h2 := hh'.2 _ _ hadj
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega

section Greedy

variable {I : Instance W} {c0 : Fin 4} {c : W → Fin 4}

lemma adj_of_mem_out {v u : W} (hu : u ∈ I.out v) : I.graph.Adj v u :=
  adj_iff.2 ⟨fun h => by subst h; exact absurd (I.out_before v v hu) (lt_irrefl _), Or.inl hu⟩

/-- A vertex `u ≠ s` not on `0` whose out-neighbour `p` is on neither `0` nor `1` is on `1`. -/
lemma child_one (hc : I.IsGreedy c0 c) {u p : W} (hu : u ≠ I.sink) (hcu : c u ≠ 0) (hp : p ∈ I.out u)
    (hcp : c p ≠ 0) (hcp1 : c p ≠ 1) : c u = 1 := by
  have h1L := parent_lists hc hu hcu hp hcp 1 (by decide)
  by_contra hne
  obtain ⟨w, hw, hw1⟩ := mem_image.1 ((hc.2 u hu).2.2 1 h1L (by omega))
  have hwp : w ≠ p := by rintro rfl; exact hcp1 hw1
  have := parent_others_zero hc hu hcu hp hcp w hw hwp
  rw [hw1] at this
  exact absurd this (by decide)

/-- An end of an edge of `F` on `3` is the sink, and the other end is on `1`. -/
lemma three_nbr (hc : I.IsGreedy c0 c) {a b : W} (hab : I.graph.Adj a b) (ha0 : c a ≠ 0) (hb0 : c b ≠ 0)
    (ha3 : c a = 3) : c b = 1 := by
  have has : a = I.sink := by
    by_contra h
    exact greedy_ne_three hc h ha3
  subst has
  have hsb : I.sink ∈ I.out b := by
    rcases (adj_iff.1 hab).2 with h | h
    · rw [I.sink_out] at h
      exact absurd h (Finset.notMem_empty b)
    · exact h
  exact child_one hc (ne_sink_of_mem_out hsb) hb0 hsb ha0 (by rw [ha3]; decide)

/-- The colour heights are a height of a greedy colouring on its forest `F`. -/
lemma hcol_isHt (hc : I.IsGreedy c0 c) : IsHt (I.fGraph c) c (fun v => hcol (c v)) := by
  refine ⟨fun v => hcol_dvd (c v), fun u v huv => ?_⟩
  obtain ⟨hadj, hu0, hv0⟩ := huv
  exact hcol_step (c u) (c v) (greedy_proper hc hadj) hu0 hv0 (three_nbr hc hadj hu0 hv0)
    (three_nbr hc hadj.symm hv0 hu0)

/-- Along a walk in `F` the colour stays off `0`. -/
lemma ne_zero_of_walk {u v : W} (p : (I.fGraph c).Walk u v) (hu : c u ≠ 0) : c v ≠ 0 := by
  induction p with
  | nil => exact hu
  | cons hadj p ih =>
    obtain ⟨-, -, hw⟩ := hadj
    exact ih hw

lemma mem_L (hc : I.IsGreedy c0 c) (h0 : c0 ∈ I.L I.sink) (v : W) : c v ∈ I.L v := by
  rcases eq_or_ne v I.sink with rfl | hv
  · rw [hc.1]
    exact h0
  · exact (hc.2 v hv).1

end Greedy

/-! ### The tree `T` of `F` containing the sink -/

section Tree

variable {I : Instance W} {α β : W → Fin 4}

lemma fGraph_eq (hg : 0 < I.g) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) : I.fGraph α = I.fGraph β := by
  ext u v
  exact and_congr_right fun _ =>
    and_congr (not_congr (zero_iff hg hα hβ u)) (not_congr (zero_iff hg hα hβ v))

lemma x_ne_zero (I : Instance W) : I.x ≠ 0 := by
  have := I.g_lt_x
  omega

lemma ne_zero_T (hα : I.IsGreedy I.x α) {v : W} (hv : (I.fGraph α).Reachable I.sink v) : α v ≠ 0 := by
  obtain ⟨p⟩ := hv
  exact ne_zero_of_walk p (by rw [hα.1]; exact x_ne_zero I)

/-- A neighbour (in the instance graph) of a vertex of `T` that is not in `T` is on `0`. -/
lemma zero_nbr_T (hα : I.IsGreedy I.x α) {v u : W} (hv : (I.fGraph α).Reachable I.sink v)
    (hvu : I.graph.Adj v u) (hu : ¬ (I.fGraph α).Reachable I.sink u) : α u = 0 := by
  by_contra hαu
  exact hu (hv.trans (SimpleGraph.Adj.reachable ⟨hvu, ne_zero_T hα hv, hαu⟩))

/-- Outside `T`, `α = β` (induction along the instance order). -/
lemma eq_outside (hg : 0 < I.g) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    ∀ v, ¬ (I.fGraph α).Reachable I.sink v → α v = β v := by
  suffices h : ∀ n, ∀ v, I.rank v = n → ¬ (I.fGraph α).Reachable I.sink v → α v = β v from
    fun v => h _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hvT
    have hvs : v ≠ I.sink := by
      rintro rfl
      exact hvT (SimpleGraph.Reachable.refl _)
    by_cases hα0 : α v = 0
    · rw [hα0, (zero_iff hg hα hβ v).1 hα0]
    · have hno : ∀ u ∈ I.out v, α u = β u := by
        intro u hu
        by_cases hαu : α u = 0
        · rw [hαu, (zero_iff hg hα hβ u).1 hαu]
        · refine ih (I.rank u) (hn ▸ I.out_before v u hu) u rfl fun huT => hvT (huT.trans ?_)
          exact SimpleGraph.Adj.reachable ⟨(adj_of_mem_out hu).symm, hαu, hα0⟩
      have h1 := hα.2 v hvs
      rw [image_congr hno] at h1
      exact leastFree_unique h1 (hβ.2 v hvs)

/-- A parent arc: `b ∈ N⁺(a)` and `b` is not on `0`. -/
def Par (I : Instance W) (α : W → Fin 4) (a b : W) : Prop := b ∈ I.out a ∧ α b ≠ 0

/-- Along a walk in `F`, "reaches the sink by parent arcs" is preserved (each vertex has at most one parent). -/
lemma anc_walk (hα : I.IsGreedy I.x α) {u v : W} (p : (I.fGraph α).Walk u v) :
    Relation.ReflTransGen (Par I α) u I.sink → Relation.ReflTransGen (Par I α) v I.sink := by
  induction p with
  | nil => exact id
  | @cons a w _ hadj p ih =>
    intro hu
    apply ih
    obtain ⟨hgr, hαu, hαw⟩ := hadj
    rcases (adj_iff.1 hgr).2 with hw | hu'
    · rcases hu.cases_head with h | ⟨q, hq, hrest⟩
      · rw [h, I.sink_out] at hw
        exact absurd hw (Finset.notMem_empty _)
      · have hwq : w = q := by
          by_contra hne
          exact hαw (parent_others_zero hα (ne_sink_of_mem_out hw) hαu hq.1 hq.2 w hw hne)
        rw [hwq]
        exact hrest
    · exact Relation.ReflTransGen.head ⟨hu', hαu⟩ hu

/-- (Claim 2, v3.90 l. 321-322) A vertex of `T` other than the sink has a parent, hence the colours `1, 2, 3` in its list. -/
lemma lists_T (hα : I.IsGreedy I.x α) {v : W} (hv : (I.fGraph α).Reachable I.sink v) (hvs : v ≠ I.sink) :
    ∀ z, z ≠ 0 → z ∈ I.L v := by
  obtain ⟨p⟩ := hv
  rcases (anc_walk hα p Relation.ReflTransGen.refl).cases_head with h | ⟨q, hq, -⟩
  · exact absurd h hvs
  · exact parent_lists hα hvs (ne_zero_T hα ⟨p⟩) hq.1 hq.2

/-- The vertices of `T`. -/
abbrev TV (I : Instance W) (α : W → Fin 4) : Type := {v // (I.fGraph α).Reachable I.sink v}

/-- The graph `T` (induced by `F` on `T`). -/
def TG (I : Instance W) (α : W → Fin 4) : SimpleGraph (TV I α) where
  Adj a b := (I.fGraph α).Adj a.1 b.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => (I.fGraph α).irrefl h⟩

/-- The lists on `T`: `L v \ {0}`. -/
def TL (I : Instance W) (α : W → Fin 4) (a : TV I α) : Finset (Fin 4) := (I.L a.1).filter (fun y => y ≠ 0)

open Classical in
/-- A colouring of `T`, extended by `α` outside `T`. -/
noncomputable def extT (I : Instance W) (α : W → Fin 4) (d : TV I α → Fin 4) (w : W) : Fin 4 :=
  if hw : (I.fGraph α).Reachable I.sink w then d ⟨w, hw⟩ else α w

lemma extT_update (d : TV I α → Fin 4) (a : TV I α) (y : Fin 4) :
    Function.update (extT I α d) a.1 y = extT I α (Function.update d a y) := by
  funext w
  by_cases hw : (I.fGraph α).Reachable I.sink w
  · by_cases hwa : w = a.1
    · have : (⟨w, hw⟩ : TV I α) = a := Subtype.ext hwa
      subst hwa
      simp only [extT, hw, ↓reduceDIte, Function.update_self, this]
    · have : (⟨w, hw⟩ : TV I α) ≠ a := fun h => hwa (congrArg Subtype.val h)
      simp only [extT, hw, ↓reduceDIte, Function.update_of_ne hwa, Function.update_of_ne this]
  · have hwa : w ≠ a.1 := fun h => hw (h ▸ a.2)
    simp only [extT, hw, ↓reduceDIte, Function.update_of_ne hwa]

/-- A sequence on `T` (lists `L \ {0}`) is a sequence of the instance, with `α` fixed outside `T`. -/
lemma lift_seq (hα : I.IsGreedy I.x α) :
    ∀ (ms' : List (TV I α × Fin 4)) (d d' : TV I α → Fin 4),
      IsSeq (TG I α) (TL I α) d ms' d' →
      IsSeq I.graph I.L (extT I α d) (ms'.map fun m => (m.1.1, m.2)) (extT I α d')
  | [], d, d', h => by
    simp only [IsSeq, List.map_nil] at h ⊢
    rw [h]
  | m :: ms', d, d', h => by
    obtain ⟨⟨hne, hyA, hnb⟩, hrest⟩ := h
    have hy := mem_filter.1 hyA
    simp only [List.map_cons, IsSeq]
    refine ⟨⟨?_, hy.1, fun u hu => ?_⟩, ?_⟩
    · simp only [extT, m.1.2, ↓reduceDIte]
      exact hne
    · by_cases huT : (I.fGraph α).Reachable I.sink u
      · simp only [extT, huT, ↓reduceDIte]
        exact hnb ⟨u, huT⟩ ⟨hu, ne_zero_T hα m.1.2, ne_zero_T hα huT⟩
      · simp only [extT, huT, ↓reduceDIte, zero_nbr_T hα m.1.2 hu huT]
        exact fun h => hy.2 h.symm
    · rw [extT_update]
      exact lift_seq hα ms' _ d' hrest

lemma movesOf_map (ms' : List (TV I α × Fin 4)) (a : TV I α) :
    movesOf (ms'.map fun m => (m.1.1, m.2)) a.1 = movesOf ms' a := by
  simp only [movesOf, List.countP_map]
  congr 1
  funext m
  simp [Subtype.ext_iff]

lemma movesOf_map_out (ms' : List (TV I α × Fin 4)) (w : W) (hw : ¬ (I.fGraph α).Reachable I.sink w) :
    movesOf (ms'.map fun m => (m.1.1, m.2)) w = 0 := by
  simp only [movesOf, List.countP_map, List.countP_eq_zero]
  intro m _
  simp only [Function.comp_apply, decide_eq_true_eq]
  intro h
  exact hw (h ▸ m.1.2)

end Tree

end CaseAPaper

open CaseA Heights CaseAPaper

theorem lem_2_3_heights_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    ∃ hA hB : W → ℤ, IsHeight (I.fGraph α) α hA ∧ IsHeight (I.fGraph α) β hB ∧
      (hB I.sink - hA I.sink = 2 ∨ hB I.sink - hA I.sink = -2) := by
  have h0α := hcol_isHt hα
  have h0β := isHt_mono (le_of_eq (fGraph_eq hg hα hβ)) (hcol_isHt hβ)
  have hgx := I.g_lt_x
  obtain ⟨k, hk⟩ : ∃ k : ℤ, hcol I.g + 3 * k - hcol I.x = 2 ∨ hcol I.g + 3 * k - hcol I.x = -2 := by
    rcases (by omega : (I.g = 1 ∧ I.x = 2) ∨ (I.g = 1 ∧ I.x = 3) ∨ (I.g = 2 ∧ I.x = 3)) with
      ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · exact ⟨1, by decide⟩
    · exact ⟨-1, by decide⟩
    · exact ⟨0, by decide⟩
  refine ⟨fun v => hcol (α v), fun v => hcol (β v) + 3 * k, (isHeight_iff _ _ _).mpr h0α,
    (isHeight_iff _ _ _).mpr (isHt_add_const h0β k), ?_⟩
  simp only [hα.1, hβ.1]
  rcases hk with hk | hk
  · left; linarith
  · right; linarith

theorem lem_2_3_offsets_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (c0 : Fin 4) (c : W → Fin 4)
    (hc : I.IsGreedy c0 c) (hc0 : c0 ≠ 0) (h : W → ℤ) (hh : IsHeight (I.fGraph c) c h) (v : W)
    (hv : (I.fGraph c).Reachable I.sink v) (hvs : v ≠ I.sink) :
    (c0 = 1 → h v - h I.sink = 0 ∨ h v - h I.sink = 1) ∧ (c0 = 2 → h v - h I.sink = -1 ∨ h v - h I.sink = 0) ∧
      (c0 = 3 → h v - h I.sink = 1 ∨ h v - h I.sink = 2) := by
  rw [isHeight_iff] at hh
  obtain ⟨p⟩ := hv
  have hd := diff_walk hh (hcol_isHt hc) p
  have hcv0 : c v ≠ 0 := ne_zero_of_walk p (by rw [hc.1]; exact hc0)
  have hcv3 : c v ≠ 3 := greedy_ne_three hc hvs
  simp only [hc.1] at hd
  have hv12 : c v = 1 ∨ c v = 2 := by omega
  rcases hv12 with e | e <;> rw [e] at hd <;> refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;>
    simp only [hcol_one, hcol_two, hcol_three] at hd <;> omega

theorem lem_2_3_E_bound_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (hA hB : W → ℤ)
    (hhA : IsHeight (I.fGraph α) α hA) (hhB : IsHeight (I.fGraph α) β hB)
    (hs : hB I.sink - hA I.sink = 2 ∨ hB I.sink - hA I.sink = -2) (v : W) (hv : (I.fGraph α).Reachable I.sink v) :
    Even (hB v - hA v) ∧ |hB v - hA v| ≤ 4 := by
  have hfe := fGraph_eq hg hα hβ
  have hgx := I.g_lt_x
  have hpar := parity_walk ((isHeight_iff _ _ _).mp hhA) ((isHeight_iff _ _ _).mp hhB) hv.some
  rw [even_iff_two_dvd]
  rcases eq_or_ne v I.sink with rfl | hvs
  · refine ⟨by omega, abs_le.mpr ⟨by omega, by omega⟩⟩
  have oA := lem_2_3_offsets_proved I I.x α hα (x_ne_zero I) hA hhA v hv hvs
  have oB := lem_2_3_offsets_proved I I.g β hβ (by omega) hB (hfe ▸ hhB) v (hfe ▸ hv) hvs
  rcases (by omega : (I.g = 1 ∧ I.x = 2) ∨ (I.g = 1 ∧ I.x = 3) ∨ (I.g = 2 ∧ I.x = 3)) with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have a := oA.2.1 e2; have b := oB.1 e1
    exact ⟨by omega, abs_le.mpr ⟨by omega, by omega⟩⟩
  · have a := oA.2.2 e2; have b := oB.1 e1
    exact ⟨by omega, abs_le.mpr ⟨by omega, by omega⟩⟩
  · have a := oA.2.2 e2; have b := oB.2.1 e1
    exact ⟨by omega, abs_le.mpr ⟨by omega, by omega⟩⟩

theorem lem_2_3_paper_route_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (hA hB : W → ℤ)
    (hhA : IsHeight (I.fGraph α) α hA) (hhB : IsHeight (I.fGraph α) β hB)
    (hs : hB I.sink - hA I.sink = 2 ∨ hB I.sink - hA I.sink = -2) :
    ∃ ms, I.IsSeq α ms β ∧
      (∀ v, (I.fGraph α).Reachable I.sink v → 2 * movesOf ms v = (hB v - hA v).natAbs) ∧
      (∀ v, ¬ (I.fGraph α).Reachable I.sink v → movesOf ms v = 0) ∧
      movesOf ms I.sink = 1 ∧ ms.length ≤ 2 * Fintype.card W := by
  let instT : Fintype (TV I α) := Fintype.ofFinite _
  have hA' := (isHeight_iff _ _ _).mp hhA
  have hB' := (isHeight_iff _ _ _).mp hhB
  have hEb := fun a : TV I α => lem_2_3_E_bound_proved I hg α β hα hβ hA hB hhA hhB hs a.1 a.2
  have hx0 := x_ne_zero I
  have hgx := I.g_lt_x
  -- the hypotheses of Lemma 2.4 on `T` with the lists `L \ {0}`
  have hpos : ∀ (a : TV I α) y, y ∈ TL I α a → 0 < y.val := fun a y hy => val_pos (mem_filter.1 hy).2
  have hsum : (fun a : TV I α => hA a.1) + (fun a => hB a.1 - hA a.1) = fun a => hB a.1 := by
    funext a
    simp
  have S : Setup (TG I α) (TL I α) (fun a => α a.1) (fun a => β a.1) (fun a => hA a.1)
      (fun a => hB a.1 - hA a.1) := by
    refine ⟨fun a => ?_, fun a => ?_, ⟨fun a => hA'.1 a.1, fun a b hab => hA'.2 a.1 b.1 hab⟩,
      fun a => (hEb a).1, ?_, fun a => ?_⟩
    · exact mem_filter.2 ⟨mem_L hα (by rw [I.L_sink]; simp) a.1, ne_zero_T hα a.2⟩
    · exact mem_filter.2 ⟨mem_L hβ (by rw [I.L_sink]; simp) a.1,
        fun h => ne_zero_T hα a.2 ((zero_iff hg hα hβ a.1).2 h)⟩
    · rw [hsum]
      exact ⟨fun a => hB'.1 a.1, fun a b hab => hB'.2 a.1 b.1 hab⟩
    · rcases eq_or_ne a.1 I.sink with ha | ha
      · right
        simp only [ha]
        rcases hs with h | h <;> omega
      · left
        exact fun y hy => mem_filter.2 ⟨lists_T hα a.2 ha y (Fin.pos_iff_ne_zero.1 hy), Fin.pos_iff_ne_zero.1 hy⟩
  obtain ⟨ms', hseq, hlen, hmov⟩ := main hpos _ _ _ _ _ S rfl
  -- map the moves back to `W`
  have hstart : extT I α (fun a => α a.1) = α := by
    funext w
    by_cases hw : (I.fGraph α).Reachable I.sink w
    · simp only [extT, hw, ↓reduceDIte]
    · simp only [extT, hw, ↓reduceDIte]
  have hend : extT I α (fun a => β a.1) = β := by
    funext w
    by_cases hw : (I.fGraph α).Reachable I.sink w
    · simp only [extT, hw, ↓reduceDIte]
    · simp only [extT, hw, ↓reduceDIte]
      exact eq_outside hg hα hβ w hw
  have hseqW := lift_seq hα ms' _ _ hseq
  rw [hstart, hend] at hseqW
  unfold Instance.IsSeq
  have hsT : (I.fGraph α).Reachable I.sink I.sink := SimpleGraph.Reachable.refl _
  refine ⟨ms'.map fun m => (m.1.1, m.2), hseqW, fun v hv => ?_, fun v hv => movesOf_map_out ms' v hv, ?_, ?_⟩
  · rw [movesOf_map ms' ⟨v, hv⟩]
    exact hmov ⟨v, hv⟩
  · rw [movesOf_map ms' ⟨I.sink, hsT⟩]
    have := hmov ⟨I.sink, hsT⟩
    simp only at this
    rcases hs with h | h <;> rw [h] at this <;> simp at this <;> omega
  · rw [List.length_map]
    have hle : ∑ a : TV I α, (hB a.1 - hA a.1).natAbs ≤ ∑ _a : TV I α, 4 :=
      Finset.sum_le_sum fun a _ => by
        have := abs_le.mp (hEb a).2
        omega
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    have hcard := @Fintype.card_le_of_injective (TV I α) W instT _ Subtype.val Subtype.val_injective
    omega

end Cereceda
