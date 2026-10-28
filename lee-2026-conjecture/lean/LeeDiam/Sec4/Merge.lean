/-
LeeDiam/Sec4/Merge.lean — Section 4 helper: merged walks (Lemma 4.3, sec_chain.tex v1.50 l. 37-45).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Chain
import LeeDiam.Sec4.Trace
import LeeDiam.Sec4.BandOrder
import LeeDiam.Sec4.Words

namespace LeeDiam.S4

open Finset Band

section ConnUnion

variable {P : Type} [PartialOrder P]

/-- Two elements of a connected subset `S` of `U` are joined inside `U` by comparable pairs. -/
theorem rtg_of_isConnSet {S U : Set P} (hS : IsConnSet S) (hSU : S ⊆ U) {x y : P} (hx : x ∈ S) (hy : y ∈ S) :
    Relation.ReflTransGen (fun u v => u ∈ U ∧ v ∈ U ∧ Comp u v) x y := by
  obtain ⟨p⟩ := SimpleGraph.Connected.preconnected hS ⟨x, hx⟩ ⟨y, hy⟩
  suffices key : ∀ (s t : S) (_ : ((compGraph P).induce S).Walk s t),
      Relation.ReflTransGen (fun u v => u ∈ U ∧ v ∈ U ∧ Comp u v) s.1 t.1 from key _ _ p
  intro s t p
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | @cons s m t hadj _ ih => exact Relation.ReflTransGen.head ⟨hSU s.2, hSU m.2, hadj⟩ ih

/-- A union of connected sets, indexed by the vertices of a connected graph whose edges join sets that contain a
comparable pair, is connected. -/
theorem isConnSet_iUnion_of_graph {ι : Type} (G : SimpleGraph ι) (hG : G.Connected) (S : ι → Set P)
    (hS : ∀ i, IsConnSet (S i)) (hadj : ∀ i j, G.Adj i j → ∃ x ∈ S i, ∃ y ∈ S j, Comp x y) :
    IsConnSet (⋃ i, S i) := by
  obtain ⟨i₀⟩ := hG.nonempty
  obtain ⟨x₀, hx₀⟩ := isConnSet_nonempty (hS i₀)
  have hsub : ∀ i, S i ⊆ ⋃ i, S i := fun i => Set.subset_iUnion S i
  have hwalk : ∀ i j (_ : G.Walk i j), (∀ x ∈ S i, Relation.ReflTransGen
      (fun u v => u ∈ ⋃ i, S i ∧ v ∈ ⋃ i, S i ∧ Comp u v) x₀ x) →
      ∀ y ∈ S j, Relation.ReflTransGen (fun u v => u ∈ ⋃ i, S i ∧ v ∈ ⋃ i, S i ∧ Comp u v) x₀ y := by
    intro i j q
    induction q with
    | nil => exact id
    | @cons i m j hij _ ih =>
      intro hi
      apply ih
      intro z hz
      obtain ⟨x, hx, y, hy, hxy⟩ := hadj i m hij
      exact ((hi x hx).tail ⟨hsub i hx, hsub m hy, hxy⟩).trans (rtg_of_isConnSet (hS m) (hsub m) hy hz)
  refine isConnSet_of_rtg (hsub i₀ hx₀) fun y hy => ?_
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
  obtain ⟨q⟩ := hG.preconnected i₀ j
  exact hwalk i₀ j q (fun x hx => rtg_of_isConnSet (hS i₀) (hsub i₀) hx₀ hx) y hj

end ConnUnion

section Merge

variable {k r M : ℕ} (W : Fin r → List (Set (Band k))) (step : (t : Fin r) → Fin ((W t).length - 1) → Fin M)

/-- The number of moves of walk `t` in the steps `0, …, α - 1`. -/
def mcnt (t : Fin r) (α : ℕ) : ℕ := (univ.filter (fun m => (step t m).val < α)).card

theorem eq_of_lt_iff {n c d : ℕ} (hc : c ≤ n) (hd : d ≤ n) (h : ∀ m : Fin n, m.val < c ↔ m.val < d) : c = d := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := (h ⟨c, by omega⟩).2 hlt
    simp at this
  · have := (h ⟨d, by omega⟩).1 hlt
    simp at this

theorem mcnt_le (t : Fin r) (α : ℕ) : mcnt W step t α ≤ (W t).length - 1 :=
  (card_filter_le _ _).trans (by simp)

theorem mcnt_zero (t : Fin r) : mcnt W step t 0 = 0 := by simp [mcnt]

theorem mcnt_of_ge (t : Fin r) {α : ℕ} (hα : M ≤ α) : mcnt W step t α = (W t).length - 1 := by
  unfold mcnt
  rw [filter_true_of_mem (fun m _ => by have := (step t m).isLt; omega)]
  simp

/-- Since `step t` is strictly monotone, the moves of walk `t` in the steps `< α` form an initial segment. -/
theorem lt_mcnt_iff {t : Fin r} (hmono : StrictMono (step t)) (m : Fin ((W t).length - 1)) (α : ℕ) :
    m.val < mcnt W step t α ↔ (step t m).val < α := by
  unfold mcnt
  constructor
  · intro h
    by_contra hge
    have hsub : univ.filter (fun m' => (step t m').val < α) ⊆ Iio m := by
      intro m' hm'
      simp only [mem_filter, mem_univ, true_and] at hm'
      rw [mem_Iio]
      by_contra hle
      have := Fin.le_iff_val_le_val.1 (hmono.monotone (not_lt.1 hle))
      omega
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have hsub : Iic m ⊆ univ.filter (fun m' => (step t m').val < α) := by
      intro m' hm'
      rw [mem_Iic] at hm'
      simp only [mem_filter, mem_univ, true_and]
      have := Fin.le_iff_val_le_val.1 (hmono.monotone hm')
      omega
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    omega

/-- The move of walk `t` in step `β` (if any) is its move number `mcnt t β`. -/
theorem mcnt_of_step {t : Fin r} (hmono : StrictMono (step t)) (m : Fin ((W t).length - 1)) {β : ℕ}
    (hm : (step t m).val = β) : mcnt W step t β = m.val ∧ mcnt W step t (β + 1) = m.val + 1 := by
  have hm' := m.isLt
  constructor
  · refine eq_of_lt_iff (mcnt_le W step t β) hm'.le fun m' => ?_
    rw [lt_mcnt_iff W step hmono, ← hm, ← Fin.lt_def, hmono.lt_iff_lt, Fin.lt_def]
  · refine eq_of_lt_iff (mcnt_le W step t (β + 1)) hm' fun m' => ?_
    rw [lt_mcnt_iff W step hmono, ← hm, Nat.lt_succ_iff, ← Fin.le_iff_val_le_val, hmono.le_iff_le,
      Fin.le_iff_val_le_val, Nat.lt_succ_iff]

theorem mcnt_of_no_step {t : Fin r} (hmono : StrictMono (step t)) {β : ℕ} (hβ : ∀ m, (step t m).val ≠ β) :
    mcnt W step t (β + 1) = mcnt W step t β := by
  refine eq_of_lt_iff (mcnt_le W step t _) (mcnt_le W step t _) fun m' => ?_
  rw [lt_mcnt_iff W step hmono, lt_mcnt_iff W step hmono]
  have := hβ m'
  omega

theorem mcnt_succ {t : Fin r} (hmono : StrictMono (step t)) (β : ℕ) :
    mcnt W step t (β + 1) = mcnt W step t β ∨ mcnt W step t (β + 1) = mcnt W step t β + 1 := by
  by_cases h : ∃ m, (step t m).val = β
  · obtain ⟨m, hm⟩ := h
    obtain ⟨h1, h2⟩ := mcnt_of_step W step hmono m hm
    right
    omega
  · simp only [not_exists] at h
    exact Or.inl (mcnt_of_no_step W step hmono h)

/-- The state of walk `t` after the steps `< α`. -/
def mstate (t : Fin r) (α : ℕ) : Set (Band k) := (W t).getD (mcnt W step t α) ∅

theorem mergedState_eq (α : ℕ) : mergedState W step α = ⋃ t, mstate W step t α := rfl

theorem mstate_mem (hW : ∀ t, IsWalk (W t)) (t : Fin r) (α : ℕ) : mstate W step t α ∈ W t := by
  have hlen : 0 < (W t).length := List.length_pos_of_ne_nil (hW t).1
  have := mcnt_le W step t α
  unfold mstate
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

variable {W step}

theorem mem_D_of_mem_merged {D : Fin r → Set (Band k)} (hW : ∀ t, IsWalk (W t)) (hWD : ∀ t, ∀ X ∈ W t, X ⊆ D t)
    {x : Band k} {α : ℕ} (hx : x ∈ mergedState W step α) : ∃ t, x ∈ D t := by
  rw [mergedState_eq, Set.mem_iUnion] at hx
  obtain ⟨t, ht⟩ := hx
  exact ⟨t, hWD t _ (mstate_mem W step hW t α) ht⟩

theorem moveDiff_sub {D : Fin r → Set (Band k)} (hWD : ∀ t, ∀ X ∈ W t, X ⊆ D t) {t : Fin r} {m : ℕ} :
    moveDiff (W t) m ⊆ D t := by
  intro x hx
  have key : ∀ i, x ∈ (W t).getD i ∅ → x ∈ D t := by
    intro i hi
    rw [List.getD_eq_getElem?_getD] at hi
    cases h : (W t)[i]? with
    | none => simp [h] at hi
    | some X =>
      rw [h] at hi
      exact hWD t X (List.mem_of_getElem? h) hi
  rcases hx with ⟨hx, -⟩ | ⟨hx, -⟩
  · exact key m hx
  · exact key (m + 1) hx

theorem moveDiff_conn (hW : ∀ t, IsWalk (W t)) {t : Fin r} (m : Fin ((W t).length - 1)) :
    IsConnSet (moveDiff (W t) m) := by
  have hc := (hW t).2.2
  rw [List.isChain_iff_getElem] at hc
  have hm := m.isLt
  have := hc m.val (by omega)
  unfold moveDiff
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem (by omega)]

variable (D : Fin r → Set (Band k)) (hD : Pairwise fun t t' => Disjoint (D t) (D t'))
  (hW : ∀ t, IsWalk (W t)) (hWD : ∀ t, ∀ X ∈ W t, X ⊆ D t)
include hD hW hWD

/-- Inside `D t`, the merged state is the state of walk `t`. -/
theorem mem_merged_iff {t : Fin r} {x : Band k} (hx : x ∈ D t) (α : ℕ) :
    x ∈ mergedState W step α ↔ x ∈ mstate W step t α := by
  rw [mergedState_eq, Set.mem_iUnion]
  refine ⟨fun ⟨t', ht'⟩ => ?_, fun h => ⟨t, h⟩⟩
  have hx' := hWD t' _ (mstate_mem W step hW t' α) ht'
  by_cases htt : t' = t
  · exact htt ▸ ht'
  · exact absurd hx (Set.disjoint_left.1 (hD htt) hx')

/-- The difference of step `β` of the merge is the union of the differences of the moves in step `β`. -/
theorem merged_diff (hmono : ∀ t, StrictMono (step t)) (β : Fin M) :
    symmDiff (mergedState W step β) (mergedState W step (β + 1)) =
      ⋃ p : {p : (t : Fin r) × Fin ((W t).length - 1) // step p.1 p.2 = β}, moveDiff (W p.1.1) p.1.2 := by
  ext x
  rw [Set.mem_iUnion]
  constructor
  · intro hx
    obtain ⟨t, hxt⟩ : ∃ t, x ∈ D t := by
      rcases hx with ⟨hx, -⟩ | ⟨hx, -⟩
      · exact mem_D_of_mem_merged hW hWD hx
      · exact mem_D_of_mem_merged hW hWD hx
    rw [Set.mem_symmDiff, mem_merged_iff D hD hW hWD hxt, mem_merged_iff D hD hW hWD hxt] at hx
    by_cases h : ∃ m, (step t m).val = β.val
    · obtain ⟨m, hm⟩ := h
      obtain ⟨h1, h2⟩ := mcnt_of_step W step (hmono t) m hm
      refine ⟨⟨⟨t, m⟩, Fin.ext hm⟩, ?_⟩
      unfold mstate at hx
      rw [h1, h2] at hx
      exact hx
    · simp only [not_exists] at h
      have := mcnt_of_no_step W step (hmono t) h
      unfold mstate at hx
      rw [this] at hx
      tauto
  · rintro ⟨⟨⟨t, m⟩, hm⟩, hx⟩
    have hxt : x ∈ D t := moveDiff_sub hWD hx
    obtain ⟨h1, h2⟩ := mcnt_of_step W step (hmono t) m (congrArg Fin.val hm)
    rw [Set.mem_symmDiff, mem_merged_iff D hD hW hWD hxt, mem_merged_iff D hD hW hWD hxt]
    unfold mstate
    rw [h1, h2]
    exact hx

end Merge

section MergeMain

variable {k r M : ℕ}

theorem sum_sub_one_add {M : ℕ} (f : Fin M → ℕ) (hf : ∀ β, 1 ≤ f β) : M + ∑ β, (f β - 1) = ∑ β, f β := by
  rw [show ∑ β, f β = ∑ β, ((f β - 1) + 1) from Finset.sum_congr rfl fun β _ => (Nat.sub_add_cancel (hf β)).symm,
    Finset.sum_add_distrib]
  simp [add_comm]

theorem getD_zero_eq_headD {α : Type} (L : List α) (d : α) : L.getD 0 d = L.headD d := by
  cases L <;> rfl

theorem getD_last_eq_getLastD {α : Type} (L : List α) (d : α) : L.getD (L.length - 1) d = L.getLastD d := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-- Lemma 4.3 (merging walks), part 1: the merged walk is a walk from the union of the initial sets to the union of
the final sets. -/
theorem merge_walk (D : Fin r → Set (Band k)) (hD : Pairwise fun t t' => Disjoint (D t) (D t'))
    (W : Fin r → List (Set (Band k))) (hW : ∀ t, IsWalk (W t)) (hWD : ∀ t, ∀ X ∈ W t, X ⊆ D t)
    (step : (t : Fin r) → Fin ((W t).length - 1) → Fin M) (hmono : ∀ t, StrictMono (step t))
    (hanti : ∀ α ≤ M, IsAntichainSet (mergedState W step α))
    (hconn : ∀ β : Fin M, (moveGraph W step β).Connected) :
    IsWalkFromTo ((List.range (M + 1)).map (mergedState W step)) (⋃ t, (W t).headD ∅) (⋃ t, (W t).getLastD ∅) := by
  refine ⟨⟨by simp, ?_, ?_⟩, ?_, ?_⟩
  · intro X hX
    obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hX
    exact hanti α (by have := List.mem_range.1 hα; omega)
  · rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range]
    have := merged_diff D hD hW hWD hmono ⟨i, by omega⟩
    simp only at this
    rw [this]
    exact isConnSet_iUnion_of_graph _ (hconn ⟨i, by omega⟩) _ (fun p => moveDiff_conn hW p.1.2)
      (fun p q hpq => hpq.2)
  · rw [List.range_succ_eq_map, List.map_cons, List.head?_cons, mergedState_eq]
    congr 1
    refine Set.iUnion_congr fun t => ?_
    rw [mstate, mcnt_zero, getD_zero_eq_headD]
  · simp only [List.getLast?_map, List.getLast?_range, Nat.add_one_ne_zero, ↓reduceIte, Option.map_some,
      Nat.add_sub_cancel, mergedState_eq]
    congr 1
    refine Set.iUnion_congr fun t => ?_
    rw [mstate, mcnt_of_ge W step t le_rfl, getD_last_eq_getLastD]

/-- Lemma 4.3, part 2: the length of the merged walk is the total number of moves minus `∑ (|S_β| - 1)`. -/
theorem merge_count (W : Fin r → List (Set (Band k))) (step : (t : Fin r) → Fin ((W t).length - 1) → Fin M)
    (hne : ∀ β : Fin M, ∃ t m, step t m = β) :
    M + ∑ β : Fin M,
        ((Finset.univ.filter (fun p : (t : Fin r) × Fin ((W t).length - 1) => step p.1 p.2 = β)).card - 1) =
      ∑ t, ((W t).length - 1) := by
  have hpos : ∀ β : Fin M,
      1 ≤ (Finset.univ.filter (fun p : (t : Fin r) × Fin ((W t).length - 1) => step p.1 p.2 = β)).card := by
    intro β
    obtain ⟨t, m, h⟩ := hne β
    exact Finset.card_pos.2 ⟨⟨t, m⟩, by simp [h]⟩
  have hsum : ∑ β : Fin M,
      (Finset.univ.filter (fun p : (t : Fin r) × Fin ((W t).length - 1) => step p.1 p.2 = β)).card =
      ∑ t, ((W t).length - 1) := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := fun p : (t : Fin r) × Fin ((W t).length - 1) => step p.1 p.2)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
    simp [Finset.card_univ, Fintype.card_sigma]
  rw [← hsum]
  exact sum_sub_one_add _ hpos

/-- Lemma 4.3, part 3: at a column all of whose elements (in states of the walks) lie in `D t`, the merged walk has
the outer trace of walk `t`. -/
theorem merge_trace (D : Fin r → Set (Band k)) (hD : Pairwise fun t t' => Disjoint (D t) (D t'))
    (W : Fin r → List (Set (Band k))) (hW : ∀ t, IsWalk (W t)) (hWD : ∀ t, ∀ X ∈ W t, X ⊆ D t)
    (step : (t : Fin r) → Fin ((W t).length - 1) → Fin M) (hmono : ∀ t, StrictMono (step t))
    (t : Fin r) (e : Fin k) (hcol : ∀ t', ∀ X ∈ W t', ∀ x ∈ X, x.1 = e → x ∈ D t) :
    outerTrace ((List.range (M + 1)).map (mergedState W step)) e = outerTrace (W t) e := by
  have hmem : ∀ α (y : Band k), y.1 = e → (y ∈ mergedState W step α ↔ y ∈ mstate W step t α) := by
    intro α y hy
    refine ⟨fun h => ?_, fun h => Set.mem_iUnion.2 ⟨t, h⟩⟩
    obtain ⟨t', ht'⟩ := Set.mem_iUnion.1 h
    have hyD : y ∈ D t := hcol t' _ (mstate_mem W step hW t' α) y ht' hy
    exact (mem_merged_iff D hD hW hWD hyD α).1 h
  have hout : ∀ α, outerAt (mergedState W step α) e = outerAt (mstate W step t α) e := by
    intro α
    have ha := hmem α (a e) rfl
    have hc := hmem α (c e) rfl
    by_cases h1 : a e ∈ mstate W step t α
    · rw [outerAt_of_a_mem h1, outerAt_of_a_mem (ha.2 h1)]
    · by_cases h2 : c e ∈ mstate W step t α
      · rw [outerAt_of_c_mem h1 h2, outerAt_of_c_mem (mt ha.1 h1) (hc.2 h2)]
      · rw [outerAt_none h1 h2, outerAt_none (mt ha.1 h1) (mt hc.1 h2)]
  have hlen : (W t).length = (W t).length - 1 + 1 := by
    have := List.length_pos_of_ne_nil (hW t).1
    omega
  have hst := stretch_of_pos M (fun i => outerAt ((W t).getD i ∅) e) (mcnt W step t) ((W t).length - 1)
    (mcnt_zero W step t) (mcnt_of_ge W step t le_rfl) (fun β _ => mcnt_succ W step (hmono t) β)
  unfold outerTrace
  rw [List.map_map]
  have h1 : ((List.range (M + 1)).map ((outerAt · e) ∘ mergedState W step)) =
      (List.range (M + 1)).map (fun α => (fun i => outerAt ((W t).getD i ∅) e) (mcnt W step t α)) :=
    List.map_congr_left fun α _ => hout α
  have h2 : (W t).map (outerAt · e) =
      (List.range ((W t).length - 1 + 1)).map (fun i => outerAt ((W t).getD i ∅) e) := by
    conv_lhs => rw [← map_range_getD (W t) ∅, List.map_map]
    rw [← hlen]
    rfl
  rw [h1, h2]
  exact stretch_destutter hst

/-- Lemma 4.3 (merging walks), all three parts, in the statement form of Sec4/Chain.lean `lem_4_3`. -/
theorem merge (D : Fin r → Set (Band k)) (hD : Pairwise fun t t' => Disjoint (D t) (D t'))
    (W : Fin r → List (Set (Band k))) (hW : ∀ t, IsWalk (W t)) (hWD : ∀ t, ∀ X ∈ W t, X ⊆ D t)
    (step : (t : Fin r) → Fin ((W t).length - 1) → Fin M) (hmono : ∀ t, StrictMono (step t))
    (hne : ∀ β : Fin M, ∃ t m, step t m = β)
    (hanti : ∀ α ≤ M, IsAntichainSet (mergedState W step α))
    (hconn : ∀ β : Fin M, (moveGraph W step β).Connected) :
    IsWalkFromTo ((List.range (M + 1)).map (mergedState W step)) (⋃ t, (W t).headD ∅) (⋃ t, (W t).getLastD ∅) ∧
      M + ∑ β : Fin M,
          ((Finset.univ.filter (fun p : (t : Fin r) × Fin ((W t).length - 1) => step p.1 p.2 = β)).card - 1) =
        ∑ t, ((W t).length - 1) ∧
      ∀ (t : Fin r) (e : Fin k), (∀ t', ∀ X ∈ W t', ∀ x ∈ X, x.1 = e → x ∈ D t) →
        outerTrace ((List.range (M + 1)).map (mergedState W step)) e = outerTrace (W t) e :=
  ⟨merge_walk D hD W hW hWD step hmono hanti hconn, merge_count W step hne,
    fun t e hcol => merge_trace D hD W hW hWD step hmono t e hcol⟩

end MergeMain

end LeeDiam.S4
