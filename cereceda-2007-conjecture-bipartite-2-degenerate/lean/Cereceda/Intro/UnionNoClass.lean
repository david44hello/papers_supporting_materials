/-
Cereceda/Intro/UnionNoClass.lean — embedding lemmas used by Intro/SemiFalse.lean
(degrees, treewidth, chordless long cycles and `mad` pass along graph embeddings; disjoint unions keep degeneracy and
do not lower the Grundy number), and `intro_union_in_no_class_proved`, an earlier proof route of Section 1 (not in
short v3.90; used by Intro/SemiFalse.lean): `K_{2,7} ⊔ (subdivided K_5) ⊔ T` with class (iii) read as chordal
bipartite graphs. (The witness `G_0` of earlier drafts, with the subdivided `K_4`, is not in short v3.90; its modules
were removed.)
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Routes. Every lower bound passes from a graph `G` to a graph `H` along a graph embedding `G ↪g H` (Mathlib's
`Embedding.sumInl`, `Embedding.sumInr` for disjoint unions): degrees (neighbourhoods map injectively), treewidth (pull
the bags back), chordless long cycles (map the walk; a chord in `H` pulls back to a chord in `G`), `mad` (the image of
the vertex set). The Grundy number of `A ⊕g B` is at least those of `A` and `B` (order `A` first, then `B`; no edge
leaves a summand, so the greedy colouring is the two greedy colourings side by side). The induced 6-cycle of the
subdivided `K_5` is the subdivided triangle `0, 01, 1, 12, 2, 20`.
-/
import Cereceda.Defs.Intro
import Cereceda.Defs.Basic
import Cereceda.Intro.Classes
import Cereceda.Setting.Misc

namespace Cereceda

open Finset

namespace UnionNoClass

section Emb

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {G : SimpleGraph α} {H : SimpleGraph β}

omit [DecidableEq α] [DecidableEq β] in
/-- A degree of `G` is at most the maximum degree of `H` when `G` embeds in `H`. -/
theorem degree_le_maxDegree [DecidableRel G.Adj] [DecidableRel H.Adj] (f : G ↪g H) (v : α) :
    G.degree v ≤ H.maxDegree := by
  refine le_trans ?_ (H.degree_le_maxDegree (f v))
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine card_le_card_of_injOn f (fun u hu => ?_) (fun _ _ _ _ h => f.injective h)
  simp only [mem_coe, SimpleGraph.mem_neighborFinset] at hu ⊢
  exact f.map_adj_iff.mpr hu

/-- The one-bag tree decomposition (so the set in `treewidth` is never empty). -/
def trivialDecomp (H : SimpleGraph β) : TreeDecomposition H (Fin 1) where
  T := SimpleGraph.pathGraph 1
  isTree := SimpleGraph.isTree_pathGraph_add_one 0
  bag := fun _ => univ
  cover_vertex := fun v => ⟨0, mem_univ v⟩
  cover_edge := fun u v _ => ⟨0, mem_univ u, mem_univ v⟩
  subtree := fun v =>
    Subdivision.connected_of_center (c := 0) (mem_univ v) (fun w _ => Or.inl (Subsingleton.elim w 0))

/-- A tree decomposition of `H` pulled back along an embedding `G ↪g H`. -/
noncomputable def restrict (f : G ↪g H) {ι : Type} [Fintype ι] (D : TreeDecomposition H ι) :
    TreeDecomposition G ι where
  T := D.T
  isTree := D.isTree
  bag i := (D.bag i).preimage f (fun _ _ _ _ h => f.injective h)
  cover_vertex v := by
    obtain ⟨i, hi⟩ := D.cover_vertex (f v)
    exact ⟨i, mem_preimage.mpr hi⟩
  cover_edge u v h := by
    obtain ⟨i, hu, hv⟩ := D.cover_edge (f u) (f v) (f.map_adj_iff.mpr h)
    exact ⟨i, mem_preimage.mpr hu, mem_preimage.mpr hv⟩
  subtree v := by
    have hS : {i | v ∈ (D.bag i).preimage f (fun _ _ _ _ h => f.injective h)} = {i | f v ∈ D.bag i} := by
      ext i
      exact Finset.mem_preimage
    rw [hS]
    exact D.subtree (f v)

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem mem_restrict_bag {f : G ↪g H} {ι : Type} [Fintype ι] {D : TreeDecomposition H ι} {i : ι} {v : α} :
    v ∈ (restrict f D).bag i ↔ f v ∈ D.bag i :=
  Finset.mem_preimage (hf := fun _ _ _ _ h => f.injective h)

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem restrict_width_le (f : G ↪g H) {ι : Type} [Fintype ι] (D : TreeDecomposition H ι) :
    (restrict f D).width ≤ D.width := by
  unfold TreeDecomposition.width
  refine Nat.sub_le_sub_right (Finset.sup_mono_fun fun i _ => ?_) 1
  exact card_le_card_of_injOn f (fun u hu => mem_restrict_bag.mp hu) (fun _ _ _ _ h => f.injective h)

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
/-- Treewidth does not drop along an embedding. -/
theorem treewidth_le (f : G ↪g H) : treewidth G ≤ treewidth H := by
  have hne : {w | ∃ (ι : Type) (_ : Fintype ι) (D : TreeDecomposition H ι), D.width = w}.Nonempty :=
    ⟨(trivialDecomp H).width, Fin 1, inferInstance, trivialDecomp H, rfl⟩
  obtain ⟨ι, _, D, hD⟩ := Nat.sInf_mem hne
  unfold treewidth
  rw [← hD]
  have hmem : (restrict f D).width ∈ {w | ∃ (ι : Type) (_ : Fintype ι) (D : TreeDecomposition G ι), D.width = w} :=
    ⟨ι, inferInstance, restrict f D, rfl⟩
  exact (Nat.sInf_le hmem).trans (restrict_width_le f D)

/-- `G` has a cycle of length at least `6` without a chord. -/
def HasChordless (G : SimpleGraph α) : Prop :=
  ∃ (v : α) (w : G.Walk v v), w.IsCycle ∧ 6 ≤ w.length ∧
    ∀ x ∈ w.support, ∀ y ∈ w.support, G.Adj x y → s(x, y) ∈ w.edges

omit [Fintype α] [DecidableEq α] in
theorem not_chordal (h : HasChordless G) : ¬ IsChordalBipartite G := by
  rintro ⟨-, hc⟩
  obtain ⟨v, w, hw, hlen, hno⟩ := h
  obtain ⟨x, hx, y, hy, hxy, hnot⟩ := hc v w hw hlen
  exact hnot (hno x hx y hy hxy)

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- A chordless long cycle maps to one along an embedding (a chord of the image pulls back). -/
theorem HasChordless.map (f : G ↪g H) (h : HasChordless G) : HasChordless H := by
  obtain ⟨v, w, hw, hlen, hno⟩ := h
  refine ⟨f v, w.map f.toHom, hw.map f.injective, by rwa [SimpleGraph.Walk.length_map], ?_⟩
  intro x hx y hy hxy
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hx hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  rw [SimpleGraph.Walk.edges_map]
  exact List.mem_map.mpr ⟨_, hno x' hx' y' hy' (f.map_adj_iff.mp hxy), by simp⟩

omit [DecidableEq α] in
/-- `mad H` is at least the average degree of any graph that embeds in `H`. -/
theorem avg_le_mad [Fintype G.edgeSet] [DecidableRel H.Adj] [Nonempty α] (f : G ↪g H) :
    2 * (G.edgeFinset.card : ℝ) / Fintype.card α ≤ mad H := by
  set s : Finset β := univ.map f.toEmbedding with hs
  have hsub : G.edgeFinset.map ⟨Sym2.map f, Sym2.map.injective f.injective⟩ ⊆
      H.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ s) := by
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    rw [mem_filter, SimpleGraph.mem_edgeFinset]
    refine ⟨f.map_mem_edgeSet_iff.mpr (SimpleGraph.mem_edgeFinset.mp he'), fun v hv => ?_⟩
    obtain ⟨u, -, rfl⟩ := Sym2.mem_map.mp hv
    exact mem_map_of_mem f.toEmbedding (mem_univ u)
  have hcard := card_le_card hsub
  rw [card_map] at hcard
  have hscard : s.card = Fintype.card α := by simp [hs]
  have hpos : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  calc 2 * (G.edgeFinset.card : ℝ) / Fintype.card α
      ≤ 2 * ((H.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ s)).card : ℝ) / s.card := by
        rw [hscard]
        gcongr
    _ ≤ mad H := by
        unfold mad
        apply le_csSup
        · refine (Set.finite_range (fun s : Finset β =>
            2 * ((H.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ s)).card : ℝ) / s.card)).bddAbove.mono ?_
          rintro r ⟨s, -, rfl⟩
          exact ⟨s, rfl⟩
        · exact ⟨s, ⟨f (Classical.arbitrary α), mem_map_of_mem f.toEmbedding (mem_univ _)⟩, rfl⟩

end Emb

section Sum

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {A : SimpleGraph α} {B : SimpleGraph β}

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- Disjoint unions of `d`-degenerate graphs are `d`-degenerate. -/
theorem isDegenerate_sum [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel (A ⊕g B).Adj] {d : ℕ}
    (hA : IsDegenerate A d) (hB : IsDegenerate B d) : IsDegenerate (A ⊕g B) d := by
  intro s hs
  by_cases hl : s.toLeft.Nonempty
  · obtain ⟨x, hx, hcard⟩ := hA _ hl
    refine ⟨.inl x, mem_toLeft.mp hx, le_trans ?_ hcard⟩
    calc (s.filter ((A ⊕g B).Adj (.inl x))).card
        ≤ ((s.toLeft.filter (A.Adj x)).map Function.Embedding.inl).card := by
          apply card_le_card
          rintro (u | u) hu
          · simp only [mem_filter, SimpleGraph.sum_adj_inl] at hu
            simp [mem_toLeft, hu]
          · simp at hu
      _ = _ := card_map _
  · have hr : s.toRight.Nonempty := by
      obtain ⟨z, hz⟩ := hs
      rcases z with x | y
      · exact absurd ⟨x, mem_toLeft.mpr hz⟩ hl
      · exact ⟨y, mem_toRight.mpr hz⟩
    obtain ⟨y, hy, hcard⟩ := hB _ hr
    refine ⟨.inr y, mem_toRight.mp hy, le_trans ?_ hcard⟩
    calc (s.filter ((A ⊕g B).Adj (.inr y))).card
        ≤ ((s.toRight.filter (B.Adj y)).map Function.Embedding.inr).card := by
          apply card_le_card
          rintro (u | u) hu
          · simp at hu
          · simp only [mem_filter, SimpleGraph.sum_adj_inr] at hu
            simp [mem_toRight, hu]
      _ = _ := card_map _

/-- The order of `α ⊕ β`: first `α` in the order `ρA`, then `β` in the order `ρB`. -/
def sumOrd {a b N : ℕ} (ρA : α ≃ Fin a) (ρB : β ≃ Fin b) (h : a + b = N) : α ⊕ β ≃ Fin N :=
  (Equiv.sumCongr ρA ρB).trans (finSumFinEquiv.trans (finCongr h))

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
@[simp] lemma sumOrd_inl {a b N : ℕ} (ρA : α ≃ Fin a) (ρB : β ≃ Fin b) (h : a + b = N) (x : α) :
    (sumOrd ρA ρB h (.inl x)).val = (ρA x).val := by
  simp [sumOrd]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
@[simp] lemma sumOrd_inr {a b N : ℕ} (ρA : α ≃ Fin a) (ρB : β ≃ Fin b) (h : a + b = N) (y : β) :
    (sumOrd ρA ρB h (.inr y)).val = a + (ρB y).val := by
  simp [sumOrd]

variable [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel (A ⊕g B).Adj]

omit [DecidableEq α] [DecidableEq β] [DecidableRel B.Adj] in
lemma image_earlier_inl {a b N : ℕ} (ρA : α ≃ Fin a) (ρB : β ≃ Fin b) (h : a + b = N) (cA : α → ℕ)
    (cB : β → ℕ) (x : α) :
    (univ.filter (fun u => (A ⊕g B).Adj (.inl x) u ∧ sumOrd ρA ρB h u < sumOrd ρA ρB h (.inl x))).image
        (Sum.elim cA cB) = (univ.filter (fun u => A.Adj x u ∧ ρA u < ρA x)).image cA := by
  ext z
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨u | u, ⟨hadj, hlt⟩, rfl⟩
    · rw [Fin.lt_def, sumOrd_inl, sumOrd_inl] at hlt
      exact ⟨u, ⟨hadj, Fin.lt_def.mpr hlt⟩, rfl⟩
    · exact absurd hadj (SimpleGraph.not_adj_sum_inl_inr _ _)
  · rintro ⟨u, ⟨hadj, hlt⟩, rfl⟩
    refine ⟨.inl u, ⟨hadj, ?_⟩, rfl⟩
    rw [Fin.lt_def, sumOrd_inl, sumOrd_inl]
    exact hlt

omit [DecidableEq α] [DecidableEq β] [DecidableRel A.Adj] in
lemma image_earlier_inr {a b N : ℕ} (ρA : α ≃ Fin a) (ρB : β ≃ Fin b) (h : a + b = N) (cA : α → ℕ)
    (cB : β → ℕ) (y : β) :
    (univ.filter (fun u => (A ⊕g B).Adj (.inr y) u ∧ sumOrd ρA ρB h u < sumOrd ρA ρB h (.inr y))).image
        (Sum.elim cA cB) = (univ.filter (fun u => B.Adj y u ∧ ρB u < ρB y)).image cB := by
  ext z
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨u | u, ⟨hadj, hlt⟩, rfl⟩
    · exact absurd hadj.symm (SimpleGraph.not_adj_sum_inl_inr _ _)
    · rw [Fin.lt_def, sumOrd_inr, sumOrd_inr] at hlt
      exact ⟨u, ⟨hadj, Fin.lt_def.mpr (by omega)⟩, rfl⟩
  · rintro ⟨u, ⟨hadj, hlt⟩, rfl⟩
    refine ⟨.inr u, ⟨hadj, ?_⟩, rfl⟩
    rw [Fin.lt_def, sumOrd_inr, sumOrd_inr]
    have := Fin.lt_def.mp hlt
    omega

omit [DecidableEq α] [DecidableEq β] in
/-- The two greedy colourings side by side form the greedy colouring of `A ⊕g B` for the order `sumOrd`. -/
theorem greedy_sum {a b N : ℕ} (ρA : α ≃ Fin a) (ρB : β ≃ Fin b) (h : a + b = N) {cA : α → ℕ} {cB : β → ℕ}
    (hA : IsGreedyRel A ρA cA) (hB : IsGreedyRel B ρB cB) :
    IsGreedyRel (A ⊕g B) (sumOrd ρA ρB h) (Sum.elim cA cB) := by
  rintro (x | y)
  · have hx := hA x
    rw [← image_earlier_inl (B := B) ρA ρB h cA cB x] at hx
    exact hx
  · have hy := hB y
    rw [← image_earlier_inr (A := A) ρA ρB h cA cB y] at hy
    exact hy

theorem grundy_le_sum_left : grundyNumber A ≤ grundyNumber (A ⊕g B) := by
  obtain ⟨ρA, cA, hA, hcard⟩ := (grundyNumber_spec_proved A).1
  obtain ⟨cB, hB⟩ := Misc.exists_greedyRel B (Fintype.equivFin β)
  have hc := greedy_sum ρA (Fintype.equivFin β) Fintype.card_sum.symm hA hB
  rw [← hcard]
  refine le_trans (card_le_card ?_) ((grundyNumber_spec_proved (A ⊕g B)).2 _ _ hc)
  intro z hz
  obtain ⟨x, -, rfl⟩ := mem_image.mp hz
  exact mem_image.mpr ⟨.inl x, mem_univ _, rfl⟩

theorem grundy_le_sum_right : grundyNumber B ≤ grundyNumber (A ⊕g B) := by
  obtain ⟨ρB, cB, hB, hcard⟩ := (grundyNumber_spec_proved B).1
  obtain ⟨cA, hA⟩ := Misc.exists_greedyRel A (Fintype.equivFin α)
  have hc := greedy_sum (Fintype.equivFin α) ρB Fintype.card_sum.symm hA hB
  rw [← hcard]
  refine le_trans (card_le_card ?_) ((grundyNumber_spec_proved (A ⊕g B)).2 _ _ hc)
  intro z hz
  obtain ⟨y, -, rfl⟩ := mem_image.mp hz
  exact mem_image.mpr ⟨.inr y, mem_univ _, rfl⟩

end Sum

/-! ### The induced 6-cycle of the subdivided `K_5`: the subdivided triangle `0, 01, 1, 12, 2, 20` -/

/-- The vertices `0, s(0,1), 1, s(1,2), 2, s(2,0)` of the subdivided `K_5`. -/
def c6map : Fin 6 → Fin 5 ⊕ (⊤ : SimpleGraph (Fin 5)).edgeSet
  | 0 => .inl 0
  | 1 => .inr ⟨s(0, 1), by simp⟩
  | 2 => .inl 1
  | 3 => .inr ⟨s(1, 2), by simp⟩
  | 4 => .inl 2
  | 5 => .inr ⟨s(2, 0), by simp⟩

theorem c6map_injective : Function.Injective c6map := by
  decide

theorem c6map_adj (a b : Fin 6) :
    (subdivision (⊤ : SimpleGraph (Fin 5))).Adj (c6map a) (c6map b) ↔ (SimpleGraph.cycleGraph 6).Adj a b := by
  revert a b
  decide

/-- The induced embedding `C_6 ↪g` (subdivided `K_5`). -/
def c6Emb : SimpleGraph.cycleGraph 6 ↪g subdivision (⊤ : SimpleGraph (Fin 5)) where
  toFun := c6map
  inj' := c6map_injective
  map_rel_iff' := c6map_adj _ _

theorem c6_hasChordless : HasChordless (SimpleGraph.cycleGraph 6) :=
  ⟨0, Classes.c6, Classes.c6_isCycle, by rw [Classes.c6_length],
    fun x _ y _ hxy => Classes.c6_edges x y hxy⟩

/-- Every graph `Y` that contains `K_{2,7}` and the subdivided `K_5` (as induced subgraphs), is bipartite and
`2`-degenerate and has Grundy number at least `4`, lies in none of the five classes. -/
theorem props {γ : Type} [Fintype γ] [DecidableEq γ] (Y : SimpleGraph γ) [DecidableRel Y.Adj]
    (eK : completeBipartiteGraph (Fin 2) (Fin 7) ↪g Y) (eS : subdivision (⊤ : SimpleGraph (Fin 5)) ↪g Y)
    (hbip : Y.IsBipartite) (hdeg : IsDegenerate Y 2) (hgr : 4 ≤ grundyNumber Y) :
    Y.IsBipartite ∧ IsDegenerate Y 2 ∧ 2 < treewidth Y ∧ 3 < Y.maxDegree ∧ ¬ IsChordalBipartite Y ∧
      3 < grundyNumber Y ∧ 3 < mad Y := by
  classical
  refine ⟨hbip, hdeg, ?_, ?_, not_chordal (c6_hasChordless.map (c6Emb.trans eS)), by omega, ?_⟩
  · have h := treewidth_le eS
    rw [Subdivision.treewidth_eq 5 (by norm_num)] at h
    omega
  · have h := degree_le_maxDegree eK (Sum.inl 0)
    rw [Classes.K2m_degree_inl] at h
    omega
  · have h := avg_le_mad eK
    rw [Examples.K2m_card_edges] at h
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    norm_num at h
    linarith

end UnionNoClass

open UnionNoClass

open Classical in
theorem intro_union_in_no_class_proved {n : ℕ} (T : SimpleGraph (Fin n)) (hT : T.IsTree) (hgT : grundyNumber T = 4) :
    let X := (completeBipartiteGraph (Fin 2) (Fin 7) ⊕g subdivision (⊤ : SimpleGraph (Fin 5))) ⊕g T
    ((completeBipartiteGraph (Fin 2) (Fin 7)).maxDegree = 7 ∧
      (2 * (completeBipartiteGraph (Fin 2) (Fin 7)).edgeFinset.card : ℝ) / 9 = 28 / 9 ∧
      4 ≤ treewidth (subdivision (⊤ : SimpleGraph (Fin 5))) ∧
      Nonempty (SimpleGraph.cycleGraph 6 ↪g subdivision (⊤ : SimpleGraph (Fin 5)))) ∧
    (X.IsBipartite ∧ IsDegenerate X 2 ∧ 2 < treewidth X ∧ 3 < X.maxDegree ∧ ¬ IsChordalBipartite X ∧
      3 < grundyNumber X ∧ 3 < mad X) ∧
    ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W), G.IsBipartite → IsDegenerate G 2 →
      (X ⊕g G).IsBipartite ∧ IsDegenerate (X ⊕g G) 2 ∧ 2 < treewidth (X ⊕g G) ∧ 3 < (X ⊕g G).maxDegree ∧
        ¬ IsChordalBipartite (X ⊕g G) ∧ 3 < grundyNumber (X ⊕g G) ∧ 3 < mad (X ⊕g G) := by
  intro X
  have eK : completeBipartiteGraph (Fin 2) (Fin 7) ↪g X :=
    SimpleGraph.Embedding.sumInl.trans SimpleGraph.Embedding.sumInl
  have eS : subdivision (⊤ : SimpleGraph (Fin 5)) ↪g X :=
    SimpleGraph.Embedding.sumInr.trans SimpleGraph.Embedding.sumInl
  have hbip : X.IsBipartite :=
    SimpleGraph.colorable_sum.2 ⟨SimpleGraph.colorable_sum.2 ⟨Classes.K2m_isBipartite,
      Subdivision.isBipartite _⟩, hT.isBipartite⟩
  have hdeg : IsDegenerate X 2 :=
    isDegenerate_sum (isDegenerate_sum (Examples.K2m_isDegenerate 7) (Subdivision.isDegenerate _))
      (Examples.isDegenerate_mono T (by norm_num) (Examples.tree_isDegenerate hT))
  have hgr : 4 ≤ grundyNumber X := hgT ▸ grundy_le_sum_right
  refine ⟨⟨?_, ?_, ?_, ⟨c6Emb⟩⟩, props X eK eS hbip hdeg hgr, ?_⟩
  · apply le_antisymm
    · refine SimpleGraph.maxDegree_le_of_forall_degree_le _ _ fun v => ?_
      rcases v with a | b
      · rw [Classes.K2m_degree_inl]
      · rw [Classes.K2m_degree_inr]
        norm_num
    · calc 7 = (completeBipartiteGraph (Fin 2) (Fin 7)).degree (Sum.inl 0) := (Classes.K2m_degree_inl 0).symm
        _ ≤ _ := SimpleGraph.degree_le_maxDegree _ _
  · rw [Examples.K2m_card_edges]
    norm_num
  · rw [Subdivision.treewidth_eq 5 (by norm_num)]
  · intro W _ _ G hG hGd
    refine props (X ⊕g G) (eK.trans SimpleGraph.Embedding.sumInl) (eS.trans SimpleGraph.Embedding.sumInl)
      (SimpleGraph.colorable_sum.2 ⟨hbip, hG⟩) (isDegenerate_sum hdeg hGd) (hgr.trans grundy_le_sum_left)

end Cereceda
