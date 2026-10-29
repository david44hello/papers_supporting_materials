/-
Cereceda/Intro/Classes.lean — fans (short v3.90 l. 105-106: `2`-degenerate but not bipartite; `intro_fans_proved`), the
chordless 6-cycle and `K_{2,m}` facts used by Intro/UnionNoClass.lean, and
`intro_no_class_contains_all_proved`, an earlier proof route of Section 1 (not in v3.90).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Routes. C_6: Mathlib's 6-cycle `cycleGraph.cycle 3` is a cycle of length 6 whose edges are all the edges of C_6, so
it has no chord. K_{2,4}: degrees 4 (left) and 2 (right). K_{2,m}: `mad` is at least the average degree (the set of
all vertices), `4m/(m+2) > 4 - ε` for `m = ⌈8/ε⌉`. Fans: treewidth <= 2 by the path decomposition with bags
`{apex, v_i, v_{i+1}}`; >= 2 by Helly (`Subdivision.helly`) for the triangle `apex, v_1, v_2`; not bipartite by the
same triangle.
-/
import Cereceda.Defs.Intro
import Cereceda.Defs.LowerBound
import Cereceda.Setting.Degeneracy
import Cereceda.Intro.Examples
import Cereceda.Intro.Subdivision
import Cereceda.LB.Facts

namespace Cereceda

open Finset

namespace Classes

/-! ### C_6 has no chord on its 6-cycle -/

/-- The 6-cycle `0 1 2 3 4 5 0` of `C_6`, as an explicit walk. -/
def c6 : (SimpleGraph.cycleGraph 6).Walk 0 0 :=
  .cons (by decide : (SimpleGraph.cycleGraph 6).Adj 0 1) <|
  .cons (by decide : (SimpleGraph.cycleGraph 6).Adj 1 2) <|
  .cons (by decide : (SimpleGraph.cycleGraph 6).Adj 2 3) <|
  .cons (by decide : (SimpleGraph.cycleGraph 6).Adj 3 4) <|
  .cons (by decide : (SimpleGraph.cycleGraph 6).Adj 4 5) <|
  .cons (by decide : (SimpleGraph.cycleGraph 6).Adj 5 0) .nil

theorem c6_isCycle : c6.IsCycle := by
  unfold c6
  rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
  decide

theorem c6_length : c6.length = 6 := rfl

/-- Every edge of `C_6` is an edge of the cycle `c6`: no chord. -/
theorem c6_edges : ∀ x y : Fin 6, (SimpleGraph.cycleGraph 6).Adj x y → s(x, y) ∈ c6.edges := by
  decide

/-! ### K_{2,m}: degrees, average degree -/

variable {m : ℕ}

theorem K2m_degree_inl [DecidableRel (completeBipartiteGraph (Fin 2) (Fin m)).Adj] (a : Fin 2) :
    (completeBipartiteGraph (Fin 2) (Fin m)).degree (Sum.inl a) = m := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have h : (completeBipartiteGraph (Fin 2) (Fin m)).neighborFinset (Sum.inl a) = univ.map Function.Embedding.inr := by
    ext u
    cases u <;> simp
  rw [h, card_map, card_univ, Fintype.card_fin]

theorem K2m_degree_inr [DecidableRel (completeBipartiteGraph (Fin 2) (Fin m)).Adj] (b : Fin m) :
    (completeBipartiteGraph (Fin 2) (Fin m)).degree (Sum.inr b) = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have h : (completeBipartiteGraph (Fin 2) (Fin m)).neighborFinset (Sum.inr b) = univ.map Function.Embedding.inl := by
    ext u
    cases u <;> simp
  rw [h, card_map, card_univ, Fintype.card_fin]

theorem K2m_isBipartite : (completeBipartiteGraph (Fin 2) (Fin m)).IsBipartite :=
  ⟨SimpleGraph.Coloring.mk (fun v => match v with | .inl _ => 0 | .inr _ => 1)
    (by intro u v huv; rcases u with u | u <;> rcases v with v | v <;> simp_all)⟩

/-- `mad` is at least the average degree `2|E| / |V|` (the set of all vertices). -/
theorem le_mad {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    2 * (G.edgeFinset.card : ℝ) / Fintype.card V ≤ mad G := by
  unfold mad
  apply le_csSup
  · refine (Set.finite_range (fun s : Finset V =>
      2 * ((G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ s)).card : ℝ) / s.card)).bddAbove.mono ?_
    rintro r ⟨s, -, rfl⟩
    exact ⟨s, rfl⟩
  · refine ⟨univ, univ_nonempty, ?_⟩
    rw [Finset.filter_true_of_mem (fun e _ v _ => mem_univ v), card_univ]

end Classes

open Classical in
theorem intro_no_class_contains_all_proved :
    (¬ IsChordalBipartite (SimpleGraph.cycleGraph 6)) ∧
    ((completeBipartiteGraph (Fin 2) (Fin 4)).IsBipartite ∧ IsDegenerate (completeBipartiteGraph (Fin 2) (Fin 4)) 2 ∧
      (completeBipartiteGraph (Fin 2) (Fin 4)).maxDegree = 4) ∧
    (∀ ε : ℝ, 0 < ε → ∃ m : ℕ, (completeBipartiteGraph (Fin 2) (Fin m)).IsBipartite ∧
      IsDegenerate (completeBipartiteGraph (Fin 2) (Fin m)) 2 ∧ 4 - ε < mad (completeBipartiteGraph (Fin 2) (Fin m))) := by
  refine ⟨?_, ⟨Classes.K2m_isBipartite, Examples.K2m_isDegenerate 4, ?_⟩, ?_⟩
  · rintro ⟨-, h⟩
    obtain ⟨x, -, y, -, hxy, hnot⟩ := h 0 Classes.c6 Classes.c6_isCycle (by rw [Classes.c6_length])
    exact hnot (Classes.c6_edges x y hxy)
  · apply le_antisymm
    · refine SimpleGraph.maxDegree_le_of_forall_degree_le _ _ fun v => ?_
      rcases v with a | b
      · rw [Classes.K2m_degree_inl]
      · rw [Classes.K2m_degree_inr]
        norm_num
    · calc 4 = (completeBipartiteGraph (Fin 2) (Fin 4)).degree (Sum.inl 0) := (Classes.K2m_degree_inl 0).symm
        _ ≤ _ := SimpleGraph.degree_le_maxDegree _ _
  · intro ε hε
    refine ⟨⌈8 / ε⌉₊, Classes.K2m_isBipartite, Examples.K2m_isDegenerate _, ?_⟩
    refine lt_of_lt_of_le ?_ (Classes.le_mad _)
    rw [Examples.K2m_card_edges]
    simp only [Fintype.card_sum, Fintype.card_fin]
    have hm : 8 / ε ≤ (⌈8 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hm' : 8 ≤ (⌈8 / ε⌉₊ : ℝ) * ε := (div_le_iff₀ hε).mp hm
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    nlinarith

namespace Classes

/-! ### Fans: `pathApex n 1 (fun _ => 0)` -/

/-- The bag `{apex, v_i, v_{i+1}}` of the path decomposition of the fan on `m + 2` path vertices. -/
def fanBag (m : ℕ) (i : Fin (m + 1)) : Finset (Fin (m + 2) ⊕ Fin 1) :=
  {Sum.inr 0, Sum.inl i.castSucc, Sum.inl i.succ}

/-- The node of the path decomposition used for the path vertex `j`. -/
def fanNode (m : ℕ) (j : Fin (m + 2)) : Fin (m + 1) :=
  if h : j.val ≤ m then ⟨j.val, by omega⟩ else ⟨m, by omega⟩

theorem mem_fanBag_node (m : ℕ) (j : Fin (m + 2)) : (Sum.inl j : Fin (m + 2) ⊕ Fin 1) ∈ fanBag m (fanNode m j) := by
  unfold fanBag fanNode
  split_ifs with h
  · simp [Fin.ext_iff]
  · simp only [mem_insert, mem_singleton, reduceCtorEq, Sum.inl.injEq, Fin.ext_iff, Fin.val_castSucc,
      Fin.val_succ, false_or]
    right
    have := j.isLt
    omega

theorem mem_fanBag_inl (m : ℕ) (i : Fin (m + 1)) (j : Fin (m + 2)) :
    (Sum.inl j : Fin (m + 2) ⊕ Fin 1) ∈ fanBag m i ↔ j.val = i.val ∨ j.val = i.val + 1 := by
  simp [fanBag, Fin.ext_iff]

theorem apex_mem_fanBag (m : ℕ) (i : Fin (m + 1)) (k : Fin 1) : (Sum.inr k : Fin (m + 2) ⊕ Fin 1) ∈ fanBag m i := by
  rw [Fin.fin_one_eq_zero k]
  simp [fanBag]

theorem card_fanBag (m : ℕ) (i : Fin (m + 1)) : (fanBag m i).card = 3 := by
  unfold fanBag
  refine Finset.card_eq_three.2 ⟨_, _, _, by simp, by simp, ?_, rfl⟩
  simp [Fin.ext_iff]

/-- The path decomposition of the fan, of width 2. -/
def fanDecomp (m : ℕ) : TreeDecomposition (pathApex (m + 2) 1 (fun _ => 0)) (Fin (m + 1)) where
  T := SimpleGraph.pathGraph (m + 1)
  isTree := SimpleGraph.isTree_pathGraph_add_one m
  bag := fanBag m
  cover_vertex := by
    rintro (j | k)
    · exact ⟨fanNode m j, mem_fanBag_node m j⟩
    · exact ⟨0, apex_mem_fanBag m 0 k⟩
  cover_edge := by
    rintro (i | k) (j | l) h
    · change i.val + 1 = j.val ∨ j.val + 1 = i.val at h
      rcases h with h | h
      · exact ⟨⟨i.val, by omega⟩, (mem_fanBag_inl m _ i).2 (Or.inl rfl), (mem_fanBag_inl m _ j).2 (Or.inr h.symm)⟩
      · exact ⟨⟨j.val, by omega⟩, (mem_fanBag_inl m _ i).2 (Or.inr h.symm), (mem_fanBag_inl m _ j).2 (Or.inl rfl)⟩
    · exact ⟨fanNode m i, mem_fanBag_node m i, apex_mem_fanBag m _ l⟩
    · exact ⟨fanNode m j, apex_mem_fanBag m _ k, mem_fanBag_node m j⟩
    · exact absurd h id
  subtree := by
    rintro (j | k)
    · refine Subdivision.connected_of_center (c := fanNode m j) (mem_fanBag_node m j) ?_
      intro w hw
      change (Sum.inl j : Fin (m + 2) ⊕ Fin 1) ∈ fanBag m w at hw
      rw [mem_fanBag_inl] at hw
      rw [SimpleGraph.pathGraph_adj]
      unfold fanNode
      split_ifs with h
      · rcases hw with hw | hw
        · left
          exact Fin.ext hw.symm
        · right
          right
          simp only
          omega
      · left
        apply Fin.ext
        simp only
        have := j.isLt
        have := w.isLt
        omega
    · have hS : {i : Fin (m + 1) | (Sum.inr k : Fin (m + 2) ⊕ Fin 1) ∈ fanBag m i} = Set.univ :=
        Set.eq_univ_of_forall fun i => apex_mem_fanBag m i k
      rw [hS]
      exact (SimpleGraph.induceUnivIso _).connected_iff.2 (SimpleGraph.connected_pathGraph_add_one m)

theorem fanDecomp_width (m : ℕ) : (fanDecomp m).width = 2 := by
  unfold TreeDecomposition.width
  change univ.sup (fun i => (fanBag m i).card) - 1 = 2
  simp only [card_fanBag]
  rw [Finset.sup_const univ_nonempty]

/-- The triangle `apex, v_1, v_2` of the fan. -/
def fanTri (m : ℕ) : Fin 3 → Fin (m + 2) ⊕ Fin 1
  | 0 => Sum.inr 0
  | 1 => Sum.inl 0
  | 2 => Sum.inl 1

theorem fanTri_adj (m : ℕ) (k l : Fin 3) (hkl : k ≠ l) :
    (pathApex (m + 2) 1 (fun _ => 0)).Adj (fanTri m k) (fanTri m l) := by
  have e01 : (pathApex (m + 2) 1 (fun _ => 0)).Adj (Sum.inr 0) (Sum.inl 0) := rfl
  have e02 : (pathApex (m + 2) 1 (fun _ => 0)).Adj (Sum.inr 0) (Sum.inl 1) := rfl
  have e12 : (pathApex (m + 2) 1 (fun _ => 0)).Adj (Sum.inl 0) (Sum.inl 1) := by
    change (0 : Fin (m + 2)).val + 1 = (1 : Fin (m + 2)).val ∨ (1 : Fin (m + 2)).val + 1 = (0 : Fin (m + 2)).val
    simp
  fin_cases k <;> fin_cases l
  · exact absurd rfl hkl
  · exact e01
  · exact e02
  · exact e01.symm
  · exact absurd rfl hkl
  · exact e12
  · exact e02.symm
  · exact e12.symm
  · exact absurd rfl hkl

theorem fanTri_injective (m : ℕ) : Function.Injective (fanTri m) := by
  intro k l h
  by_contra hkl
  exact (pathApex (m + 2) 1 (fun _ => 0)).loopless.irrefl _ (h ▸ fanTri_adj m k l hkl)

/-- Every tree decomposition of the fan has width at least 2 (Helly for the triangle). -/
theorem two_le_width {ι : Type} [Fintype ι] (m : ℕ) (D : TreeDecomposition (pathApex (m + 2) 1 (fun _ => 0)) ι) :
    2 ≤ D.width := by
  obtain ⟨i, hi⟩ := Subdivision.helly D.isTree (fun k : Fin 3 => {i | fanTri m k ∈ D.bag i})
    (fun k => Subdivision.setConn_of_connected (D.subtree (fanTri m k))) (by
      intro k l
      by_cases hkl : k = l
      · subst hkl
        obtain ⟨i, hi⟩ := D.cover_vertex (fanTri m k)
        exact ⟨i, hi, hi⟩
      · obtain ⟨i, hi, hi'⟩ := D.cover_edge _ _ (fanTri_adj m k l hkl)
        exact ⟨i, hi, hi'⟩)
  have hsub : univ.image (fanTri m) ⊆ D.bag i := by
    intro v hv
    obtain ⟨k, -, rfl⟩ := mem_image.1 hv
    exact hi k
  have h3 : 3 ≤ (D.bag i).card := by
    have := card_le_card hsub
    rwa [card_image_of_injective _ (fanTri_injective m), card_univ, Fintype.card_fin] at this
  have hle : (D.bag i).card ≤ univ.sup (fun i => (D.bag i).card) := le_sup (f := fun i => (D.bag i).card) (mem_univ i)
  unfold TreeDecomposition.width
  omega

end Classes

theorem intro_fans_proved (n : ℕ) (hn : 2 ≤ n) :
    IsDegenerate (pathApex n 1 (fun _ => 0)) 2 ∧ ¬ (pathApex n 1 (fun _ => 0)).IsBipartite := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  refine ⟨FactsAux.degenerate_of_order _ 2 _ (FactsAux.pathApex_order (m + 2) 1 _), ?_⟩
  · rintro ⟨C⟩
    have h01 := C.valid (Classes.fanTri_adj m 0 1 (by decide))
    have h02 := C.valid (Classes.fanTri_adj m 0 2 (by decide))
    have h12 := C.valid (Classes.fanTri_adj m 1 2 (by decide))
    revert h01 h02 h12
    generalize C (Classes.fanTri m 0) = a
    generalize C (Classes.fanTri m 1) = b
    generalize C (Classes.fanTri m 2) = c
    revert a b c
    decide

end Cereceda
