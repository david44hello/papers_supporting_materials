/-
Cereceda/Bip/Triangle.lean — proofs of the rows of Remark 3.9 (short v3.90 l. 550-563), the sentence after Table 2
(l. 487-489), open problems 1-2 (5-cycle, l. 751; 6-cycles and girth, l. 755-759) and Propositions 4.1 / 4.6 in the
vertex count (l. 581, 588, 673, 683) (`*_proved`; the vertex forms take the finiteness of
the diameter, which Statements supplies from Theorem 1.2, as `prop_4_1_proved` does).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Triangle
import Cereceda.Defs.Bipartite
import Cereceda.Setting.Small
import Cereceda.Bip.Sides
import Cereceda.Bip.Example8
import Cereceda.LB.LowerBounds

namespace Cereceda

open Finset

namespace TriAux

/-- `α` of the instance of Remark 3.9: `(s, u₁, u₂, u₃) ↦ (1, 0, 1, 2)`. -/
def alphaT : Fin 4 → Fin 4 := ![1, 0, 1, 2]

/-- `β` of the instance of Remark 3.9: `(s, u₁, u₂, u₃) ↦ (0, 1, 2, 0)`. -/
def betaT : Fin 4 → Fin 4 := ![0, 1, 2, 0]

theorem adj_iff (u v : Fin 4) : tri.graph.Adj u v ↔ (u ≠ v ∧ (v ∈ triOut u ∨ u ∈ triOut v)) := by
  simp only [Skeleton.graph, SimpleGraph.fromRel_adj]
  exact Iff.rfl

theorem alpha_greedy : tri.IsGreedy tri.x alphaT := by
  unfold Instance.IsGreedy IsLeastFree
  decide

theorem beta_greedy : tri.IsGreedy tri.g betaT := by
  unfold Instance.IsGreedy IsLeastFree
  decide

theorem alpha_eq {α : Fin 4 → Fin 4} (hα : tri.IsGreedy tri.x α) : α = alphaT :=
  (def_2_2_greedy_proved tri tri.x).unique hα alpha_greedy

theorem beta_eq {β : Fin 4 → Fin 4} (hβ : tri.IsGreedy tri.g β) : β = betaT :=
  (def_2_2_greedy_proved tri tri.g).unique hβ beta_greedy

theorem singleSink : tri.IsSingleSink := by
  unfold Skeleton.IsSingleSink
  decide

theorem edges (u v : Fin 4) :
    tri.graph.Adj u v ↔ s(u, v) ∈ ({s(1, 2), s(2, 3), s(1, 3), s(0, 1)} : Finset (Sym2 (Fin 4))) := by
  rw [adj_iff]
  revert u v
  decide

theorem notBipartite : ¬ tri.graph.IsBipartite := by
  rintro ⟨C⟩
  have e12 := C.valid ((adj_iff 1 2).mpr (by decide))
  have e23 := C.valid ((adj_iff 2 3).mpr (by decide))
  have e13 := C.valid ((adj_iff 1 3).mpr (by decide))
  have key : ∀ a b c : Fin 2, a ≠ b → b ≠ c → a ≠ c → False := by
    intro a b c h1 h2 h3
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
  exact key _ _ _ e12 e23 e13

/-- The paper's argument (v3.90 l. 554-556): a colouring with `μ ≥ α`, `μ ≥ β`, `μ(s) = x` and `μ(u₁) ≠ μ(s)` has
`μ(u₁) ≥ 1`, `μ(u₁) ≠ 1` and `μ(u₂), μ(u₃) ≥ 2`, so it uses only `2` and `3` on the triangle. -/
theorem mu_forced (μ : Fin 4 → Fin 4) (ha : ∀ v, alphaT v ≤ μ v) (hb : ∀ v, betaT v ≤ μ v)
    (hs : μ tri.sink = tri.x) (hne : μ 1 ≠ μ tri.sink) :
    1 ≤ μ 1 ∧ μ 1 ≠ 1 ∧ 2 ≤ μ 2 ∧ 2 ≤ μ 3 ∧
      μ 1 ∈ ({2, 3} : Finset (Fin 4)) ∧ μ 2 ∈ ({2, 3} : Finset (Fin 4)) ∧ μ 3 ∈ ({2, 3} : Finset (Fin 4)) := by
  have hs' : μ 0 = 1 := hs
  have hne' : μ 1 ≠ μ 0 := hne
  have b1 : (1 : Fin 4) ≤ μ 1 := hb 1
  have b2 : (2 : Fin 4) ≤ μ 2 := hb 2
  have a3 : (2 : Fin 4) ≤ μ 3 := ha 3
  have key : ∀ m0 m1 m2 m3 : Fin 4, m0 = 1 → m1 ≠ m0 → 1 ≤ m1 → 2 ≤ m2 → 2 ≤ m3 →
      1 ≤ m1 ∧ m1 ≠ 1 ∧ 2 ≤ m2 ∧ 2 ≤ m3 ∧
        m1 ∈ ({2, 3} : Finset (Fin 4)) ∧ m2 ∈ ({2, 3} : Finset (Fin 4)) ∧ m3 ∈ ({2, 3} : Finset (Fin 4)) := by
    decide
  exact key (μ 0) (μ 1) (μ 2) (μ 3) hs' hne' b1 b2 a3

/-- No colouring as in Lemma 3.4 (v3.90 l. 554-556): it would colour the triangle with the two colours `2` and `3`. -/
theorem no_mu : ¬ ∃ μ : Fin 4 → Fin 4, IsProperFn tri.graph μ ∧ (∀ v, μ v ∈ tri.L v) ∧ (∀ v, alphaT v ≤ μ v) ∧
    (∀ v, betaT v ≤ μ v) ∧ μ tri.sink = tri.x := by
  rintro ⟨μ, hp, -, hα, hβ, hs⟩
  have h01 := hp 0 1 ((adj_iff 0 1).mpr (by decide))
  have h12 := hp 1 2 ((adj_iff 1 2).mpr (by decide))
  have h23 := hp 2 3 ((adj_iff 2 3).mpr (by decide))
  have h13 := hp 1 3 ((adj_iff 1 3).mpr (by decide))
  have b1 : (1 : Fin 4) ≤ μ 1 := hβ 1
  have b2 : (2 : Fin 4) ≤ μ 2 := hβ 2
  have a3 : (2 : Fin 4) ≤ μ 3 := hα 3
  have hs' : μ 0 = 1 := hs
  have key : ∀ m0 m1 m2 m3 : Fin 4, m0 = 1 → m0 ≠ m1 → m1 ≠ m2 → m2 ≠ m3 → m1 ≠ m3 → 1 ≤ m1 → 2 ≤ m2 →
      2 ≤ m3 → False := by decide
  exact key (μ 0) (μ 1) (μ 2) (μ 3) hs' h01 h12 h23 h13 b1 b2 a3

theorem seq : tri.IsSeq alphaT triMoves betaT := by
  unfold Instance.IsSeq triMoves
  simp only [IsSeq, LegalMove, adj_iff]
  decide

end TriAux

open TriAux

theorem rem_3_9_proved :
    tri.IsSingleSink ∧ tri.g = 0 ∧
    (∀ u v, tri.graph.Adj u v ↔ s(u, v) ∈ ({s(1, 2), s(2, 3), s(1, 3), s(0, 1)} : Finset (Sym2 (Fin 4)))) ∧
    ¬ tri.graph.IsBipartite ∧
    ∀ α β : Fin 4 → Fin 4, tri.IsGreedy tri.x α → tri.IsGreedy tri.g β →
      ((α 1, β 1) = (0, 1) ∧ (α 2, β 2) = (1, 2) ∧ (α 3, β 3) = (2, 0)) ∧
      (∀ μ : Fin 4 → Fin 4, (∀ v, α v ≤ μ v) → (∀ v, β v ≤ μ v) → μ tri.sink = tri.x → μ 1 ≠ μ tri.sink →
        1 ≤ μ 1 ∧ μ 1 ≠ 1 ∧ 2 ≤ μ 2 ∧ 2 ≤ μ 3 ∧
          μ 1 ∈ ({2, 3} : Finset (Fin 4)) ∧ μ 2 ∈ ({2, 3} : Finset (Fin 4)) ∧ μ 3 ∈ ({2, 3} : Finset (Fin 4))) ∧
      (¬ ∃ μ : Fin 4 → Fin 4, IsProperFn tri.graph μ ∧ (∀ v, μ v ∈ tri.L v) ∧ (∀ v, α v ≤ μ v) ∧
        (∀ v, β v ≤ μ v) ∧ μ tri.sink = tri.x) ∧
      ((tri.out 3).card = 2 ∧ ¬ IsFixed α β 3 ∧ α 3 = 2 ∧ (∀ u ∈ tri.out 3, ¬ IsFixed α β u) ∧
        ¬ ∃ p ∈ tri.out 3, IsFixed α β p ∧ (α p = 0 ∨ α p = 1)) ∧
      (tri.IsSeq α triMoves β ∧ triMoves.length = 5 ∧ movesOf triMoves tri.sink = 1 ∧
        ∀ v, v ≠ tri.sink → movesOf triMoves v ≤ 2) := by
  refine ⟨singleSink, rfl, edges, notBipartite, fun α β hα hβ => ?_⟩
  obtain rfl := alpha_eq hα
  obtain rfl := beta_eq hβ
  refine ⟨by decide, mu_forced, no_mu, ⟨by decide, ?_, by decide, ?_, ?_⟩, seq, rfl, by decide, by decide⟩
  · unfold IsFixed
    decide
  · unfold IsFixed
    decide
  · unfold IsFixed
    decide

theorem sec3_table_fixed_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots)
    (hg0 : I.g = 0) (side : W → Fin 2) (hside : IsProperFn I.graph side) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (v : W) :
    (v ≠ I.sink → IsJoiner α β v → side v = side I.sink) ∧ (IsLeaver α β v → side v ≠ side I.sink) ∧
    (v ≠ I.sink → side v = side I.sink → (α v = 0 ∨ β v = 1) → IsFixed α β v) ∧
    (side v ≠ side I.sink → (α v = 1 ∨ β v = 0) → IsFixed α β v) := by
  obtain ⟨h0, h1⟩ := lem_3_5_proved I hnr hg0 side hside α β hα hβ v
  obtain ⟨hj, hl, -⟩ := lem_3_5_equiv_proved I hnr hg0 side hside α β hα hβ
  refine ⟨fun _ h => hj v h, hl v, fun hv hs h => ?_, fun hs h => ?_⟩
  · have hp := h0 hv hs
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hp
    unfold IsFixed
    rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rcases h with h | h <;> simp_all
  · have hp := h1 hs
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hp
    unfold IsFixed
    rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rcases h with h | h <;> simp_all

theorem open_1_five_cycle_proved :
    ex8.graph.Adj 0 1 ∧ ex8.graph.Adj 1 3 ∧ ex8.graph.Adj 3 4 ∧ ex8.graph.Adj 4 2 ∧ ex8.graph.Adj 2 0 ∧
    [(0 : Fin 8), 1, 3, 4, 2].Nodup := by
  refine ⟨(Ex8Aux.adj_iff 0 1).mpr (by decide), (Ex8Aux.adj_iff 1 3).mpr (by decide),
    (Ex8Aux.adj_iff 3 4).mpr (by decide), (Ex8Aux.adj_iff 4 2).mpr (by decide),
    (Ex8Aux.adj_iff 2 0).mpr (by decide), by decide⟩

/-- `i + 1` and `i` lie in different residue classes mod `p ≥ 2`. -/
theorem succ_mod_ne (p i : ℕ) (hp : 2 ≤ p) : (i + 1) % p ≠ i % p := by
  intro h
  have h0 := Nat.sub_mod_eq_zero_of_mod_eq h
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  rw [show i + 1 - i = 1 by omega, h1] at h0
  omega

theorem open_2_six_cycle_proved (n p : ℕ) (hp : 2 ≤ p) (i : ℕ) (hi : 1 ≤ i) (hin : i + p + 1 ≤ n) :
    let G := spacedGraph n p (by omega)
    let aj : Fin n ⊕ Fin p := .inr ⟨i % p, Nat.mod_lt _ (by omega)⟩
    let aj1 : Fin n ⊕ Fin p := .inr ⟨(i + 1) % p, Nat.mod_lt _ (by omega)⟩
    let vi : Fin n ⊕ Fin p := .inl ⟨i - 1, by omega⟩
    let vi1 : Fin n ⊕ Fin p := .inl ⟨i, by omega⟩
    let vip1 : Fin n ⊕ Fin p := .inl ⟨i + p, by omega⟩
    let vip : Fin n ⊕ Fin p := .inl ⟨i + p - 1, by omega⟩
    G.Adj aj vi ∧ G.Adj vi vi1 ∧ G.Adj vi1 aj1 ∧ G.Adj aj1 vip1 ∧ G.Adj vip1 vip ∧ G.Adj vip aj ∧
      [aj, vi, vi1, aj1, vip1, vip].Nodup := by
  intro G aj aj1 vi vi1 vip1 vip
  have hmod := succ_mod_ne p i hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (⟨(i - 1 + 1) % p, _⟩ : Fin p) = ⟨i % p, _⟩
    exact Fin.ext (by simp only; rw [Nat.sub_add_cancel hi])
  · show (i - 1) + 1 = i ∨ i + 1 = i - 1
    omega
  · rfl
  · show (⟨(i + p + 1) % p, _⟩ : Fin p) = ⟨(i + 1) % p, _⟩
    exact Fin.ext (by simp only; rw [show i + p + 1 = (i + 1) + p by omega, Nat.add_mod_right])
  · show i + p + 1 = i + p - 1 ∨ i + p - 1 + 1 = i + p
    omega
  · show (⟨(i + p - 1 + 1) % p, _⟩ : Fin p) = ⟨i % p, _⟩
    exact Fin.ext (by simp only; rw [show i + p - 1 + 1 = i + p by omega, Nat.add_mod_right])
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, aj, aj1, vi, vi1, vip1, vip,
      reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq, Fin.mk.injEq, false_or, List.nodup_nil, and_true,
      not_false_eq_true, true_and]
    and_intros
    all_goals omega

theorem open_2_girth_proved (n p : ℕ) (hp : 2 ≤ p) (hn : p + 2 ≤ n) :
    (spacedGraph n p (by omega)).egirth ≤ 6 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hnd⟩ := open_2_six_cycle_proved n p hp 1 le_rfl (by omega)
  let w := SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h3 (SimpleGraph.Walk.cons h4
    (SimpleGraph.Walk.cons h5 (SimpleGraph.Walk.cons h6 SimpleGraph.Walk.nil))))
  have hpath : w.IsPath := SimpleGraph.Walk.IsPath.mk' ((List.nodup_rotate (n := 1)).mpr hnd)
  have hcyc : (SimpleGraph.Walk.cons h1 w).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨hpath, ?_⟩
    simp [w, SimpleGraph.Walk.edges_cons]
    omega
  calc (spacedGraph n p (by omega)).egirth ≤ (SimpleGraph.Walk.cons h1 w).length := hcyc.egirth_le_length
    _ = 6 := by simp [w]

theorem prop_4_1_vertices_proved (l : ℕ) (hl : 5 ≤ l) (hfin : (recolGraph (Hgraph l) 4).ediam ≠ ⊤) :
    Fintype.card (Fin l ⊕ Fin 2) = l + 2 ∧
    (((Fintype.card (Fin l ⊕ Fin 2) : ℕ) : ℝ) - 7) ^ 2 / 8 ≤ ((recolGraph (Hgraph l) 4).diam : ℝ) := by
  have hc : Fintype.card (Fin l ⊕ Fin 2) = l + 2 := by simp
  refine ⟨hc, ?_⟩
  rw [hc]
  exact (prop_4_1_proved l hl hfin).2

theorem prop_4_6_vertices_proved (l : ℕ) (hl : 29 ≤ l) (hfin : (recolGraph (Jgraph l) 4).ediam ≠ ⊤) :
    Fintype.card (Fin l ⊕ Fin 4) = l + 4 ∧
    (((Fintype.card (Fin l ⊕ Fin 4) : ℕ) : ℝ) - 33) ^ 2 / 128 ≤ ((recolGraph (Jgraph l) 4).diam : ℝ) := by
  have hc : Fintype.card (Fin l ⊕ Fin 4) = l + 4 := by simp
  refine ⟨hc, ?_⟩
  rw [hc]
  exact (prop_4_6_proved l hl hfin).2

end Cereceda
