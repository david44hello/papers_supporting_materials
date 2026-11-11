/-
EulerFlow/Sec2/ShortClaims6.lean — cycles through edges of even graphs and degrees at a triangle replacement.
Part of the Lean 4 proof of the paper "The Cranston–Li–Su–Wang–Xu (2026) conjecture is true" by Dave Goel.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import EulerFlow.Sec2.ShortClaims
import EulerFlow.Sec2.ShortClaims3
import EulerFlow.Reduction.Triangle

namespace EulerFlow

open MGraph Finset

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-! Every edge of an even graph lies on a directed cycle. -/

omit [Fintype V] in
theorem even_edge_on_cycle (G : MGraph V E) (hev : G.IsEven) (e : E) :
    ∃ Q : G.DirCycle, ∃ d ∈ Q.darts, d.1 = e := by
  obtain ⟨⟨D, hD⟩, hall⟩ := even_three_flow_named_proved G hev
  have hflow : G.IsFlow (constFlow (1 : ℤ) D) := (hall D hD).1
  have hval : ∀ e', constFlow (1 : ℤ) D e' = -1 ∨ constFlow (1 : ℤ) D e' = 0 ∨ constFlow (1 : ℤ) D e' = 1 := by
    intro e'; unfold constFlow; split_ifs <;> simp
  obtain ⟨Qs, -, -, hsum, -⟩ := G.circ_decomp (constFlow (1 : ℤ) D) hval hflow
  have hne : constFlow (1 : ℤ) D e ≠ 0 := by unfold constFlow; split_ifs <;> simp
  have hex : ∃ Q ∈ Qs, Q.chi e ≠ 0 := by
    by_contra hcon
    apply hne
    rw [← hsum e]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hx
    by_contra hx0
    exact hcon ⟨Q, hQ, hx0⟩
  obtain ⟨Q, -, hQe⟩ := hex
  obtain ⟨d, hd, hde⟩ := List.mem_map.1 ((Q.chi_ne_zero_iff e).1 hQe)
  exact ⟨Q, d, hd, hde⟩

/-! Cutting a cycle at an edge gives a path in the graph with that edge deleted. -/

/-- A closed chain `pre ++ d :: post`, read from `d` once around. -/
private lemma chain_cut {α : Type} {R : α → α → Prop} {d : α} (pre post : List α)
    (hchain : (pre ++ d :: post).IsChain R)
    (hclose : ∀ x ∈ (pre ++ d :: post).getLast?, ∀ y ∈ (pre ++ d :: post).head?, R x y) :
    (d :: (post ++ pre ++ [d])).IsChain R := by
  have key : ((d :: post) ++ (pre ++ [d])).IsChain R := by
    rw [List.isChain_append] at hchain ⊢
    obtain ⟨hpre, hdpost, hjoin⟩ := hchain
    refine ⟨hdpost, ?_, ?_⟩
    · rw [List.isChain_append]
      exact ⟨hpre, List.isChain_singleton _, fun x hx y hy => hjoin x hx y hy⟩
    · intro x hx y hy
      have hx' : x ∈ (pre ++ d :: post).getLast? := by
        rw [List.getLast?_append]; rw [Option.mem_def] at hx ⊢; rw [hx]; rfl
      cases pre with
      | nil => exact hclose x hx' y hy
      | cons p pre' => exact hclose x hx' y hy
  have hlist : d :: (post ++ pre ++ [d]) = (d :: post) ++ (pre ++ [d]) := by simp
  rw [hlist]; exact key

/-- The inner part of a chain `d :: (L ++ [d])`. -/
private lemma chain_inner {α : Type} {R : α → α → Prop} {d : α} {L : List α} (hL : L ≠ [])
    (h : (d :: (L ++ [d])).IsChain R) : L.IsChain R ∧ R d (L.head hL) ∧ R (L.getLast hL) d := by
  rw [List.isChain_cons, List.isChain_append] at h
  obtain ⟨hhead, hLc, -, hlast⟩ := h
  refine ⟨hLc, hhead _ ?_, hlast _ (List.getLast_mem_getLast? hL) d rfl⟩
  cases L with
  | nil => exact absurd rfl hL
  | cons a L' => rfl

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem path_of_cycle_through (G : MGraph V E) (Q : G.DirCycle) {e : E} (hQ : (e, true) ∈ Q.darts)
    (hloop : ¬ G.IsLoop e) : Nonempty ((G.deleteEdge e).Path (G.src e) (G.tgt e)) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hQ
  have hclose : ∀ x ∈ Q.darts.getLast?, ∀ y ∈ Q.darts.head?, G.dartHead x = G.dartTail y := by
    intro x hx y hy
    rw [Option.mem_unique hx (List.getLast_mem_getLast? Q.ne_nil),
      Option.mem_unique hy (List.head_mem_head? Q.ne_nil)]
    exact Q.closes
  have hchain := Q.chain
  have hedges := Q.edges_nodup
  have htails := Q.tails_nodup
  rw [hsplit] at hclose hchain hedges htails
  have hcut := chain_cut pre post hchain hclose
  -- the darts of the rest avoid `e`
  have hne : ∀ x ∈ post ++ pre, x.1 ≠ e := by
    intro x hx hxe
    rw [List.map_append, List.map_cons, List.nodup_middle, List.nodup_cons] at hedges
    refine hedges.1 ?_
    rcases List.mem_append.1 hx with h | h
    · exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨x, h, hxe⟩))
    · exact List.mem_append.2 (Or.inl (List.mem_map.2 ⟨x, h, hxe⟩))
  -- the same darts as darts of `G - e`; from here on only `hmap` is used
  obtain ⟨P', hmap⟩ : ∃ P' : List ({x : E // x ≠ e} × Bool),
      P'.map (fun x => ((x.1 : E), x.2)) = post ++ pre :=
    ⟨(post ++ pre).pmap (fun x (h : x.1 ≠ e) => ((⟨x.1, h⟩ : {x : E // x ≠ e}), x.2)) hne, by
      rw [List.map_pmap]
      exact (List.pmap_eq_map (f := fun a => a) hne).trans (by simp)⟩
  have hP' : P' ≠ [] := by
    rintro rfl
    have h0 : post ++ pre = [] := hmap.symm
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h0
    have h := hclose (e, true) rfl (e, true) rfl
    simp [dartHead, dartTail, endVertex] at h
    exact hloop h
  have hL : P'.map (fun x => ((x.1 : E), x.2)) ≠ [] := by simpa using hP'
  have hperm1 : (post ++ pre ++ [(e, true)]).Perm ((e, true) :: (post ++ pre)) := by
    exact (List.perm_append_comm : (post ++ pre ++ [(e, true)]).Perm ([(e, true)] ++ (post ++ pre)))
  have hperm : (post ++ pre ++ [(e, true)]).Perm (pre ++ (e, true) :: post) :=
    hperm1.trans ((List.Perm.cons (e, true)
      (List.perm_append_comm : (post ++ pre).Perm (pre ++ post))).trans List.perm_middle.symm)
  have hnd : ((post ++ pre ++ [(e, true)]).map G.dartTail).Nodup := (hperm.map G.dartTail).nodup_iff.2 htails
  have hverts : P'.map (G.deleteEdge e).dartTail ++ [G.tgt e] =
      (post ++ pre ++ [(e, true)]).map G.dartTail := by
    rw [List.map_append, ← hmap, List.map_map]
    rfl
  rw [← hmap] at hcut
  obtain ⟨hLchain, hstart, hend⟩ := chain_inner hL hcut
  refine ⟨⟨P', hP', ?_, ?_, ?_, ?_⟩⟩
  · exact ((List.isChain_map _).1 hLchain).imp (fun _ _ h => h)
  · have h := hstart; rw [List.head_map] at h; exact h.symm
  · have h := hend; rw [List.getLast_map] at h; exact h
  · rw [hverts]; exact hnd

theorem intro_even_no_bridge_proved (G : MGraph V E) (hev : G.IsEven) (e : E) :
    (∃ Q : G.DirCycle, ∃ d ∈ Q.darts, d.1 = e) ∧
    (¬ G.IsLoop e → Nonempty ((G.deleteEdge e).Path (G.src e) (G.tgt e))) := by
  have h1 := even_edge_on_cycle G hev e
  refine ⟨h1, fun hloop => ?_⟩
  obtain ⟨Q, ⟨e', b⟩, hd, hde⟩ := h1
  obtain rfl : e' = e := hde
  cases b with
  | true => exact path_of_cycle_through G Q hd hloop
  | false =>
    exact path_of_cycle_through G (cycleReverse G Q)
      (List.mem_reverse.2 (List.mem_map.2 ⟨(e', false), hd, rfl⟩)) hloop


omit [Fintype V] in
private theorem outside_ends_sum (G : MGraph V E) (D : Finset E) (v : V) :
    (univ.filter fun i : E × Bool => i.1 ∉ D ∧ G.endVertex i = v).card =
      ∑ e ∈ univ.filter (fun e => e ∉ D), G.endCount v e := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Finset.sum_filter, MGraph.endVertex, MGraph.endCount]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e ∈ D <;> simp [he, add_comm]

private theorem degree_outside_add (G : MGraph V E) (D : Finset E) (v : V) :
    G.degree v =
      (univ.filter fun i : E × Bool => i.1 ∉ D ∧ G.endVertex i = v).card +
        ∑ e ∈ D, G.endCount v e := by
  rw [MGraph.degree_eq_sum_endCount, outside_ends_sum,
    ← Finset.sum_filter_add_sum_filter_not univ (fun e => e ∉ D)]
  congr 1
  simp

private theorem degree_contract_triangle (G : MGraph V E) (D : Finset E) (x₁ x₂ x₃ : V)
    (h12 : x₁ ≠ x₂) (h23 : x₂ ≠ x₃) (h31 : x₃ ≠ x₁) :
    (G.contract {x₁, x₂, x₃} D).degree none =
      (univ.filter fun i : E × Bool => i.1 ∉ D ∧ G.endVertex i = x₁).card +
      (univ.filter fun i : E × Bool => i.1 ∉ D ∧ G.endVertex i = x₂).card +
      (univ.filter fun i : E × Bool => i.1 ∉ D ∧ G.endVertex i = x₃).card := by
  simp_rw [outside_ends_sum]
  rw [MGraph.degree_eq_sum_endCount]
  simp only [MGraph.endCount, MGraph.contract_src_none, MGraph.contract_tgt_none]
  have hsub (f : E → ℕ) : (∑ e : {e : E // e ∉ D}, f e.1) =
      ∑ e ∈ univ.filter (fun e => e ∉ D), f e := by
    exact (Finset.sum_subtype _ (p := fun e => e ∉ D) (by simp) f).symm
  rw [hsub (fun e => (if G.src e ∈ ({x₁, x₂, x₃} : Finset V) then 1 else 0) +
    (if G.tgt e ∈ ({x₁, x₂, x₃} : Finset V) then 1 else 0))]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : G.src e = x₁ <;> by_cases h2 : G.src e = x₂ <;>
    by_cases h3 : G.src e = x₃ <;> by_cases h4 : G.tgt e = x₁ <;>
    by_cases h5 : G.tgt e = x₂ <;> by_cases h6 : G.tgt e = x₃ <;> simp_all

/-- In the triangle-replacement construction, the two ends sent to each of the first two vertices,
together with their two triangle ends, give degrees four. The remaining vertex has degree d - 2.
Here h₁ and h₂ are exactly those two prescribed pairs of ends outside the triangle. Existence of such
a replacement for every vertex of degree at least six is part of the proof of Theorem 2.3. -/
theorem fig_5_degrees_proved (G : MGraph V E) (x₁ x₂ x₃ : V) (d₁₂ d₂₃ d₃₁ : E)
    (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁)
    (h₁ : (Finset.univ.filter fun i : E × Bool =>
      i.1 ∉ ({d₁₂, d₂₃, d₃₁} : Finset E) ∧ G.endVertex i = x₁).card = 2)
    (h₂ : (Finset.univ.filter fun i : E × Bool =>
      i.1 ∉ ({d₁₂, d₂₃, d₃₁} : Finset E) ∧ G.endVertex i = x₂).card = 2) :
    G.degree x₁ = 4 ∧ G.degree x₂ = 4 ∧
    G.degree x₃ + 2 = (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).degree none ∧
    (Finset.univ.filter fun i : E × Bool =>
      i.1 ∉ ({d₁₂, d₂₃, d₃₁} : Finset E) ∧ G.endVertex i = x₃).card + 4 =
        (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).degree none := by
  obtain ⟨h12, h23, h31⟩ := hΔ.d_ne
  have hm12 := hΔ.x_ne₁₂
  have hm23 := hΔ.x_ne₂₃
  have hm31 := hΔ.x_ne₃₁
  have hinside (v : V) :
      (∑ e ∈ ({d₁₂, d₂₃, d₃₁} : Finset E), G.endCount v e) =
        (if x₁ = v then 2 else 0) + (if x₂ = v then 2 else 0) + (if x₃ = v then 2 else 0) := by
    rcases hΔ.joins₁₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rcases hΔ.joins₂₃ with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
      rcases hΔ.joins₃₁ with ⟨he, hf⟩ | ⟨he, hf⟩ <;>
      simp [Finset.sum_insert, h12, h23, Ne.symm h31, MGraph.endCount, ha, hb, hc, hd, he, hf] <;>
      split_ifs <;> omega
  have hd1 := degree_outside_add G {d₁₂, d₂₃, d₃₁} x₁
  have hd2 := degree_outside_add G {d₁₂, d₂₃, d₃₁} x₂
  have hd3 := degree_outside_add G {d₁₂, d₂₃, d₃₁} x₃
  rw [hinside] at hd1 hd2 hd3
  simp only [ite_true, hm12, hm23, hm31, Ne.symm hm12, Ne.symm hm23, Ne.symm hm31,
    ite_false, add_zero, zero_add] at hd1 hd2 hd3
  have hdc := degree_contract_triangle G {d₁₂, d₂₃, d₃₁} x₁ x₂ x₃ hm12 hm23 hm31
  rw [h₁, h₂] at hdc
  omega


end EulerFlow

