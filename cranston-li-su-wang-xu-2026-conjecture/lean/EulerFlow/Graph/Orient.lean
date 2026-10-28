/-
EulerFlow/Graph/Orient.lean — paper 002 foundation: Eulerian orientations (Lemma 3.3, tex l.272-274).
* `isEulerOrient_iff`: `D` is Eulerian iff `σ_D` (`-1` on reversed edges, `1` on the others) is an integer flow;
* `exists_eulerOrient`: every even graph has an Eulerian orientation (repeatedly remove a cycle);
* `lem_3_3_exists_proved`: the Statements form.
-/
import EulerFlow.Graph.MultiStep

namespace EulerFlow

namespace MGraph

open Finset

variable {V E : Type} {G : MGraph V E} [Fintype E] [DecidableEq E] [DecidableEq V]

/-- The degree in an edge set, as a sum over its edges (a loop counts twice). -/
lemma sdeg_eq_sum (S : Finset E) (v : V) :
    G.sdeg S v = ∑ e ∈ S, ((if G.src e = v then 1 else 0) + (if G.tgt e = v then 1 else 0)) := by
  unfold sdeg
  rw [Finset.card_filter, Fintype.sum_prod_type]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun e => e ∈ S)]
  have h1 : univ.filter (fun e => e ∈ S) = S := by ext; simp
  rw [h1]
  have h2 : ∑ e ∈ univ.filter (fun e => e ∉ S),
      ∑ b : Bool, (if (e, b).1 ∈ S ∧ G.endVertex (e, b) = v then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    simp [he]
  rw [h2, add_zero]
  apply Finset.sum_congr rfl
  intro e he
  rw [Fintype.sum_bool]
  simp only [he, true_and, endVertex, ↓reduceIte, Bool.false_eq_true]
  ring

/-- The degree of the edge set of a directed cycle is even at every vertex. -/
lemma even_sdeg_cycle (Q : G.DirCycle) (v : V) : Even (G.sdeg (Q.darts.map Prod.fst).toFinset v) := by
  rw [sdeg_eq_sum, List.sum_toFinset _ Q.edges_nodup, List.map_map]
  have hdart : ∀ d : E × Bool,
      ((fun e => (if G.src e = v then 1 else 0) + (if G.tgt e = v then 1 else 0)) ∘ Prod.fst) d =
        (if G.dartTail d = v then 1 else 0) + (if G.dartHead d = v then 1 else 0) := by
    rintro ⟨e, _ | _⟩ <;> simp [add_comm]
  rw [List.map_congr_left (fun d _ => hdart d)]
  have hperm : (Q.darts.map (fun d => (if G.dartHead d = v then 1 else 0 : ℕ))).sum =
      (Q.darts.map (fun d => (if G.dartTail d = v then 1 else 0 : ℕ))).sum := by
    have := (Q.heads_perm_tails.map (fun x => (if x = v then (1 : ℕ) else 0))).sum_eq
    simpa [List.map_map, Function.comp_def] using this
  have hsplit : ∀ l : List (E × Bool), (l.map (fun d => (if G.dartTail d = v then 1 else 0) +
      (if G.dartHead d = v then 1 else 0))).sum = (l.map (fun d => (if G.dartTail d = v then 1 else 0 : ℕ))).sum +
      (l.map (fun d => (if G.dartHead d = v then 1 else 0 : ℕ))).sum := by
    intro l; induction l with
    | nil => simp
    | cons d l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [hsplit, hperm]
  exact ⟨_, rfl⟩

/-- **Every edge set with even degrees carries a `±1`-valued integer circulation** (an Eulerian orientation of
the edges of `S`): remove a cycle and repeat (tex l.272: "it exists because G is even"). -/
theorem exists_sign_circ (S : Finset E) (hS : ∀ v, Even (G.sdeg S v)) :
    ∃ σ : E → ℤ, (∀ e ∈ S, σ e = 1 ∨ σ e = -1) ∧ (∀ e ∉ S, σ e = 0) ∧ G.IsFlow σ := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hne : S.Nonempty
    · have hdeg : ∀ v, G.sdeg S v ≠ 1 := by
        intro v h1
        have := hS v
        rw [h1] at this
        exact absurd this (by decide)
      obtain ⟨Q, hQ⟩ := G.exists_dirCycle_of_sdeg_ne_one S hne hdeg
      set EQ := (Q.darts.map Prod.fst).toFinset with hEQ
      have hEQS : EQ ⊆ S := by
        intro e he
        rw [hEQ, List.mem_toFinset] at he
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
        exact hQ d hd
      have hEQne : EQ.Nonempty := by
        obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ Q.ne_nil
        exact ⟨d.1, by rw [hEQ, List.mem_toFinset]; exact List.mem_map_of_mem hd⟩
      have hlt : S \ EQ ⊂ S := Finset.sdiff_ssubset hEQS hEQne
      have heven' : ∀ v, Even (G.sdeg (S \ EQ) v) := by
        intro v
        have hsum : G.sdeg (S \ EQ) v + G.sdeg EQ v = G.sdeg S v := by
          rw [sdeg_eq_sum, sdeg_eq_sum, sdeg_eq_sum, Finset.sum_sdiff hEQS]
        have h1 := hS v
        have h2 := even_sdeg_cycle Q v
        rw [← hsum] at h1
        exact (Nat.even_add.1 h1).2 h2
      obtain ⟨σ', h1, h2, h3⟩ := ih (S \ EQ) hlt heven'
      refine ⟨fun e => σ' e + Q.chi e, ?_, ?_, ?_⟩
      · intro e he
        dsimp only
        by_cases heq : e ∈ EQ
        · have : σ' e = 0 := h2 e (by simp [heq])
          rw [hEQ, List.mem_toFinset] at heq
          obtain ⟨d, hd, rfl⟩ := List.mem_map.1 heq
          rw [this, zero_add, Q.chi_of_mem hd]
          cases d.2 <;> simp [dartSign]
        · have hnot : e ∉ Q.darts.map Prod.fst := by rw [hEQ, List.mem_toFinset] at heq; exact heq
          rw [Q.chi_of_not_mem hnot, add_zero]
          exact h1 e (by simp [he, heq])
      · intro e he
        dsimp only
        have heq : e ∉ Q.darts.map Prod.fst := fun h => he (hEQS (by rw [hEQ, List.mem_toFinset]; exact h))
        rw [h2 e (by simp [he]), Q.chi_of_not_mem heq, add_zero]
      · exact IsFlow.add h3 Q.isFlow_chi
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      exact ⟨fun _ => 0, by simp, fun _ _ => rfl, fun v => by simp⟩

omit [DecidableEq E] in
/-- (EO-bridge) `D` is Eulerian iff `σ_D` (`-1` on the reversed edges, `1` on the others) is an integer flow. -/
theorem isEulerOrient_iff (D : E → Bool) :
    G.IsEulerOrient D ↔ G.IsFlow (fun e => if D e then (-1 : ℤ) else 1) := by
  have key : ∀ v, ((univ.filter fun e => G.dartTail (e, D e) = v).card : ℤ) -
      (univ.filter fun e => G.dartHead (e, D e) = v).card =
      ∑ e ∈ univ.filter (fun e => G.src e = v), (if D e then (-1 : ℤ) else 1) -
      ∑ e ∈ univ.filter (fun e => G.tgt e = v), (if D e then (-1 : ℤ) else 1) := by
    intro v
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_filter]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    cases D e
    · simp
    · simp only [dartTail_mk_true, dartHead_mk_true, ↓reduceIte]
      split_ifs <;> norm_num
  constructor
  · intro hD v
    have := key v
    rw [hD v, sub_self] at this
    linarith
  · intro hF v
    have := key v
    rw [hF v, sub_self] at this
    exact_mod_cast sub_eq_zero.1 this

/-- (EO) **Every even graph has an Eulerian orientation** (Lemma 3.3, tex l.272-273). -/
theorem exists_eulerOrient (heven : G.IsEven) : ∃ D : E → Bool, G.IsEulerOrient D := by
  obtain ⟨σ, h1, _, h3⟩ := exists_sign_circ (G := G) univ (fun v => by
    rw [← degree_eq_sdeg_univ]; exact heven v)
  refine ⟨fun e => decide (σ e = -1), (isEulerOrient_iff _).2 ?_⟩
  have : (fun e => if decide (σ e = -1) then (-1 : ℤ) else 1) = σ := by
    funext e
    rcases h1 e (mem_univ e) with h | h <;> simp [h]
  rw [this]; exact h3

/-- `lem_3_3_exists` (tex l.272-273): every even graph has an Eulerian orientation. -/
theorem lem_3_3_exists_proved [Fintype V] (G : MGraph V E) (hG : G.IsEven) : ∃ D : E → Bool, G.IsEulerOrient D :=
  exists_eulerOrient hG

end MGraph

end EulerFlow
