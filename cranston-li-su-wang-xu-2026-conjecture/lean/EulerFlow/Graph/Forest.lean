/-
EulerFlow/Graph/Forest.lean — paper 002 foundation: the two counting facts of Props 4.4, 6.3, 9.6.
* `card_lt_of_acyclic` (C3): an edge set with no cycle, all of whose ends lie in a nonempty vertex set `W`, has
  fewer than `|W|` edges ("a forest on n vertices has at most n − 1 edges", tex l.398-399);
* `exists_dirCycle_of_card_le` (C3'): the contrapositive ("the small edges contain a cycle", tex l.399-400);
* `card_le_of_cycle_ends_two` (C4): if every vertex of every cycle of `H` has exactly two ends of `H`, then
  `|H| ≤ |W|` ("every cycle is a whole component, every component a tree or a cycle", tex l.510-513, l.833-836).
Same names and types as the stub EulerFlow/Graph/ForestStub.lean (v0.01, md5 16e186d1), which this replaces.
-/
import EulerFlow.Graph.Cycles
import EulerFlow.Graph.DirCycleBasic

namespace EulerFlow

namespace MGraph

open Finset

variable {V E : Type} {G : MGraph V E} [Fintype E] [DecidableEq E] [DecidableEq V]

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
/-- An end of an edge whose two ends lie in `W` lies in `W`. -/
lemma endVertex_mem_of {W : Finset V} (i : E × Bool) (h : G.src i.1 ∈ W ∧ G.tgt i.1 ∈ W) :
    G.endVertex i ∈ W := by
  rcases i with ⟨e, _ | _⟩ <;> simp [endVertex, h.1, h.2]

/-- (C3) **Forest bound**: an edge set `S` with all ends in a nonempty vertex set `W` and containing no cycle has
fewer edges than `W` has vertices. -/
theorem card_lt_of_acyclic (S : Finset E) (W : Finset V) (hW : W.Nonempty)
    (hend : ∀ e ∈ S, G.src e ∈ W ∧ G.tgt e ∈ W)
    (hac : ∀ Q : G.DirCycle, ¬ ∀ d ∈ Q.darts, d.1 ∈ S) : S.card < W.card := by
  induction S using Finset.strongInduction generalizing W with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simpa using hW.card_pos
    -- some vertex has exactly one end of `S`
    have hv1 : ∃ v, G.sdeg S v = 1 := by
      by_contra h
      simp only [not_exists] at h
      obtain ⟨Q, hQ⟩ := G.exists_dirCycle_of_sdeg_ne_one S hne h
      exact hac Q hQ
    obtain ⟨v, hv⟩ := hv1
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hv
    have hmemF : ∀ i : E × Bool, i ∈ univ.filter (fun i : E × Bool => i.1 ∈ S ∧ G.endVertex i = v) ↔
        i.1 ∈ S ∧ G.endVertex i = v := by
      intro i; simp
    have haS : a.1 ∈ S ∧ G.endVertex a = v := by
      rw [← hmemF, ha]; exact mem_singleton_self a
    have huniq : ∀ i : E × Bool, i.1 ∈ S → G.endVertex i = v → i = a := by
      intro i h1 h2
      have : i ∈ univ.filter (fun i : E × Bool => i.1 ∈ S ∧ G.endVertex i = v) := (hmemF i).2 ⟨h1, h2⟩
      rw [ha] at this
      exact mem_singleton.1 this
    -- the other end of the edge `a.1` is not `v`
    have hrev : G.endVertex (dartRev a) ≠ v := by
      intro h
      have := huniq (dartRev a) haS.1 h
      rcases a with ⟨e, b⟩
      cases b <;> simp [dartRev] at this
    have hvW : v ∈ W := haS.2 ▸ endVertex_mem_of a (hend a.1 haS.1)
    have huW : G.endVertex (dartRev a) ∈ W := endVertex_mem_of (dartRev a) (hend a.1 haS.1)
    have hlt : S.erase a.1 ⊂ S := Finset.erase_ssubset haS.1
    have hW' : (W.erase v).Nonempty := ⟨_, mem_erase.2 ⟨hrev, huW⟩⟩
    have hend' : ∀ e ∈ S.erase a.1, G.src e ∈ W.erase v ∧ G.tgt e ∈ W.erase v := by
      intro e he
      obtain ⟨hne', heS⟩ := mem_erase.1 he
      refine ⟨mem_erase.2 ⟨fun h => hne' ?_, (hend e heS).1⟩, mem_erase.2 ⟨fun h => hne' ?_, (hend e heS).2⟩⟩
      · exact congr_arg Prod.fst (huniq (e, false) heS (by simp [endVertex, h]))
      · exact congr_arg Prod.fst (huniq (e, true) heS (by simp [endVertex, h]))
    have hac' : ∀ Q : G.DirCycle, ¬ ∀ d ∈ Q.darts, d.1 ∈ S.erase a.1 :=
      fun Q h => hac Q (fun d hd => mem_of_mem_erase (h d hd))
    have := ih (S.erase a.1) hlt (W.erase v) hW' hend' hac'
    rw [card_erase_of_mem haS.1, card_erase_of_mem hvW] at this
    have := S.card_pos.2 hne
    omega

/-- (C3') The contrapositive: a nonempty edge set with all ends in `W` and at least `|W|` edges contains a
cycle. -/
theorem exists_dirCycle_of_card_le (S : Finset E) (W : Finset V) (hS : S.Nonempty)
    (hend : ∀ e ∈ S, G.src e ∈ W ∧ G.tgt e ∈ W) (hcard : W.card ≤ S.card) :
    ∃ Q : G.DirCycle, ∀ d ∈ Q.darts, d.1 ∈ S := by
  by_contra h
  simp only [not_exists] at h
  obtain ⟨e, he⟩ := hS
  have := card_lt_of_acyclic S W ⟨_, (hend e he).1⟩ hend h
  omega

/-- (C4) **Cycle-vertex count**: if every vertex of every cycle of the edge set `H` has exactly two ends of `H`,
then `H` has at most `|W|` edges (`W` contains all ends of `H`). -/
theorem card_le_of_cycle_ends_two (H : Finset E) (W : Finset V)
    (hend : ∀ e ∈ H, G.src e ∈ W ∧ G.tgt e ∈ W)
    (hdeg2 : ∀ Q : G.DirCycle, (∀ d ∈ Q.darts, d.1 ∈ H) → ∀ d ∈ Q.darts,
      (univ.filter fun i : E × Bool => i.1 ∈ H ∧ G.endVertex i = G.dartTail d).card = 2) :
    H.card ≤ W.card := by
  induction H using Finset.strongInduction generalizing W with
  | H H ih =>
    by_cases hcyc : ∃ Q : G.DirCycle, ∀ d ∈ Q.darts, d.1 ∈ H
    swap
    · -- no cycle: the forest bound
      simp only [not_exists] at hcyc
      rcases H.eq_empty_or_nonempty with rfl | ⟨e, he⟩
      · simp
      · exact (card_lt_of_acyclic H W ⟨_, (hend e he).1⟩ hend hcyc).le
    obtain ⟨Q, hQ⟩ := hcyc
    set EQ := (Q.darts.map Prod.fst).toFinset with hEQ
    set VQ := (Q.darts.map G.dartTail).toFinset with hVQ
    have hEQcard : EQ.card = Q.darts.length := by
      rw [hEQ, List.toFinset_card_of_nodup Q.edges_nodup, List.length_map]
    have hVQcard : VQ.card = Q.darts.length := by
      rw [hVQ, List.toFinset_card_of_nodup Q.tails_nodup, List.length_map]
    have hmemEQ : ∀ e, e ∈ EQ ↔ ∃ d ∈ Q.darts, d.1 = e := by
      intro e; rw [hEQ, List.mem_toFinset, List.mem_map]
    have hmemVQ : ∀ x, x ∈ VQ ↔ ∃ d ∈ Q.darts, G.dartTail d = x := by
      intro x; rw [hVQ, List.mem_toFinset, List.mem_map]
    have hEQH : EQ ⊆ H := by
      intro e he
      obtain ⟨d, hd, rfl⟩ := (hmemEQ e).1 he
      exact hQ d hd
    have hVQW : VQ ⊆ W := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := (hmemVQ x).1 hx
      exact endVertex_mem_of d (hend d.1 (hQ d hd))
    -- every end of an edge of `Q` is at a vertex of `Q`
    have hendQ : ∀ i : E × Bool, i.1 ∈ EQ → G.endVertex i ∈ VQ := by
      intro i hi
      obtain ⟨d, hd, hdi⟩ := (hmemEQ _).1 hi
      by_cases hid : i = d
      · subst hid; exact (hmemVQ _).2 ⟨i, hd, rfl⟩
      · have hrev : i = dartRev d := eq_dartRev_of_fst_eq hdi (Ne.symm hid)
        obtain ⟨d', hd', h'⟩ := Q.exists_leave hd
        rw [hrev, endVertex_eq_dartTail, dartTail_dartRev, ← h']
        exact (hmemVQ _).2 ⟨d', hd', rfl⟩
    -- an edge of `H` off `Q` has no end at a vertex of `Q`
    have hkey : ∀ i : E × Bool, i.1 ∈ H → i.1 ∉ EQ → G.endVertex i ∉ VQ := by
      intro i hiH hiQ hx
      obtain ⟨d0, hd0, hx0⟩ := (hmemVQ _).1 hx
      obtain ⟨d1, hd1, hx1⟩ := Q.exists_enter hd0
      have h2 := hdeg2 Q hQ d0 hd0
      have hsub : ({i, d0, dartRev d1} : Finset (E × Bool)) ⊆
          univ.filter fun j : E × Bool => j.1 ∈ H ∧ G.endVertex j = G.dartTail d0 := by
        intro j hj
        simp only [mem_insert, mem_singleton] at hj
        simp only [mem_filter, mem_univ, true_and]
        rcases hj with rfl | rfl | rfl
        · exact ⟨hiH, hx0.symm⟩
        · exact ⟨hQ j hd0, rfl⟩
        · exact ⟨hQ d1 hd1, by rw [endVertex_eq_dartTail, dartTail_dartRev, hx1]⟩
      have hi0 : i ≠ d0 := fun h => hiQ ((hmemEQ _).2 ⟨d0, hd0, by rw [h]⟩)
      have hi1 : i ≠ dartRev d1 := fun h => hiQ ((hmemEQ _).2 ⟨d1, hd1, by rw [h]; rfl⟩)
      have h01 : d0 ≠ dartRev d1 := by
        intro h
        have hfst : d0.1 = d1.1 := by rw [h]; rfl
        have := Q.eq_of_fst_eq hd0 hd1 hfst
        rw [this] at h
        rcases d1 with ⟨e, b⟩
        cases b <;> simp [dartRev] at h
      have h3 : ({i, d0, dartRev d1} : Finset (E × Bool)).card = 3 := by
        rw [card_insert_of_notMem (by simp [hi0, hi1]), card_insert_of_notMem (by simp [h01]), card_singleton]
      have := card_le_card hsub
      omega
    -- recurse on `H ∖ E(Q)` and `W ∖ V(Q)`
    have hEQne : EQ.Nonempty := by
      obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ Q.ne_nil
      exact ⟨d.1, (hmemEQ _).2 ⟨d, hd, rfl⟩⟩
    have hlt : H \ EQ ⊂ H := Finset.sdiff_ssubset hEQH hEQne
    have hend' : ∀ e ∈ H \ EQ, G.src e ∈ W \ VQ ∧ G.tgt e ∈ W \ VQ := by
      intro e he
      obtain ⟨heH, heQ⟩ := mem_sdiff.1 he
      exact ⟨mem_sdiff.2 ⟨(hend e heH).1, by simpa [endVertex] using hkey (e, false) heH heQ⟩,
        mem_sdiff.2 ⟨(hend e heH).2, by simpa [endVertex] using hkey (e, true) heH heQ⟩⟩
    have hdeg2' : ∀ Q' : G.DirCycle, (∀ d ∈ Q'.darts, d.1 ∈ H \ EQ) → ∀ d ∈ Q'.darts,
        (univ.filter fun i : E × Bool => i.1 ∈ H \ EQ ∧ G.endVertex i = G.dartTail d).card = 2 := by
      intro Q' hQ' d hd
      have hQ'H : ∀ d ∈ Q'.darts, d.1 ∈ H := fun d hd => (mem_sdiff.1 (hQ' d hd)).1
      have hxQ : G.dartTail d ∉ VQ := by
        have := hkey d (hQ'H d hd) (mem_sdiff.1 (hQ' d hd)).2
        rwa [endVertex_eq_dartTail] at this
      rw [← hdeg2 Q' hQ'H d hd]
      congr 1
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_sdiff]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, fun hj => hxQ ?_⟩, h2⟩
        rw [← h2]; exact hendQ j hj
    have := ih (H \ EQ) hlt (W \ VQ) hend' hdeg2'
    rw [card_sdiff_of_subset hEQH, card_sdiff_of_subset hVQW] at this
    have h1 := card_le_card hEQH
    have h2 := card_le_card hVQW
    omega

end MGraph

end EulerFlow
