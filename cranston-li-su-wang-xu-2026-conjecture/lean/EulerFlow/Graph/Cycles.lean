/-
EulerFlow/Graph/Cycles.lean — paper 002 foundation: cycles in edge sets and the decomposition of circulations.
* `exists_dirCycle_of_sdeg_ne_one`: a nonempty edge set in which no vertex has exactly one end contains a cycle
  (used for Eulerian orientations, the forest bound, and the rounding Lemma 8.2);
* `exists_conformal_dirCycle`: a nonzero `{-1,0,1}`-valued circulation contains a directed cycle along its arcs;
* `circ_decomp`: such a circulation is the sum of `χ` of pairwise edge-disjoint directed cycles, each following
  the sign of the circulation (used by Lemmas 3.2(b), 3.3(a), 5.1(b), 8.4: "multi-step").
-/
import EulerFlow.Graph.Chi

namespace EulerFlow

namespace MGraph

open Finset

variable {V E : Type} (G : MGraph V E)

section Degree

variable [Fintype E] [DecidableEq E] [DecidableEq V]

/-- The degree of `v` in the edge set `S`: the number of ends at `v` of edges in `S` (a loop counts twice). -/
def sdeg (S : Finset E) (v : V) : ℕ :=
  (univ.filter fun i : E × Bool => i.1 ∈ S ∧ G.endVertex i = v).card

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
lemma endVertex_eq_dartTail (i : E × Bool) : G.endVertex i = G.dartTail i := rfl

/-- `G.degree` is the degree in the set of all edges. -/
lemma degree_eq_sdeg_univ (v : V) : G.degree v = G.sdeg univ v := by
  simp [degree, sdeg]

end Degree

section CycleInSet

variable [Fintype E] [DecidableEq E] [DecidableEq V]

/-- **An edge set with no vertex of degree one contains a cycle.** If `S` is nonempty and no vertex meets
exactly one end of an edge of `S`, some directed cycle uses only edges of `S`. -/
theorem exists_dirCycle_of_sdeg_ne_one (S : Finset E) (hS : S.Nonempty) (hdeg : ∀ v, G.sdeg S v ≠ 1) :
    ∃ Q : G.DirCycle, ∀ d ∈ Q.darts, d.1 ∈ S := by
  have hnext : ∀ d : E × Bool, d.1 ∈ S →
      ∃ d' : E × Bool, d'.1 ∈ S ∧ G.dartTail d' = G.dartHead d ∧ d' ≠ dartRev d := by
    intro d hd
    have hmem : dartRev d ∈ univ.filter (fun i : E × Bool => i.1 ∈ S ∧ G.endVertex i = G.dartHead d) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hd, by rw [endVertex_eq_dartTail, dartTail_dartRev]⟩
    have h2 : 1 < G.sdeg S (G.dartHead d) :=
      lt_of_le_of_ne (Finset.card_pos.2 ⟨_, hmem⟩) (hdeg _).symm
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h2
    replace ha := (Finset.mem_filter.1 ha).2
    replace hb := (Finset.mem_filter.1 hb).2
    rw [endVertex_eq_dartTail] at ha hb
    by_cases had : a = dartRev d
    · exact ⟨b, hb.1, hb.2, fun h => hab (had.trans h.symm)⟩
    · exact ⟨a, ha.1, ha.2, had⟩
  choose! nxt hnxtS hnxtT hnxtR using hnext
  obtain ⟨e, he⟩ := hS
  exact G.exists_dirCycle_of_succ (fun d => d.1 ∈ S) nxt hnxtS (fun d hd => (hnxtT d hd).symm) hnxtR
    (e, false) he

end CycleInSet

section Conformal

variable [Fintype E] [DecidableEq E] [DecidableEq V]

omit [Fintype E] [DecidableEq E] in
/-- A sum of non-negative terms is at least any one of them (integer version, for filtered sums). -/
private lemma le_sum_of_nonneg (s : Finset E) (x : E → ℤ) (hx : ∀ e ∈ s, 0 ≤ x e) {e0 : E} (he0 : e0 ∈ s) :
    x e0 ≤ ∑ e ∈ s, x e :=
  Finset.single_le_sum hx he0

omit [Fintype E] [DecidableEq E] in
private lemma sum_le_of_nonpos (s : Finset E) (x : E → ℤ) (hx : ∀ e ∈ s, x e ≤ 0) {e0 : E} (he0 : e0 ∈ s) :
    ∑ e ∈ s, x e ≤ x e0 := by
  have := Finset.single_le_sum (f := fun e => -x e) (fun e he => neg_nonneg.2 (hx e he)) he0
  simp only [Finset.sum_neg_distrib] at this
  linarith

omit [DecidableEq E] in
/-- In a `{-1,0,1}`-valued circulation, a vertex that some arc enters is left by some arc. (An ARC of `h` is a
dart `d` with `h d.1 = dartSign d.2`.) -/
lemma exists_out_arc (h : E → ℤ) (hval : ∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1) (hflow : G.IsFlow h)
    (d : E × Bool) (hd : h d.1 = dartSign d.2) :
    ∃ d' : E × Bool, h d'.1 = dartSign d'.2 ∧ G.dartTail d' = G.dartHead d := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  set v := G.dartHead d with hv
  have hsrc : ∀ e ∈ univ.filter (fun e => G.src e = v), h e ≤ 0 := by
    intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    have : h e ≠ 1 := fun h1 => hno (e, false) (by simpa [dartSign] using h1) (by simpa using he)
    rcases hval e with h' | h' | h' <;> omega
  have htgt : ∀ e ∈ univ.filter (fun e => G.tgt e = v), 0 ≤ h e := by
    intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    have : h e ≠ -1 := fun h1 => hno (e, true) (by simpa [dartSign] using h1) (by simpa using he)
    rcases hval e with h' | h' | h' <;> omega
  have hfl := hflow v
  rcases d with ⟨e0, _ | _⟩
  · -- the arc `(e0, false)` enters `v = tgt e0`, and `h e0 = 1`
    have hmem : e0 ∈ univ.filter (fun e => G.tgt e = v) := by simp [hv]
    have h1 := le_sum_of_nonneg _ h htgt hmem
    have h2 := Finset.sum_nonpos hsrc
    simp only [dartSign] at hd
    simp at hd
    omega
  · -- the arc `(e0, true)` enters `v = src e0`, and `h e0 = -1`
    have hmem : e0 ∈ univ.filter (fun e => G.src e = v) := by simp [hv]
    have h1 := sum_le_of_nonpos _ h hsrc hmem
    have h2 := Finset.sum_nonneg htgt
    simp only [dartSign] at hd
    simp at hd
    omega

omit [DecidableEq E] in
/-- **A nonzero `{-1,0,1}`-valued circulation contains a directed cycle along its arcs.** -/
theorem exists_conformal_dirCycle (h : E → ℤ) (hval : ∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1)
    (hflow : G.IsFlow h) (hne : ∃ e, h e ≠ 0) :
    ∃ Q : G.DirCycle, ∀ d ∈ Q.darts, h d.1 = dartSign d.2 := by
  have hnext := G.exists_out_arc h hval hflow
  choose! nxt hnxtP hnxtT using hnext
  have hrev : ∀ d, h d.1 = dartSign d.2 → nxt d ≠ dartRev d := by
    rintro ⟨e, b⟩ hd heq
    have := hnxtP _ hd
    rw [heq] at this
    simp only [dartRev] at this hd
    rw [hd] at this
    cases b <;> simp [dartSign] at this
  obtain ⟨e, he⟩ := hne
  have hd0 : ∃ d0 : E × Bool, h d0.1 = dartSign d0.2 := by
    rcases hval e with h' | h' | h'
    · exact ⟨(e, true), by simp [dartSign, h']⟩
    · exact absurd h' he
    · exact ⟨(e, false), by simp [dartSign, h']⟩
  obtain ⟨d0, hd0⟩ := hd0
  exact G.exists_dirCycle_of_succ (fun d => h d.1 = dartSign d.2) nxt hnxtP (fun d hd => (hnxtT d hd).symm)
    hrev d0 hd0

end Conformal

section Decomp

variable [Fintype E] [DecidableEq E] [DecidableEq V]

omit [DecidableEq E] in
variable {G} in
/-- The flow condition is linear: a difference of circulations is a circulation. -/
lemma IsFlow.sub {h h' : E → ℤ} (hh : G.IsFlow h) (hh' : G.IsFlow h') : G.IsFlow (fun e => h e - h' e) := by
  intro v
  simp only [Finset.sum_sub_distrib, hh v, hh' v]

omit [Fintype E] [DecidableEq V] in
/-- The step of the decomposition: remove one conformal cycle. -/
private lemma decomp_step (h : E → ℤ) (Q : G.DirCycle) (hQ : ∀ d ∈ Q.darts, h d.1 = dartSign d.2) (e : E) :
    (e ∈ Q.darts.map Prod.fst → h e - Q.chi e = 0) ∧ (e ∉ Q.darts.map Prod.fst → h e - Q.chi e = h e) := by
  constructor
  · intro he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
    rw [Q.chi_of_mem hd, hQ d hd, sub_self]
  · intro he
    rw [Q.chi_of_not_mem he, sub_zero]

/-- **Decomposition of a `{-1,0,1}`-valued circulation** into pairwise edge-disjoint directed cycles, each
following the sign of `h` (paper: "they are the union of directed cycles ... no two of which have a common arc",
tex l.283, l.629). The number of cycles is at most the number of edges where `h ≠ 0`. -/
theorem circ_decomp_darts (h : E → ℤ) (hval : ∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1) (hflow : G.IsFlow h) :
    ∃ Qs : List G.DirCycle, Qs.Pairwise G.EdgeDisjoint ∧
      (∀ Q ∈ Qs, ∀ d ∈ Q.darts, h d.1 = dartSign d.2) ∧
      (∀ e, (Qs.map fun Q => Q.chi e).sum = h e) ∧
      Qs.length ≤ (univ.filter fun e => h e ≠ 0).card := by
  suffices key : ∀ n : ℕ, ∀ h : E → ℤ, (univ.filter fun e => h e ≠ 0).card ≤ n →
      (∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1) → G.IsFlow h →
      ∃ Qs : List G.DirCycle, Qs.Pairwise G.EdgeDisjoint ∧
        (∀ Q ∈ Qs, ∀ d ∈ Q.darts, h d.1 = dartSign d.2) ∧
        (∀ e, (Qs.map fun Q => Q.chi e).sum = h e) ∧
        Qs.length ≤ (univ.filter fun e => h e ≠ 0).card from key _ h le_rfl hval hflow
  intro n
  induction n with
  | zero =>
    intro h hcard _ _
    have h0 : ∀ e, h e = 0 := by
      intro e
      by_contra he
      have : e ∈ univ.filter fun e => h e ≠ 0 := by simp [he]
      have := Finset.card_pos.2 ⟨e, this⟩
      omega
    exact ⟨[], by simp, by simp, by simp [h0], by simp⟩
  | succ n ih =>
    intro h hcard hval hflow
    by_cases hz : ∀ e, h e = 0
    · exact ⟨[], by simp, by simp, by simp [hz], by simp⟩
    simp only [not_forall] at hz
    obtain ⟨Q, hQ⟩ := G.exists_conformal_dirCycle h hval hflow hz
    set h' : E → ℤ := fun e => h e - Q.chi e with hh'
    have hval' : ∀ e, h' e = -1 ∨ h' e = 0 ∨ h' e = 1 := by
      intro e
      by_cases he : e ∈ Q.darts.map Prod.fst
      · exact Or.inr (Or.inl ((decomp_step G h Q hQ e).1 he))
      · simp only [hh']; rw [(decomp_step G h Q hQ e).2 he]; exact hval e
    have hflow' : G.IsFlow h' := IsFlow.sub hflow Q.isFlow_chi
    -- the support shrinks strictly
    have hsub : (univ.filter fun e => h' e ≠ 0) ⊂ (univ.filter fun e => h e ≠ 0) := by
      rw [Finset.ssubset_iff_of_subset]
      · obtain ⟨d0, hd0⟩ : ∃ d0, d0 ∈ Q.darts := List.exists_mem_of_ne_nil _ Q.ne_nil
        refine ⟨d0.1, ?_, ?_⟩
        · simp [hQ d0 hd0, dartSign_ne_zero]
        · simp only [mem_filter, mem_univ, true_and, not_not]
          exact (decomp_step G h Q hQ d0.1).1 (List.mem_map_of_mem hd0)
      · intro e he
        simp only [mem_filter, mem_univ, true_and] at he ⊢
        intro hz'
        by_cases hq : e ∈ Q.darts.map Prod.fst
        · exact he ((decomp_step G h Q hQ e).1 hq)
        · simp only [hh'] at he; rw [(decomp_step G h Q hQ e).2 hq] at he; exact he hz'
    have hlt := Finset.card_lt_card hsub
    obtain ⟨Qs, hdisj, hconf, hsum, hlen⟩ := ih h' (by omega) hval' hflow'
    -- a dart of a later cycle is not on `Q`
    have hoff : ∀ Q' ∈ Qs, ∀ d' ∈ Q'.darts, d'.1 ∉ Q.darts.map Prod.fst := by
      intro Q' hQ' d' hd' hmem
      have h1 := hconf Q' hQ' d' hd'
      simp only [hh'] at h1
      rw [(decomp_step G h Q hQ d'.1).1 hmem] at h1
      exact dartSign_ne_zero _ h1.symm
    refine ⟨Q :: Qs, ?_, ?_, ?_, ?_⟩
    · refine List.pairwise_cons.2 ⟨fun Q' hQ' d hd d' hd' heq => ?_, hdisj⟩
      exact hoff Q' hQ' d' hd' (heq ▸ List.mem_map_of_mem hd)
    · intro Q' hQ' d' hd'
      rcases List.mem_cons.1 hQ' with rfl | hQ'
      · exact hQ d' hd'
      · have := hconf Q' hQ' d' hd'
        simp only [hh'] at this
        rwa [(decomp_step G h Q hQ d'.1).2 (hoff Q' hQ' d' hd')] at this
    · intro e
      simp only [List.map_cons, List.sum_cons, hsum e, hh']
      ring
    · simp only [List.length_cons]
      omega

end Decomp

end MGraph

end EulerFlow
