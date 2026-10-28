/-
EulerFlow/Graph/MultiStep.lean — paper 002 foundation: multi-steps are chains of steps (tex l.148-151, l.713-715),
and the decomposition interface used by Section 3.
* `multistep_chain_I`: for `I`-flows `f` and `f + t(χ_{Q_1} + ⋯ + χ_{Q_r})` with edge-disjoint `Q_i`, every
  partial sum is an `I`-flow and there is a walk of exactly `r` steps with the value `t` (gives
  `sec2_multistep_chain` with `I = {x ≠ 0}` and `sec9_multistep_chain` with `I = Ipq p q`);
* `circ_decomp`, `sum_chi_mem`, `sum_chi_ne_zero`, `reachable_of_circ`, `walk_of_circ`.
-/
import EulerFlow.Graph.Cycles

namespace EulerFlow

namespace MGraph

open Finset

variable {V E : Type} {G : MGraph V E} [Fintype E] [DecidableEq E] [DecidableEq V]

/-! ### Sums of `χ` over edge-disjoint cycles -/

omit [Fintype E] [DecidableEq V] in
/-- If no cycle of the list passes `e`, the `χ`-sum at `e` is `0`. -/
lemma sum_chi_eq_zero (Qs : List G.DirCycle) (e : E) (h : ∀ Q ∈ Qs, Q.chi e = 0) :
    (Qs.map fun Q => Q.chi e).sum = 0 :=
  List.sum_eq_zero (fun x hx => by
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hx
    exact h Q hQ)

omit [Fintype E] [DecidableEq V] in
/-- In a list of pairwise edge-disjoint cycles, the `χ`-sum at an edge of one cycle `Q` is `χ_Q`. -/
lemma sum_chi_eq_of_mem (Qs : List G.DirCycle) (hQs : Qs.Pairwise G.EdgeDisjoint) {Q : G.DirCycle}
    (hQ : Q ∈ Qs) {e : E} (he : Q.chi e ≠ 0) : (Qs.map fun Q => Q.chi e).sum = Q.chi e := by
  induction Qs with
  | nil => simp at hQ
  | cons Q₀ Qs ih =>
    rw [List.pairwise_cons] at hQs
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ((Q.chi_ne_zero_iff e).1 he)
    rcases List.mem_cons.1 hQ with rfl | hQ'
    · -- every later cycle misses the edge `d.1`
      have : (Qs.map fun Q' => Q'.chi d.1).sum = 0 := by
        apply sum_chi_eq_zero
        intro Q' hQ'
        by_contra hne
        obtain ⟨d', hd', hdd'⟩ := List.mem_map.1 ((Q'.chi_ne_zero_iff _).1 hne)
        exact hQs.1 Q' hQ' d hd d' hd' hdd'.symm
      simp [this]
    · -- `Q₀` misses the edge `d.1`
      have h0 : Q₀.chi d.1 = 0 := by
        by_contra hne
        obtain ⟨d', hd', hdd'⟩ := List.mem_map.1 ((Q₀.chi_ne_zero_iff _).1 hne)
        exact hQs.1 Q hQ' d' hd' d hd hdd'
      simp [h0, ih hQs.2 hQ']

omit [Fintype E] [DecidableEq V] in
/-- (chi-2) The `χ`-sum of pairwise edge-disjoint directed cycles has values in `{-1, 0, 1}`. -/
theorem sum_chi_mem (Qs : List G.DirCycle) (hQs : Qs.Pairwise G.EdgeDisjoint) (e : E) :
    (Qs.map fun Q => Q.chi e).sum = -1 ∨ (Qs.map fun Q => Q.chi e).sum = 0 ∨
      (Qs.map fun Q => Q.chi e).sum = 1 := by
  by_cases h : ∃ Q ∈ Qs, Q.chi e ≠ 0
  · obtain ⟨Q, hQ, he⟩ := h
    rw [sum_chi_eq_of_mem Qs hQs hQ he]
    exact Q.chi_mem e
  · simp only [not_exists, not_and, not_not] at h
    exact Or.inr (Or.inl (sum_chi_eq_zero Qs e h))

omit [Fintype E] [DecidableEq V] in
/-- (chi-3) The `χ`-sum of a nonempty list of pairwise edge-disjoint directed cycles is not the zero map. -/
theorem sum_chi_ne_zero (Qs : List G.DirCycle) (hQs : Qs.Pairwise G.EdgeDisjoint) (hne : Qs ≠ []) :
    (fun e => (Qs.map fun Q => Q.chi e).sum) ≠ 0 := by
  obtain ⟨Q, hQ⟩ := List.exists_mem_of_ne_nil Qs hne
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ Q.ne_nil
  intro h0
  have h1 := congr_fun h0 d.1
  simp only [Pi.zero_apply] at h1
  have hne0 : Q.chi d.1 ≠ 0 := by rw [Q.chi_of_mem hd]; exact dartSign_ne_zero _
  rw [sum_chi_eq_of_mem Qs hQs hQ hne0] at h1
  exact hne0 h1

/-! ### Flows from integer circulations -/

omit [DecidableEq E] in
/-- `x • t` of an integer circulation `x` satisfies the flow condition. -/
lemma IsFlow.zsmul_const {A : Type} [AddCommGroup A] {x : E → ℤ} (hx : G.IsFlow x) (t : A) :
    G.IsFlow (fun e => x e • t) := by
  intro v
  rw [← Finset.sum_smul, ← Finset.sum_smul, hx v]

omit [DecidableEq E] in
lemma IsFlow.add {A : Type} [AddCommGroup A] {x y : E → A} (hx : G.IsFlow x) (hy : G.IsFlow y) :
    G.IsFlow (x + y) := by
  intro v
  simp only [Pi.add_apply, Finset.sum_add_distrib, hx v, hy v]

/-- The `χ`-sum of any list of directed cycles is an integer circulation. -/
lemma isFlow_sum_chi (Qs : List G.DirCycle) : G.IsFlow (fun e => (Qs.map fun Q => Q.chi e).sum) := by
  induction Qs with
  | nil => intro v; simp
  | cons Q Qs ih =>
    have h2 := IsFlow.add Q.isFlow_chi ih
    intro v
    have := h2 v
    simp only [Pi.add_apply] at this
    simpa only [List.map_cons, List.sum_cons] using this

/-! ### Multi-steps are chains of steps -/

omit [Fintype E] [DecidableEq V] in
/-- On every edge, a partial sum of a multi-step takes the value of `f` or of `f'`. -/
lemma partial_value (Qs : List G.DirCycle) (hdisj : Qs.Pairwise G.EdgeDisjoint) {A : Type} [AddCommGroup A]
    (t : A) (f : E → A) (j : ℕ) (e : E) :
    (f + fun e => ((Qs.take j).map fun Q => Q.chi e).sum • t) e = f e ∨
      (f + fun e => ((Qs.take j).map fun Q => Q.chi e).sum • t) e =
        (f + fun e => (Qs.map fun Q => Q.chi e).sum • t) e := by
  by_cases h : ∃ Q ∈ Qs.take j, Q.chi e ≠ 0
  · obtain ⟨Q, hQ, he⟩ := h
    right
    have htake : (Qs.take j).Pairwise G.EdgeDisjoint := hdisj.sublist (List.take_sublist _ _)
    simp only [Pi.add_apply]
    rw [sum_chi_eq_of_mem _ htake hQ he, sum_chi_eq_of_mem _ hdisj (List.mem_of_mem_take hQ) he]
  · left
    simp only [not_exists, not_and, not_not] at h
    simp only [Pi.add_apply]
    rw [sum_chi_eq_zero _ e h, zero_smul, add_zero]

/-- **A multi-step is a chain of steps** (tex l.148-151, l.713-715), for `I`-flows: if `f` and
`f' = f + t(χ_{Q_1} + ⋯ + χ_{Q_r})` are `I`-flows and no two `Q_i` share an edge, every partial sum is an
`I`-flow and `f`, `f'` are joined by a walk of exactly `r` steps with the value `t`. -/
theorem multistep_chain_I {A : Type} [AddCommGroup A] (I : Set A) (t : A) (ht : t ≠ 0)
    (Qs : List G.DirCycle) (hdisj : Qs.Pairwise G.EdgeDisjoint) (f : E → A) (hf : G.IsIFlow I f)
    (hf' : G.IsIFlow I (f + fun e => (Qs.map fun Q => Q.chi e).sum • t)) :
    (∀ j ≤ Qs.length, G.IsIFlow I (f + fun e => ((Qs.take j).map fun Q => Q.chi e).sum • t)) ∧
    ∃ w : (G.stepGraph I {t}).Walk ⟨f, hf⟩ ⟨_, hf'⟩, w.length = Qs.length := by
  -- partial sums are `I`-flows
  have hpart : ∀ j, G.IsIFlow I (f + fun e => ((Qs.take j).map fun Q => Q.chi e).sum • t) := by
    intro j
    refine ⟨IsFlow.add hf.1 (IsFlow.zsmul_const (isFlow_sum_chi _) t), fun e => ?_⟩
    rcases partial_value Qs hdisj t f j e with h | h <;> rw [h]
    · exact hf.2 e
    · exact hf'.2 e
  refine ⟨fun j _ => hpart j, ?_⟩
  -- the walk to the `j`-th partial sum has exactly `j` steps
  have key : ∀ j ≤ Qs.length, ∃ w : (G.stepGraph I {t}).Walk ⟨f, hf⟩ ⟨_, hpart j⟩, w.length = j := by
    intro j
    induction j with
    | zero =>
      intro _
      have hff : (⟨f, hf⟩ : {f : E → A // G.IsIFlow I f}) = ⟨_, hpart 0⟩ := by
        apply Subtype.ext; funext e; simp
      exact ⟨(SimpleGraph.Walk.nil).copy rfl hff, by rw [SimpleGraph.Walk.length_copy]; rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨w, hw⟩ := ih (by omega)
      have hjlt : j < Qs.length := by omega
      set Q := Qs[j] with hQdef
      have htake : Qs.take (j + 1) = Qs.take j ++ [Q] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hjlt]; rfl
      have hnext : (f + fun e => ((Qs.take (j + 1)).map fun Q => Q.chi e).sum • t) =
          (f + fun e => ((Qs.take j).map fun Q => Q.chi e).sum • t) + fun e => Q.chi e • t := by
        funext e
        simp only [htake, List.map_append, List.sum_append, Pi.add_apply, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero, add_smul]
        abel
      have hadj : (G.stepGraph I {t}).Adj ⟨_, hpart j⟩ ⟨_, hpart (j + 1)⟩ := by
        rw [stepGraph, SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inl ⟨Q, t, rfl, ht, hnext⟩⟩
        intro heq
        have hval := congr_arg Subtype.val heq
        simp only at hval
        rw [hnext] at hval
        obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ Q.ne_nil
        have := congr_fun hval d.1
        simp only [Pi.add_apply] at this
        have hy : Q.chi d.1 • t = 0 := add_left_cancel (this.symm.trans (add_zero _).symm)
        rw [Q.chi_of_mem hd] at hy
        cases hb : d.2 <;> simp [hb, dartSign, ht] at hy
      exact ⟨w.concat hadj, by simp [hw]⟩
  obtain ⟨w, hw⟩ := key Qs.length le_rfl
  have hfin : (⟨_, hpart Qs.length⟩ : {f : E → A // G.IsIFlow I f}) = ⟨_, hf'⟩ := by
    apply Subtype.ext; simp
  exact ⟨w.copy rfl hfin, by simp [hw]⟩

/-! ### The interface used by Section 3 -/

/-- (C1) **Decomposition of a `{-1,0,1}`-valued integer circulation** into pairwise edge-disjoint directed cycles,
each following the sign of `h`, at most one per edge where `h ≠ 0` (tex l.283, l.629). -/
theorem circ_decomp (h : E → ℤ) (hval : ∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1) (hcirc : G.IsFlow h) :
    ∃ Qs : List G.DirCycle, Qs.Pairwise G.EdgeDisjoint ∧ (∀ Q ∈ Qs, ∀ e, Q.chi e ≠ 0 → Q.chi e = h e) ∧
      (∀ e, (Qs.map fun Q => Q.chi e).sum = h e) ∧ Qs.length ≤ (univ.filter fun e => h e ≠ 0).card := by
  obtain ⟨Qs, h1, h2, h3, h4⟩ := G.circ_decomp_darts h hval hcirc
  refine ⟨Qs, h1, fun Q hQ e he => ?_, h3, h4⟩
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ((Q.chi_ne_zero_iff e).1 he)
  rw [Q.chi_of_mem hd, h2 Q hQ d hd]

/-- (MS, walk form) If `f` and `f + h·t` are `I`-flows and `h` is a `{-1,0,1}`-valued integer circulation, they
are joined by at most `#{e | h e ≠ 0}` steps with the value `t`. -/
theorem walk_of_circ {A : Type} [AddCommGroup A] {I : Set A} (f f' : {f : E → A // G.IsIFlow I f})
    (h : E → ℤ) (hval : ∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1) (hcirc : G.IsFlow h) (t : A) (ht0 : t ≠ 0)
    (hf : f'.1 = f.1 + fun e => h e • t) :
    ∃ w : (G.stepGraph I {t}).Walk f f', w.length ≤ (univ.filter fun e => h e ≠ 0).card := by
  obtain ⟨Qs, hdisj, _, hsum, hlen⟩ := circ_decomp h hval hcirc
  have hf'' : G.IsIFlow I (f.1 + fun e => (Qs.map fun Q => Q.chi e).sum • t) := by
    have : (f.1 + fun e => (Qs.map fun Q => Q.chi e).sum • t) = f'.1 := by
      rw [hf]; funext e; simp [hsum e]
    rw [this]; exact f'.2
  obtain ⟨_, w, hw⟩ := multistep_chain_I I t ht0 Qs hdisj f.1 f.2 hf''
  have hend : (⟨_, hf''⟩ : {f : E → A // G.IsIFlow I f}) = f' := by
    apply Subtype.ext; rw [hf]; funext e; simp [hsum e]
  exact ⟨w.copy rfl hend, by rw [SimpleGraph.Walk.length_copy, hw]; exact hlen⟩

/-- `stepGraph` is monotone in the step set. -/
lemma stepGraph_mono {A : Type} [AddCommGroup A] (I : Set A) {T T' : Set A} (hT : T ⊆ T') :
    G.stepGraph I T ≤ G.stepGraph I T' := by
  intro f f' hadj
  rw [stepGraph, SimpleGraph.fromRel_adj] at hadj ⊢
  refine ⟨hadj.1, ?_⟩
  rcases hadj.2 with ⟨Q, t, ht, ht0, h⟩ | ⟨Q, t, ht, ht0, h⟩
  · exact Or.inl ⟨Q, t, hT ht, ht0, h⟩
  · exact Or.inr ⟨Q, t, hT ht, ht0, h⟩

/-- (MS, combined form) If `f` and `f + h·t` are `I`-flows, `h` a `{-1,0,1}`-valued integer flow and `t ∈ T`,
`t ≠ 0`, then they are joined by `T`-steps. -/
theorem reachable_of_circ {A : Type} [AddCommGroup A] {I T : Set A} (f f' : {f : E → A // G.IsIFlow I f})
    (h : E → ℤ) (hval : ∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1) (hcirc : G.IsFlow h) (t : A) (ht : t ∈ T) (ht0 : t ≠ 0)
    (hf : f'.1 = f.1 + fun e => h e • t) : (G.stepGraph I T).Reachable f f' := by
  obtain ⟨w, _⟩ := walk_of_circ f f' h hval hcirc t ht0 hf
  exact ⟨w.mapLe (stepGraph_mono I (Set.singleton_subset_iff.2 ht))⟩

/-! ### The two Statements claims on multi-steps -/

/-- `sec2_multistep_chain` (tex l.148-151): a multi-step between nowhere-zero flows is a chain of steps. -/
theorem sec2_multistep_chain_proved [Fintype V] {A : Type} [AddCommGroup A] (G : MGraph V E) (t : A) (ht : t ≠ 0)
    (Qs : List G.DirCycle) (hdisj : Qs.Pairwise G.EdgeDisjoint) (f : E → A) (hf : G.IsNZFlow f)
    (hf' : G.IsNZFlow (f + fun e => (Qs.map fun Q => Q.chi e).sum • t)) :
    (∀ j ≤ Qs.length, G.IsNZFlow (f + fun e => ((Qs.take j).map fun Q => Q.chi e).sum • t)) ∧
    ∃ w : (G.tStepGraph {t}).Walk ⟨f, hf⟩ ⟨_, hf'⟩, w.length = Qs.length :=
  multistep_chain_I {x | x ≠ 0} t ht Qs hdisj f hf hf'

/-- `sec9_multistep_chain` (tex l.713-715): a multi-step between `(p,q)`-flows is a chain of steps. -/
theorem sec9_multistep_chain_proved [Fintype V] (p q : ℕ) (G : MGraph V E) (t : ZMod p) (ht : t ≠ 0) (Qs : List G.DirCycle)
    (hdisj : Qs.Pairwise G.EdgeDisjoint) (f : E → ZMod p) (hf : G.IsIFlow (Ipq p q) f)
    (hf' : G.IsIFlow (Ipq p q) (f + fun e => (Qs.map fun Q => Q.chi e).sum • t)) :
    (∀ j ≤ Qs.length, G.IsIFlow (Ipq p q) (f + fun e => ((Qs.take j).map fun Q => Q.chi e).sum • t)) ∧
    ∃ w : (G.stepGraph (Ipq p q) {t}).Walk ⟨f, hf⟩ ⟨_, hf'⟩, w.length = Qs.length :=
  multistep_chain_I (Ipq p q) t ht Qs hdisj f hf hf'

end MGraph

end EulerFlow
