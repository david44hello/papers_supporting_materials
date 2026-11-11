/-
EulerFlow/Sec2/ShortClaims5.lean — claims of the captions and of the running text that are new in version 2.00 of the
paper "The Cranston–Li–Su–Wang–Xu (2026) conjecture is true": the values after a step (Figure 1); at most one flow when
the group has at most two elements; the adjacency rules of the two source papers give the step graph; the first step of
the chain in the proof of Lemma 6.2 (b); the example of Remark 6.4; constant flows are joined to each other.
Part of the Lean 4 proof of the paper "The Cranston–Li–Su–Wang–Xu (2026) conjecture is true" by Dave Goel.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import EulerFlow.Sec6.Local
import EulerFlow.Sec2.ShortClaims3
import EulerFlow.Sec2.ShortClaims
import EulerFlow.Graph.AgreeOutside
import EulerFlow.Graph.MultiStep
import EulerFlow.Reduction.Const

namespace EulerFlow

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-! ### Figure 1: the values after a step, and the flow condition -/

omit [Fintype V] in
/-- Caption of Figure 1: after a step with the value `t` along a directed cycle `Q`, an edge that `Q` passes in its
reference direction has the value `f e + t`, an edge that `Q` passes against it has the value `f e - t`, an edge not on
`Q` keeps its value, and the flow condition still holds. -/
theorem fig_1_step_proved {A : Type} [AddCommGroup A] (G : MGraph V E) (Q : G.DirCycle) (f : E → A) (t : A) :
    (∀ e, (e, false) ∈ Q.darts → (f + fun e => Q.chi e • t) e = f e + t) ∧
    (∀ e, (e, true) ∈ Q.darts → (f + fun e => Q.chi e • t) e = f e - t) ∧
    (∀ e, (e, false) ∉ Q.darts → (e, true) ∉ Q.darts → (f + fun e => Q.chi e • t) e = f e) ∧
    (G.IsFlow f → G.IsFlow (f + fun e => Q.chi e • t)) := by
  refine ⟨fun e he => ?_, fun e he => ?_, fun e h1 h2 => ?_, fun hf => isFlow_add_chi_smul hf Q t⟩
  · have h : Q.chi e = 1 := by simpa [dartSign] using Q.chi_of_mem he
    simp [h]
  · have h : Q.chi e = -1 := by simpa [dartSign] using Q.chi_of_mem he
    simp [h, sub_eq_add_neg]
  · have h : Q.chi e = 0 := by simp [DirCycle.chi, h1, h2]
    simp [h]

/-! ### Groups with at most two elements -/

omit [Fintype V] in
/-- If `A` has at most two elements, a graph has at most one nowhere-zero `A`-flow; so it is `A`-flow-connected. -/
theorem intro_card_le_two_proved (A : Type) [AddCommGroup A] [Fintype A] (hA : Fintype.card A ≤ 2)
    (G : MGraph V E) :
    (∀ f f' : E → A, G.IsNZFlow f → G.IsNZFlow f' → f = f') ∧ G.FlowConnected A := by
  classical
  have key : ∀ x y : A, x ≠ 0 → y ≠ 0 → x = y := by
    intro x y hx hy
    by_contra hxy
    have h3 : ({0, x, y} : Finset A).card = 3 :=
      Finset.card_eq_three.mpr ⟨0, x, y, Ne.symm hx, Ne.symm hy, hxy, rfl⟩
    have hle := Finset.card_le_univ ({0, x, y} : Finset A)
    omega
  have huniq : ∀ f f' : E → A, G.IsNZFlow f → G.IsNZFlow f' → f = f' :=
    fun f f' hf hf' => funext fun e => key _ _ (hf.2 e) (hf'.2 e)
  refine ⟨huniq, fun f f' => ?_⟩
  obtain rfl : f = f' := Subtype.ext (huniq f.1 f'.1 f.2 f'.2)
  exact SimpleGraph.Reachable.refl _

/-! ### The two adjacency rules of the source papers give the step graph -/

/-- For one directed cycle `Q` and two maps `f`, `f'` that satisfy the flow condition: `f ≠ f'` and they agree outside
`Q`, iff `f' = f + t χ_Q` with `t ≠ 0`; and the support of `f' - f` is the edge set of `Q`, iff the same. -/
theorem same_graph_cycle {A : Type} [AddCommGroup A] (G : MGraph V E) (Q : G.DirCycle) (f f' : E → A)
    (hf : G.IsFlow f) (hf' : G.IsFlow f') :
    ((f ≠ f' ∧ ∀ e, Q.chi e = 0 → f e = f' e) ↔ ∃ t : A, t ≠ 0 ∧ f' = f + fun e => Q.chi e • t) ∧
    ((∀ e, f' e - f e ≠ 0 ↔ Q.chi e ≠ 0) ↔ ∃ t : A, t ≠ 0 ∧ f' = f + fun e => Q.chi e • t) := by
  have hagree := sec2_agree_outside_cycle_proved G Q f f' hf hf'
  obtain ⟨d₀, hd₀⟩ := List.exists_mem_of_ne_nil _ Q.ne_nil
  have hchi₀ : Q.chi d₀.1 ≠ 0 := (Q.chi_ne_zero_iff _).2 (List.mem_map.2 ⟨d₀, hd₀, rfl⟩)
  have hsm : ∀ (t : A) (e : E), t ≠ 0 → Q.chi e ≠ 0 → Q.chi e • t ≠ 0 := by
    intro t e ht he
    rcases Q.chi_mem e with h | h | h
    · rw [h]; simpa using ht
    · exact absurd h he
    · rw [h]; simpa using ht
  have hdiff : ∀ t : A, f' = (f + fun e => Q.chi e • t) → ∀ e, f' e - f e = Q.chi e • t := by
    intro t h e
    rw [h]
    simp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨hne, hout⟩
    obtain ⟨t, ht⟩ := hagree.1 hout
    refine ⟨t, fun ht0 => hne ?_, ht⟩
    rw [ht, ht0]
    funext e
    simp
  · rintro ⟨t, ht0, ht⟩
    refine ⟨fun heq => ?_, hagree.2 ⟨t, ht⟩⟩
    have h := hdiff t ht d₀.1
    rw [← heq, sub_self] at h
    exact hsm t d₀.1 ht0 hchi₀ h.symm
  · intro hsupp
    have hout : ∀ e, Q.chi e = 0 → f e = f' e := by
      intro e he
      by_contra hne
      exact (hsupp e).1 (fun h => hne (sub_eq_zero.1 h).symm) he
    obtain ⟨t, ht⟩ := hagree.1 hout
    refine ⟨t, fun ht0 => (hsupp d₀.1).2 hchi₀ ?_, ht⟩
    rw [hdiff t ht d₀.1, ht0]
    simp
  · rintro ⟨t, ht0, ht⟩ e
    rw [hdiff t ht e]
    exact ⟨fun h hc => h (by rw [hc]; simp), hsm t e ht0⟩

/-- Adjacency in the step graph on `I`-flows (steps of every non-zero value): one flow comes from the other by a step. -/
theorem stepGraph_adj_iff {A : Type} [AddCommGroup A] (G : MGraph V E) (I : Set A)
    (f f' : {f : E → A // G.IsIFlow I f}) :
    (G.stepGraph I {x | x ≠ 0}).Adj f f' ↔
      ∃ Q : G.DirCycle, ∃ t : A, t ≠ 0 ∧ f'.1 = f.1 + fun e => Q.chi e • t := by
  simp only [stepGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨Q, t, -, ht0, h⟩ | ⟨Q, t, -, ht0, h⟩⟩
    · exact ⟨Q, t, ht0, h⟩
    · refine ⟨Q, -t, neg_ne_zero.2 ht0, ?_⟩
      rw [h]
      funext e
      simp
  · rintro ⟨Q, t, ht0, h⟩
    refine ⟨fun heq => ?_, Or.inl ⟨Q, t, ht0, ht0, h⟩⟩
    exact ((same_graph_cycle G Q f.1 f'.1 f.2.1 f'.2.1).1.2 ⟨t, ht0, h⟩).1 (congrArg Subtype.val heq)

/-- The two adjacency rules give the step graph: two `I`-flows are adjacent in the step graph iff they are different
and agree outside a cycle, and iff the support of their difference is a cycle. With `I = {x | x ≠ 0}` the step graph is
`𝓕(G, A)` (`flowGraph A`); with `A = ℤ` and `I = Ik k` it is `𝓕(G, k)` (`kFlowGraph k`). The second part gives the two
rules for one fixed cycle. -/
theorem sec2_same_graph_proved {A : Type} [AddCommGroup A] (G : MGraph V E) (I : Set A) :
    (∀ f f' : {f : E → A // G.IsIFlow I f},
      ((G.stepGraph I {x | x ≠ 0}).Adj f f' ↔
        f.1 ≠ f'.1 ∧ ∃ Q : G.DirCycle, ∀ e, Q.chi e = 0 → f.1 e = f'.1 e) ∧
      ((G.stepGraph I {x | x ≠ 0}).Adj f f' ↔
        ∃ Q : G.DirCycle, ∀ e, f'.1 e - f.1 e ≠ 0 ↔ Q.chi e ≠ 0)) ∧
    (∀ (Q : G.DirCycle) (f f' : E → A), G.IsFlow f → G.IsFlow f' →
      ((f ≠ f' ∧ ∀ e, Q.chi e = 0 → f e = f' e) ↔ ∃ t : A, t ≠ 0 ∧ f' = f + fun e => Q.chi e • t) ∧
      ((∀ e, f' e - f e ≠ 0 ↔ Q.chi e ≠ 0) ↔ ∃ t : A, t ≠ 0 ∧ f' = f + fun e => Q.chi e • t)) := by
  refine ⟨fun f f' => ⟨?_, ?_⟩, fun Q f f' hf hf' => same_graph_cycle G Q f f' hf hf'⟩
  · rw [stepGraph_adj_iff]
    constructor
    · rintro ⟨Q, t, ht0, h⟩
      have h2 := (same_graph_cycle G Q f.1 f'.1 f.2.1 f'.2.1).1.2 ⟨t, ht0, h⟩
      exact ⟨h2.1, Q, h2.2⟩
    · rintro ⟨hne, Q, hout⟩
      obtain ⟨t, ht0, h⟩ := (same_graph_cycle G Q f.1 f'.1 f.2.1 f'.2.1).1.1 ⟨hne, hout⟩
      exact ⟨Q, t, ht0, h⟩
  · rw [stepGraph_adj_iff]
    constructor
    · rintro ⟨Q, t, ht0, h⟩
      exact ⟨Q, (same_graph_cycle G Q f.1 f'.1 f.2.1 f'.2.1).2.2 ⟨t, ht0, h⟩⟩
    · rintro ⟨Q, hsupp⟩
      obtain ⟨t, ht0, h⟩ := (same_graph_cycle G Q f.1 f'.1 f.2.1 f'.2.1).2.1 hsupp
      exact ⟨Q, t, ht0, h⟩

/-! ### The proof of Lemma 6.2 (b): the chain does not start with a step with value 1 -/

/-- In the situation of Lemma 6.2 (`d` the dart of `Q` that leaves `v`, `d'` the dart of `Q` that enters `v`): one of
the two edges of `Q` at `v` has the value `-1` in the direction of `Q`, the map `f + χ_Q` is `0` on that edge, and so
`f + χ_Q` is not a flow. -/
theorem lem_6_2_b_first_step_proved (m : ℕ) (hm : 4 ≤ m) (G : MGraph V E) (f : E → ZMod m)
    (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle)
    (hQ : ∀ d ∈ Q.darts, f d.1 = 1 ∨ f d.1 = -1) (v : V) (d d' : E × Bool) (hd : d ∈ Q.darts)
    (hd' : d' ∈ Q.darts) (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) :
    (dirVal f d = -1 ∨ dirVal f d' = -1) ∧
    ((f + fun e => Q.chi e • (1 : ZMod m)) d.1 = 0 ∨ (f + fun e => Q.chi e • (1 : ZMod m)) d'.1 = 0) ∧
    ¬ G.IsNZFlow (f + fun e => Q.chi e • (1 : ZMod m)) := by
  obtain ⟨h1, h2⟩ := MGraph.Sec6.lem_6_2_a_main m hm f hnb Q hQ v d d' hd hd' hdv hd'v
  have hflip : dirVal f (d'.1, !d'.2) = -dirVal f d' := by
    rcases d' with ⟨e', b'⟩
    cases b' <;> simp [dirVal]
  have hstep : ∀ d₀ ∈ Q.darts, dirVal f d₀ = -1 → (f + fun e => Q.chi e • (1 : ZMod m)) d₀.1 = 0 := by
    rintro ⟨e₀, b₀⟩ hd₀ hval
    have hchi := Q.chi_of_mem hd₀
    cases b₀
    · have hc : Q.chi e₀ = 1 := by simpa [dartSign] using hchi
      have hf0 : f e₀ = -1 := by simpa [dirVal] using hval
      simp [hc, hf0]
    · have hc : Q.chi e₀ = -1 := by simpa [dartSign] using hchi
      have hf0 : f e₀ = 1 := by simpa [dirVal] using hval
      simp [hc, hf0]
  have hval : dirVal f d = -1 ∨ dirVal f d' = -1 := by
    rcases h2 with h | h
    · right
      have h3 : dirVal f d' = -dirVal f d := by rw [h1, hflip, neg_neg]
      rw [h3, h]
    · exact Or.inl h
  refine ⟨hval, ?_, fun hnz => ?_⟩
  · rcases hval with h | h
    · exact Or.inl (hstep d hd h)
    · exact Or.inr (hstep d' hd' h)
  · rcases hval with h | h
    · exact hnz.2 d.1 (hstep d hd h)
    · exact hnz.2 d'.1 (hstep d' hd' h)

/-! ### Remark 6.4: a vertex of a cycle of small edges on more than two small edges -/

/-- The directed cycle of the graph with two vertices and six parallel edges that passes the edge `0` in its reference
direction and comes back along the edge `1`. -/
def dipoleTwoCycle : (dipole 6).DirCycle where
  darts := [((0 : Fin 6), false), ((1 : Fin 6), true)]
  ne_nil := by simp
  chain := by decide
  closes := by decide
  edges_nodup := by decide
  tails_nodup := by decide

/-- Remark 6.4, in `ℤ_3 × ℤ_3` with `S` of any cyclic decomposition and a small `a`: `6a = 0` and `2a ≠ 0`; the graph
with two vertices and six parallel edges has a flow with no balanced pair in which every end at the vertex `0` has the
outward value `a`; all six edges are small, all six are at the vertex `0`, and the vertex `0` lies on a cycle (of small
edges). So a vertex of a cycle of small edges lies on six small edges. -/
theorem rem_6_4_small_cycle_proved (D : CyclicDecomp (ZMod 3 × ZMod 3)) (a : ZMod 3 × ZMod 3) (ha : a ∈ D.S) :
    (6 : ℕ) • a = 0 ∧ (2 : ℕ) • a ≠ 0 ∧
    ∃ f : Fin 6 → ZMod 3 × ZMod 3, (dipole 6).IsNZFlow f ∧ ¬ (dipole 6).HasBalancedPair f ∧
      (∀ i : Fin 6 × Bool, (dipole 6).endVertex i = 0 → dirVal f i = a) ∧
      (∀ e, f e ∈ D.S) ∧ (∀ e, (dipole 6).IsAt e 0) ∧
      ∃ Q : (dipole 6).DirCycle, ∃ d ∈ Q.darts, (dipole 6).dartTail d = 0 := by
  obtain ⟨hneg, f, hf, hnb, hends⟩ := MGraph.Sec6.remark_Z3Z3 D a ha
  have ha0 : a ≠ 0 := by
    obtain ⟨k, hk | hk⟩ := ha
    · rw [hk]; exact D.s_ne k
    · rw [hk, neg_ne_zero]; exact D.s_ne k
  refine ⟨z3z3_six a, fun h2 => ?_, f, hf, hnb, hends, fun e => ?_, fun e => Or.inl rfl, dipoleTwoCycle,
    (0, false), by simp [dipoleTwoCycle], rfl⟩
  · rw [h2, neg_zero] at hneg
    exact ha0 hneg.symm
  · have h : f e = a := by simpa [dirVal] using hends (e, false) rfl
    rw [h]
    exact ha

/-! ### Constant flows are joined to each other -/

/-- Two constant flows with the value `a` along Eulerian orientations are `T`-joined, when the value `-2a` is in `T`
or is `0` (Lemma 3.3 (a): they are equal, or one comes from the other by a multi-step with the value `-2a`, which is a
chain of steps with that value). -/
theorem const_reachable {A : Type} [AddCommGroup A] (G : MGraph V E) (T : Set A) (a : A)
    (hT : -(2 • a) ≠ 0 → -(2 • a) ∈ T) (D D₂ : E → Bool) (hD : G.IsEulerOrient D) (hD₂ : G.IsEulerOrient D₂)
    (h : G.IsNZFlow (constFlow a D)) (h₂ : G.IsNZFlow (constFlow a D₂)) :
    (G.tStepGraph T).Reachable ⟨constFlow a D, h⟩ ⟨constFlow a D₂, h₂⟩ := by
  have key : ∀ (g : E → A) (hg : G.IsNZFlow g), g = constFlow a D₂ →
      (G.tStepGraph {-(2 • a)}).Reachable ⟨constFlow a D, h⟩ ⟨g, hg⟩ → -(2 • a) ≠ 0 →
      (G.tStepGraph T).Reachable ⟨constFlow a D, h⟩ ⟨constFlow a D₂, h₂⟩ := by
    rintro g hg rfl hr ht
    exact hr.mono (stepGraph_mono {x : A | x ≠ 0} (Set.singleton_subset_iff.2 (hT ht)))
  rcases constFlow_eq_or_multiStep a hD hD₂ with heq | ⟨ht, Qs, -, hdisj, hsum⟩
  · have hsub : (⟨constFlow a D, h⟩ : {f : E → A // G.IsNZFlow f}) = ⟨constFlow a D₂, h₂⟩ := Subtype.ext heq.symm
    rw [hsub]
  · have h₂' : G.IsNZFlow (constFlow a D + fun e => (Qs.map fun Q => Q.chi e).sum • (-(2 • a))) := hsum ▸ h₂
    obtain ⟨-, w, -⟩ := sec2_multistep_chain_proved G (-(2 • a)) ht Qs hdisj (constFlow a D) h h₂'
    exact key _ h₂' hsum.symm ⟨w⟩ ht

/-- All constant flows with the value `a` along Eulerian orientations are joined to each other by steps (of any
value), for every `a`; and in `ℤ_m` the constant flows with the value `1` are joined to each other by steps with
values in `{1, -1, 2, -2}`. (The hypotheses `h`, `h₂` say that the constant maps are flows; Lemma 3.3 proves this for
`a ≠ 0`.) -/
theorem intro_const_joined_proved (G : MGraph V E) (D D₂ : E → Bool) (hD : G.IsEulerOrient D)
    (hD₂ : G.IsEulerOrient D₂) :
    (∀ {A : Type} [AddCommGroup A] (a : A) (h : G.IsNZFlow (constFlow a D)) (h₂ : G.IsNZFlow (constFlow a D₂)),
      (G.flowGraph A).Reachable ⟨constFlow a D, h⟩ ⟨constFlow a D₂, h₂⟩) ∧
    (∀ (m : ℕ) (h : G.IsNZFlow (constFlow (1 : ZMod m) D)) (h₂ : G.IsNZFlow (constFlow (1 : ZMod m) D₂)),
      (G.tStepGraph (Tcyc m)).Reachable ⟨constFlow (1 : ZMod m) D, h⟩ ⟨constFlow (1 : ZMod m) D₂, h₂⟩) := by
  refine ⟨fun {A} _ a h h₂ => ?_, fun m h h₂ => ?_⟩
  · exact const_reachable G {x : A | x ≠ 0} a (fun ht => ht) D D₂ hD hD₂ h h₂
  · exact const_reachable G (Tcyc m) 1 (fun _ => by simp [Tcyc]) D D₂ hD hD₂ h h₂

end EulerFlow
