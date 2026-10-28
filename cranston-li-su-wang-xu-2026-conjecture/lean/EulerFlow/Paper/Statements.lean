/-
EulerFlow/Paper/Statements.lean — every claim of paper 002, Dave Goel, "Eulerian graphs are flow-connected" (v0.30),
one theorem per claim, named by the PDF numbering (theorem counter per section; Definition 2.1 shares it).
Bodies link to proofs in other files.
## (older version lines: in the header of versions/Statements_version_0.61.lean)
-/
import EulerFlow.Defs.Constructions
import EulerFlow.Concrete.K5Tri
import EulerFlow.Reduction.OneCycle
import EulerFlow.Reduction.Reorient
import EulerFlow.Count.StepsC
import EulerFlow.Concrete.Extra
import EulerFlow.Count.StepsB
import EulerFlow.Reduction.Thm23
import EulerFlow.Count.StepsA
import EulerFlow.Sec9.Replace
import EulerFlow.Sec2.Basic
import EulerFlow.Sec6.Local
import EulerFlow.IntFlow.Transfer
import EulerFlow.Graph.AgreeOutside
import EulerFlow.Reduction.Paper9
import EulerFlow.Concrete.Small
import EulerFlow.Reduction.Paper3
import EulerFlow.Sec4.Prop44
import EulerFlow.Concrete.Dipole
import EulerFlow.Sec6.Acyc
import EulerFlow.Sec4.Decomp
import EulerFlow.Graph.Orient
import EulerFlow.Sec2.ShortClaims
import EulerFlow.Reduction.BalancedJoined

namespace EulerFlow

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-! ## Section 2: multi-steps (tex l.148-151) -/

/-- SHORT v1.51: Section 2 (text, multi-steps), l.161-164.
Section 2 (tex l.148-151): for a multi-step `f' = f + t(χ_{Q_1} + ⋯ + χ_{Q_r})` between flows, every partial
sum `f + t(χ_{Q_1} + ⋯ + χ_{Q_j})` is a flow; so a multi-step with the value `t` is a chain of `r` steps with
the value `t`. -/
theorem sec2_multistep_chain {A : Type} [AddCommGroup A] (G : MGraph V E) (t : A) (ht : t ≠ 0)
    (Qs : List G.DirCycle) (hdisj : Qs.Pairwise G.EdgeDisjoint) (f : E → A) (hf : G.IsNZFlow f)
    (hf' : G.IsNZFlow (f + fun e => (Qs.map fun Q => Q.chi e).sum • t)) :
    (∀ j ≤ Qs.length, G.IsNZFlow (f + fun e => ((Qs.take j).map fun Q => Q.chi e).sum • t)) ∧
    ∃ w : (G.tStepGraph {t}).Walk ⟨f, hf⟩ ⟨_, hf'⟩, w.length = Qs.length :=
  MGraph.sec2_multistep_chain_proved G t ht Qs hdisj f hf hf'

/-- SHORT v1.51: Section 2 (text, Flows), l.154-155.
Section 2 (tex l.138-139, again l.709-711): two flows that agree outside a cycle differ by a flow on that
cycle, which is constant along the cycle: `f' = f + t χ_Q` (and conversely, tex l.709-711). -/
theorem sec2_agree_outside_cycle {A : Type} [AddCommGroup A] (G : MGraph V E) (Q : G.DirCycle) (f f' : E → A)
    (hf : G.IsFlow f) (hf' : G.IsFlow f') :
    (∀ e, Q.chi e = 0 → f e = f' e) ↔ ∃ t : A, f' = f + fun e => Q.chi e • t :=
  MGraph.sec2_agree_outside_cycle_proved G Q f f' hf hf'

/-- SHORT v1.51: Section 2 (text, Flows; definition of step), l.152-153.
Section 2 (SHORT paper v1.46 l.155-157): the value `t` of a step "is determined only up to sign, as reversing `Q`
or exchanging `f` and `f'` replaces `t` by `-t`": (i) the reversed cycle (same edges, each in the other direction, in
reverse order) is a directed cycle `Q'` with `f + tχ_Q = f + (-t)χ_{Q'}`; (ii) `f' = f + tχ_Q` gives
`f = f' + (-t)χ_Q`; (iii) if `f' = f + tχ_Q = f + t'χ_{Q'}` with `t ≠ 0`, then `t' = t` or `t' = -t`. -/
theorem sec2_step_value_sign {A : Type} [AddCommGroup A] (G : MGraph V E) :
    (∀ Q : G.DirCycle, ∃ Q' : G.DirCycle, Q'.darts = (Q.darts.map fun d => (d.1, !d.2)).reverse ∧
      ∀ (t : A) (f : E → A), (f + fun e => Q.chi e • t) = f + fun e => Q'.chi e • (-t)) ∧
    (∀ (Q : G.DirCycle) (t : A) (f f' : E → A), f' = (f + fun e => Q.chi e • t) →
      f = f' + fun e => Q.chi e • (-t)) ∧
    (∀ (Q Q' : G.DirCycle) (t t' : A) (f f' : E → A), t ≠ 0 → f' = (f + fun e => Q.chi e • t) →
      f' = (f + fun e => Q'.chi e • t') → t' = t ∨ t' = -t) :=
  ⟨fun Q => ⟨cycleReverse G Q, rfl, fun t f => step_reverse G Q t f⟩,
   fun Q t f f' h => step_exchange G Q t f f' h,
   fun Q Q' t t' f f' ht h h' => step_value_up_to_sign G Q Q' t t' ht f f' h h'⟩

/-- SHORT v1.51: Section 2 (text, Ends of edges), l.167-168.
Section 2 (SHORT paper v1.46 l.171-172): the outward value `y_i(f)` "is non-zero if `f` is a flow". -/
theorem sec2_outward_value_ne_zero {A : Type} [AddCommGroup A] (G : MGraph V E) (f : E → A) (hf : G.IsNZFlow f)
    (i : E × Bool) : dirVal f i ≠ 0 :=
  outward_ne_zero G f hf i

/-- SHORT v1.51: Definition 2.1 (the parenthesis), l.180.
Definition 2.1 (SHORT paper v1.46 l.184): "the two ends of a loop always satisfy `y_i(f) + y_j(f) = 0`": for every
loop `l` and every `f`, the ends `(l, false)` and `(l, true)` are different ends at the same vertex, and their outward
values sum to `0`. -/
theorem def_2_1_loop_ends {A : Type} [AddCommGroup A] (G : MGraph V E) (f : E → A) (l : E) (hl : G.IsLoop l) :
    (l, false) ≠ (l, true) ∧ G.endVertex (l, false) = G.endVertex (l, true) ∧
      dirVal f (l, false) + dirVal f (l, true) = 0 :=
  loop_ends G f l hl

/-- SHORT v1.51: Section 5 (proof of Theorem 2.2, first sentence), l.394 (also l.155-156, l.294).
Section 2 (tex l.140-142): for the group with one element, a graph with an edge has no flow, a graph with no
edge has one flow, and every graph is flow-connected. -/
theorem sec2_trivial_group (A : Type) [AddCommGroup A] [Fintype A] (hA : Fintype.card A = 1) (G : MGraph V E) :
    (Nonempty E → ∀ f : E → A, ¬ G.IsNZFlow f) ∧ (IsEmpty E → ∃! f : E → A, G.IsNZFlow f) ∧
      G.FlowConnected A := by
  apply sec2_trivial_group_proved <;> assumption

/-- SHORT v1.51: Section 2, equation (1), l.168-172.
Equation (2.1) (tex l.155-159): the flow condition at `v` says that the outward values at `v` sum to `0`. -/
theorem sec2_kirchhoff {A : Type} [AddCommGroup A] (G : MGraph V E) (f : E → A) :
    G.IsFlow f ↔ ∀ v, ∑ i ∈ Finset.univ.filter (fun i : E × Bool => G.endVertex i = v), dirVal f i = 0 :=
  MGraph.Sec2.kirchhoff_iff G f

/-- SHORT v1.51: Section 2, equation (2), l.173-177.
Equation (2.2) (tex l.160-164): if `Q` enters `v` through the end `i = (d'.1, !d'.2)` and leaves `v` through the
end `j = d`, then `y_i(f + tχ_Q) = y_i(f) - t`, `y_j(f + tχ_Q) = y_j(f) + t`, and the other ends at `v` keep their
outward values. -/
theorem sec2_ends {A : Type} [AddCommGroup A] (G : MGraph V E) (f : E → A) (t : A) (Q : G.DirCycle) (v : V)
    (d d' : E × Bool) (hd : d ∈ Q.darts) (hd' : d' ∈ Q.darts) (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) :
    dirVal (f + fun e => Q.chi e • t) (d'.1, !d'.2) = dirVal f (d'.1, !d'.2) - t ∧
    dirVal (f + fun e => Q.chi e • t) d = dirVal f d + t ∧
    ∀ i, G.endVertex i = v → i ≠ d → i ≠ (d'.1, !d'.2) → dirVal (f + fun e => Q.chi e • t) i = dirVal f i :=
  MGraph.Sec2.ends G f t Q v d d' hd hd' hdv hd'v

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Section 2 (tex l.129, l.640-642, l.704): the notions do not depend on the reference directions: reversing the
reference direction of any set of edges does not change whether the `I`-flows are joined by steps with values in `T`
(for `I = -I`; this covers `A`-flow-, `k`-flow- and `(p,q)`-flow-connectedness). -/
theorem sec2_ref_dir_indep {A : Type} [AddCommGroup A] (G : MGraph V E) (R : E → Bool) (I T : Set A)
    (hI : ∀ x ∈ I, -x ∈ I) :
    ((G.reorient R).stepGraph I T).Preconnected ↔ (G.stepGraph I T).Preconnected :=
  sec2_ref_dir_indep_proved G R I T hI

/-! ## Section 3: the reduction (tex l.210-319) -/

/-- SHORT v1.51: Section 3 (text), l.210 (also l.394).
Section 3 (tex l.219): (T1) and (T2) hold for `T = A ∖ {0}` (for `|A| ≥ 2`). -/
theorem sec3_T_nonzero (A : Type) [AddCommGroup A] [Nontrivial A] :
    CondT1 ({x | x ≠ 0} : Set A) ∧ CondT2 ({x | x ≠ 0} : Set A) :=
  sec3_T_nonzero_proved A

/-- SHORT v1.51: Section 3 (text), l.210-211 (T non-zero, T=-T: l.202-204).
Section 3 (tex l.212-220): `T = {1, -1, 2, -2}` in `ℤ_m`, `m ≥ 3`, is a set of non-zero elements with `T = -T`,
and (T1), (T2) hold for it. -/
theorem sec3_T_cyc (m : ℕ) (hm : 3 ≤ m) :
    CondT1 (Tcyc m) ∧ CondT2 (Tcyc m) ∧ (0 : ZMod m) ∉ Tcyc m ∧ ∀ t ∈ Tcyc m, -t ∈ Tcyc m :=
  sec3_T_cyc_proved m hm

/-- SHORT v1.51: Lemma 3.1, l.215-216.
Lemma 3.1 (loops, tex l.222-232). -/
theorem lem_3_1 {A : Type} [AddCommGroup A] (T : Set A) (hT0 : (0 : A) ∉ T) (hTneg : ∀ t ∈ T, -t ∈ T)
    (hT1 : CondT1 T) (G : MGraph V E) (l : E) (hl : G.IsLoop l)
    (h : ((G.deleteEdge l).tStepGraph T).Preconnected) : (G.tStepGraph T).Preconnected :=
  lem_3_1_proved T hT0 hTneg hT1 G l hl h

/-- SHORT v1.51: Lemma 3.2 (a), l.235 (setup l.226-233).
Lemma 3.2 (a) (splitting off, tex l.234-245): `L` is a bijection from the flows of `G'` onto `B(v; e, e')`. -/
theorem lem_3_2_a {A : Type} [AddCommGroup A] (G : MGraph V E) (hG : G.Loopless) (v : V) (e e' : E)
    (hne : e ≠ e') (he : G.IsAt e v) (he' : G.IsAt e' v) :
    Set.BijOn (G.splitLift (A := A) v e e') {f' | (G.splitOff v e e').IsNZFlow f'} {f | G.InB v e e' f} :=
  lem_3_2_a_proved G hG v e e' hne he he'

/-- SHORT v1.51: Lemma 3.2 (b), l.236-237.
Lemma 3.2 (b) (tex l.246-247): `L` maps a multi-step of `G'` with the value `t` to a multi-step of `G` with
the value `t`. -/
theorem lem_3_2_b {A : Type} [AddCommGroup A] (G : MGraph V E) (hG : G.Loopless) (v : V) (e e' : E)
    (hne : e ≠ e') (he : G.IsAt e v) (he' : G.IsAt e' v) (t : A) (f₁ f₂ : Option {x : E // x ≠ e ∧ x ≠ e'} → A)
    (h₁ : (G.splitOff v e e').IsNZFlow f₁) (h₂ : (G.splitOff v e e').IsNZFlow f₂)
    (hstep : (G.splitOff v e e').IsMultiStep t f₁ f₂) :
    G.IsMultiStep t (G.splitLift v e e' f₁) (G.splitLift v e e' f₂) :=
  lem_3_2_b_proved G hG v e e' hne he he' t f₁ f₂ h₁ h₂ hstep

/-- SHORT v1.51: Lemma 3.2 (b), second sentence, l.237-238.
Lemma 3.2 (b), second sentence (tex l.247-248): if two flows of `G'` are `T`-joined, their images under `L`
are `T`-joined. -/
theorem lem_3_2_b_joined {A : Type} [AddCommGroup A] (T : Set A) (G : MGraph V E) (hG : G.Loopless) (v : V)
    (e e' : E) (hne : e ≠ e') (he : G.IsAt e v) (he' : G.IsAt e' v)
    (f₁ f₂ : {f : Option {x : E // x ≠ e ∧ x ≠ e'} → A // (G.splitOff v e e').IsNZFlow f})
    (hj : ((G.splitOff v e e').tStepGraph T).Reachable f₁ f₂) :
    ∃ (k₁ : G.IsNZFlow (G.splitLift v e e' f₁.1)) (k₂ : G.IsNZFlow (G.splitLift v e e' f₂.1)),
      (G.tStepGraph T).Reachable ⟨_, k₁⟩ ⟨_, k₂⟩ :=
  lem_3_2_b_joined_proved T G hG v e e' hne he he' f₁ f₂ hj

/-- SHORT v1.51: Lemma 3.3 (preamble), l.262-263.
Lemma 3.3, preamble (tex l.272-273): an even graph has an Eulerian orientation. -/
theorem lem_3_3_exists (G : MGraph V E) (hG : G.IsEven) : ∃ D : E → Bool, G.IsEulerOrient D :=
  MGraph.lem_3_3_exists_proved G hG

/-- SHORT v1.51: Lemma 3.3 (preamble), l.263-264.
Lemma 3.3, preamble (tex l.273): for an Eulerian orientation `D` and `a ≠ 0`, `a 𝟙_D` is a flow. -/
theorem lem_3_3_flow {A : Type} [AddCommGroup A] (G : MGraph V E) (D : E → Bool) (hD : G.IsEulerOrient D)
    (a : A) (ha : a ≠ 0) : G.IsNZFlow (constFlow a D) :=
  lem_3_3_flow_proved G D hD a ha

/-- SHORT v1.51: Lemma 3.3 (a), l.266-267.
Lemma 3.3 (a) (tex l.276-277): for two Eulerian orientations, `a 𝟙_{D₂} = a 𝟙_D`, or `a 𝟙_{D₂}` comes from
`a 𝟙_D` by one multi-step with the value `-2a`. -/
theorem lem_3_3_a {A : Type} [AddCommGroup A] (G : MGraph V E) (a : A) (ha : a ≠ 0) (D D₂ : E → Bool)
    (hD : G.IsEulerOrient D) (hD₂ : G.IsEulerOrient D₂) :
    constFlow a D₂ = constFlow a D ∨ G.IsMultiStep (-(2 • a)) (constFlow a D) (constFlow a D₂) :=
  lem_3_3_a_proved G a ha D D₂ hD hD₂

/-- SHORT v1.51: Lemma 3.3 (b); also Section 1 (Outline: any two edges at a vertex, any a ≠ 0), l.268 (also l.118-119).
Lemma 3.3 (b) (tex l.278): in the situation of Lemma 3.2 (and `G` even), `B(v; e, e')` contains a flow
`a 𝟙_D`. -/
theorem lem_3_3_b {A : Type} [AddCommGroup A] (G : MGraph V E) (hev : G.IsEven) (hG : G.Loopless) (v : V)
    (e e' : E) (hne : e ≠ e') (he : G.IsAt e v) (he' : G.IsAt e' v) (a : A) (ha : a ≠ 0) :
    ∃ D : E → Bool, G.IsEulerOrient D ∧ G.InB v e e' (constFlow a D) :=
  lem_3_3_b_proved G hev hG v e e' hne he he' a ha

/-- SHORT v1.51: Proposition 3.4; also Section 1 (Outline: (LOCAL) is needed only for loopless graphs with all degrees 0 or at least 4), l.284-291 (also l.124).
Proposition 3.4 (the reduction, tex l.294-303). `𝒢` is a class of even graphs closed under deleting a loop
and under splitting off; `T = -T ⊆ A ∖ {0}` satisfies (T1) and (T2); (LOCAL) holds. Then in every `G ∈ 𝒢` any two
flows are `T`-joined. -/
theorem prop_3_4 {A : Type} [AddCommGroup A] (T : Set A) (hT0 : (0 : A) ∉ T) (hTneg : ∀ t ∈ T, -t ∈ T)
    (hT1 : CondT1 T) (hT2 : CondT2 T)
    (𝒢 : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E], MGraph V E → Prop)
    (h_even : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      𝒢 V E G → G.IsEven)
    (h_loop : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E) (l : E),
      𝒢 V E G → G.IsLoop l → 𝒢 V {x : E // x ≠ l} (G.deleteEdge l))
    (h_split : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E)
      (v : V) (e e' : E), 𝒢 V E G → G.Loopless → e ≠ e' → G.IsAt e v → G.IsAt e' v →
      𝒢 V (Option {x : E // x ≠ e ∧ x ≠ e'}) (G.splitOff v e e'))
    (h_local : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      𝒢 V E G → Nonempty E → G.Loopless → (∀ v, G.degree v = 0 ∨ 4 ≤ G.degree v) →
      ∀ f : {f : E → A // G.IsNZFlow f}, ∃ f' : {f : E → A // G.IsNZFlow f},
        G.HasBalancedPair f'.1 ∧ (G.tStepGraph T).Reachable f f')
    (G : MGraph V E) (hG : 𝒢 V E G) : (G.tStepGraph T).Preconnected :=
  prop_3_4_proved T hT0 hTneg hT1 hT2 𝒢 h_even h_loop h_split h_local G hG

/-- SHORT v1.51: Section 5 (proof of Theorem 2.2), l.394-395 (G' even: l.278).
Section 3 (tex l.308-309, l.408-410, l.747-748): deleting a loop lowers the degree of its vertex by `2`; splitting
off lowers the degree of `v` by `2` and keeps the other degrees (a new loop counts twice); both keep a graph even. -/
theorem sec3_closure (G : MGraph V E) :
    (∀ l, G.IsLoop l → ∀ z, (G.deleteEdge l).degree z + (if G.src l = z then 2 else 0) = G.degree z) ∧
    (∀ l, G.IsLoop l → G.IsEven → (G.deleteEdge l).IsEven) ∧
    (G.Loopless → ∀ (v : V) (e e' : E), e ≠ e' → G.IsAt e v → G.IsAt e' v →
      (∀ z, (G.splitOff v e e').degree z + (if v = z then 2 else 0) = G.degree z) ∧
      (G.IsEven → (G.splitOff v e e').IsEven)) :=
  ⟨fun _ hl z => degree_deleteEdge hl z, fun _ hl hev => isEven_deleteEdge hl hev,
    fun hG _ _ _ hne he he' => ⟨fun z => degree_splitOff (SplitData.of hG hne he he') z,
      fun hev => isEven_splitOff (SplitData.of hG hne he he') hev⟩⟩

/-! ## Section 4: the local step for every group, on 4-regular graphs (tex l.321-402) -/

/-- SHORT v1.51: Section 4 (text), l.314-319.
Section 4 (tex l.323-327): every finite abelian group is a direct sum of cyclic groups `⟨s_k⟩`, `s_k ≠ 0`. -/
theorem sec4_decomp_exists (A : Type) [AddCommGroup A] [Fintype A] : Nonempty (CyclicDecomp A) := by
  apply sec4_decomp_exists_proved <;> assumption

/-- SHORT v1.51: Section 4 (text), l.320.
Section 4 (tex l.329): `S = -S`, `0 ∉ S`, and `S` generates `A`. -/
theorem sec4_S_props {A : Type} [AddCommGroup A] (D : CyclicDecomp A) :
    (∀ x ∈ D.S, -x ∈ D.S) ∧ (0 : A) ∉ D.S ∧ AddSubgroup.closure D.S = ⊤ := by
  apply sec4_S_props_proved <;> assumption

/-- SHORT v1.51: Section 4 (text), l.320-321.
Section 4 (SHORT paper v1.46 l.324): "an edge is small if its value is small (this does not depend on the
direction)". -/
theorem sec4_small_dir_indep {A : Type} [AddCommGroup A] (D : CyclicDecomp A) (f : E → A) (d : E × Bool) :
    dirVal f d ∈ D.S ↔ dirVal f (d.1, !d.2) ∈ D.S :=
  small_dir_indep D f d

/-- SHORT v1.51: Section 4 (text), l.318-322.
Section 4 (SHORT paper v1.46 l.323-326): "the color of `s ∈ S` is the index `h` with `s ∈ ⟨s_h⟩`" — such an `h`
exists and is unique — and the color of a small edge "is the color of its value, which is the same in both
directions": `-s` has the color of `s`. -/
theorem sec4_color_unique {A : Type} [AddCommGroup A] (D : CyclicDecomp A) (s : A) (hs : s ∈ D.S) :
    (∃! h, s ∈ AddSubgroup.zmultiples (D.s h)) ∧
      ∀ h, (s ∈ AddSubgroup.zmultiples (D.s h) ↔ -s ∈ AddSubgroup.zmultiples (D.s h)) :=
  color_unique D s hs

/-- SHORT v1.51: Lemma 4.1, l.326-327.
Lemma 4.1 (tex l.334-337): if no edge of the cycle `Q` is small, some step `f' = f + t χ_Q` has
`ρ(f') ≤ ρ(f) - 1`. -/
theorem lem_4_1 {A : Type} [AddCommGroup A] [Fintype A] (D : CyclicDecomp A) (G : MGraph V E) (f : E → A)
    (hf : G.IsNZFlow f) (Q : G.DirCycle) (hQ : ∀ d ∈ Q.darts, f d.1 ∉ D.S) :
    ∃ t : A, t ≠ 0 ∧ G.IsNZFlow (f + fun e => Q.chi e • t) ∧ D.rho (f + fun e => Q.chi e • t) + 1 ≤ D.rho f := by
  apply MGraph.Sec4.lem_4_1_main <;> assumption

/-- SHORT v1.51: Corollary 4.2, l.339-340.
Corollary 4.2 (tex l.348-350): every flow `f` is joined by at most `ρ(f)` steps to a flow whose edges that
are not small contain no cycle. -/
theorem cor_4_2 {A : Type} [AddCommGroup A] [Fintype A] (D : CyclicDecomp A) (G : MGraph V E)
    (f : {f : E → A // G.IsNZFlow f}) :
    ∃ f' : {f : E → A // G.IsNZFlow f}, (∃ w : (G.flowGraph A).Walk f f', w.length ≤ D.rho f.1) ∧
      ∀ Q : G.DirCycle, ∃ d ∈ Q.darts, f'.1 d.1 ∈ D.S := by
  apply MGraph.Sec4.cor_4_2_main <;> assumption

/-- SHORT v1.51: Lemma 4.3, l.347-348.
Lemma 4.3 (tex l.357-361): no loop, all degrees `0` or `4`, `f` without balanced pair, `Q` a cycle of small
edges: some step `f + t χ_Q` is a flow with a balanced pair. -/
theorem lem_4_3 {A : Type} [AddCommGroup A] [Fintype A] (D : CyclicDecomp A) (G : MGraph V E)
    (hG : G.Loopless) (hdeg : ∀ v, G.degree v = 0 ∨ G.degree v = 4) (f : E → A) (hf : G.IsNZFlow f)
    (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle) (hQ : ∀ d ∈ Q.darts, f d.1 ∈ D.S) :
    ∃ t : A, t ≠ 0 ∧ G.IsNZFlow (f + fun e => Q.chi e • t) ∧ G.HasBalancedPair (f + fun e => Q.chi e • t) := by
  apply MGraph.Sec4.lem_4_3_main <;> assumption

/-- SHORT v1.51: Proposition 4.4, l.377.
Proposition 4.4 (tex l.391-394): at least one edge, no loop, all degrees `0` or `4`: every flow `f` is
joined by at most `ρ(f) + 1` steps to a flow with a balanced pair. -/
theorem prop_4_4 {A : Type} [AddCommGroup A] [Fintype A] (D : CyclicDecomp A) (G : MGraph V E)
    (hE : Nonempty E) (hG : G.Loopless) (hdeg : ∀ v, G.degree v = 0 ∨ G.degree v = 4)
    (f : {f : E → A // G.IsNZFlow f}) :
    ∃ f' : {f : E → A // G.IsNZFlow f}, G.HasBalancedPair f'.1 ∧
      ∃ w : (G.flowGraph A).Walk f f', w.length ≤ D.rho f.1 + 1 := by
  apply MGraph.Sec4.prop_4_4_main <;> assumption

/-! ## Sections 2 and 5: Theorems 2.2, 2.3 and Lemma 5.1 (tex l.172-179, l.404-457) -/

/-- SHORT v1.51: Theorem 2.2; also Section 1 (Further results: of any order), l.186 (also l.103-104).
Theorem 2.2 (tex l.172-175): every even graph with all degrees at most `4` is `A`-flow-connected, for every
finite abelian group `A`. -/
theorem thm_2_2 (A : Type) [AddCommGroup A] [Fintype A] (G : MGraph V E) (hev : G.IsEven)
    (hdeg : ∀ v, G.degree v ≤ 4) : G.FlowConnected A :=
  thm_2_2_proved A G hev hdeg

/-- SHORT v1.51: Lemma 5.1 (a), l.406 (setup l.401-404).
Lemma 5.1 (a) (contracting a triangle, tex l.415-421): `p f` is a flow of `G = G⁺/Δ`, and every flow of `G`
is `p f` for some flow `f` of `G⁺`. -/
theorem lem_5_1_a {A : Type} [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A) (G : MGraph V E)
    (x₁ x₂ x₃ : V) (d₁₂ d₂₃ d₃₁ : E) (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁) :
    (∀ f : E → A, G.IsNZFlow f →
      (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).IsNZFlow (restrictTo {d₁₂, d₂₃, d₃₁} f)) ∧
    (∀ h, (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).IsNZFlow h →
      ∃ f : E → A, G.IsNZFlow f ∧ restrictTo {d₁₂, d₂₃, d₃₁} f = h) :=
  lem_5_1_a_proved hA G x₁ x₂ x₃ d₁₂ d₂₃ d₃₁ hΔ

/-- SHORT v1.51: Lemma 5.1 (b), l.407-408.
Lemma 5.1 (b) (tex l.422-423): a multi-step with the value `t` is mapped by `p` to an equality or to a
multi-step with the value `t`. -/
theorem lem_5_1_b {A : Type} [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A) (G : MGraph V E)
    (x₁ x₂ x₃ : V) (d₁₂ d₂₃ d₃₁ : E) (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁) (t : A) (f₁ f₂ : E → A)
    (h₁ : G.IsNZFlow f₁) (h₂ : G.IsNZFlow f₂) (hstep : G.IsMultiStep t f₁ f₂) :
    restrictTo {d₁₂, d₂₃, d₃₁} f₂ = restrictTo {d₁₂, d₂₃, d₃₁} f₁ ∨
      (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).IsMultiStep t (restrictTo {d₁₂, d₂₃, d₃₁} f₁)
        (restrictTo {d₁₂, d₂₃, d₃₁} f₂) :=
  lem_5_1_b_proved hA G x₁ x₂ x₃ d₁₂ d₂₃ d₃₁ hΔ t f₁ f₂ h₁ h₂ hstep

/-- SHORT v1.51: Lemma 5.1, last sentence, l.410.
Lemma 5.1, last sentence (tex l.425): if `G⁺` is `A`-flow-connected, then `G⁺/Δ` is `A`-flow-connected. -/
theorem lem_5_1_c {A : Type} [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A) (G : MGraph V E)
    (x₁ x₂ x₃ : V) (d₁₂ d₂₃ d₃₁ : E) (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁)
    (hconn : G.FlowConnected A) : (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).FlowConnected A :=
  lem_5_1_c_proved hA G x₁ x₂ x₃ d₁₂ d₂₃ d₃₁ hΔ hconn

/-- SHORT v1.51: Section 1 (text, Outline of the proof), l.128-129.
Introduction (tex l.110-111): a triangle is `A`-connected in the sense of [JLPT] when `|A| ≥ 4`: for every
`β : V → A` with sum `0` there is a nowhere-zero map on the edges with boundary `β`. -/
theorem intro_triangle_A_connected {A : Type} [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A)
    (β : Fin 3 → A) (hβ : ∑ v, β v = 0) :
    ∃ x : Fin 3 → A, (∀ e, x e ≠ 0) ∧ (cycleGraph 3).boundary x = β :=
  intro_triangle_A_connected_proved hA β hβ

/-- SHORT v1.51: Theorem 2.3, l.190.
Theorem 2.3 (tex l.177-179): for every finite abelian group `A` with `|A| ≥ 4`, every even graph is
`A`-flow-connected. -/
theorem thm_2_3 (A : Type) [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A) (G : MGraph V E)
    (hev : G.IsEven) : G.FlowConnected A :=
  thm_2_3_proved A hA G hev

/-! ## Section 6: cyclic groups (tex l.459-528) -/

/-- SHORT v1.51: Lemma 6.1, l.450-451.
Lemma 6.1 (tex l.465-468): `m ≥ 4`; if no edge of the cycle `Q` is small (value `±1`), then `f` is joined, by
steps along `Q` with the value `-1`, to a flow `f'` with `ρ(f') ≤ ρ(f) - 1`. -/
theorem lem_6_1 (m : ℕ) (hm : 4 ≤ m) (G : MGraph V E) (f : E → ZMod m) (hf : G.IsNZFlow f) (Q : G.DirCycle)
    (hQ : ∀ d ∈ Q.darts, f d.1 ≠ 1 ∧ f d.1 ≠ -1) :
    ∃ ts : List (ZMod m), (∀ t ∈ ts, t = -1) ∧ G.StepsAlong {x | x ≠ 0} (Tcyc m) Q f ts ∧
      rhoCyc (f + fun e => Q.chi e • ts.sum) + 1 ≤ rhoCyc f := by
  apply lem_6_1_proved <;> assumption

/-- SHORT v1.51: Lemma 6.2 (a), l.464 (setup l.461-462).
Lemma 6.2 (a) (tex l.476-480): `m ≥ 4`, no loop, `f` without balanced pair, `Q` a cycle of small edges
through `v`: the two ends of `Q` at `v` (the end `d` through which `Q` leaves `v`, and the end through which the
dart `d'` of `Q` enters `v`) have the same outward value `a ∈ {1, -1}`. -/
theorem lem_6_2_a (m : ℕ) (hm : 4 ≤ m) (G : MGraph V E) (hG : G.Loopless) (f : E → ZMod m)
    (hf : G.IsNZFlow f) (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle)
    (hQ : ∀ d ∈ Q.darts, f d.1 = 1 ∨ f d.1 = -1) (v : V) (d d' : E × Bool) (hd : d ∈ Q.darts)
    (hd' : d' ∈ Q.darts) (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) :
    dirVal f d = dirVal f (d'.1, !d'.2) ∧ (dirVal f d = 1 ∨ dirVal f d = -1) :=
  MGraph.Sec6.lem_6_2_a_main m hm f hnb Q hQ v d d' hd hd' hdv hd'v

/-- SHORT v1.51: Lemma 6.2 (b), l.465-466.
Lemma 6.2 (b) (tex l.481-482): if another end `i` at `v` has an outward value `c ≠ -2a`, then `f` is
`T`-joined, by steps along `Q`, to a flow with a balanced pair at `v`. -/
theorem lem_6_2_b (m : ℕ) (hm : 4 ≤ m) (G : MGraph V E) (hG : G.Loopless) (f : E → ZMod m)
    (hf : G.IsNZFlow f) (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle)
    (hQ : ∀ d ∈ Q.darts, f d.1 = 1 ∨ f d.1 = -1) (v : V) (d d' : E × Bool) (hd : d ∈ Q.darts)
    (hd' : d' ∈ Q.darts) (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) (i : E × Bool)
    (hiv : G.endVertex i = v) (hid : i ≠ d) (hid' : i ≠ (d'.1, !d'.2))
    (hc : dirVal f i ≠ -(2 • dirVal f d)) :
    ∃ ts : List (ZMod m), G.StepsAlong {x | x ≠ 0} (Tcyc m) Q f ts ∧
      G.HasBalancedPairAt (f + fun e => Q.chi e • ts.sum) v :=
  MGraph.Sec6.lem_6_2_b_main m hm f hf hnb Q hQ v d d' hd hd' hdv hd'v i hiv hid hid' hc

/-- SHORT v1.51: Proposition 6.3, l.483.
Proposition 6.3 (tex l.497-500): `m ≥ 4`, `G` even with an edge, no loop, all degrees `0` or `≥ 4`: every
`ℤ_m`-flow is `T`-joined to a flow with a balanced pair. -/
theorem prop_6_3 (m : ℕ) (hm : 4 ≤ m) (G : MGraph V E) (hev : G.IsEven) (hE : Nonempty E)
    (hG : G.Loopless) (hdeg : ∀ v, G.degree v = 0 ∨ 4 ≤ G.degree v)
    (f : {f : E → ZMod m // G.IsNZFlow f}) :
    ∃ f' : {f : E → ZMod m // G.IsNZFlow f}, G.HasBalancedPair f'.1 ∧ (G.tStepGraph (Tcyc m)).Reachable f f' :=
  MGraph.Sec6.prop_6_3_main m hm G hE hG hdeg f

/-- SHORT v1.51: Theorem 2.4, l.194-195.
Theorem 2.4 (tex l.181-184): `m ≥ 4`; in every even graph any two nowhere-zero `ℤ_m`-flows are joined by a
chain of steps with values in `{1, -1, 2, -2}`. -/
theorem thm_2_4 (m : ℕ) (hm : 4 ≤ m) (G : MGraph V E) (hev : G.IsEven) :
    (G.tStepGraph (Tcyc m)).Preconnected :=
  prop_3_4 (Tcyc m) (sec3_T_cyc m (by omega)).2.2.1 (sec3_T_cyc m (by omega)).2.2.2
    (sec3_T_cyc m (by omega)).1 (sec3_T_cyc m (by omega)).2.1 (fun V E _ _ _ _ G => G.IsEven)
    (fun _ _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ _ _ h hl => isEven_deleteEdge hl h)
    (fun _ _ _ _ _ _ _ _ _ _ h hG hne he he' => isEven_splitOff (SplitData.of hG hne he he') h)
    (fun _ _ _ _ _ _ G hev hE hG hdeg f => prop_6_3 m hm G hev hE hG hdeg f) G hev

/-- SHORT v1.51: Remark 6.4, first sentence; also Section 1 (Outline: Theorem 2.4 also proves part (a) for cyclic groups), l.508 (also l.134).
Section 6 (tex l.522-523): Theorem 2.4 proves Theorem 2.3 for cyclic groups again, without Lemma 5.1:
every even graph is `ℤ_m`-flow-connected for `m ≥ 4`. (Route: from `thm_2_4`, checked by a dependency walk.) -/
theorem sec6_cyclic_flow_connected (m : ℕ) (hm : 4 ≤ m) (G : MGraph V E) (hev : G.IsEven) :
    G.FlowConnected (ZMod m) :=
  SimpleGraph.Preconnected.mono
    (stepGraph_mono {x | x ≠ 0} (fun t ht => fun h0 => (sec3_T_cyc m (by omega)).2.2.1 (h0 ▸ ht)))
    (thm_2_4 m hm G hev)

/-- SHORT v1.51: Section 6 (proof of Proposition 6.3); also Remark 6.4, l.492-493 (also l.510).
Section 6 (tex l.524-526): the value `-2a` of Lemma 6.2 (b) is not small in `ℤ_m`, `m ≥ 4`. -/
theorem sec6_neg_two_not_small (m : ℕ) (hm : 4 ≤ m) (a : ZMod m) (ha : a = 1 ∨ a = -1) :
    -(2 • a) ≠ 1 ∧ -(2 • a) ≠ -1 :=
  MGraph.Sec6.neg_two_not_small m hm a ha

/-- SHORT v1.51: Section 6 (text, opening paragraph), l.446-447.
Section 6 (SHORT paper v1.46 l.445-446): in `ℤ_m`, `m ≥ 4`, for a flow `f`, "the value of an edge that is not small
is, in each direction, the residue of an integer in `{2, …, m-2}`". -/
theorem sec6_not_small_range {m : ℕ} (hm : 4 ≤ m) (G : MGraph V E) (f : E → ZMod m) (hf : G.IsNZFlow f) (e : E)
    (hs : f e ≠ 1 ∧ f e ≠ -1) (b : Bool) :
    ∃ n : ℕ, 2 ≤ n ∧ n ≤ m - 2 ∧ (n : ZMod m) = dirVal f (e, b) :=
  not_small_range_dir hm f (e, b) (hf.2 e) hs.1 hs.2

/-- SHORT v1.51: Remark 6.4 (the Z_3 x Z_3 example), l.510-512.
Remark after Theorem 2.4 (tex l.525-527): in `ℤ_3 × ℤ_3`, with `S` of any cyclic decomposition, `-2a = a` for
a small `a`, and a vertex can have six ends with the same small outward value `a` (here: vertex `0` of the graph
with two vertices and six parallel edges; that flow has no balanced pair). -/
theorem sec6_remark_Z3Z3 (D : CyclicDecomp (ZMod 3 × ZMod 3)) (a : ZMod 3 × ZMod 3) (ha : a ∈ D.S) :
    -(2 • a) = a ∧ ∃ f : Fin 6 → ZMod 3 × ZMod 3, (dipole 6).IsNZFlow f ∧ ¬ (dipole 6).HasBalancedPair f ∧
      ∀ i : Fin 6 × Bool, (dipole 6).endVertex i = 0 → dirVal f i = a :=
  MGraph.Sec6.remark_Z3Z3 D a ha

/-! ## Section 7: the number of steps (tex l.530-557) -/

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Section 7 (tex l.534-543): `c(G) ≤ M(M+3)/2` — in an even graph with all degrees at most `4`, every flow is joined
to some flow `a 𝟙_D` by a chain of at most `M(M+3)/2` multi-steps (`a ≠ 0`). -/
theorem sec7_c_bound (A : Type) [AddCommGroup A] [Fintype A] (a : A) (ha : a ≠ 0) (G : MGraph V E)
    (hev : G.IsEven) (hdeg : ∀ v, G.degree v ≤ 4) (f : {f : E → A // G.IsNZFlow f}) :
    ∃ D : E → Bool, G.IsEulerOrient D ∧ ∃ hnz : G.IsNZFlow (constFlow a D),
      ∃ w : (G.multiStepGraph A).Walk f ⟨_, hnz⟩, 2 * w.length ≤ Fintype.card E * (Fintype.card E + 3) :=
  Count.sec7_c_bound_proved a ha G hev hdeg f

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Section 7 (tex l.545-546): in an even graph with `M` edges and all degrees at most `4`, any two flows are joined
by at most `M² + 3M + 1` multi-steps. -/
theorem sec7_multistep_bound (A : Type) [AddCommGroup A] [Fintype A] (G : MGraph V E) (hev : G.IsEven)
    (hdeg : ∀ v, G.degree v ≤ 4) (f f' : {f : E → A // G.IsNZFlow f}) :
    ∃ w : (G.multiStepGraph A).Walk f f',
      w.length ≤ Fintype.card E ^ 2 + 3 * Fintype.card E + 1 :=
  Count.sec7_multistep_bound_proved G hev hdeg f f'

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Section 7 (tex l.553-555): `|A| ≥ 4`; any two flows of an even graph `G₀` with no loop and `M` edges are joined by
at most `16M² + 12M + 1` multi-steps of `G₀`. -/
theorem sec7_multistep_bound_loopless (A : Type) [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A)
    (G : MGraph V E) (hev : G.IsEven) (hG : G.Loopless) (f f' : {f : E → A // G.IsNZFlow f}) :
    ∃ w : (G.multiStepGraph A).Walk f f',
      w.length ≤ 16 * Fintype.card E ^ 2 + 12 * Fintype.card E + 1 :=
  Count.sec7_multistep_bound_loopless_proved hA G hev hG f f'

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Theorem 2.5, first part (tex l.187-188): an even graph with `M` edges and all degrees at most `4`: any two
flows are joined by at most `M³ + 3M² + M` steps. -/
theorem thm_2_5_a (A : Type) [AddCommGroup A] [Fintype A] (G : MGraph V E) (hev : G.IsEven)
    (hdeg : ∀ v, G.degree v ≤ 4) (f f' : {f : E → A // G.IsNZFlow f}) :
    ∃ w : (G.flowGraph A).Walk f f',
      w.length ≤ Fintype.card E ^ 3 + 3 * Fintype.card E ^ 2 + Fintype.card E :=
  Count.thm_2_5_a_proved A G hev hdeg f f'

/-- SHORT v1.51: Section 1 (text, Further results; cited as [G, Theorem 2.5], not proved here), l.110-111.
Theorem 2.5, second part (tex l.188-189): `|A| ≥ 4`, an even graph with `M` edges: any two flows are joined
by at most `16M³ + 12M² + M` steps. -/
theorem thm_2_5_b (A : Type) [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A) (G : MGraph V E)
    (hev : G.IsEven) (f f' : {f : E → A // G.IsNZFlow f}) :
    ∃ w : (G.flowGraph A).Walk f f',
      w.length ≤ 16 * Fintype.card E ^ 3 + 12 * Fintype.card E ^ 2 + Fintype.card E :=
  Count.thm_2_5_b_proved A hA G hev f f'

/-! ## Section 8: integer flows (tex l.566-697) -/

/-- SHORT v1.51: Section 7 (text, Definitions), l.526-527.
Section 8 (tex l.579-580): the residues modulo `k` of a `k`-flow are a nowhere-zero `ℤ_k`-flow. -/
theorem sec8_residues (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (F : E → ℤ) (hF : G.IsIFlow (Ik k) F) :
    G.IsNZFlow (fun e => ((F e : ℤ) : ZMod k)) :=
  Sec8.sec8_residues_proved k hk G F hF

/-- SHORT v1.51: Section 7 (text, Definitions), l.520.
Section 8 (tex l.571): a map `x` is a flow if and only if `∂x = 0`. -/
theorem sec8_flow_iff_boundary {M : Type} [AddCommGroup M] (G : MGraph V E) (x : E → M) :
    G.IsFlow x ↔ G.boundary x = 0 :=
  Sec8.sec8_flow_iff_boundary_proved G x

/-- SHORT v1.51: Section 7 (text, Definitions), l.520.
Section 8 (tex l.572): `∂χ_Q = 0` for every directed cycle `Q`. -/
theorem sec8_chi_flow (G : MGraph V E) (Q : G.DirCycle) : G.IsFlow Q.chi :=
  Sec8.sec8_chi_flow_proved G Q

/-- SHORT v1.51: Lemma 7.2, l.539-541.
Lemma 8.2 (rounding, tex l.593-597). -/
theorem lem_8_2 (G : MGraph V E) (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1)
    (hint : ∀ v, ∃ n : ℤ, G.boundary x v = n) :
    ∃ z : E → ℤ, (∀ e, z e = 0 ∨ z e = 1) ∧ G.boundary (fun e => (z e : ℝ)) = G.boundary x ∧
      ∀ e, (x e = 0 → z e = 0) ∧ (x e = 1 → z e = 1) :=
  MGraph.lem_8_2_proved G x hx hint

/-- SHORT v1.51: Section 7 (text, before Lemma 7.3), l.554-556.
Section 8 (tex l.608-610): for a `ℤ_k`-flow `f`, with `r_f(e) ∈ {1, …, k-1}` the representative of `f(e)`:
`∂ r_f ≡ 0 (mod k)`, and an integer lift has on every edge the value `r_f(e)` or `r_f(e) - k`. -/
theorem sec8_rf (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (f : E → ZMod k) (hf : G.IsNZFlow f) :
    (∀ v, (k : ℤ) ∣ G.boundary (fun e => ((f e).val : ℤ)) v) ∧
    ∀ F, G.IsIntLift k f F → ∀ e, F e = (f e).val ∨ F e = (f e).val - k :=
  Sec8.sec8_rf_proved k hk G f hf

/-- SHORT v1.51: Lemma 7.3, l.559.
Lemma 8.3 (integer lifts, tex l.612-614): every `ℤ_k`-flow has an integer lift (`k ≥ 2`). -/
theorem lem_8_3 (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (f : E → ZMod k) (hf : G.IsNZFlow f) :
    ∃ F : E → ℤ, G.IsIntLift k f F :=
  Sec8.lem_8_3_proved k hk G f hf

/-- SHORT v1.51: Lemma 7.4, l.568-569.
Lemma 8.4 (the fibres are connected, tex l.621-624). -/
theorem lem_8_4 (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (f : E → ZMod k) (F F' : E → ℤ)
    (hF : G.IsIntLift k f F) (hF' : G.IsIntLift k f F') :
    (G.kFlowGraph k).Reachable ⟨F, hF.1⟩ ⟨F', hF'.1⟩ :=
  Sec8.lem_8_4_proved k hk G f F F' hF hF'

/-- SHORT v1.51: Lemma 7.5, l.582-583.
Lemma 8.5 (a step with the value `1`, tex l.635-638). -/
theorem lem_8_5 (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (Q : G.DirCycle) (f : E → ZMod k) (hf : G.IsNZFlow f)
    (hf1 : G.IsNZFlow (f + fun e => Q.chi e • (1 : ZMod k))) (F : E → ℤ) (hF : G.IsIntLift k f F) :
    G.IsIntLift k (f + fun e => Q.chi e • (1 : ZMod k)) (F + fun e => Q.chi e • (1 : ℤ)) :=
  Sec8.lem_8_5_proved k hk G Q f hf hf1 F hF

/-- SHORT v1.51: Lemma 7.6, l.594-595.
Lemma 8.6 (a step with the value `2`, tex l.648-651). -/
theorem lem_8_6 (k : ℕ) (hk : 3 ≤ k) (G : MGraph V E) (Q : G.DirCycle) (f : E → ZMod k) (hf : G.IsNZFlow f)
    (hf2 : G.IsNZFlow (f + fun e => Q.chi e • (2 : ZMod k))) :
    ∃ F : E → ℤ, G.IsIntLift k f F ∧
      G.IsIntLift k (f + fun e => Q.chi e • (2 : ZMod k)) (F + fun e => Q.chi e • (2 : ℤ)) :=
  Sec8.lem_8_6_proved k hk G Q f hf hf2

/-- SHORT v1.51: Section 7 (proof of Lemma 7.6, first sentence), l.598.
After Lemma 8.6 (tex l.652): `f + χ_Q` can have zeros, so Lemma 8.5 cannot be used twice. (An instance: the
one-loop graph, `k ≥ 3`, `f = -1`: `f` and `f + 2χ_Q` are flows, `f + χ_Q` has a zero.) -/
theorem rem_8_6_zeros (k : ℕ) (hk : 3 ≤ k) :
    ∃ (Q : (cycleGraph 1).DirCycle) (f : Fin 1 → ZMod k), (cycleGraph 1).IsNZFlow f ∧
      (cycleGraph 1).IsNZFlow (f + fun e => Q.chi e • (2 : ZMod k)) ∧
      ¬ (cycleGraph 1).IsNZFlow (f + fun e => Q.chi e • (1 : ZMod k)) := by
  apply rem_8_6_zeros_proved <;> assumption

/-- SHORT v1.51: Proposition 7.7, l.614-615.
Proposition 8.7 (the transfer, tex l.671-674): `k ≥ 3`; if any two `ℤ_k`-flows of `G` are joined by a chain of
steps with values in `{1, -1, 2, -2}`, then `G` is `k`-flow-connected. -/
theorem prop_8_7 (k : ℕ) (hk : 3 ≤ k) (G : MGraph V E) (h : (G.tStepGraph (Tcyc k)).Preconnected) :
    G.KFlowConnected k :=
  Sec8.prop_8_7_proved k hk G h

/-- SHORT v1.51: Theorem 7.1, l.530.
Theorem 8.1 (tex l.582-584): `k ≥ 4`; every even graph is `k`-flow-connected. -/
theorem thm_8_1 (k : ℕ) (hk : 4 ≤ k) (G : MGraph V E) (hev : G.IsEven) : G.KFlowConnected k :=
  Sec8.thm_8_1_proved k hk G hev (thm_2_4 k hk G hev)

/-- SHORT v1.51: Proposition 7.7 (case k = 3), implicit, l.614-615.
Remark 8.8, `k = 3` (tex l.693-694): for every graph, if `𝓕(G, ℤ_3)` is connected, so is `𝓕(G, 3)`. -/
theorem rem_8_8_k3 (G : MGraph V E) (h : G.FlowConnected (ZMod 3)) : G.KFlowConnected 3 :=
  Sec8.rem_8_8_k3_proved G h

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Remark 8.8, `k = 2` (tex l.694-695): a graph has at most one `ℤ_2`-flow, and every `2`-flow is an integer lift
of it. -/
theorem rem_8_8_Z2 (G : MGraph V E) :
    (∀ f f' : E → ZMod 2, G.IsNZFlow f → G.IsNZFlow f' → f = f') ∧
    ∀ f : E → ZMod 2, G.IsNZFlow f → ∀ F, G.IsIFlow (Ik 2) F → G.IsIntLift 2 f F :=
  Sec8.rem_8_8_Z2_proved G

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Remark 8.8, `k = 2` (tex l.694-696): `𝓕(G, 2)` is connected for every graph `G`. -/
theorem rem_8_8_k2 (G : MGraph V E) : G.KFlowConnected 2 :=
  Sec8.rem_8_8_k2_proved G

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Remark 8.8 (tex l.691-692) and the introduction (tex l.97-98): for even graphs and every `k ≥ 2`, if
`𝓕(G, ℤ_k)` is connected then `𝓕(G, k)` is connected. -/
theorem rem_8_8 (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (hev : G.IsEven) (h : G.FlowConnected (ZMod k)) :
    G.KFlowConnected k :=
  Sec8.rem_8_8_proved k hk G hev h (fun h4 => thm_2_4 k h4 G hev)

/-! ## Section 9: modular (p,q)-flows (tex l.699-862) -/

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Section 9 (tex l.702): `I = -I`, `0 ∉ I`, and `q ≠ -q` in `ℤ_p` (for `q ≥ 1`, `p > 2q`). -/
theorem sec9_I_props (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) :
    (∀ x ∈ Ipq p q, -x ∈ Ipq p q) ∧ (0 : ZMod p) ∉ Ipq p q ∧ (q : ZMod p) ≠ -(q : ZMod p) := by
  apply sec9_I_props_proved <;> assumption

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Section 9 (tex l.705-706, l.728-729): for `q = 1` the `(p,q)`-flows are the nowhere-zero `ℤ_p`-flows, and the
step values of Theorem 9.1 are those of Theorem 2.4 ("For q = 1, Theorem 9.1 is Theorem 2.4"). -/
theorem sec9_I_one (p : ℕ) (hp : 2 < p) : Ipq p 1 = {x | x ≠ 0} ∧ Tpq p 1 = Tcyc p := by
  apply sec9_I_one_proved <;> assumption

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Section 9 (tex l.705-706, l.95): for `q = 1`, `(p,q)`-flow-connected is `ℤ_p`-flow-connected. -/
theorem sec9_pq_one_iff (p : ℕ) (hp : 2 < p) (G : MGraph V E) :
    G.PQFlowConnected p 1 ↔ G.FlowConnected (ZMod p) :=
  pq_one_iff p hp G

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Section 9 (tex l.713-715): a multi-step between `(p,q)`-flows is a chain of steps with the same value: every
partial sum is a `(p,q)`-flow. -/
theorem sec9_multistep_chain (p q : ℕ) (G : MGraph V E) (t : ZMod p) (ht : t ≠ 0) (Qs : List G.DirCycle)
    (hdisj : Qs.Pairwise G.EdgeDisjoint) (f : E → ZMod p) (hf : G.IsIFlow (Ipq p q) f)
    (hf' : G.IsIFlow (Ipq p q) (f + fun e => (Qs.map fun Q => Q.chi e).sum • t)) :
    (∀ j ≤ Qs.length, G.IsIFlow (Ipq p q) (f + fun e => ((Qs.take j).map fun Q => Q.chi e).sum • t)) ∧
    ∃ w : (G.stepGraph (Ipq p q) {t}).Walk ⟨f, hf⟩ ⟨_, hf'⟩, w.length = Qs.length :=
  MGraph.sec9_multistep_chain_proved p q G t ht Qs hdisj f hf hf'

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Section 9 (tex l.745-747): `T` has no zero, `T = -T`, `q ∈ I`, and `2q ∈ T` (so (T2) holds with `a = q`). -/
theorem sec9_T_props (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) :
    (0 : ZMod p) ∉ Tpq p q ∧ (∀ t ∈ Tpq p q, -t ∈ Tpq p q) ∧ (q : ZMod p) ∈ Ipq p q ∧
      2 • (q : ZMod p) ∈ Tpq p q := by
  apply sec9_T_props_proved <;> assumption

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Lemma 9.3 (the reduction for (p,q)-flows, tex l.735-740). -/
theorem lem_9_3 (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p)
    (h_local : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      G.IsEven → Nonempty E → G.Loopless → (∀ v, G.degree v = 0 ∨ 4 ≤ G.degree v) →
      ∀ f : {f : E → ZMod p // G.IsIFlow (Ipq p q) f}, ∃ f' : {f : E → ZMod p // G.IsIFlow (Ipq p q) f},
        G.HasBalancedPair f'.1 ∧ (G.stepGraph (Ipq p q) (Tpq p q)).Reachable f f')
    (G : MGraph V E) (hev : G.IsEven) : (G.stepGraph (Ipq p q) (Tpq p q)).Preconnected :=
  lem_9_3_of p q (sec9_I_props p q hq hpq).1 (sec9_T_props p q hq hpq).1
    (sec9_T_props p q hq hpq).2.1 (sec9_T_props p q hq hpq).2.2.1 (sec9_T_props p q hq hpq).2.2.2
    h_local G hev

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Lemma 9.3, proof (tex l.752-753): the chain `q, q+1, …, p-q` joins any two elements of `I` inside `I`, with
differences `1` or `-1` of neighbours (this takes the place of (T1)). -/
theorem lem_9_3_chain (p q : ℕ) (a b : ZMod p) (ha : a ∈ Ipq p q) (hb : b ∈ Ipq p q) :
    Relation.ReflTransGen (fun x y : ZMod p => y ∈ Ipq p q ∧ (y - x = 1 ∨ y - x = -1)) a b :=
  MGraph.Sec9R.chain p q a b ha hb

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Lemma 9.3, proof (tex l.751-753): Lemma 3.1 for `(p,q)`-flows. -/
theorem lem_9_3_loop (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) (G : MGraph V E) (l : E) (hl : G.IsLoop l)
    (h : ((G.deleteEdge l).stepGraph (Ipq p q) (Tpq p q)).Preconnected) :
    (G.stepGraph (Ipq p q) (Tpq p q)).Preconnected :=
  MGraph.Sec9R.loop p q hq hpq G l hl h

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Lemma 9.3, proof (tex l.755-758): Lemma 3.2 for `(p,q)`-flows: `L` is a bijection from the `(p,q)`-flows of
`G'` onto the `(p,q)`-flows of `G` in which the ends of `e` and `e'` at `v` are a balanced pair, and it sends a
multi-step to a multi-step with the same value. -/
theorem lem_9_3_split (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) (G : MGraph V E) (hG : G.Loopless) (v : V)
    (e e' : E) (hne : e ≠ e') (he : G.IsAt e v) (he' : G.IsAt e' v) :
    Set.BijOn (G.splitLift v e e') {f' | (G.splitOff v e e').IsIFlow (Ipq p q) f'}
      {f | G.IsIFlow (Ipq p q) f ∧ dirVal f (G.endAt e v) + dirVal f (G.endAt e' v) = 0} ∧
    ∀ (t : ZMod p) (f₁ f₂ : Option {x : E // x ≠ e ∧ x ≠ e'} → ZMod p),
      (G.splitOff v e e').IsMultiStep t f₁ f₂ → G.IsMultiStep t (G.splitLift v e e' f₁) (G.splitLift v e e' f₂) :=
  MGraph.Sec9R.split p q hq hpq G hG v e e' hne he he'

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Lemma 9.3, proof (tex l.760-763): Lemma 3.3 with `a = q`: `q 𝟙_D` is a `(p,q)`-flow, `-2q ∈ T`, and in the
situation of Lemma 3.2 (`G` even) `B(v; e, e')` contains a flow `q 𝟙_D`. -/
theorem lem_9_3_const (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) (G : MGraph V E) :
    (∀ D : E → Bool, G.IsEulerOrient D → G.IsIFlow (Ipq p q) (constFlow (q : ZMod p) D)) ∧
    -(2 • (q : ZMod p)) ∈ Tpq p q ∧
    (G.IsEven → G.Loopless → ∀ (v : V) (e e' : E), e ≠ e' → G.IsAt e v → G.IsAt e' v →
      ∃ D : E → Bool, G.IsEulerOrient D ∧
        dirVal (constFlow (q : ZMod p) D) (G.endAt e v) + dirVal (constFlow (q : ZMod p) D) (G.endAt e' v) = 0) :=
  MGraph.Sec9R.const p q hq hpq G

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Lemma 9.4 (tex l.776-779): `p > 2q`; if no edge of the cycle `Q` is small (value `±q`), then `f` is joined, by
steps along `Q` with the value `-1`, to a `(p,q)`-flow `f'` with `ρ(f') ≤ ρ(f) - 1`. -/
theorem lem_9_4 (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) (G : MGraph V E) (f : E → ZMod p)
    (hf : G.IsIFlow (Ipq p q) f) (Q : G.DirCycle) (hQ : ∀ d ∈ Q.darts, f d.1 ≠ q ∧ f d.1 ≠ -(q : ZMod p)) :
    ∃ ts : List (ZMod p), (∀ t ∈ ts, t = -1) ∧ G.StepsAlong (Ipq p q) (Tpq p q) Q f ts ∧
      rhoPQ q (f + fun e => Q.chi e • ts.sum) + 1 ≤ rhoPQ q f := by
  apply lem_9_4_proved <;> assumption

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Lemma 9.5 (a) (tex l.788-793). -/
theorem lem_9_5_a (p q : ℕ) (hq : 1 ≤ q) (hpq : 4 * q ≤ p) (G : MGraph V E) (hG : G.Loopless)
    (f : E → ZMod p) (hf : G.IsIFlow (Ipq p q) f) (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle)
    (hQ : ∀ d ∈ Q.darts, f d.1 = q ∨ f d.1 = -(q : ZMod p)) (v : V) (d d' : E × Bool) (hd : d ∈ Q.darts)
    (hd' : d' ∈ Q.darts) (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) :
    dirVal f d = dirVal f (d'.1, !d'.2) ∧ (dirVal f d = q ∨ dirVal f d = -(q : ZMod p)) :=
  MGraph.Sec9.lem_9_5_a_main p q hq hpq f hnb Q hQ v d d' hd hd' hdv hd'v

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Lemma 9.5 (b) (tex l.794-795): if another end at `v` has an outward value `c` with `a + c ∈ J`, then `f` is
`T`-joined, by steps along `Q`, to a `(p,q)`-flow with a balanced pair at `v`. -/
theorem lem_9_5_b (p q : ℕ) (hq : 1 ≤ q) (hpq : 4 * q ≤ p) (G : MGraph V E) (hG : G.Loopless)
    (f : E → ZMod p) (hf : G.IsIFlow (Ipq p q) f) (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle)
    (hQ : ∀ d ∈ Q.darts, f d.1 = q ∨ f d.1 = -(q : ZMod p)) (v : V) (d d' : E × Bool) (hd : d ∈ Q.darts)
    (hd' : d' ∈ Q.darts) (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) (i : E × Bool)
    (hiv : G.endVertex i = v) (hid : i ≠ d) (hid' : i ≠ (d'.1, !d'.2))
    (hJ : dirVal f d + dirVal f i ∈ Jpq p q) :
    ∃ ts : List (ZMod p), G.StepsAlong (Ipq p q) (Tpq p q) Q f ts ∧
      G.HasBalancedPairAt (f + fun e => Q.chi e • ts.sum) v :=
  MGraph.Sec9.lem_9_5_b_main p q hq hpq f hf hnb Q hQ v d d' hd hd' hdv hd'v i hiv hid hid' hJ

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Lemma 9.5 (c) (tex l.796-797): if another end at `v` has an outward value `c` with `a + c ∉ J`, this end is
not small. -/
theorem lem_9_5_c (p q : ℕ) (hq : 1 ≤ q) (hpq : 4 * q ≤ p) (G : MGraph V E) (hG : G.Loopless)
    (f : E → ZMod p) (hf : G.IsIFlow (Ipq p q) f) (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle)
    (hQ : ∀ d ∈ Q.darts, f d.1 = q ∨ f d.1 = -(q : ZMod p)) (v : V) (d d' : E × Bool) (hd : d ∈ Q.darts)
    (hd' : d' ∈ Q.darts) (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) (i : E × Bool)
    (hiv : G.endVertex i = v) (hid : i ≠ d) (hid' : i ≠ (d'.1, !d'.2))
    (hJ : dirVal f d + dirVal f i ∉ Jpq p q) :
    dirVal f i ≠ q ∧ dirVal f i ≠ -(q : ZMod p) :=
  MGraph.Sec9.lem_9_5_c_main p q hq hpq f hnb Q hQ v d hd hdv i hiv hid hJ

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Proposition 9.6 (tex l.822-825). -/
theorem prop_9_6 (p q : ℕ) (hq : 1 ≤ q) (hpq : 4 * q ≤ p) (G : MGraph V E) (hev : G.IsEven)
    (hE : Nonempty E) (hG : G.Loopless) (hdeg : ∀ v, G.degree v = 0 ∨ 4 ≤ G.degree v)
    (f : {f : E → ZMod p // G.IsIFlow (Ipq p q) f}) :
    ∃ f' : {f : E → ZMod p // G.IsIFlow (Ipq p q) f}, G.HasBalancedPair f'.1 ∧
      (G.stepGraph (Ipq p q) (Tpq p q)).Reachable f f' :=
  MGraph.Sec9.prop_9_6_main p q hq hpq G hE hG hdeg f

/-- SHORT v1.51: Section 1 (text, Further results; cited as [G, Theorems 9.1 and 9.2]) [PARTIAL: only 'p>=4q => every even graph is (p,q)-flow-connected'; the step values {1,-1,2q,-2q} are not in the short paper], l.111-112.
Theorem 9.1 (tex l.718-721): `p ≥ 4q ≥ 4`; in every even graph any two `(p,q)`-flows are joined by a chain of
steps with values in `{1, -1, 2q, -2q}`; in particular every even graph is `(p,q)`-flow-connected. -/
theorem thm_9_1 (p q : ℕ) (hq : 1 ≤ q) (hpq : 4 * q ≤ p) (G : MGraph V E) (hev : G.IsEven) :
    (G.stepGraph (Ipq p q) (Tpq p q)).Preconnected ∧ G.PQFlowConnected p q :=
  thm_9_1_of p q (sec9_I_props p q hq (by omega)).1 (sec9_T_props p q hq (by omega)).1
    (sec9_T_props p q hq (by omega)).2.1 (sec9_T_props p q hq (by omega)).2.2.1
    (sec9_T_props p q hq (by omega)).2.2.2
    (fun V E _ _ _ _ G hev hE hG hdeg f => prop_9_6 p q hq hpq G hev hE hG hdeg f) G hev

/-- SHORT v1.51: Section 1 (text, Further results; cited as [G, Theorems 9.1 and 9.2]) [PARTIAL: only 'for 2q<p<4q not every even graph is (p,q)-flow-connected'; the witness (two vertices, 2p parallel edges) is not in the short paper], l.111-112.
Theorem 9.2 (tex l.723-726): `2q < p < 4q`; the graph with two vertices and `2p` parallel edges is even and is
not `(p,q)`-flow-connected. -/
theorem thm_9_2 (p q : ℕ) (hpq : 2 * q < p) (hp : p < 4 * q) :
    (dipole (2 * p)).IsEven ∧ ¬ (dipole (2 * p)).PQFlowConnected p q := by
  apply thm_9_2_proved <;> assumption

/-- SHORT v1.51: Section 1 (text, Further results; cited as [G, Theorems 9.1 and 9.2]), l.111-112.
Section 9 (tex l.728) and the abstract (tex l.42-43): for `p > 2q`, every even graph is
`(p,q)`-flow-connected if and only if `p ≥ 4q`. -/
theorem sec9_iff (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) :
    (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      G.IsEven → G.PQFlowConnected p q) ↔ 4 * q ≤ p :=
  sec9_iff_of p q (fun h4 V E _ _ _ _ G hev => (thm_9_1 p q hq h4 G hev).2) (fun hlt => thm_9_2 p q hpq hlt)

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Section 9 (tex l.731-732): every even graph admits a circular `(2k+1, k)`-flow: the value `k` on every arc of
an Eulerian orientation (an integer flow with `k ≤ |F(e)| ≤ (2k+1) - k`). -/
theorem sec9_circular (k : ℕ) (hk : 1 ≤ k) (G : MGraph V E) (hev : G.IsEven) :
    ∃ F : E → ℤ, G.IsFlow F ∧ ∀ e, (k : ℤ) ≤ |F e| ∧ |F e| ≤ (2 * k + 1 : ℤ) - k :=
  sec9_circular_proved k hk G hev

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Remark 9.7 (tex l.857-861): a graph that is one cycle is `(p,q)`-flow-connected (for `p > 2q`). -/
theorem rem_9_7 (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) (n : ℕ) (hn : 1 ≤ n) :
    (cycleGraph n).IsEven ∧ (cycleGraph n).PQFlowConnected p q :=
  ⟨cycleGraph_isEven n, rem_9_7_proved p q hq hpq n hn⟩

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Remark 9.7 (tex l.859-861), for every graph that is one cycle: if all edges and all vertices of `G` lie on one
directed cycle `Q`, then `G` is even and `(p,q)`-flow-connected (any two different `(p,q)`-flows differ by a non-zero
constant along the cycle, which is one step). -/
theorem rem_9_7_one_cycle (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) (G : MGraph V E) (Q : G.DirCycle)
    (hE : ∀ e, ∃ d ∈ Q.darts, d.1 = e) (hV : ∀ v, ∃ d ∈ Q.darts, G.dartTail d = v) :
    G.IsEven ∧ G.PQFlowConnected p q :=
  rem_9_7_one_cycle_proved p q hq hpq G Q hE hV

/-! ## Section 1 and Remark 2.6 -/

/-- SHORT v1.51: Theorem 1.1 (a), l.71-73.
Theorem 1.1 (a) (tex l.68-71): an even graph is `A`-flow-connected for every finite abelian `A`, `|A| ≥ 4`. -/
theorem thm_1_1_a (G : MGraph V E) (hev : G.IsEven) (A : Type) [AddCommGroup A] [Fintype A]
    (hA : 4 ≤ Fintype.card A) : G.FlowConnected A :=
  thm_2_3 A hA G hev

/-- SHORT v1.51: Theorem 1.1 (b), l.71, l.74.
Theorem 1.1 (b) (tex l.72): an even graph is `k`-flow-connected for every integer `k ≥ 4`. -/
theorem thm_1_1_b (G : MGraph V E) (hev : G.IsEven) (k : ℕ) (hk : 4 ≤ k) : G.KFlowConnected k :=
  Sec8.thm_1_1_b_proved G hev k hk (thm_2_4 k hk G hev)

/-- SHORT v1.51: Section 1 (text, after the table), l.99-101.
Introduction (tex l.77-80): the number `4` cannot be replaced by `3`. The graph with two vertices and six
parallel edges is even and is neither `ℤ_3`-flow-connected nor `3`-flow-connected. -/
theorem intro_example :
    (dipole 6).IsEven ∧ ¬ (dipole 6).FlowConnected (ZMod 3) ∧ ¬ (dipole 6).KFlowConnected 3 := by
  apply intro_example_proved <;> assumption

/-- SHORT v1.51: Section 1 (text, Outline of the proof); also the proof of Proposition 3.4, l.121 (also l.305-306).
Proof of Proposition 3.4 (tex l.312-318) and the Outline of the short paper: "So all flows with a balanced pair
are joined to each other". In an even graph with no loop, with `T` as in Proposition 3.4 (`0 ∉ T`, `T = -T`, (T2)) and
the induction hypothesis of its proof (for every vertex `v` and two different edges `e, e'` at `v`, any two flows of
the splitting off `G'` are `T`-joined), any two flows with a balanced pair are `T`-joined. -/
theorem intro_balanced_joined {A : Type} [AddCommGroup A] (T : Set A) (hT0 : (0 : A) ∉ T)
    (hTneg : ∀ t ∈ T, -t ∈ T) (hT2 : CondT2 T) (G : MGraph V E) (hev : G.IsEven) (hG : G.Loopless)
    (hind : ∀ (v : V) (e e' : E), e ≠ e' → G.IsAt e v → G.IsAt e' v →
      ((G.splitOff v e e').tStepGraph T).Preconnected)
    (f₁ f₂ : {f : E → A // G.IsNZFlow f}) (h₁ : G.HasBalancedPair f₁.1) (h₂ : G.HasBalancedPair f₂.1) :
    (G.tStepGraph T).Reachable f₁ f₂ :=
  intro_balanced_joined_proved T hT0 hTneg hT2 G hev hG hind f₁ f₂ h₁ h₂

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Remark after Theorem 2.5 (tex l.195-196): an even graph with all degrees at most `4` has no two vertices
joined by more than four edge-disjoint paths. -/
theorem sec2_paths_le_four (G : MGraph V E) (hev : G.IsEven) (hdeg : ∀ v, G.degree v ≤ 4) (u w : V)
    (huw : u ≠ w) (Ps : List (G.Path u w)) (hdisj : Ps.Pairwise Path.EdgeDisjoint) : Ps.length ≤ 4 := by
  apply sec2_paths_le_four_proved <;> assumption

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Remark 2.6 (tex l.200-207): `K₅` is even, contains a triangle, and is `ℤ_4`-flow-connected (Theorem 2.3). -/
theorem rem_2_6 : K5.IsEven ∧ (∃ Q : K5.DirCycle, Q.darts.length = 3) ∧ K5.FlowConnected (ZMod 4) :=
  ⟨rem_2_6_proved.1, rem_2_6_proved.2.1, thm_2_3 (ZMod 4) (by simp) K5 rem_2_6_proved.1⟩

/-- SHORT v1.51: not in the short paper (long paper v0.30 only).
Remark 2.6 (tex l.205-207): `K₅` is triangularly connected in the sense of [CLSWX] (so it is a spanning
triangularly connected subgraph of itself), is even, and is `ℤ_4`-flow-connected (`|A| = 4`, `A ≠ ℤ_2 × ℤ_2`): the
"only if" half of [CLSWX, Corollary 5.15 (iii)] fails for `K₅`. -/
theorem rem_2_6_triangular : K5.IsTriConnectedOn Set.univ ∧ K5.IsEven ∧ K5.FlowConnected (ZMod 4) :=
  ⟨K5Tri.triConnected, rem_2_6_proved.1, thm_2_3 (ZMod 4) (by simp) K5 rem_2_6_proved.1⟩

end EulerFlow
