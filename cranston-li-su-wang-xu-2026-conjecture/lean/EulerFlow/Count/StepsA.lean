/-
EulerFlow/Count/StepsA.lean — paper 002, Theorem 2.5, first part (tex l.532-547): for an even graph with `M` edges
and all degrees at most 4, any two flows are joined by at most `M³ + 3M² + M` steps.
Route = the paper's: `c(G)` multi-steps to some `a 𝟙_D`, counted along the induction of Proposition 3.4
(loop: `+1`; vertex of degree 2: splitting off maps multi-steps to multi-steps; otherwise Proposition 4.4, at most
`ρ(f) + 1 ≤ M + 1` steps to a balanced pair, then splitting off), so `2c(G) ≤ M(M+3)`; two flows `a 𝟙_D` are at
most one multi-step apart; a multi-step is at most `M` steps.
A multi-step is used in its `h`-form (`CircStep`): `f' = f + h•t`, `h` a nonzero `{-1,0,1}` integer circulation
(equivalent to the paper's definition by `circ_decomp`).
-/
import EulerFlow.Reduction.Reduce
import EulerFlow.Sec4.Prop44
import EulerFlow.Sec4.Decomp

namespace EulerFlow

namespace Count

open Finset MGraph

section Machinery

variable {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E] {A : Type} [AddCommGroup A]

/-- A multi-step in `h`-form: `f' = f + h•t` with `t ≠ 0` and `h` a nonzero `{-1,0,1}`-valued integer flow. -/
def CircStep (G : MGraph V E) (f f' : E → A) : Prop :=
  ∃ t : A, t ≠ 0 ∧ ∃ h : E → ℤ, (∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1) ∧ G.IsFlow h ∧ (∃ e, h e ≠ 0) ∧
    f' = f + fun e => h e • t

/-- The graph of nowhere-zero flows joined by multi-steps. -/
def msGraph (G : MGraph V E) (A : Type) [AddCommGroup A] : SimpleGraph {f : E → A // G.IsNZFlow f} :=
  SimpleGraph.fromRel fun f f' => CircStep G f.1 f'.1

/-- A step is a multi-step. -/
lemma flowGraph_le_msGraph (G : MGraph V E) : G.flowGraph A ≤ msGraph G A := by
  intro f f' hadj
  have hadj' : f ≠ f' ∧ ((∃ Q : G.DirCycle, ∃ t ∈ ({x | x ≠ 0} : Set A), t ≠ 0 ∧
      f'.1 = f.1 + fun e => Q.chi e • t) ∨ (∃ Q : G.DirCycle, ∃ t ∈ ({x | x ≠ 0} : Set A), t ≠ 0 ∧
      f.1 = f'.1 + fun e => Q.chi e • t)) := hadj
  have hcs : ∀ g g' : {f : E → A // G.IsNZFlow f}, (∃ Q : G.DirCycle, ∃ t ∈ ({x | x ≠ 0} : Set A), t ≠ 0 ∧
      g'.1 = g.1 + fun e => Q.chi e • t) → CircStep G g.1 g'.1 := by
    rintro g g' ⟨Q, t, _, ht, h⟩
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ Q.ne_nil
    refine ⟨t, ht, Q.chi, Q.chi_mem, Q.isFlow_chi, ⟨d.1, ?_⟩, h⟩
    rw [Q.chi_of_mem hd]; exact dartSign_ne_zero _
  rw [msGraph, SimpleGraph.fromRel_adj]
  rcases hadj'.2 with h | h
  · exact ⟨hadj'.1, Or.inl (hcs f f' h)⟩
  · exact ⟨hadj'.1, Or.inr (hcs f' f h)⟩

/-- A multi-step is at most `M` steps. -/
lemma flowWalk_of_circStep (G : MGraph V E) {f f' : {f : E → A // G.IsNZFlow f}} (h : CircStep G f.1 f'.1) :
    ∃ w : (G.flowGraph A).Walk f f', w.length ≤ Fintype.card E := by
  obtain ⟨t, ht, h, hval, hfl, _, heq⟩ := h
  obtain ⟨w, hw⟩ := walk_of_circ (I := {x : A | x ≠ 0}) f f' h hval hfl t ht heq
  have hle := stepGraph_mono (G := G) {x : A | x ≠ 0}
    (Set.singleton_subset_iff.2 (show t ∈ ({x : A | x ≠ 0} : Set A) from ht))
  have hl := SimpleGraph.Walk.length_mapLe hle w
  exact ⟨w.mapLe hle, hl.trans_le (hw.trans ((Finset.card_filter_le _ _).trans (by rw [Finset.card_univ])))⟩

/-- A walk of `L` multi-steps gives a walk of at most `M·L` steps. -/
lemma flowWalk_of_msWalk (G : MGraph V E) {f f' : {f : E → A // G.IsNZFlow f}} (w : (msGraph G A).Walk f f') :
    ∃ w' : (G.flowGraph A).Walk f f', w'.length ≤ Fintype.card E * w.length := by
  induction w with
  | nil => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | cons hadj w ih =>
    obtain ⟨w', hw'⟩ := ih
    rw [msGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨w1, hw1⟩ : ∃ w1 : (G.flowGraph A).Walk _ _, w1.length ≤ Fintype.card E := by
      rcases hadj.2 with h | h
      · exact flowWalk_of_circStep G h
      · obtain ⟨w1, hw1⟩ := flowWalk_of_circStep G h
        exact ⟨w1.reverse, by rw [SimpleGraph.Walk.length_reverse]; exact hw1⟩
    refine ⟨w1.append w', ?_⟩
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
    calc w1.length + w'.length ≤ Fintype.card E + Fintype.card E * w.length := add_le_add hw1 hw'
      _ = Fintype.card E * (w.length + 1) := by ring

/-- A paper multi-step is a `CircStep`. -/
lemma circStep_of_multiStep (G : MGraph V E) {t : A} {f f' : E → A} (h : G.IsMultiStep t f f') :
    CircStep G f f' := by
  obtain ⟨ht, Qs, hne, hdisj, heq⟩ := h
  refine ⟨t, ht, fun e => (Qs.map fun Q => Q.chi e).sum, sum_chi_mem Qs hdisj, isFlow_sum_chi Qs, ?_, heq⟩
  by_contra h0
  simp only [ne_eq, not_exists, not_not] at h0
  exact sum_chi_ne_zero Qs hdisj hne (funext h0)

omit [DecidableEq E] in
/-- Two equal-or-`CircStep` flows are joined by at most one multi-step. -/
lemma msWalk_le_one (G : MGraph V E) (f f' : {f : E → A // G.IsNZFlow f}) (h : f'.1 = f.1 ∨ CircStep G f.1 f'.1) :
    ∃ w : (msGraph G A).Walk f f', w.length ≤ 1 := by
  rcases h with h | h
  · have : f = f' := Subtype.ext h.symm
    subst this
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · by_cases hff : f = f'
    · subst hff; exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · have hadj : (msGraph G A).Adj f f' := by
        rw [msGraph, SimpleGraph.fromRel_adj]; exact ⟨hff, Or.inl h⟩
      exact ⟨hadj.toWalk, by simp⟩

omit [DecidableEq E] in
/-- A `±1`-valued integer flow is the sign map of an Eulerian orientation, and `σ • a` is `a 𝟙_D`. -/
lemma constFlow_of_sign [Fintype V] (G : MGraph V E) (σ : E → ℤ) (hσ : ∀ e, σ e = 1 ∨ σ e = -1)
    (hfl : G.IsFlow σ) (a : A) :
    ∃ D : E → Bool, G.IsEulerOrient D ∧ constFlow a D = fun e => σ e • a := by
  have hσD : (fun e => if decide (σ e = -1) then (-1 : ℤ) else 1) = σ := by
    funext e; rcases hσ e with h | h <;> simp [h]
  refine ⟨fun e => decide (σ e = -1), (isEulerOrient_iff _).2 (by rw [hσD]; exact hfl), ?_⟩
  funext e
  rcases hσ e with h | h <;> simp [constFlow, h]

end Machinery

section Transport

variable {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E] {A : Type} [AddCommGroup A]

/-- Splitting off maps the multi-step graph of `G'` into that of `G` (Lemma 3.2 (b)). -/
def splitHom {G : MGraph V E} {v : V} {e e' : E} (hd : SplitData G v e e') :
    msGraph (G.splitOff v e e') A →g msGraph G A where
  toFun g := ⟨G.splitLift v e e' g.1, (isIFlow_splitLift_iff nonzero_neg hd _).2 g.2⟩
  map_rel' := by
    intro g₁ g₂ hadj
    rw [msGraph, SimpleGraph.fromRel_adj] at hadj ⊢
    have hinj := splitLift_injective (M := A) (e' := e') hd.at₁ hd.nl₁
    have hinjZ := splitLift_injective (M := ℤ) (e' := e') hd.at₁ hd.nl₁
    have key : ∀ x y : {f : Option {x : E // x ≠ e ∧ x ≠ e'} → A // (G.splitOff v e e').IsNZFlow f}, CircStep (G.splitOff v e e') x.1 y.1 →
        CircStep G (G.splitLift v e e' x.1) (G.splitLift v e e' y.1) := by
      rintro x y ⟨t, ht, h, hval, hfl, ⟨o, ho⟩, heq⟩
      refine ⟨t, ht, G.splitLift v e e' h, fun z => ?_, (isFlow_splitLift_iff hd h).2 hfl, ?_, ?_⟩
      · have := splitLift_mem (G := G) (v := v) (e := e) (e' := e') (I := unitVals) unitVals_neg h hval z
        exact this
      · by_contra h0
        simp only [ne_eq, not_exists, not_not] at h0
        have : G.splitLift v e e' h = G.splitLift v e e' 0 := by rw [splitLift_zero]; exact funext h0
        exact ho (congr_fun (hinjZ this) o)
      · rw [heq, splitLift_add, splitLift_zsmul]
    refine ⟨fun h => hadj.1 (Subtype.ext (hinj (congr_arg Subtype.val h))), ?_⟩
    rcases hadj.2 with h | h
    · exact Or.inl (key g₁ g₂ h)
    · exact Or.inr (key g₂ g₁ h)

/-- Deleting a loop: a flow of `G - l` with the value `x` on `l` is a flow of `G`, and multi-steps of `G - l` are
multi-steps of `G` (Lemma 3.1). -/
def loopHom {G : MGraph V E} {l : E} (hl : G.IsLoop l) (x : A) (hx : x ≠ 0) :
    msGraph (G.deleteEdge l) A →g msGraph G A where
  toFun g := ⟨extLoop l g.1 x, (isIFlow_extLoop_iff hl g.1 (I := {y : A | y ≠ 0}) hx).2 g.2⟩
  map_rel' := by
    intro g₁ g₂ hadj
    rw [msGraph, SimpleGraph.fromRel_adj] at hadj ⊢
    have key : ∀ p q : {f : {x : E // x ≠ l} → A // (G.deleteEdge l).IsNZFlow f}, CircStep (G.deleteEdge l) p.1 q.1 →
        CircStep G (extLoop l p.1 x) (extLoop l q.1 x) := by
      rintro p q ⟨t, ht, h, hval, hfl, ⟨o, ho⟩, heq⟩
      refine ⟨t, ht, extLoop l h 0, extLoop_mem_int hval (Or.inr (Or.inl rfl)),
        (isFlow_extLoop_iff hl h 0).2 hfl, ⟨o.1, ?_⟩, ?_⟩
      · simpa [extLoop, o.2] using ho
      · rw [heq, extLoop_add_smul]
    refine ⟨fun h => hadj.1 ?_, ?_⟩
    · apply Subtype.ext; funext y
      have := congr_fun (congr_arg Subtype.val h) y.1
      simpa [extLoop, y.2] using this
    · rcases hadj.2 with h | h
      · exact Or.inl (key g₁ g₂ h)
      · exact Or.inr (key g₂ g₁ h)

end Transport

section Induction

variable {A : Type} [AddCommGroup A]

/-- `c(G) ≤ M(M+3)/2`: every flow is joined to some `a 𝟙_D` by at most `M(M+3)/2` multi-steps. -/
def CountBound (a : A) (ha : a ≠ 0) {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MGraph V E) : Prop :=
  ∀ f : {f : E → A // G.IsNZFlow f}, ∃ D : E → Bool, ∃ hD : G.IsEulerOrient D,
    ∃ w : (msGraph G A).Walk f ⟨constFlow a D, isIFlow_constFlow nonzero_neg hD (show a ∈ {x : A | x ≠ 0} from ha)⟩,
      2 * w.length ≤ Fintype.card E * (Fintype.card E + 3)

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- A flow in `B(v; e, e')` is joined to a constant flow with the count of the split graph (Lemma 3.2 (b) and the
proof of Lemma 3.3 (b): `L(a 𝟙_{D'})` is a flow `a 𝟙_D`). -/
lemma count_balanced {G : MGraph V E} (a : A) (ha : a ≠ 0) {v : V} {e e' : E} (hd : SplitData G v e e')
    (hIH : CountBound a ha (G.splitOff v e e')) (f : {f : E → A // G.IsNZFlow f})
    (hf : dirVal f.1 (G.endAt e v) + dirVal f.1 (G.endAt e' v) = 0) :
    ∃ D : E → Bool, ∃ hD : G.IsEulerOrient D,
      ∃ w : (msGraph G A).Walk f ⟨constFlow a D, isIFlow_constFlow nonzero_neg hD (show a ∈ {x : A | x ≠ 0} from ha)⟩,
        2 * w.length ≤ Fintype.card (Option {x : E // x ≠ e ∧ x ≠ e'}) *
          (Fintype.card (Option {x : E // x ≠ e ∧ x ≠ e'}) + 3) := by
  have hg : (G.splitOff v e e').IsNZFlow (G.splitRes v e e' f.1) :=
    (isIFlow_splitLift_iff nonzero_neg hd (G.splitRes v e e' f.1)).1
      (by rw [splitLift_splitRes hd f.1 hf]; exact f.2)
  obtain ⟨D', hD', w', hw'⟩ := hIH ⟨_, hg⟩
  have hσ'f : (G.splitOff v e e').IsFlow (orientSign D') := (isEulerOrient_iff D').1 hD'
  have hσ : ∀ x, G.splitLift v e e' (orientSign D') x = 1 ∨ G.splitLift v e e' (orientSign D') x = -1 := by
    intro x
    exact splitLift_mem (I := {y : ℤ | y = 1 ∨ y = -1}) (by rintro y (rfl | rfl) <;> simp)
      (orientSign D') (fun o => by unfold orientSign; split_ifs <;> simp) x
  obtain ⟨D, hD, hDc⟩ := constFlow_of_sign G _ hσ ((isFlow_splitLift_iff hd _).2 hσ'f) a
  have hL : G.splitLift v e e' (constFlow a D') = constFlow a D := by
    rw [constFlow_eq_smul, splitLift_zsmul, hDc]
  refine ⟨D, hD, (w'.map (splitHom hd)).copy (Subtype.ext ?_) (Subtype.ext ?_), ?_⟩
  · exact splitLift_splitRes hd f.1 hf
  · exact hL
  · rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]; exact hw'

omit [Fintype V] in
/-- The loop step: changing the value on a loop is one multi-step. -/
lemma loop_circStep {G : MGraph V E} {l : E} (hl : G.IsLoop l) (f : E → A) (x : A) (hx : x ≠ f l) :
    CircStep G f (f + fun y => (if y = l then 1 else 0 : ℤ) • (x - f l)) := by
  refine ⟨x - f l, sub_ne_zero.2 hx, fun y => if y = l then 1 else 0, fun y => by dsimp only; split_ifs <;> simp, ?_,
    ⟨l, by simp⟩, rfl⟩
  intro z
  simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show G.src l = G.tgt l from hl]

/-- **The count along Proposition 3.4** (tex l.536-543): `2 c(G) ≤ M(M+3)` for even graphs with all degrees at
most 4. -/
theorem count_bound [Fintype A] (a : A) (ha : a ≠ 0) :
    ∀ n, ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      Fintype.card E = n → G.IsEven → (∀ v, G.degree v ≤ 4) → CountBound a ha G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V E _ _ _ _ G hn hev hdeg4
  subst hn
  have hmono : ∀ m, m < Fintype.card E → m * (m + 3) + 2 * Fintype.card E + 2 ≤
      Fintype.card E * (Fintype.card E + 3) := by intro m hm; nlinarith
  -- a loop: Lemma 3.1, one more multi-step
  by_cases hloop : ∃ l, G.IsLoop l
  · obtain ⟨l, hl⟩ := hloop
    have hlt := card_deleteEdge_lt l
    have hIH := ih _ hlt V _ (G.deleteEdge l) rfl (isEven_deleteEdge hl hev)
      (fun z => by have := degree_deleteEdge hl z; have := hdeg4 z; omega)
    intro f
    obtain ⟨D', hD', w', hw'⟩ := hIH ⟨fun x => f.1 x.1, isIFlow_restrict hl f.2⟩
    have hσ : ∀ x, extLoop l (orientSign D') 1 x = 1 ∨ extLoop l (orientSign D') 1 x = -1 := by
      intro x; unfold extLoop orientSign; split_ifs <;> simp
    have hσf : G.IsFlow (extLoop l (orientSign D') 1) :=
      (isFlow_extLoop_iff hl _ 1).2 ((isEulerOrient_iff D').1 hD')
    obtain ⟨D, hD, hDc⟩ := constFlow_of_sign G _ hσ hσf a
    set φ := loopHom (A := A) hl (f.1 l) (f.2.2 l) with hφ
    have hstart : φ ⟨fun x => f.1 x.1, isIFlow_restrict hl f.2⟩ = f := Subtype.ext (extLoop_restrict f.1)
    -- the constant flow of `G - l`, extended by `f l`, versus `a 𝟙_D`
    have hlast : ∃ w1 : (msGraph G A).Walk (φ ⟨_, isIFlow_constFlow nonzero_neg hD' (show a ∈ {x : A | x ≠ 0} from ha)⟩)
        ⟨constFlow a D, isIFlow_constFlow nonzero_neg hD (show a ∈ {x : A | x ≠ 0} from ha)⟩, w1.length ≤ 1 := by
      apply msWalk_le_one
      have hoff : ∀ y, y ≠ l → constFlow a D y = extLoop l (constFlow a D') (f.1 l) y := by
        intro y hy
        rw [hDc, constFlow_eq_smul]
        simp [extLoop, hy]
      have hat : constFlow a D l = a := by rw [hDc]; simp [extLoop]
      by_cases hfa : f.1 l = a
      · left
        show constFlow a D = extLoop l (constFlow a D') (f.1 l)
        funext y
        by_cases hy : y = l
        · subst hy; rw [hat]; simp [extLoop, hfa]
        · exact hoff y hy
      · right
        show CircStep G (extLoop l (constFlow a D') (f.1 l)) (constFlow a D)
        have := loop_circStep hl (extLoop l (constFlow a D') (f.1 l)) a (by simp [extLoop]; exact Ne.symm hfa)
        convert this using 1
        funext y
        by_cases hy : y = l
        · subst hy; simp [hat, extLoop]
        · simp [hy, hoff y hy]
    obtain ⟨w1, hw1⟩ := hlast
    refine ⟨D, hD, ((w'.map φ).copy hstart rfl).append w1, ?_⟩
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
    have := hmono _ hlt
    omega
  have hGl : G.Loopless := fun e he => hloop ⟨e, he⟩
  -- the split graphs satisfy the count
  have ihsplit : ∀ (v : V) (e e' : E), SplitData G v e e' → CountBound a ha (G.splitOff v e e') :=
    fun v e e' hd => ih _ (card_splitOff_lt hd.ne) V _ (G.splitOff v e e') rfl (isEven_splitOff hd hev)
      (fun z => by have := degree_splitOff hd z; have := hdeg4 z; omega)
  -- a vertex of degree 2: every flow is in `B(v; e, e')`
  by_cases hdeg2 : ∃ v, G.degree v = 2
  · obtain ⟨v, hv⟩ := hdeg2
    obtain ⟨e, e', hd, hbal⟩ := splitData_of_degree_two hGl hv
    intro f
    obtain ⟨D, hD, w, hw⟩ := count_balanced a ha hd (ihsplit v e e' hd) f (hbal f.1 f.2.1)
    have := hmono _ (card_splitOff_lt hd.ne)
    exact ⟨D, hD, w, by omega⟩
  -- no edge: the only flow is constant
  by_cases hE : IsEmpty E
  · intro f
    obtain ⟨D, hD⟩ := exists_eulerOrient hev
    have : f = ⟨constFlow a D, isIFlow_constFlow nonzero_neg hD (show a ∈ {x : A | x ≠ 0} from ha)⟩ :=
      Subtype.ext (funext fun e => isEmptyElim e)
    exact ⟨D, hD, SimpleGraph.Walk.nil.copy rfl this, by simp⟩
  have hne : Nonempty E := not_isEmpty_iff.1 hE
  -- otherwise all degrees are `0` or `4`: Proposition 4.4, then a split
  have hdeg04 : ∀ v, G.degree v = 0 ∨ G.degree v = 4 := by
    intro v
    obtain ⟨k, hk⟩ := hev v
    have h1 := hdeg4 v
    have h2 : G.degree v ≠ 2 := fun h => hdeg2 ⟨v, h⟩
    omega
  obtain ⟨Dc⟩ := sec4_decomp_exists_proved A
  intro f
  obtain ⟨fs, ⟨v, hv⟩, w1, hw1⟩ := MGraph.Sec4.prop_4_4_main Dc hne hGl hdeg04 f
  have hrho : Dc.rho f.1 ≤ Fintype.card E := by
    show Dc.rho f.1 ≤ Fintype.card E
    unfold CyclicDecomp.rho
    calc Set.ncard {e | f.1 e ∉ Dc.S} ≤ Set.ncard (Set.univ : Set E) :=
          Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
      _ = Fintype.card E := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  obtain ⟨e, e', hd, hfb⟩ := splitData_of_balanced hGl hv
  obtain ⟨D, hD, w2, hw2⟩ := count_balanced a ha hd (ihsplit v e e' hd) fs hfb
  refine ⟨D, hD, (w1.mapLe (flowGraph_le_msGraph G)).append w2, ?_⟩
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_mapLe]
  have := hmono _ (card_splitOff_lt hd.ne)
  omega

/-- Any two flows are joined by at most `M² + 3M + 1` multi-steps (tex l.545-546). -/
theorem ms_bound [Fintype A] (G : MGraph V E) (hev : G.IsEven) (hdeg : ∀ v, G.degree v ≤ 4)
    (f f' : {f : E → A // G.IsNZFlow f}) :
    ∃ w : (msGraph G A).Walk f f', w.length ≤ Fintype.card E ^ 2 + 3 * Fintype.card E + 1 := by
  by_cases hE : IsEmpty E
  · have : f = f' := Subtype.ext (funext fun e => isEmptyElim e)
    subst this
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  obtain ⟨e0⟩ := not_isEmpty_iff.1 hE
  have ha : f.1 e0 ≠ 0 := f.2.2 e0
  have hc := count_bound (f.1 e0) ha _ V E G rfl hev hdeg
  obtain ⟨D1, hD1, w1, hw1⟩ := hc f
  obtain ⟨D2, hD2, w2, hw2⟩ := hc f'
  obtain ⟨wm, hwm⟩ := msWalk_le_one G
    ⟨constFlow (f.1 e0) D1, isIFlow_constFlow nonzero_neg hD1 (show f.1 e0 ∈ {x : A | x ≠ 0} from ha)⟩
    ⟨constFlow (f.1 e0) D2, isIFlow_constFlow nonzero_neg hD2 (show f.1 e0 ∈ {x : A | x ≠ 0} from ha)⟩
    ((constFlow_eq_or_multiStep (f.1 e0) hD1 hD2).imp id (circStep_of_multiStep G))
  refine ⟨(w1.append wm).append w2.reverse, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  nlinarith

/-- `thm_2_5_a` (Theorem 2.5, first part, tex l.187-188, l.532-547). -/
theorem thm_2_5_a_proved (A : Type) [AddCommGroup A] [Fintype A] (G : MGraph V E) (hev : G.IsEven)
    (hdeg : ∀ v, G.degree v ≤ 4) (f f' : {f : E → A // G.IsNZFlow f}) :
    ∃ w : (G.flowGraph A).Walk f f',
      w.length ≤ Fintype.card E ^ 3 + 3 * Fintype.card E ^ 2 + Fintype.card E := by
  obtain ⟨w, hw⟩ := ms_bound G hev hdeg f f'
  obtain ⟨w', hw'⟩ := flowWalk_of_msWalk G w
  refine ⟨w', hw'.trans ?_⟩
  calc Fintype.card E * w.length ≤ Fintype.card E * (Fintype.card E ^ 2 + 3 * Fintype.card E + 1) :=
        Nat.mul_le_mul_left _ hw
    _ = Fintype.card E ^ 3 + 3 * Fintype.card E ^ 2 + Fintype.card E := by ring

end Induction

end Count

end EulerFlow
