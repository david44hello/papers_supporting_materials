/-
EulerFlow/Reduction/SplitLemma.lean — Lemma 3.2 of paper 002 (splitting off, tex l.234-269): (a) `L` is a
bijection from the flows of `G'` onto `B(v; e, e')`; (b) it maps multi-steps to multi-steps with the same value,
and `T`-joined flows to `T`-joined flows. Proved for `I`-flows, then stated for nowhere-zero flows.
Route note: the paper builds the cycles of `G` from a cycle of `G'` through `g` by cutting a closed walk at `v`;
here `L(χ_{Q'})` is a `{-1,0,1}`-valued integer flow of `G` and the decomposition into edge-disjoint cycles
(`circ_decomp`) supplies them.
-/
import EulerFlow.Reduction.Basic

namespace EulerFlow

open Finset

namespace MGraph

variable {V E : Type} {G : MGraph V E} [DecidableEq V] [Fintype E] [DecidableEq E] {v : V} {e e' : E}

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem SplitData.of (hG : G.Loopless) (hne : e ≠ e') (he : G.IsAt e v) (he' : G.IsAt e' v) :
    SplitData G v e e' := ⟨hne, he, he', hG e, hG e'⟩

/-- The integer values `-1, 0, 1`, a symmetric set. -/
def unitVals : Set ℤ := {y | y = -1 ∨ y = 0 ∨ y = 1}

theorem unitVals_neg : ∀ y ∈ unitVals, -y ∈ unitVals := by
  intro y hy; simp only [unitVals, Set.mem_ofPred_eq] at *; omega

theorem nonzero_neg {A : Type} [AddCommGroup A] : ∀ y ∈ ({x | x ≠ 0} : Set A), -y ∈ ({x | x ≠ 0} : Set A) := by
  intro y hy; simpa using hy

variable {A : Type} [AddCommGroup A] {I T : Set A}

/-- `L` on `I`-flows. -/
def splitLiftV (hI : ∀ y ∈ I, -y ∈ I) (hd : SplitData G v e e')
    (f' : {f' // (G.splitOff v e e').IsIFlow I f'}) : {f // G.IsIFlow I f} :=
  ⟨G.splitLift v e e' f'.1, (isIFlow_splitLift_iff hI hd _).2 f'.2⟩

/-- Lemma 3.2 (b), second sentence, for `I`-flows: `T`-joined flows of `G'` have `T`-joined images. -/
theorem splitLift_reachable (hI : ∀ y ∈ I, -y ∈ I) (hd : SplitData G v e e')
    {a b : {f' // (G.splitOff v e e').IsIFlow I f'}} (hab : ((G.splitOff v e e').stepGraph I T).Reachable a b) :
    (G.stepGraph I T).Reachable (splitLiftV hI hd a) (splitLiftV hI hd b) := by
  refine reachable_transport (splitLiftV hI hd) (fun f Q t hft => ?_) hab
  refine ⟨G.splitLift v e e' Q.chi, fun x => splitLift_mem unitVals_neg Q.chi Q.chi_mem x,
    (isFlow_splitLift_iff hd _).2 Q.isFlow_chi, ?_⟩
  show G.splitLift v e e' (f.1 + fun o => Q.chi o • t) = G.splitLift v e e' f.1 + _
  rw [splitLift_add, splitLift_zsmul]

/-- Lemma 3.2 (b), first sentence: a multi-step of `G'` with the value `t` is mapped to a multi-step of `G` with
the value `t`. -/
theorem splitLift_multiStep (hd : SplitData G v e e') {t : A} {f₁ f₂ : Option {x : E // x ≠ e ∧ x ≠ e'} → A}
    (hstep : (G.splitOff v e e').IsMultiStep t f₁ f₂) :
    G.IsMultiStep t (G.splitLift v e e' f₁) (G.splitLift v e e' f₂) := by
  obtain ⟨ht, Qs, hne, hpw, hf⟩ := hstep
  have hS0 := sum_chi_ne_zero Qs hpw hne
  set h := G.splitLift v e e' (chiSum Qs) with hh
  have hflow : G.IsFlow h := (isFlow_splitLift_iff hd _).2 (isFlow_chiSum Qs)
  have hval : ∀ x, h x = -1 ∨ h x = 0 ∨ h x = 1 :=
    fun x => splitLift_mem unitVals_neg (chiSum Qs) (sum_chi_mem Qs hpw) x
  have hh0 : h ≠ 0 := fun h0 => hS0 (splitLift_injective hd.at₁ hd.nl₁ (h0.trans splitLift_zero.symm))
  obtain ⟨Qs₂, hpw₂, -, hsum₂, -⟩ := circ_decomp h hval hflow
  refine ⟨ht, Qs₂, ?_, hpw₂, ?_⟩
  · rintro rfl
    apply hh0; funext x; rw [← hsum₂ x]; simp
  · rw [hf]
    have : (fun o => (Qs.map fun Q => Q.chi o).sum • t) = fun o => chiSum Qs o • t := rfl
    rw [this, splitLift_add, splitLift_zsmul]
    funext x; simp only [Pi.add_apply, hsum₂, hh]

end MGraph

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] in
/-- Lemma 3.2 (a) (tex l.234-245), exactly the Statements type. -/
theorem lem_3_2_a_proved {A : Type} [AddCommGroup A] (G : MGraph V E) (hG : G.Loopless) (v : V) (e e' : E)
    (hne : e ≠ e') (he : G.IsAt e v) (he' : G.IsAt e' v) :
    Set.BijOn (G.splitLift (A := A) v e e') {f' | (G.splitOff v e e').IsNZFlow f'} {f | G.InB v e e' f} := by
  have hd := SplitData.of hG hne he he'
  refine ⟨fun f' hf' => ⟨(isIFlow_splitLift_iff nonzero_neg hd f').2 hf',
      splitLift_balanced hd.ne hd.at₁ hd.nl₁ hd.at₂ hd.nl₂ f'⟩,
    (splitLift_injective hd.at₁ hd.nl₁).injOn, fun f hf => ?_⟩
  refine ⟨G.splitRes v e e' f, ?_, splitLift_splitRes hd f hf.2⟩
  show (G.splitOff v e e').IsNZFlow _
  rw [IsNZFlow, ← isIFlow_splitLift_iff nonzero_neg hd, splitLift_splitRes hd f hf.2]
  exact hf.1

omit [Fintype V] in
/-- Lemma 3.2 (b) (tex l.246-247), exactly the Statements type. -/
theorem lem_3_2_b_proved {A : Type} [AddCommGroup A] (G : MGraph V E) (hG : G.Loopless) (v : V) (e e' : E)
    (hne : e ≠ e') (he : G.IsAt e v) (he' : G.IsAt e' v) (t : A) (f₁ f₂ : Option {x : E // x ≠ e ∧ x ≠ e'} → A)
    (_h₁ : (G.splitOff v e e').IsNZFlow f₁) (_h₂ : (G.splitOff v e e').IsNZFlow f₂)
    (hstep : (G.splitOff v e e').IsMultiStep t f₁ f₂) :
    G.IsMultiStep t (G.splitLift v e e' f₁) (G.splitLift v e e' f₂) :=
  splitLift_multiStep (SplitData.of hG hne he he') hstep

omit [Fintype V] in
/-- Lemma 3.2 (b), second sentence (tex l.247-248), exactly the Statements type. -/
theorem lem_3_2_b_joined_proved {A : Type} [AddCommGroup A] (T : Set A) (G : MGraph V E) (hG : G.Loopless) (v : V)
    (e e' : E) (hne : e ≠ e') (he : G.IsAt e v) (he' : G.IsAt e' v)
    (f₁ f₂ : {f : Option {x : E // x ≠ e ∧ x ≠ e'} → A // (G.splitOff v e e').IsNZFlow f})
    (hj : ((G.splitOff v e e').tStepGraph T).Reachable f₁ f₂) :
    ∃ (k₁ : G.IsNZFlow (G.splitLift v e e' f₁.1)) (k₂ : G.IsNZFlow (G.splitLift v e e' f₂.1)),
      (G.tStepGraph T).Reachable ⟨_, k₁⟩ ⟨_, k₂⟩ := by
  have hd := SplitData.of hG hne he he'
  exact ⟨(splitLiftV nonzero_neg hd f₁).2, (splitLiftV nonzero_neg hd f₂).2, splitLift_reachable nonzero_neg hd hj⟩

end EulerFlow
