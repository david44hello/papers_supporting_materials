/-
EulerFlow/Sec9/Replace.lean — the "rule of replacement" claims inside the proof of Lemma 9.3 (tex l.751-763): the
(p,q) versions of Lemmas 3.1, 3.2, 3.3, read off the general I-flow lemmas (EulerFlow/Reduction/).
-/
import EulerFlow.Reduction.Paper9
import EulerFlow.Concrete.Small

namespace EulerFlow.MGraph.Sec9R

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

set_option linter.unusedSectionVars false

/-- tex l.752-753: the chain `q, q+1, …, p-q` joins any two elements of `I` inside `I` with differences `±1`. -/
theorem chain (p q : ℕ) (a b : ZMod p) (ha : a ∈ Ipq p q) (hb : b ∈ Ipq p q) :
    Relation.ReflTransGen (fun x y : ZMod p => y ∈ Ipq p q ∧ (y - x = 1 ∨ y - x = -1)) a b := by
  obtain ⟨n₁, h₁, h₁', rfl⟩ := ha
  obtain ⟨n₂, h₂, h₂', rfl⟩ := hb
  have h := zmod_chain (I := Ipq p q) (T := ({1, -1} : Set (ZMod p))) (by simp) (by simp)
    (fun n h h' => ⟨n, h, h', rfl⟩) ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
  refine Relation.ReflTransGen.mono ?_ _ _ h
  intro x y hxy
  exact ⟨hxy.1, by simpa using hxy.2⟩

/-- tex l.751-753: Lemma 3.1 for `(p,q)`-flows. -/
theorem loop (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) (G : MGraph V E) (l : E) (hl : G.IsLoop l)
    (h : ((G.deleteEdge l).stepGraph (Ipq p q) (Tpq p q)).Preconnected) :
    (G.stepGraph (Ipq p q) (Tpq p q)).Preconnected :=
  loop_preconnected (sec9_T_props_proved p q hq hpq).1 (ipq_chain p q) hl h

/-- tex l.755-758: Lemma 3.2 for `(p,q)`-flows: `L` is a bijection from the `(p,q)`-flows of `G'` onto the
`(p,q)`-flows of `G` in which the ends of `e, e'` at `v` are a balanced pair, and it maps multi-steps to multi-steps. -/
theorem split (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) (G : MGraph V E) (hG : G.Loopless) (v : V) (e e' : E)
    (hne : e ≠ e') (he : G.IsAt e v) (he' : G.IsAt e' v) :
    Set.BijOn (G.splitLift v e e') {f' | (G.splitOff v e e').IsIFlow (Ipq p q) f'}
      {f | G.IsIFlow (Ipq p q) f ∧ dirVal f (G.endAt e v) + dirVal f (G.endAt e' v) = 0} ∧
    ∀ (t : ZMod p) (f₁ f₂ : Option {x : E // x ≠ e ∧ x ≠ e'} → ZMod p),
      (G.splitOff v e e').IsMultiStep t f₁ f₂ → G.IsMultiStep t (G.splitLift v e e' f₁) (G.splitLift v e e' f₂) := by
  have hd := SplitData.of hG hne he he'
  have hI : ∀ y, y ∈ Ipq p q → -y ∈ Ipq p q := fun y hy => (sec9_I_props_proved p q hq hpq).1 y hy
  refine ⟨⟨fun f' hf' => ⟨(isIFlow_splitLift_iff hI hd f').mpr hf',
      splitLift_balanced hne he (hG e) he' (hG e') f'⟩,
    (splitLift_injective he (hG e)).injOn, fun f hf => ?_⟩, fun t f₁ f₂ h => splitLift_multiStep hd h⟩
  refine ⟨G.splitRes v e e' f, ?_, splitLift_splitRes hd f hf.2⟩
  have := splitLift_splitRes hd f hf.2
  show (G.splitOff v e e').IsIFlow (Ipq p q) (G.splitRes v e e' f)
  rw [← isIFlow_splitLift_iff hI hd, this]
  exact hf.1

/-- tex l.760-763: Lemma 3.3 for `(p,q)`-flows with `a = q`: `q 𝟙_D` is a `(p,q)`-flow, `-2q ∈ T`, and (for `G`
even, in the situation of Lemma 3.2) `B(v; e, e')` contains a flow `q 𝟙_D`. -/
theorem const (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) (G : MGraph V E) :
    (∀ D : E → Bool, G.IsEulerOrient D → G.IsIFlow (Ipq p q) (constFlow (q : ZMod p) D)) ∧
    -(2 • (q : ZMod p)) ∈ Tpq p q ∧
    (G.IsEven → G.Loopless → ∀ (v : V) (e e' : E), e ≠ e' → G.IsAt e v → G.IsAt e' v →
      ∃ D : E → Bool, G.IsEulerOrient D ∧
        dirVal (constFlow (q : ZMod p) D) (G.endAt e v) + dirVal (constFlow (q : ZMod p) D) (G.endAt e' v) = 0) := by
  obtain ⟨_, hTneg, hqI, h2q⟩ := sec9_T_props_proved p q hq hpq
  have hI : ∀ y ∈ Ipq p q, -y ∈ Ipq p q := fun y hy => (sec9_I_props_proved p q hq hpq).1 y hy
  exact ⟨fun D hD => isIFlow_constFlow hI hD hqI, hTneg _ h2q,
    fun hev hG v e e' hne he he' => exists_eulerOrient_balanced (SplitData.of hG hne he he') hev _⟩

end EulerFlow.MGraph.Sec9R
