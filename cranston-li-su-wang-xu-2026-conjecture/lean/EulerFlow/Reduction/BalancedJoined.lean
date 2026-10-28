/-
EulerFlow/Reduction/BalancedJoined.lean — the Outline sentence "So all flows with a balanced pair are joined to each
other" (short paper v1.51 l.121; the same step in the proof of Proposition 3.4, l.305-306), as its own statement.
It is the step `hbal` inside `reduction_preconnected`, for nowhere-zero flows, with the induction hypothesis of that
proof (any two flows of every splitting off are joined) as a hypothesis.
-/
import EulerFlow.Reduction.Reduce

namespace EulerFlow

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Every flow with a balanced pair is `T`-joined to the constant flow `a 𝟙_{D₀}` (short l.300-306: by the
induction hypothesis for `G'` and Lemma 3.2, then Lemma 3.3 (b), then Lemma 3.3 (a) with (T2)). -/
theorem balanced_reachable_const {A : Type} [AddCommGroup A] {T : Set A} (hT0 : (0 : A) ∉ T)
    (hTneg : ∀ t ∈ T, -t ∈ T) {a : A} (ha : a ≠ 0) (h2a : 2 • a = 0 ∨ 2 • a ∈ T) {G : MGraph V E}
    (hev : G.IsEven) (hG : G.Loopless)
    (hind : ∀ (v : V) (e e' : E), e ≠ e' → G.IsAt e v → G.IsAt e' v →
      ((G.splitOff v e e').tStepGraph T).Preconnected)
    {D₀ : E → Bool} (hD₀ : G.IsEulerOrient D₀) (f : {f : E → A // G.IsNZFlow f})
    (hf : G.HasBalancedPair f.1) :
    (G.tStepGraph T).Reachable f ⟨_, isIFlow_constFlow nonzero_neg hD₀ ha⟩ := by
  obtain ⟨v, hv⟩ := hf
  obtain ⟨e, e', hd, hfb⟩ := splitData_of_balanced hG hv
  obtain ⟨D, hD, hDb⟩ := exists_eulerOrient_balanced hd hev a
  exact (reachable_of_balanced nonzero_neg hd (hind v e e' hd.ne hd.at₁ hd.at₂) f
    ⟨_, isIFlow_constFlow nonzero_neg hD ha⟩ hfb hDb).trans
    (reachable_constFlow nonzero_neg hT0 hTneg ha h2a hD hD₀)

/-- The Outline sentence (short l.121, and l.305-306): in an even graph with no loop, if any two flows of every
splitting off are `T`-joined (the induction hypothesis), then any two flows with a balanced pair are `T`-joined.
`T` as in Proposition 3.4, of which only `0 ∉ T`, `T = -T` and (T2) are used. -/
theorem intro_balanced_joined_proved {A : Type} [AddCommGroup A] (T : Set A) (hT0 : (0 : A) ∉ T)
    (hTneg : ∀ t ∈ T, -t ∈ T) (hT2 : CondT2 T) (G : MGraph V E) (hev : G.IsEven) (hG : G.Loopless)
    (hind : ∀ (v : V) (e e' : E), e ≠ e' → G.IsAt e v → G.IsAt e' v →
      ((G.splitOff v e e').tStepGraph T).Preconnected)
    (f₁ f₂ : {f : E → A // G.IsNZFlow f}) (h₁ : G.HasBalancedPair f₁.1) (h₂ : G.HasBalancedPair f₂.1) :
    (G.tStepGraph T).Reachable f₁ f₂ := by
  obtain ⟨a, ha, h2a⟩ := hT2
  obtain ⟨D₀, hD₀⟩ := exists_eulerOrient hev
  exact (balanced_reachable_const hT0 hTneg ha h2a hev hG hind hD₀ f₁ h₁).trans
    (balanced_reachable_const hT0 hTneg ha h2a hev hG hind hD₀ f₂ h₂).symm

end EulerFlow
