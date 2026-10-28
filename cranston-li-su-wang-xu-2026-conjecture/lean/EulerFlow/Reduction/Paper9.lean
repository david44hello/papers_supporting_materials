/-
EulerFlow/Reduction/Paper9.lean — Theorem 9.1 (tex l.718-721, proof l.839-841), the "if and only if" of Section 9
(tex l.728 and the abstract), and the circular (2k+1,k)-flow of tex l.731-732. Theorem 9.1 and the "iff" take their
inputs from the paper (Proposition 9.6, Theorem 9.2, the Section 9 facts on I and T) as hypotheses; the Statements
bodies link them.
-/
import EulerFlow.Reduction.Paper3

namespace EulerFlow

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Theorem 9.1 from Lemma 9.3 and Proposition 9.6 (tex l.839-841: "Lemma 9.3 and Proposition 9.6"). The second
part, `(p,q)`-flow-connectedness, holds because steps with values in `T ⊆ ℤ_p ∖ {0}` are steps. -/
theorem thm_9_1_of (p q : ℕ) (hI : ∀ x ∈ Ipq p q, -x ∈ Ipq p q) (hT0 : (0 : ZMod p) ∉ Tpq p q)
    (hTneg : ∀ t ∈ Tpq p q, -t ∈ Tpq p q) (hqI : (q : ZMod p) ∈ Ipq p q) (h2q : 2 • (q : ZMod p) ∈ Tpq p q)
    (h96 : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      G.IsEven → Nonempty E → G.Loopless → (∀ v, G.degree v = 0 ∨ 4 ≤ G.degree v) →
      ∀ f : {f : E → ZMod p // G.IsIFlow (Ipq p q) f}, ∃ f' : {f : E → ZMod p // G.IsIFlow (Ipq p q) f},
        G.HasBalancedPair f'.1 ∧ (G.stepGraph (Ipq p q) (Tpq p q)).Reachable f f')
    (G : MGraph V E) (hev : G.IsEven) :
    (G.stepGraph (Ipq p q) (Tpq p q)).Preconnected ∧ G.PQFlowConnected p q := by
  have h1 := lem_9_3_of p q hI hT0 hTneg hqI h2q h96 G hev
  refine ⟨h1, fun f₁ f₂ => (h1 f₁ f₂).mono (stepGraph_mono _ fun t ht => ?_)⟩
  exact fun h0 => hT0 (h0 ▸ ht)

/-- Section 9 (tex l.728): for `p > 2q`, every even graph is `(p,q)`-flow-connected iff `p ≥ 4q`: Theorem 9.1 gives
"if", the graph of Theorem 9.2 gives "only if". -/
theorem sec9_iff_of (p q : ℕ)
    (h91 : 4 * q ≤ p → ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      G.IsEven → G.PQFlowConnected p q)
    (h92 : p < 4 * q → (dipole (2 * p)).IsEven ∧ ¬ (dipole (2 * p)).PQFlowConnected p q) :
    (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      G.IsEven → G.PQFlowConnected p q) ↔ 4 * q ≤ p := by
  refine ⟨fun h => ?_, h91⟩
  by_contra hlt
  obtain ⟨hev, hnot⟩ := h92 (by omega)
  exact hnot (h (Fin 2) (Fin (2 * p)) (dipole (2 * p)) hev)

omit [Fintype V] in
/-- Section 9 (tex l.731-732): every even graph admits a circular `(2k+1, k)`-flow, the value `k` on every arc of
an Eulerian orientation; exactly the Statements type. -/
theorem sec9_circular_proved (k : ℕ) (_hk : 1 ≤ k) (G : MGraph V E) (hev : G.IsEven) :
    ∃ F : E → ℤ, G.IsFlow F ∧ ∀ e, (k : ℤ) ≤ |F e| ∧ |F e| ≤ (2 * k + 1 : ℤ) - k := by
  obtain ⟨D, hD⟩ := exists_eulerOrient hev
  refine ⟨constFlow (k : ℤ) D, ?_, fun e => ?_⟩
  · rw [constFlow_eq_smul]; exact isFlow_zsmul ((isEulerOrient_iff D).1 hD) _
  · simp only [constFlow]
    split_ifs <;> simp only [abs_neg, Nat.abs_cast] <;> omega

end EulerFlow
