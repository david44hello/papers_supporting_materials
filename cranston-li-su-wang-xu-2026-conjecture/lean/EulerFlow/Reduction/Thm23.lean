/-
EulerFlow/Reduction/Thm23.lean — Theorem 2.3 of paper 002 (tex l.177-178, proof l.448-457): every even graph is
A-flow-connected for every finite abelian group A with |A| ≥ 4; Theorem 1.1 (a) (the same statement); Remark 2.6
(K5 is even, has a triangle, and is ℤ₄-flow-connected).
-/
import EulerFlow.Reduction.Expand
import EulerFlow.Reduction.Triangle
import EulerFlow.Reduction.Thm22

namespace EulerFlow

open MGraph

/-- Theorem 2.3 for loopless graphs, by induction on `Φ(G)` (tex l.450-456): `Φ = 0` is Theorem 2.2; otherwise a
vertex of degree `≥ 6` is blown up into a triangle, `G⁺` is flow-connected by induction, then `G⁺/Δ` by Lemma 5.1,
and `G ≅ G⁺/Δ`. -/
theorem flowConnected_of_loopless {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (hA : 4 ≤ Fintype.card A) :
    ∀ n, ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      G.phi = n → G.Loopless → G.IsEven → G.FlowConnected A := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V E _ _ _ _ G hn hG hev
  by_cases hdeg : ∀ v, G.degree v ≤ 4
  · exact thm_2_2_proved A G hev hdeg
  push Not at hdeg
  obtain ⟨v, hv⟩ := hdeg
  have hv6 : 6 ≤ G.degree v := by obtain ⟨k, hk⟩ := hev v; omega
  obtain ⟨S₁, S₂, hΔ, hl, hev', hphi, ⟨φ⟩⟩ := exists_expand hG hev hv6
  have h1 := ih _ (by omega) _ _ (G.expandAt v S₁ S₂) rfl hl hev'
  exact φ.flowConnected (flowConnected_contract hA hΔ h1)

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Theorem 2.3 (tex l.177-178, proof l.448-457), exactly the Statements type. The loops are deleted first with
Lemma 3.1 (`T = A ∖ {0}`). -/
theorem thm_2_3_proved (A : Type) [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A) (G : MGraph V E)
    (hev : G.IsEven) : G.FlowConnected A := by
  classical
  have : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨hT1, -⟩ := sec3_T_nonzero_proved A
  suffices H : ∀ n, ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      Fintype.card E = n → G.IsEven → G.FlowConnected A from H _ V E G rfl hev
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V E _ _ _ _ G hn hev
  by_cases hloop : ∃ l, G.IsLoop l
  · obtain ⟨l, hl⟩ := hloop
    exact lem_3_1_proved {x | x ≠ 0} (by simp) (fun t ht => by simpa using ht) hT1 G l hl
      (ih _ (hn ▸ card_deleteEdge_lt l) V _ (G.deleteEdge l) rfl (isEven_deleteEdge hl hev))
  · exact flowConnected_of_loopless hA _ V E G rfl (fun e he => hloop ⟨e, he⟩) hev

/-- Theorem 1.1 (a) (tex l.68-71), exactly the Statements type. -/
theorem thm_1_1_a_proved (G : MGraph V E) (hev : G.IsEven) (A : Type) [AddCommGroup A] [Fintype A]
    (hA : 4 ≤ Fintype.card A) : G.FlowConnected A :=
  thm_2_3_proved A hA G hev

/-- `K₅` is even: every vertex has degree `4`. -/
theorem K5_isEven : K5.IsEven := by
  intro v
  fin_cases v <;> exact ⟨2, by decide⟩

/-- A triangle of `K₅`: `0 → 1 → 2 → 0`. -/
def K5_triangle : K5.DirCycle where
  darts := [(⟨(0, 1), by decide⟩, false), (⟨(1, 2), by decide⟩, false), (⟨(0, 2), by decide⟩, true)]
  ne_nil := by simp
  chain := by decide
  closes := by decide
  edges_nodup := by decide
  tails_nodup := by decide

/-- Remark 2.6 (tex l.200-207), exactly the Statements type: `K₅` is even, contains a triangle, and is
`ℤ₄`-flow-connected (Theorem 2.3 with `A = ℤ₄`). -/
theorem rem_2_6_proved : K5.IsEven ∧ (∃ Q : K5.DirCycle, Q.darts.length = 3) ∧ K5.FlowConnected (ZMod 4) :=
  ⟨K5_isEven, ⟨K5_triangle, rfl⟩, thm_2_3_proved (ZMod 4) (by simp) K5 K5_isEven⟩

end EulerFlow
