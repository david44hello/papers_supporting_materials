/-
EulerFlow/Reduction/Thm22.lean — Theorem 2.2 of paper 002 (tex l.172-175, proof l.406-413): every even graph with
all degrees at most 4 is A-flow-connected, for every finite abelian group A. Proposition 3.4 for the class "even,
all degrees ≤ 4" with T = A ∖ {0}; (LOCAL) is Proposition 4.4 (EulerFlow/Sec4/Prop44.lean).
-/
import EulerFlow.Reduction.Paper3
import EulerFlow.Sec4.Prop44
import EulerFlow.Sec4.Decomp

namespace EulerFlow

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] in
/-- For the group with one element a graph has at most one flow, so it is flow-connected (tex l.407). -/
theorem flowConnected_of_subsingleton (A : Type) [AddCommGroup A] [Subsingleton A] (G : MGraph V E) :
    G.FlowConnected A := by
  intro f₁ f₂
  have : f₁ = f₂ := Subtype.ext (funext fun _ => Subsingleton.elim _ _)
  rw [this]

omit [Fintype V] in
/-- The class of Theorem 2.2 is closed under deleting a loop and splitting off (tex l.408-410). -/
theorem degree_le_four_deleteEdge {G : MGraph V E} {l : E} (hl : G.IsLoop l) (hdeg : ∀ v, G.degree v ≤ 4) (z : V) :
    (G.deleteEdge l).degree z ≤ 4 := by
  have h1 := degree_deleteEdge hl z
  have h2 := hdeg z
  split_ifs at h1 <;> omega

omit [Fintype V] in
theorem degree_le_four_splitOff {G : MGraph V E} {v : V} {e e' : E} (hd : SplitData G v e e')
    (hdeg : ∀ v, G.degree v ≤ 4) (z : V) : (G.splitOff v e e').degree z ≤ 4 := by
  have h1 := degree_splitOff hd z
  have h2 := hdeg z
  split_ifs at h1 <;> omega

/-- Theorem 2.2 (tex l.172-175, proof l.406-413), exactly the Statements type. -/
theorem thm_2_2_proved (A : Type) [AddCommGroup A] [Fintype A] (G : MGraph V E) (hev : G.IsEven)
    (hdeg : ∀ v, G.degree v ≤ 4) : G.FlowConnected A := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact flowConnected_of_subsingleton A G
  obtain ⟨D⟩ := sec4_decomp_exists_proved A
  obtain ⟨hT1, hT2⟩ := sec3_T_nonzero_proved A
  exact prop_3_4_proved {x | x ≠ 0} (by simp) (fun t ht => by simpa using ht) hT1 hT2
    (fun _ _ _ _ _ _ G => G.IsEven ∧ ∀ v, G.degree v ≤ 4)
    (fun _ _ _ _ _ _ _ hG => hG.1)
    (fun _ _ _ _ _ _ _ _ hG hl => ⟨isEven_deleteEdge hl hG.1, degree_le_four_deleteEdge hl hG.2⟩)
    (fun _ _ _ _ _ _ _ _ _ _ hG hGl hne he he' =>
      ⟨isEven_splitOff (SplitData.of hGl hne he he') hG.1, degree_le_four_splitOff (SplitData.of hGl hne he he') hG.2⟩)
    (fun _ _ _ _ _ _ _ hG hE hGl hdeg0 f => by
      obtain ⟨f', hb, w, -⟩ := Sec4.prop_4_4_main D hE hGl
        (fun v => (hdeg0 v).imp id fun h => le_antisymm (hG.2 v) h) f
      exact ⟨f', hb, ⟨w⟩⟩)
    G ⟨hev, hdeg⟩

end EulerFlow
