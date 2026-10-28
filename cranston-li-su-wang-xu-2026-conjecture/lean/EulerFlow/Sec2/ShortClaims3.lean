/-
EulerFlow/Sec2/ShortClaims3.lean — three in-text claims of the SHORT paper: the named nowhere-zero 3-flow of an even
graph (the value 1 on every edge, directed by an Eulerian orientation); the ends of a cycle at one of its
vertices (there are exactly two); for k = 3 the k-flows are the nowhere-zero 3-flows of Section 1.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import EulerFlow.Reduction.Const
import EulerFlow.Graph.Orient
import EulerFlow.Graph.DirCycleBasic

namespace EulerFlow

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] in
/-- An even graph has an Eulerian orientation, and for EVERY Eulerian orientation `D` the constant integer flow with
value `1` along `D` is a nowhere-zero `3`-flow (its values are `1` and `-1`). -/
theorem even_three_flow_named_proved (G : MGraph V E) (hev : G.IsEven) :
    (∃ D : E → Bool, G.IsEulerOrient D) ∧
    ∀ D : E → Bool, G.IsEulerOrient D → G.IsIFlow (Ik 3) (constFlow (1 : ℤ) D) :=
  ⟨exists_eulerOrient (G := G) hev,
    fun _D hD => isIFlow_constFlow (fun y hy => by simpa [Ik, abs_neg] using hy) hD (by simp [Ik])⟩

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- The ends of a cycle `Q` at a vertex `v` of `Q` are exactly two: the end `d` of a dart of `Q` leaving `v`, and the
end at `v` of the dart `d'` of `Q` entering `v`; they are different, and every end at `v` of an edge of `Q` is one of
them. -/
theorem cycle_ends_proved (G : MGraph V E) (Q : G.DirCycle) {v : V} {d : E × Bool} (hd : d ∈ Q.darts)
    (hdv : G.dartTail d = v) :
    ∃ d' ∈ Q.darts, G.dartHead d' = v ∧ (d'.1, !d'.2) ≠ d ∧
      ∀ i : E × Bool, G.endVertex i = v → (∃ d₀ ∈ Q.darts, d₀.1 = i.1) → i = d ∨ i = (d'.1, !d'.2) := by
  obtain ⟨d', hd', hd'v⟩ := Q.exists_enter hd
  refine ⟨d', hd', hd'v.trans hdv, fun h => Q.flip_not_mem hd ?_, ?_⟩
  · have hflip : d' = (d.1, !d.2) := by rw [← h]; simp
    exact hflip ▸ hd'
  · rintro i hiv ⟨d₀, hd₀, hd₀i⟩
    by_contra hne
    obtain ⟨hne1, hne2⟩ := not_or.mp hne
    obtain ⟨h1, h2⟩ := Q.other_end_not_mem hd hd' hdv (hd'v.trans hdv) hiv hne1 hne2
    obtain ⟨e₀, b₀⟩ := d₀
    obtain ⟨e, b⟩ := i
    simp only at hd₀i
    subst hd₀i
    cases b₀ <;> cases b <;> simp_all

/-- The values allowed for a `3`-flow: `1 ≤ |x| ≤ 2` means `x ∈ {1, -1, 2, -2}`. -/
theorem mem_Ik_three (x : ℤ) : x ∈ Ik 3 ↔ x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 := by
  show (1 ≤ |x| ∧ |x| ≤ 3 - 1) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    rcases abs_cases x with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rw [hx] at h1 h2 <;> omega
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num

omit [Fintype V] [DecidableEq E] in
/-- For `k = 3` the `k`-flows (integer flows with `1 ≤ |F(e)| ≤ k - 1`) are the nowhere-zero `3`-flows of Section 1
(integer flows with values in `{1, -1, 2, -2}`). -/
theorem three_flows_proved (G : MGraph V E) (F : E → ℤ) :
    G.IsIFlow (Ik 3) F ↔ G.IsFlow F ∧ ∀ e, F e = 1 ∨ F e = -1 ∨ F e = 2 ∨ F e = -2 :=
  and_congr Iff.rfl (forall_congr' fun e => mem_Ik_three (F e))

end EulerFlow
