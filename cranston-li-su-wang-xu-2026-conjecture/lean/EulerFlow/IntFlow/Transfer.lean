/-
EulerFlow/IntFlow/Transfer.lean — paper 002, Proposition 8.7 (the transfer, tex l.671-684), Theorem 8.1
(tex l.686-688), Remark 8.8 (tex l.690-697) and Theorem 1.1(b).
Route = the paper's: every step of a `{1,-1,2,-2}`-chain of `ℤ_k`-flows lifts to adjacent integer lifts
(Lemma 8.5 for the value 1, Lemma 8.6 for the value 2; for -1 and -2 the same lemmas from the other end), and the
lifts of one flow are joined (Lemma 8.4). Theorem 2.4 enters only as the hypothesis `h24`.
-/
import EulerFlow.IntFlow.Steps
import EulerFlow.Defs.Constructions

namespace EulerFlow

namespace Sec8

open Finset MGraph

variable {V E : Type} {G : MGraph V E} [Fintype E] [DecidableEq E] [DecidableEq V]

/-- Two `k`-flows differing by `λ χ_Q`, `λ ≠ 0`, are equal or adjacent in `𝓕(G, k)`. -/
lemma reachable_of_step {k : ℕ} (Q : G.DirCycle) (F F' : {F : E → ℤ // G.IsIFlow (Ik k) F}) (l : ℤ)
    (hl : l ≠ 0) (h : F'.1 = F.1 + fun e => Q.chi e • l) : (G.kFlowGraph k).Reachable F F' := by
  by_cases heq : F = F'
  · rw [heq]
  · refine SimpleGraph.Adj.reachable ?_
    rw [kFlowGraph, stepGraph, SimpleGraph.fromRel_adj]
    exact ⟨heq, Or.inl ⟨Q, l, hl, hl, h⟩⟩

/-- One step `b = a + t χ_Q` with `t ∈ {1, 2}` between `ℤ_k`-flows lifts to two joined integer lifts. -/
lemma lift_step_pos [Fintype V] {k : ℕ} (hk : 3 ≤ k) (Q : G.DirCycle) (a b : E → ZMod k) (ha : G.IsNZFlow a)
    (hb : G.IsNZFlow b) (t : ℕ) (ht : t = 1 ∨ t = 2) (hab : b = a + fun e => Q.chi e • (t : ZMod k)) :
    ∃ Fa Fb : E → ℤ, ∃ (hFa : G.IsIntLift k a Fa) (hFb : G.IsIntLift k b Fb),
      (G.kFlowGraph k).Reachable ⟨Fa, hFa.1⟩ ⟨Fb, hFb.1⟩ := by
  rcases ht with rfl | rfl
  · obtain ⟨Fa, hFa⟩ := lem_8_3_proved k (by omega) G a ha
    have hb' : G.IsNZFlow (a + fun e => Q.chi e • (1 : ZMod k)) := by simpa [hab] using hb
    have hFb := lem_8_5_proved k (by omega) G Q a ha hb' Fa hFa
    have hFb' : G.IsIntLift k b (Fa + fun e => Q.chi e • (1 : ℤ)) := by simpa [hab] using hFb
    exact ⟨Fa, _, hFa, hFb', reachable_of_step Q ⟨Fa, hFa.1⟩ ⟨_, hFb'.1⟩ 1 one_ne_zero rfl⟩
  · have hb' : G.IsNZFlow (a + fun e => Q.chi e • (2 : ZMod k)) := by simpa [hab] using hb
    obtain ⟨Fa, hFa, hFb⟩ := lem_8_6_proved k hk G Q a ha hb'
    have hFb' : G.IsIntLift k b (Fa + fun e => Q.chi e • (2 : ℤ)) := by simpa [hab] using hFb
    exact ⟨Fa, _, hFa, hFb', reachable_of_step Q ⟨Fa, hFa.1⟩ ⟨_, hFb'.1⟩ 2 two_ne_zero rfl⟩

/-- One step `b = a + t χ_Q` with `t ∈ {1, -1, 2, -2}` lifts to two joined integer lifts. -/
lemma lift_step [Fintype V] {k : ℕ} (hk : 3 ≤ k) (Q : G.DirCycle) (a b : E → ZMod k) (ha : G.IsNZFlow a)
    (hb : G.IsNZFlow b) (t : ZMod k) (ht : t ∈ Tcyc k) (hab : b = a + fun e => Q.chi e • t) :
    ∃ Fa Fb : E → ℤ, ∃ (hFa : G.IsIntLift k a Fa) (hFb : G.IsIntLift k b Fb),
      (G.kFlowGraph k).Reachable ⟨Fa, hFa.1⟩ ⟨Fb, hFb.1⟩ := by
  simp only [Tcyc, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact lift_step_pos hk Q a b ha hb 1 (Or.inl rfl) (by simpa using hab)
  · -- `a = b + χ_Q`: the value-1 step from the other end
    obtain ⟨Fb, Fa, hFb, hFa, hr⟩ := lift_step_pos hk Q b a hb ha 1 (Or.inl rfl)
      (by rw [hab]; funext e; simp)
    exact ⟨Fa, Fb, hFa, hFb, hr.symm⟩
  · exact lift_step_pos hk Q a b ha hb 2 (Or.inr rfl) (by simpa using hab)
  · obtain ⟨Fb, Fa, hFb, hFa, hr⟩ := lift_step_pos hk Q b a hb ha 2 (Or.inr rfl)
      (by rw [hab]; funext e; simp)
    exact ⟨Fa, Fb, hFa, hFb, hr.symm⟩

/-- Along a `{1,-1,2,-2}`-chain from `a` to `b`, every integer lift of `a` is joined to every integer lift of
`b` (tex l.680-683). -/
lemma lifts_joined_of_walk [Fintype V] {k : ℕ} (hk : 3 ≤ k) {a b : {f : E → ZMod k // G.IsNZFlow f}}
    (w : (G.tStepGraph (Tcyc k)).Walk a b) :
    ∀ Fa Fb (hFa : G.IsIntLift k a.1 Fa) (hFb : G.IsIntLift k b.1 Fb),
      (G.kFlowGraph k).Reachable ⟨Fa, hFa.1⟩ ⟨Fb, hFb.1⟩ := by
  induction w with
  | nil =>
    intro Fa Fb hFa hFb
    exact lem_8_4_proved k (by omega) G _ Fa Fb hFa hFb
  | @cons a c b hadj w ih =>
    intro Fa Fb hFa hFb
    have hadj' : a ≠ c ∧ ((∃ Q : G.DirCycle, ∃ t ∈ Tcyc k, t ≠ 0 ∧ c.1 = a.1 + fun e => Q.chi e • t) ∨
        (∃ Q : G.DirCycle, ∃ t ∈ Tcyc k, t ≠ 0 ∧ a.1 = c.1 + fun e => Q.chi e • t)) := hadj
    obtain ⟨Ga, Gc, hGa, hGc, hr⟩ : ∃ Ga Gc : E → ℤ, ∃ (hGa : G.IsIntLift k a.1 Ga)
        (hGc : G.IsIntLift k c.1 Gc), (G.kFlowGraph k).Reachable ⟨Ga, hGa.1⟩ ⟨Gc, hGc.1⟩ := by
      rcases hadj'.2 with ⟨Q, t, ht, _, h⟩ | ⟨Q, t, ht, _, h⟩
      · exact lift_step hk Q a.1 c.1 a.2 c.2 t ht h
      · obtain ⟨Fc, Fa', hFc, hFa', hr⟩ := lift_step hk Q c.1 a.1 c.2 a.2 t ht h
        exact ⟨Fa', Fc, hFa', hFc, hr.symm⟩
    exact (lem_8_4_proved k (by omega) G _ Fa Ga hFa hGa).trans (hr.trans (ih Gc Fb hGc hFb))

omit [DecidableEq E] in
/-- A `k`-flow is an integer lift of its residues. -/
lemma isIntLift_residues {k : ℕ} (F : E → ℤ) (hF : G.IsIFlow (Ik k) F) :
    G.IsIntLift k (fun e => ((F e : ℤ) : ZMod k)) F := ⟨hF, fun _ => rfl⟩

/-- `prop_8_7` (Proposition 8.7, the transfer, tex l.671-684). -/
theorem prop_8_7_proved [Fintype V] (k : ℕ) (hk : 3 ≤ k) (G : MGraph V E)
    (h : (G.tStepGraph (Tcyc k)).Preconnected) : G.KFlowConnected k := by
  intro F F'
  have hf := sec8_residues_proved k (by omega) G F.1 F.2
  have hf' := sec8_residues_proved k (by omega) G F'.1 F'.2
  obtain ⟨w⟩ := h ⟨_, hf⟩ ⟨_, hf'⟩
  exact lifts_joined_of_walk hk w F.1 F'.1 (isIntLift_residues F.1 F.2) (isIntLift_residues F'.1 F'.2)

/-- `thm_8_1` (Theorem 8.1, tex l.686-688): Theorem 2.4 with `m = k` (the hypothesis `h24`) and
Proposition 8.7. -/
theorem thm_8_1_proved [Fintype V] (k : ℕ) (hk : 4 ≤ k) (G : MGraph V E) (_hev : G.IsEven)
    (h24 : (G.tStepGraph (Tcyc k)).Preconnected) : G.KFlowConnected k :=
  prop_8_7_proved k (by omega) G h24

/-- `thm_1_1_b` (Theorem 1.1(b), tex l.72, l.76): Theorem 8.1. -/
theorem thm_1_1_b_proved [Fintype V] (G : MGraph V E) (hev : G.IsEven) (k : ℕ) (hk : 4 ≤ k)
    (h24 : (G.tStepGraph (Tcyc k)).Preconnected) : G.KFlowConnected k :=
  thm_8_1_proved k hk G hev h24

/-- In `ℤ_3` the set `{1, -1, 2, -2}` is the set of all non-zero elements. -/
lemma tcyc_three : Tcyc 3 = {x : ZMod 3 | x ≠ 0} := by
  ext x
  simp only [Tcyc, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  revert x
  decide

/-- `rem_8_8_k3` (Remark 8.8, tex l.693-694): if `𝓕(G, ℤ_3)` is connected, so is `𝓕(G, 3)`; every step of
`𝓕(G, ℤ_3)` has the value `1` or `-1` (`= 2`), so Proposition 8.7 applies. -/
theorem rem_8_8_k3_proved [Fintype V] (G : MGraph V E) (h : G.FlowConnected (ZMod 3)) : G.KFlowConnected 3 := by
  apply prop_8_7_proved 3 le_rfl G
  have : G.tStepGraph (Tcyc 3) = G.flowGraph (ZMod 3) := by
    rw [tStepGraph, flowGraph, tcyc_three]
  rw [this]; exact h

/-- `rem_8_8_k2` (Remark 8.8, tex l.694-696): `𝓕(G, 2)` is connected for every graph: a graph has at most one
`ℤ₂`-flow, every `2`-flow is an integer lift of it, and Lemma 8.4 joins any two integer lifts. -/
theorem rem_8_8_k2_proved [Fintype V] (G : MGraph V E) : G.KFlowConnected 2 := by
  intro F F'
  have hf := sec8_residues_proved 2 le_rfl G F.1 F.2
  have hf' := sec8_residues_proved 2 le_rfl G F'.1 F'.2
  have heq := (rem_8_8_Z2_proved G).1 _ _ hf hf'
  have hF' : G.IsIntLift 2 (fun e => ((F.1 e : ℤ) : ZMod 2)) F'.1 := by
    rw [heq]; exact isIntLift_residues F'.1 F'.2
  exact lem_8_4_proved 2 le_rfl G _ F.1 F'.1 (isIntLift_residues F.1 F.2) hF'

/-- `rem_8_8` (Remark 8.8, tex l.691-697, and tex l.97-98): for even graphs and every `k ≥ 2`, if `𝓕(G, ℤ_k)` is
connected then `𝓕(G, k)` is connected. For `k ≥ 4` this is Theorem 8.1 (hypothesis `h24` = Theorem 2.4). -/
theorem rem_8_8_proved [Fintype V] (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (hev : G.IsEven)
    (h : G.FlowConnected (ZMod k)) (h24 : 4 ≤ k → (G.tStepGraph (Tcyc k)).Preconnected) :
    G.KFlowConnected k := by
  rcases (by omega : k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | h4
  · exact rem_8_8_k2_proved G
  · exact rem_8_8_k3_proved G h
  · exact thm_8_1_proved k h4 G hev (h24 h4)

end Sec8

end EulerFlow
