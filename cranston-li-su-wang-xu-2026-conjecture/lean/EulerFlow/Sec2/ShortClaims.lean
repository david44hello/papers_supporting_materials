/-
EulerFlow/Sec2/ShortClaims.lean — six in-text claims of the SHORT paper (v1.46) that a review
found without a statement: the sign of a step value (l.155-157), outward values of a flow are non-zero
(l.171-172), the two ends of a loop (l.184), small edges and colors (l.322-324), non-small values in ℤ_m (l.445-446).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import EulerFlow.Graph.DirCycleBasic
import EulerFlow.Graph.CycleFind
import EulerFlow.Sec4.Decomp
import EulerFlow.Sec4.Prop44

namespace EulerFlow

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The reversed directed cycle: the same edges, each passed in the other direction, in the reverse order. -/
def cycleReverse (G : MGraph V E) (Q : G.DirCycle) : G.DirCycle where
  darts := (Q.darts.map dartRev).reverse
  ne_nil := by simpa using Q.ne_nil
  chain := by
    rw [List.isChain_reverse, List.isChain_map]
    refine Q.chain.imp ?_
    intro a b h
    simp [flip, h]
  closes := by
    simp [List.getLast_reverse, List.head_reverse]
    exact Q.closes.symm
  edges_nodup := by
    simpa [List.map_reverse, List.map_map, Function.comp_def, dartRev] using Q.edges_nodup
  tails_nodup := by
    have := DirCycle.heads_nodup (G := G) Q
    simpa [List.map_reverse, List.map_map, Function.comp_def] using this

/-- `χ_{rev Q} = -χ_Q`. -/
theorem cycleReverse_chi (G : MGraph V E) (Q : G.DirCycle) (e : E) : (cycleReverse G Q).chi e = -Q.chi e := by
  have hf := DirCycle.flip_not_mem (G := G) Q (d := (e, false))
  have ht := DirCycle.flip_not_mem (G := G) Q (d := (e, true))
  simp only [DirCycle.chi, cycleReverse, List.mem_reverse, List.mem_map, dartRev]
  by_cases h0 : (e, false) ∈ Q.darts <;> by_cases h1 : (e, true) ∈ Q.darts
  · exact absurd h1 (hf h0)
  · have : ∃ a ∈ Q.darts, (a.1, !a.2) = (e, true) := ⟨(e, false), h0, rfl⟩
    have h2 : ¬ ∃ a ∈ Q.darts, (a.1, !a.2) = (e, false) := by
      rintro ⟨⟨a1, a2⟩, ha, hh⟩; simp at hh; obtain ⟨rfl, rfl⟩ := hh; exact h1 ha
    simp [h0, h1, this, h2]
  · have : ∃ a ∈ Q.darts, (a.1, !a.2) = (e, false) := ⟨(e, true), h1, rfl⟩
    simp [h0, h1, this]
  · have h2 : ¬ ∃ a ∈ Q.darts, (a.1, !a.2) = (e, false) := by
      rintro ⟨⟨a1, a2⟩, ha, hh⟩; simp at hh; obtain ⟨rfl, rfl⟩ := hh; exact h1 ha
    have h3 : ¬ ∃ a ∈ Q.darts, (a.1, !a.2) = (e, true) := by
      rintro ⟨⟨a1, a2⟩, ha, hh⟩; simp at hh; obtain ⟨rfl, rfl⟩ := hh; exact h0 ha
    simp [h0, h1, h2]

/-- `χ_Q` is `±1` on every edge of `Q`. -/
theorem chi_of_mem (G : MGraph V E) (Q : G.DirCycle) (d : E × Bool) (hd : d ∈ Q.darts) :
    Q.chi d.1 = 1 ∨ Q.chi d.1 = -1 := by
  obtain ⟨e, b⟩ := d
  unfold DirCycle.chi
  cases b
  · simp [hd]
  · by_cases h : (e, false) ∈ Q.darts <;> simp [h, hd]

/-- tex l.157: reversing `Q` replaces `t` by `-t`. -/
theorem step_reverse {A : Type} [AddCommGroup A] (G : MGraph V E) (Q : G.DirCycle) (t : A) (f : E → A) :
    (f + fun e => Q.chi e • t) = f + fun e => (cycleReverse G Q).chi e • (-t) := by
  funext e
  simp [cycleReverse_chi]

/-- tex l.157: exchanging `f` and `f'` replaces `t` by `-t`. -/
theorem step_exchange {A : Type} [AddCommGroup A] (G : MGraph V E) (Q : G.DirCycle) (t : A) (f f' : E → A)
    (h : f' = f + fun e => Q.chi e • t) : f = f' + fun e => Q.chi e • (-t) := by
  subst h; funext e; simp

/-- tex l.157: the value of a step is determined only up to sign. -/
theorem step_value_up_to_sign {A : Type} [AddCommGroup A] (G : MGraph V E) (Q Q' : G.DirCycle) (t t' : A)
    (ht : t ≠ 0) (f f' : E → A) (h : f' = f + fun e => Q.chi e • t) (h' : f' = f + fun e => Q'.chi e • t') :
    t' = t ∨ t' = -t := by
  have heq : (fun e => Q.chi e • t) = fun e => Q'.chi e • t' := by
    have := h.symm.trans h'
    exact add_left_cancel this
  obtain ⟨d, hd⟩ : ∃ d, d ∈ Q.darts := List.exists_mem_of_ne_nil _ Q.ne_nil
  have hv : Q.chi d.1 • t = Q'.chi d.1 • t' := congrFun heq d.1
  have hQ := chi_of_mem G Q d hd
  have hQ' : Q'.chi d.1 = 1 ∨ Q'.chi d.1 = -1 ∨ Q'.chi d.1 = 0 := by
    unfold DirCycle.chi; split_ifs <;> simp
  rcases hQ with hQ | hQ <;> rcases hQ' with hQ' | hQ' | hQ' <;> rw [hQ, hQ'] at hv <;> simp at hv
  · exact Or.inl hv.symm
  · exact Or.inr (by rw [hv]; simp)
  · exact absurd hv ht
  · exact Or.inr hv.symm
  · exact Or.inl (by simpa using hv.symm)
  · exact absurd hv ht

/-- tex l.184: the two ends of a loop are different ends at the same vertex, and their outward values sum to `0`. -/
theorem loop_ends {A : Type} [AddCommGroup A] (G : MGraph V E) (f : E → A) (l : E) (hl : G.IsLoop l) :
    (l, false) ≠ (l, true) ∧ G.endVertex (l, false) = G.endVertex (l, true) ∧
      dirVal f (l, false) + dirVal f (l, true) = 0 := by
  refine ⟨by simp, by simp [endVertex, hl.symm, IsLoop], by simp [dirVal]⟩

/-- tex l.171-172: every outward value of a flow is non-zero. -/
theorem outward_ne_zero {A : Type} [AddCommGroup A] (G : MGraph V E) (f : E → A) (hf : G.IsNZFlow f)
    (i : E × Bool) : dirVal f i ≠ 0 := by
  rw [Ne, dirVal_eq_zero_iff]
  exact hf.2 i.1

/-- tex l.324: whether an edge is small does not depend on its direction. -/
theorem small_dir_indep {A : Type} [AddCommGroup A] (D : CyclicDecomp A) (f : E → A) (d : E × Bool) :
    dirVal f d ∈ D.S ↔ dirVal f (d.1, !d.2) ∈ D.S := by
  rw [Sec4.dirVal_mem_S_iff, Sec4.dirVal_mem_S_iff]

/-- tex l.323-325: every small element has exactly one color `h` (`s ∈ ⟨s_h⟩`), and `-s` has the same color. -/
theorem color_unique {A : Type} [AddCommGroup A] (D : CyclicDecomp A) (s : A) (hs : s ∈ D.S) :
    (∃! h, s ∈ AddSubgroup.zmultiples (D.s h)) ∧
      ∀ h, (s ∈ AddSubgroup.zmultiples (D.s h) ↔ -s ∈ AddSubgroup.zmultiples (D.s h)) := by
  obtain ⟨k, hk⟩ := hs
  refine ⟨⟨k, D.pm_mem hk, fun j hj => ?_⟩, fun h => neg_mem_iff.symm⟩
  by_contra hjk
  exact D.pm_ne_zero hk (D.eq_zero_of_mem_mem hjk hj (D.pm_mem hk))

/-- In `ℤ_m`, a value other than `0, 1, -1` is the residue of an integer in `{2, …, m-2}`. -/
theorem not_small_range (m : ℕ) (hm : 4 ≤ m) (x : ZMod m) (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ -1) :
    ∃ n : ℕ, 2 ≤ n ∧ n ≤ m - 2 ∧ (n : ZMod m) = x := by
  haveI : NeZero m := ⟨by omega⟩
  refine ⟨x.val, ?_, ?_, ZMod.natCast_zmod_val x⟩
  · by_contra hc
    interval_cases hv : x.val
    · exact h0 ((ZMod.val_eq_zero x).mp hv)
    · apply h1; rw [← ZMod.natCast_zmod_val x, hv]; simp
  · by_contra hc
    have hlt := ZMod.val_lt x
    have hv : x.val = m - 1 := by omega
    apply h2
    rw [← ZMod.natCast_zmod_val x, hv]
    have : ((m - 1 : ℕ) : ZMod m) = (m : ZMod m) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]; simp

/-- tex l.445-446: in `ℤ_m` (`m ≥ 4`), the value of an edge that is not small is, in each direction, the residue of an
integer in `{2, …, m-2}`. -/
theorem not_small_range_dir {m : ℕ} (hm : 4 ≤ m) (f : E → ZMod m) (d : E × Bool) (h0 : f d.1 ≠ 0)
    (h1 : f d.1 ≠ 1) (h2 : f d.1 ≠ -1) : ∃ n : ℕ, 2 ≤ n ∧ n ≤ m - 2 ∧ (n : ZMod m) = dirVal f d := by
  obtain ⟨e, b⟩ := d
  cases b
  · exact not_small_range m hm _ h0 h1 h2
  · have hneg : dirVal f (e, true) = -f e := by simp [dirVal]
    rw [hneg]
    exact not_small_range m hm _ (neg_ne_zero.mpr h0) (fun h => h2 (neg_eq_iff_eq_neg.mp h))
      (fun h => h1 (neg_inj.mp h))

end EulerFlow
