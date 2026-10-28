/-
EulerFlow/Sec9/Local.lean — Lemma 9.5 (tex l.788-820) for (p,q)-flows; Lemma 6.2 is its case q = 1.
Also: a chain of steps along Q gives reachability in the step graph.
-/
import EulerFlow.Sec4.Prop44
import EulerFlow.Sec6.Acyc

namespace EulerFlow.MGraph.Sec9

open Finset

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V] {G : MGraph V E}

set_option linter.unusedSectionVars false

/-! ### Steps along `Q` give reachability -/

theorem smul_chi_add {A : Type} [AddCommGroup A] (Q : G.DirCycle) (f : E → A) (a b : A) :
    (f + fun e => Q.chi e • (a + b)) = (f + fun e => Q.chi e • a) + fun e => Q.chi e • b := by
  funext e; simp [smul_add, add_assoc]

theorem stepGraph_reachable_step {A : Type} [AddCommGroup A] {I T : Set A} (Q : G.DirCycle) (t : A)
    (htT : t ∈ T) (ht0 : t ≠ 0) (g g' : {f : E → A // G.IsIFlow I f})
    (h : g'.1 = g.1 + fun e => Q.chi e • t) : (G.stepGraph I T).Reachable g g' := by
  by_cases hgg : g = g'
  · rw [hgg]
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hgg, Or.inl ⟨Q, t, htT, ht0, h⟩⟩)

theorem add_zero_fun {A : Type} [AddCommGroup A] (f : E → A) : (f + fun _ => (0 : A)) = f := by
  funext e; simp

/-- A chain of steps along `Q` (`StepsAlong`) joins its two ends in the step graph. -/
theorem reachable_of_stepsAlong {A : Type} [AddCommGroup A] {I T : Set A} (Q : G.DirCycle) (f : E → A)
    (ts : List A) (h : G.StepsAlong I T Q f ts) (hf : G.IsIFlow I f)
    (hf' : G.IsIFlow I (f + fun e => Q.chi e • ts.sum)) :
    (G.stepGraph I T).Reachable ⟨f, hf⟩ ⟨_, hf'⟩ := by
  have key : ∀ j (hj : j ≤ ts.length), (G.stepGraph I T).Reachable ⟨f, hf⟩ ⟨_, h.2 j hj⟩ := by
    intro j
    induction j with
    | zero =>
      intro hj
      have e0 : (⟨_, h.2 0 hj⟩ : {f : E → A // G.IsIFlow I f}) = ⟨f, hf⟩ :=
        Subtype.ext (by simp only [List.take_zero, List.sum_nil, smul_zero]; exact add_zero_fun f)
      rw [e0]
    | succ j ih =>
      intro hj
      have hjl : j < ts.length := hj
      refine (ih (by omega)).trans (stepGraph_reachable_step Q ts[j] (h.1 _ (List.getElem_mem hjl)).1
        (h.1 _ (List.getElem_mem hjl)).2 _ _ ?_)
      simp only
      rw [List.take_succ, List.getElem?_eq_getElem hjl, Option.toList_some, List.sum_append, List.sum_singleton,
        smul_chi_add]
  have e1 : (⟨_, h.2 ts.length le_rfl⟩ : {f : E → A // G.IsIFlow I f}) = ⟨_, hf'⟩ :=
    Subtype.ext (by simp only [List.take_length])
  rw [← e1]; exact key _ le_rfl

/-! ### Small facts on `ZMod p` for `p ≥ 4q` -/

theorem q_ne_neg_q {p q : ℕ} (hq : 1 ≤ q) (hpq : 2 * q < p) : (q : ZMod p) ≠ -(q : ZMod p) := by
  intro h
  have h2 : ((2 * q : ℕ) : ZMod p) = 0 := by push_cast; rw [two_mul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)

/-- `y ∈ {q, -q}` shifted by `J ∈ [2q, p - 2q]` stays in `I(p,q)` (tex l.805-807). -/
theorem mem_Ipq_shift {p q : ℕ} (hq : 1 ≤ q) (hpq : 4 * q ≤ p) {y : ZMod p} (hy : y = q ∨ y = -(q : ZMod p))
    {J : ℕ} (hJ1 : 2 * q ≤ J) (hJ2 : J ≤ p - 2 * q) : y + (J : ZMod p) ∈ Ipq p q := by
  rcases hy with rfl | rfl
  · exact ⟨q + J, by omega, by omega, by push_cast; ring⟩
  · refine ⟨J - q, by omega, by omega, ?_⟩
    rw [Nat.cast_sub (by omega)]; ring

/-- For `J ∈ [2q, p - 2q]`, the step `f + J χ_Q` of a `(p,q)`-flow whose edges on `Q` are small is a `(p,q)`-flow. -/
theorem isIFlow_shift {p q : ℕ} (hq : 1 ≤ q) (hpq : 4 * q ≤ p) {f : E → ZMod p} (hf : G.IsIFlow (Ipq p q) f)
    (Q : G.DirCycle) (hQ : ∀ d ∈ Q.darts, f d.1 = q ∨ f d.1 = -(q : ZMod p)) {J : ℕ} (hJ1 : 2 * q ≤ J)
    (hJ2 : J ≤ p - 2 * q) : G.IsIFlow (Ipq p q) (f + fun e => Q.chi e • (J : ZMod p)) := by
  have hneg : ∀ y ∈ Ipq p q, -y ∈ Ipq p q := fun y hy => neg_mem_Ipq (by omega) hy
  refine ⟨isFlow_add_chi_smul hf.1 Q _, fun e => ?_⟩
  by_cases hon : ∃ d ∈ Q.darts, d.1 = e
  · obtain ⟨d, hd, rfl⟩ := hon
    apply mem_of_dirVal_mem hneg
    rw [Q.dirVal_step_mem f _ hd]
    exact mem_Ipq_shift hq hpq (Sec4.pm_dirVal f d (hQ d hd)) hJ1 hJ2
  · push Not at hon
    rw [step_off Q f _ hon]; exact hf.2 e

/-! ### Lemma 9.5 -/

theorem lem_9_5_a_main (p q : ℕ) (hq : 1 ≤ q) (hpq : 4 * q ≤ p) (f : E → ZMod p)
    (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle)
    (hQ : ∀ d ∈ Q.darts, f d.1 = q ∨ f d.1 = -(q : ZMod p)) (v : V) (d d' : E × Bool) (hd : d ∈ Q.darts)
    (hd' : d' ∈ Q.darts) (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) :
    dirVal f d = dirVal f (d'.1, !d'.2) ∧ (dirVal f d = q ∨ dirVal f d = -(q : ZMod p)) := by
  have hqq := q_ne_neg_q (p := p) hq (by omega)
  have h2 := Sec4.pm_dirVal f d (hQ d hd)
  have h1 : dirVal f (d'.1, !d'.2) = q ∨ dirVal f (d'.1, !d'.2) = -(q : ZMod p) := by
    rw [dirVal_flip]; rcases Sec4.pm_dirVal f d' (hQ d' hd') with h | h <;> simp [h]
  have h0 : dirVal f (d'.1, !d'.2) + dirVal f d ≠ 0 := by
    intro h0
    have he1 : G.endVertex (d'.1, !d'.2) = v := by rw [endVertex_flip]; exact hd'v
    have h12 : (d'.1, !d'.2) ≠ d := by intro h; exact Q.flip_not_mem hd' (h ▸ hd)
    exact hnb ⟨v, _, _, h12, he1, hdv, h0⟩
  refine ⟨?_, h2⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · rw [h1, h2]
  · exact absurd (by rw [h1, h2, add_neg_cancel]) h0
  · exact absurd (by rw [h1, h2, neg_add_cancel]) h0
  · rw [h1, h2]

theorem lem_9_5_b_main (p q : ℕ) (hq : 1 ≤ q) (hpq : 4 * q ≤ p) (f : E → ZMod p)
    (hf : G.IsIFlow (Ipq p q) f) (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle)
    (hQ : ∀ d ∈ Q.darts, f d.1 = q ∨ f d.1 = -(q : ZMod p)) (v : V) (d d' : E × Bool) (hd : d ∈ Q.darts)
    (hd' : d' ∈ Q.darts) (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) (i : E × Bool)
    (hiv : G.endVertex i = v) (hid : i ≠ d) (hid' : i ≠ (d'.1, !d'.2))
    (hJ : dirVal f d + dirVal f i ∈ Jpq p q) :
    ∃ ts : List (ZMod p), G.StepsAlong (Ipq p q) (Tpq p q) Q f ts ∧
      G.HasBalancedPairAt (f + fun e => Q.chi e • ts.sum) v := by
  obtain ⟨τ, hτ1, hτ2, hτ⟩ := hJ
  have ha := lem_9_5_a_main p q hq hpq f hnb Q hQ v d d' hd hd' hdv hd'v
  refine ⟨((2 * q : ℕ) : ZMod p) :: List.replicate (τ - 2 * q) 1, ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.mem_replicate] at ht
    rcases ht with rfl | ⟨-, rfl⟩
    · refine ⟨by simp [Tpq], ?_⟩
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hdvd => absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
    · refine ⟨by simp [Tpq], ?_⟩
      have : Fact (1 < p) := ⟨by omega⟩
      exact one_ne_zero
  · intro j hj
    rcases j with _ | j
    · simp only [List.take_zero, List.sum_nil, smul_zero]; rw [add_zero_fun]; exact hf
    · have hsum : ((((2 * q : ℕ) : ZMod p) :: List.replicate (τ - 2 * q) 1).take (j + 1)).sum =
          ((2 * q + min j (τ - 2 * q) : ℕ) : ZMod p) := by
        simp [List.take_succ_cons, List.take_replicate, List.sum_replicate]
      rw [hsum]
      simp only [List.length_cons, List.length_replicate] at hj
      exact isIFlow_shift hq hpq hf Q hQ (by omega) (by omega)
  · have hsum : (((2 * q : ℕ) : ZMod p) :: List.replicate (τ - 2 * q) 1).sum = (τ : ZMod p) := by
      simp only [List.sum_cons, List.sum_replicate, nsmul_eq_mul, mul_one]
      rw [← Nat.cast_add, Nat.add_sub_cancel' hτ1]
    rw [hsum, hτ]
    have hoff := Q.other_end_not_mem hd hd' hdv hd'v hiv hid hid'
    refine ⟨(d'.1, !d'.2), i, Ne.symm hid', by rw [endVertex_flip]; exact hd'v, hiv, ?_⟩
    rw [Q.dirVal_step_flip f _ hd', Q.dirVal_step_off f _ hoff.1 hoff.2, ← ha.1]
    abel

theorem lem_9_5_c_main (p q : ℕ) (hq : 1 ≤ q) (hpq : 4 * q ≤ p) (f : E → ZMod p)
    (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle)
    (hQ : ∀ d ∈ Q.darts, f d.1 = q ∨ f d.1 = -(q : ZMod p)) (v : V) (d : E × Bool) (hd : d ∈ Q.darts)
    (hdv : G.dartTail d = v) (i : E × Bool) (hiv : G.endVertex i = v) (hid : i ≠ d)
    (hJ : dirVal f d + dirVal f i ∉ Jpq p q) :
    dirVal f i ≠ q ∧ dirVal f i ≠ -(q : ZMod p) := by
  have hbal : dirVal f d + dirVal f i ≠ 0 := fun h0 => hnb ⟨v, d, i, Ne.symm hid, hdv, hiv, h0⟩
  have h2q : ((2 * q : ℕ) : ZMod p) ∈ Jpq p q := ⟨2 * q, le_rfl, by omega, rfl⟩
  have hm2q : -((2 * q : ℕ) : ZMod p) ∈ Jpq p q := by
    refine ⟨p - 2 * q, by omega, le_rfl, ?_⟩
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
  rcases Sec4.pm_dirVal f d (hQ d hd) with ha | ha <;> rw [ha] at hJ hbal <;> constructor <;> intro hc <;>
    rw [hc] at hJ hbal
  · exact hJ (by push_cast; ring_nf; simpa [two_mul, mul_comm] using h2q)
  · exact hbal (add_neg_cancel _)
  · exact hbal (neg_add_cancel _)
  · exact hJ (by push_cast; ring_nf; simpa [two_mul, mul_comm, neg_add] using hm2q)

end EulerFlow.MGraph.Sec9
