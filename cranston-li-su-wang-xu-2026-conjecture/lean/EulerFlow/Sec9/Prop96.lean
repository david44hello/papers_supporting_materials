/-
EulerFlow/Sec9/Prop96.lean — Proposition 9.6 (tex l.822-837): every (p,q)-flow of an even loopless graph with all
degrees 0 or ≥ 4 is T-joined to a (p,q)-flow with a balanced pair (p ≥ 4q). Proposition 6.3 is its case q = 1.
-/
import EulerFlow.Sec9.Local

namespace EulerFlow.MGraph.Sec9

open Finset

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V] {G : MGraph V E}

set_option linter.unusedSectionVars false

/-- By Lemma 9.4, used as long as the edges that are not small contain a cycle (tex l.828-829). -/
theorem forest_reach (p q : ℕ) (hq : 1 ≤ q) (hpq : 4 * q ≤ p) (f : {f : E → ZMod p // G.IsIFlow (Ipq p q) f}) :
    ∃ f' : {f : E → ZMod p // G.IsIFlow (Ipq p q) f}, (G.stepGraph (Ipq p q) (Tpq p q)).Reachable f f' ∧
      ∀ Q : G.DirCycle, ∃ d ∈ Q.darts, f'.1 d.1 = q ∨ f'.1 d.1 = -(q : ZMod p) := by
  induction hn : rhoPQ q f.1 using Nat.strong_induction_on generalizing f with
  | _ n ih =>
    by_cases hacyc : ∀ Q : G.DirCycle, ∃ d ∈ Q.darts, f.1 d.1 = q ∨ f.1 d.1 = -(q : ZMod p)
    · exact ⟨f, SimpleGraph.Reachable.refl _, hacyc⟩
    · push Not at hacyc
      obtain ⟨Q, hQ⟩ := hacyc
      obtain ⟨ts, -, hsteps, hrho⟩ := lem_9_4_proved p q hq (by omega) G f.1 f.2 Q hQ
      have hf1 : G.IsIFlow (Ipq p q) (f.1 + fun e => Q.chi e • ts.sum) := by
        simpa [List.take_length] using hsteps.2 ts.length le_rfl
      have hreach := reachable_of_stepsAlong Q f.1 ts hsteps f.2 hf1
      obtain ⟨f', h', hf'⟩ := ih (rhoPQ q (f.1 + fun e => Q.chi e • ts.sum)) (by omega) ⟨_, hf1⟩ rfl
      exact ⟨f', hreach.trans h', hf'⟩

theorem prop_9_6_main (p q : ℕ) (hq : 1 ≤ q) (hpq : 4 * q ≤ p) (G : MGraph V E) (hE : Nonempty E)
    (hG : G.Loopless) (hdeg : ∀ v, G.degree v = 0 ∨ 4 ≤ G.degree v)
    (f : {f : E → ZMod p // G.IsIFlow (Ipq p q) f}) :
    ∃ f' : {f : E → ZMod p // G.IsIFlow (Ipq p q) f}, G.HasBalancedPair f'.1 ∧
      (G.stepGraph (Ipq p q) (Tpq p q)).Reachable f f' := by
  classical
  obtain ⟨fs, hreach, hfs⟩ := forest_reach p q hq hpq f
  by_cases hb : G.HasBalancedPair fs.1
  · exact ⟨fs, hb, hreach⟩
  by_cases hloc : ∃ Q : G.DirCycle, (∀ d ∈ Q.darts, fs.1 d.1 = q ∨ fs.1 d.1 = -(q : ZMod p)) ∧
      ∃ d ∈ Q.darts, ∃ d' ∈ Q.darts, G.dartHead d' = G.dartTail d ∧ ∃ i : E × Bool,
        G.endVertex i = G.dartTail d ∧ i ≠ d ∧ i ≠ (d'.1, !d'.2) ∧ dirVal fs.1 d + dirVal fs.1 i ∈ Jpq p q
  · -- Lemma 9.5 (b) applies
    obtain ⟨Q, hQ, d, hd, d', hd', hcons, i, hiv, hid, hid', hJ⟩ := hloc
    obtain ⟨ts, hsteps, hbal⟩ := lem_9_5_b_main p q hq hpq fs.1 fs.2 hb Q hQ _ d d' hd hd' rfl hcons i hiv
      hid hid' hJ
    have hf1 : G.IsIFlow (Ipq p q) (fs.1 + fun e => Q.chi e • ts.sum) := by
      simpa [List.take_length] using hsteps.2 ts.length le_rfl
    exact ⟨⟨_, hf1⟩, ⟨_, hbal⟩, hreach.trans (reachable_of_stepsAlong Q fs.1 ts hsteps fs.2 hf1)⟩
  · -- otherwise every vertex of a cycle of small edges has exactly two small ends: count (tex l.830-836)
    exfalso
    push Not at hloc
    set W := univ.filter (fun v => 4 ≤ G.degree v) with hW
    have hend_deg : ∀ e, 4 ≤ G.degree (G.src e) ∧ 4 ≤ G.degree (G.tgt e) := by
      intro e
      have hpos : ∀ i : E × Bool, 0 < G.degree (G.endVertex i) := fun i =>
        Finset.card_pos.mpr ⟨i, by simp⟩
      have h1 := hpos (e, false)
      have h2 := hpos (e, true)
      simp only [endVertex, Bool.false_eq_true, ite_false, ite_true] at h1 h2
      refine ⟨?_, ?_⟩
      · rcases hdeg (G.src e) with h | h <;> omega
      · rcases hdeg (G.tgt e) with h | h <;> omega
    have hend : ∀ (S : Finset E), ∀ e ∈ S, G.src e ∈ W ∧ G.tgt e ∈ W := fun S e _ => by
      simp [hW, (hend_deg e).1, (hend_deg e).2]
    have hWne : W.Nonempty := by
      obtain ⟨e⟩ := hE; exact ⟨G.src e, by simp [hW, (hend_deg e).1]⟩
    have hcardE : 2 * W.card ≤ Fintype.card E := by
      have h := Sec4.sum_degree (G := G)
      have : ∑ v ∈ W, 4 ≤ ∑ v, G.degree v := by
        calc ∑ v ∈ W, 4 ≤ ∑ v ∈ W, G.degree v := Finset.sum_le_sum (fun v hv => by simpa [hW] using hv)
          _ ≤ ∑ v, G.degree v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      rw [Finset.sum_const, smul_eq_mul] at this; omega
    set Ss := univ.filter (fun e => fs.1 e = q ∨ fs.1 e = -(q : ZMod p)) with hSs
    set Sn := univ.filter (fun e => ¬ (fs.1 e = q ∨ fs.1 e = -(q : ZMod p))) with hSn
    have hSnlt : Sn.card < W.card := card_lt_of_acyclic Sn W hWne (hend Sn) (by
      intro Q hQ
      obtain ⟨d, hd, hds⟩ := hfs Q
      have := hQ d hd
      simp [hSn] at this
      rcases hds with h | h
      · exact this.1 h
      · exact this.2 h)
    have hSsle : Ss.card ≤ W.card := card_le_of_cycle_ends_two Ss W (hend Ss) (by
      intro Q hQ d hd
      have hQs : ∀ d ∈ Q.darts, fs.1 d.1 = q ∨ fs.1 d.1 = -(q : ZMod p) := fun d hd => by
        simpa [hSs] using hQ d hd
      obtain ⟨d', hd', hcons⟩ := Q.exists_enter hd
      have h12 : d ≠ (d'.1, !d'.2) := by intro h; exact Q.flip_not_mem hd' (h ▸ hd)
      have hset : (univ.filter fun i : E × Bool => i.1 ∈ Ss ∧ G.endVertex i = G.dartTail d) =
          {d, (d'.1, !d'.2)} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨his, hiv⟩
          by_contra hne
          push Not at hne
          have hJ := hloc Q hQs d hd d' hd' hcons i hiv hne.1 hne.2
          have hc := lem_9_5_c_main p q hq hpq fs.1 hb Q hQs _ d hd rfl i hiv hne.1 hJ
          have hsm : fs.1 i.1 = q ∨ fs.1 i.1 = -(q : ZMod p) := by simpa [hSs] using his
          rcases Sec4.pm_dirVal fs.1 i hsm with h | h
          · exact hc.1 h
          · exact hc.2 h
        · rintro (rfl | rfl)
          · exact ⟨hQ _ hd, rfl⟩
          · exact ⟨hQ d' hd', by rw [endVertex_flip]; exact hcons⟩
      rw [hset, Finset.card_pair h12])
    have hsplit : Ss.card + Sn.card = Fintype.card E := by
      rw [hSs, hSn, Finset.card_filter_add_card_filter_not]; rfl
    omega

/-- Proposition 9.6 with the value set and the step set given by equations (so that `q = 1` can be read with
`{x | x ≠ 0}` and `Tcyc`). -/
theorem prop_9_6_gen (p q : ℕ) (hq : 1 ≤ q) (hpq : 4 * q ≤ p) (I T : Set (ZMod p)) (hI : I = Ipq p q)
    (hT : T = Tpq p q) (G : MGraph V E) (hE : Nonempty E) (hG : G.Loopless)
    (hdeg : ∀ v, G.degree v = 0 ∨ 4 ≤ G.degree v) (f : {f : E → ZMod p // G.IsIFlow I f}) :
    ∃ f' : {f : E → ZMod p // G.IsIFlow I f}, G.HasBalancedPair f'.1 ∧ (G.stepGraph I T).Reachable f f' := by
  subst hI hT
  exact prop_9_6_main p q hq hpq G hE hG hdeg f

end EulerFlow.MGraph.Sec9
