/-
EulerFlow/Sec4/Prop44.lean — Section 4 of paper 002: Lemma 4.1, Corollary 4.2, Lemma 4.3 (case choice), Prop. 4.4.
-/
import EulerFlow.Sec4.Bstar
import EulerFlow.Sec4.Decomp
import EulerFlow.Graph.Forest

namespace EulerFlow.MGraph.Sec4

open Finset

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V] {G : MGraph V E}
variable {A : Type} [AddCommGroup A]

set_option linter.unusedSectionVars false

/-! ### Lemma 4.3: choosing Case 1 or Case 2 -/

theorem lem_4_3_main [Fintype A] (D : CyclicDecomp A) (hG : G.Loopless)
    (hdeg : ∀ v, G.degree v = 0 ∨ G.degree v = 4) (f : E → A) (hf : G.IsNZFlow f)
    (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle) (hQ : ∀ d ∈ Q.darts, f d.1 ∈ D.S) :
    ∃ t : A, t ≠ 0 ∧ G.IsNZFlow (f + fun e => Q.chi e • t) ∧ G.HasBalancedPair (f + fun e => Q.chi e • t) := by
  have hss : SmallSumEq D := fun _ _ _ _ _ _ h3 h4 ha hb hij h => D.small_sum_eq h3 h4 ha hb hij h
  by_cases hcase : ∃ d ∈ Q.darts, ∃ d' ∈ Q.darts, G.dartHead d' = G.dartTail d ∧
      ∀ k : Fin D.r, ¬ ((f d.1 = D.s k ∨ f d.1 = -D.s k) ∧ (f d'.1 = D.s k ∨ f d'.1 = -D.s k))
  · obtain ⟨d, hd, d', hd', hcons, hnc⟩ := hcase
    obtain ⟨j, hj⟩ := hQ d hd
    obtain ⟨i, hi⟩ := hQ d' hd'
    have hij : i ≠ j := by
      rintro rfl
      exact hnc i ⟨hj, hi⟩
    exact case1 D hss hG hdeg hf hnb Q hQ hd hd' hcons hi hj hij
  · push Not at hcase
    obtain ⟨k, hk⟩ := hQ _ (List.head_mem Q.ne_nil)
    have hall : ∀ n (hn : n < Q.darts.length),
        f (Q.darts[n]).1 = D.s k ∨ f (Q.darts[n]).1 = -D.s k := by
      intro n
      induction n with
      | zero => intro hn; simpa [List.head_eq_getElem] using hk
      | succ n ih =>
        intro hn
        have hn' : n < Q.darts.length := by omega
        have hch := Q.chain.getElem n hn
        obtain ⟨k', hk'1, hk'2⟩ := hcase _ (List.getElem_mem hn) _ (List.getElem_mem hn') hch
        have hkk := D.colour_unique (ih hn') hk'2
        rw [hkk]; exact hk'1
    have hk' : ∀ d ∈ Q.darts, f d.1 = D.s k ∨ f d.1 = -D.s k := by
      intro d hd
      obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hd
      exact hall n hn
    exact case2 D hG hdeg hf hnb Q hk'

/-! ### Lemma 4.1 (tex l.334-346) -/

theorem dirVal_mem_S_iff (D : CyclicDecomp A) (f : E → A) (d : E × Bool) : dirVal f d ∈ D.S ↔ f d.1 ∈ D.S := by
  unfold dirVal; split_ifs
  · exact ⟨fun h => by simpa using S_neg D h, S_neg D⟩
  · exact Iff.rfl

theorem lem_4_1_main [Fintype A] (D : CyclicDecomp A) (f : E → A) (hf : G.IsNZFlow f) (Q : G.DirCycle)
    (hQ : ∀ d ∈ Q.darts, f d.1 ∉ D.S) :
    ∃ t : A, t ≠ 0 ∧ G.IsNZFlow (f + fun e => Q.chi e • t) ∧
      D.rho (f + fun e => Q.chi e • t) + 1 ≤ D.rho f := by
  classical
  set X : Set A := {x | ∃ d ∈ Q.darts, dirVal f d = x} with hX
  -- there are x ∈ X and s ∈ S with x - s ∉ X
  have hex : ∃ d ∈ Q.darts, ∃ s ∈ D.S, dirVal f d - s ∉ X := by
    by_contra hc
    push Not at hc
    have hadd : ∀ x ∈ X, ∀ s ∈ D.S, x + s ∈ X := by
      rintro x ⟨d, hd, rfl⟩ s hs
      simpa using hc d hd (-s) (S_neg D hs)
    have hcl : ∀ g ∈ AddSubmonoid.closure D.S, ∀ x ∈ X, x + g ∈ X := by
      intro g hg
      induction hg using AddSubmonoid.closure_induction with
      | mem s hs => exact fun x hx => hadd x hx s hs
      | zero => exact fun x hx => by simpa using hx
      | add g h _ _ ihg ihh => exact fun x hx => by simpa [add_assoc] using ihh _ (ihg x hx)
    have htop : ∀ g : A, g ∈ AddSubmonoid.closure D.S := by
      intro g
      have h1 : g ∈ (AddSubgroup.closure D.S : Set A) := by
        rw [(sec4_S_props_proved D).2.2]; trivial
      rw [D.closure_S_eq_closure_submonoid] at h1
      exact h1
    have hx0 : dirVal f (Q.darts.head Q.ne_nil) ∈ X := ⟨_, List.head_mem _, rfl⟩
    obtain ⟨d, _, hd0⟩ := hcl _ (htop (-dirVal f (Q.darts.head Q.ne_nil))) _ hx0
    rw [add_neg_cancel, dirVal_eq_zero_iff] at hd0
    exact hf.2 _ hd0
  obtain ⟨d₀, hd₀, s, hs, hxs⟩ := hex
  set t := s - dirVal f d₀ with ht
  have hxS : dirVal f d₀ ∉ D.S := by rw [dirVal_mem_S_iff]; exact hQ d₀ hd₀
  have ht0 : t ≠ 0 := by
    intro h0; rw [ht, sub_eq_zero] at h0; exact hxS (h0 ▸ hs)
  have hnz : G.IsNZFlow (f + fun e => Q.chi e • t) := by
    rw [isNZFlow_step_iff hf]
    intro d hd h0
    apply hxs
    refine ⟨d, hd, ?_⟩
    rw [ht] at h0
    rw [← sub_eq_zero, ← h0]; abel
  refine ⟨t, ht0, hnz, ?_⟩
  -- the non-small edges after the step: inside the old ones, minus the edge of d₀
  have hsub : {e | (f + fun e => Q.chi e • t) e ∉ D.S} ⊆ {e | f e ∉ D.S} \ {d₀.1} := by
    intro e he
    simp only [Set.mem_setOf_eq] at he
    by_cases hon : ∃ d ∈ Q.darts, d.1 = e
    · obtain ⟨d, hd, rfl⟩ := hon
      refine ⟨hQ d hd, ?_⟩
      intro hmem
      have hdd : d = d₀ := Q.eq_of_fst_eq hd hd₀ hmem
      subst hdd
      apply he
      rw [← dirVal_mem_S_iff, Q.dirVal_step_mem f t hd, ht]
      simpa using hs
    · push Not at hon
      have h0 := Q.chi_eq_zero hon
      refine ⟨by simpa [h0] using he, ?_⟩
      intro hmem
      exact hon d₀ hd₀ (Set.mem_singleton_iff.mp hmem).symm
  have hmem : d₀.1 ∈ {e | f e ∉ D.S} := hQ d₀ hd₀
  unfold CyclicDecomp.rho
  calc Set.ncard {e | (f + fun e => Q.chi e • t) e ∉ D.S} + 1
      ≤ Set.ncard ({e | f e ∉ D.S} \ {d₀.1}) + 1 := by
        have := Set.ncard_le_ncard hsub (Set.toFinite _); omega
    _ = Set.ncard {e | f e ∉ D.S} := Set.ncard_sdiff_singleton_add_one hmem

/-! ### Corollary 4.2 (tex l.348-355) -/

theorem flowGraph_adj_of_step {f f' : {f : E → A // G.IsNZFlow f}} (Q : G.DirCycle) (t : A) (ht : t ≠ 0)
    (hne : f ≠ f') (h : f'.1 = f.1 + fun e => Q.chi e • t) : (G.flowGraph A).Adj f f' :=
  (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl ⟨Q, t, ht, ht, h⟩⟩

theorem cor_4_2_main [Fintype A] (D : CyclicDecomp A) (f : {f : E → A // G.IsNZFlow f}) :
    ∃ f' : {f : E → A // G.IsNZFlow f}, (∃ w : (G.flowGraph A).Walk f f', w.length ≤ D.rho f.1) ∧
      ∀ Q : G.DirCycle, ∃ d ∈ Q.darts, f'.1 d.1 ∈ D.S := by
  induction hn : D.rho f.1 using Nat.strong_induction_on generalizing f with
  | _ n ih =>
    by_cases hacyc : ∀ Q : G.DirCycle, ∃ d ∈ Q.darts, f.1 d.1 ∈ D.S
    · exact ⟨f, ⟨SimpleGraph.Walk.nil, by simp⟩, hacyc⟩
    · push Not at hacyc
      obtain ⟨Q, hQ⟩ := hacyc
      obtain ⟨t, ht0, hnz, hrho⟩ := lem_4_1_main D f.1 f.2 Q hQ
      have hlt : D.rho (f.1 + fun e => Q.chi e • t) < n := by omega
      obtain ⟨f', ⟨w, hw⟩, hf'⟩ := ih _ hlt ⟨_, hnz⟩ rfl
      have hne : f ≠ ⟨_, hnz⟩ := by
        intro h
        have := congrArg (fun g : {f : E → A // G.IsNZFlow f} => D.rho g.1) h
        simp only at this
        omega
      exact ⟨f', ⟨SimpleGraph.Walk.cons (flowGraph_adj_of_step Q t ht0 hne rfl) w, by simp; omega⟩, hf'⟩

/-! ### Proposition 4.4 (tex l.391-402) -/

/-- The degrees sum to twice the number of edges. -/
theorem sum_degree : ∑ v, G.degree v = 2 * Fintype.card E := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (E × Bool))) (t := (univ : Finset V))
    (f := G.endVertex) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool] at h
  unfold degree
  rw [← h]; ring

theorem prop_4_4_main [Fintype A] (D : CyclicDecomp A) (hE : Nonempty E) (hG : G.Loopless)
    (hdeg : ∀ v, G.degree v = 0 ∨ G.degree v = 4) (f : {f : E → A // G.IsNZFlow f}) :
    ∃ f' : {f : E → A // G.IsNZFlow f}, G.HasBalancedPair f'.1 ∧
      ∃ w : (G.flowGraph A).Walk f f', w.length ≤ D.rho f.1 + 1 := by
  classical
  obtain ⟨fs, ⟨w, hw⟩, hfs⟩ := cor_4_2_main D f
  by_cases hb : G.HasBalancedPair fs.1
  · exact ⟨fs, hb, w, by omega⟩
  -- the n vertices of degree 4 carry 2n edges; at most n - 1 are not small
  set W := univ.filter (fun v => G.degree v = 4) with hW
  have hend_deg : ∀ e, G.degree (G.src e) = 4 ∧ G.degree (G.tgt e) = 4 := by
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
  have hcardE : Fintype.card E = 2 * W.card := by
    have h := sum_degree (G := G)
    have : ∑ v, G.degree v = ∑ v ∈ W, 4 := by
      rw [hW, Finset.sum_filter]; congr 1; ext v; rcases hdeg v with h | h <;> simp [h]
    rw [this, Finset.sum_const, smul_eq_mul] at h; omega
  set Sn := univ.filter (fun e => fs.1 e ∉ D.S)
  set Ss := univ.filter (fun e => fs.1 e ∈ D.S)
  have hSn : Sn.card < W.card := card_lt_of_acyclic Sn W hWne (hend Sn) (by
    intro Q hQ
    obtain ⟨d, hd, hds⟩ := hfs Q
    have := hQ d hd
    simp [Sn] at this
    exact this hds)
  have hsplit : Sn.card + Ss.card = Fintype.card E := by
    rw [add_comm, Finset.card_filter_add_card_filter_not]; rfl
  have hSsne : Ss.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨Q, hQ⟩ := exists_dirCycle_of_card_le Ss W hSsne (hend Ss) (by omega)
  have hQs : ∀ d ∈ Q.darts, fs.1 d.1 ∈ D.S := fun d hd => by simpa [Ss] using hQ d hd
  have hdeg' : ∀ v, G.degree v = 0 ∨ G.degree v = 4 := hdeg
  obtain ⟨t, ht0, hnz, hbal⟩ := lem_4_3_main D hG hdeg' fs.1 fs.2 hb Q hQs
  set f' : {f : E → A // G.IsNZFlow f} := ⟨_, hnz⟩
  have hne : fs ≠ f' := by
    intro h
    apply hb
    have : fs.1 = f'.1 := congrArg Subtype.val h
    rw [this]; exact hbal
  exact ⟨f', hbal, w.append (SimpleGraph.Walk.cons (flowGraph_adj_of_step Q t ht0 hne rfl) .nil),
    by simp; omega⟩

end EulerFlow.MGraph.Sec4
