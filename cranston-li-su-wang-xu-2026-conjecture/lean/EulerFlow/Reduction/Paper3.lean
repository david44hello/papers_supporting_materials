/-
EulerFlow/Reduction/Paper3.lean — the Section 3 claims of paper 002 in exactly the Statements types: (T1)/(T2)
for `A ∖ {0}` and for `{±1, ±2}` (tex l.219-220), Lemma 3.1, Proposition 3.4; and Lemma 9.3 (tex l.735-769) as
the instance of the same engine for `(p,q)`-flows, with the Section 9 facts on `I` and `T` as hypotheses
(they are the claims `sec9_I_props`, `sec9_T_props`).
-/
import EulerFlow.Reduction.Reduce

namespace EulerFlow

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Section 3 (tex l.219): (T1) and (T2) hold for `T = A ∖ {0}`, exactly the Statements type. -/
theorem sec3_T_nonzero_proved (A : Type) [AddCommGroup A] [Nontrivial A] :
    CondT1 ({x | x ≠ 0} : Set A) ∧ CondT2 ({x | x ≠ 0} : Set A) := by
  refine ⟨fun a b _ hb => ?_, ?_⟩
  · by_cases hab : a = b
    · subst hab; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hb, sub_ne_zero.2 (Ne.symm hab)⟩
  · obtain ⟨a, ha⟩ := exists_ne (0 : A)
    by_cases h2 : 2 • a = 0
    · exact ⟨a, ha, Or.inl h2⟩
    · exact ⟨a, ha, Or.inr h2⟩

/-- Section 3 (tex l.219-220): (T1) and (T2) hold for `ℤ_m`, `m ≥ 3`, `T = {1, -1, 2, -2}` (the chain
`1, 2, …, m-1`, and `a = 1`), exactly the Statements type. -/
theorem sec3_T_cyc_proved (m : ℕ) (hm : 3 ≤ m) :
    CondT1 (Tcyc m) ∧ CondT2 (Tcyc m) ∧ (0 : ZMod m) ∉ Tcyc m ∧ ∀ t ∈ Tcyc m, -t ∈ Tcyc m := by
  have : NeZero m := ⟨by omega⟩
  have : Fact (1 < m) := ⟨by omega⟩
  have hI : ∀ n, 1 ≤ n → n ≤ m - 1 → (n : ZMod m) ∈ ({x | x ≠ 0} : Set (ZMod m)) := by
    intro n h1 h2 h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact absurd (Nat.le_of_dvd (by omega) h0) (by omega)
  have hval : ∀ a : ZMod m, a ≠ 0 → 1 ≤ a.val ∧ a.val ≤ m - 1 := by
    intro a ha
    have h1 : a.val ≠ 0 := fun h => ha ((ZMod.val_eq_zero a).1 h)
    have h2 := ZMod.val_lt a
    omega
  have h2 : (2 : ZMod m) ≠ 0 := by
    have := hI 2 (by norm_num) (by omega)
    simpa using this
  refine ⟨fun a b ha hb => ?_, ⟨1, one_ne_zero, Or.inr (by simp [Tcyc])⟩, ?_, ?_⟩
  · have := zmod_chain (I := {x | x ≠ 0}) (T := Tcyc m) (by simp [Tcyc]) (by simp [Tcyc]) hI (hval a ha) (hval b hb)
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
  · simp only [Tcyc, Set.mem_insert_iff, Set.mem_singleton_iff, not_or, zero_eq_neg]
    exact ⟨(one_ne_zero).symm, one_ne_zero, h2.symm, h2⟩
  · intro t ht
    simp only [Tcyc, Set.mem_insert_iff, Set.mem_singleton_iff] at ht ⊢
    rcases ht with rfl | rfl | rfl | rfl <;> simp

omit [Fintype V] in
/-- Lemma 3.1 (loops, tex l.222-232), exactly the Statements type. -/
theorem lem_3_1_proved {A : Type} [AddCommGroup A] (T : Set A) (hT0 : (0 : A) ∉ T) (_hTneg : ∀ t ∈ T, -t ∈ T)
    (hT1 : CondT1 T) (G : MGraph V E) (l : E) (hl : G.IsLoop l)
    (h : ((G.deleteEdge l).tStepGraph T).Preconnected) : (G.tStepGraph T).Preconnected :=
  loop_preconnected (I := {x | x ≠ 0}) hT0 hT1 hl h

/-- Proposition 3.4 (the reduction, tex l.294-319), exactly the Statements type. -/
theorem prop_3_4_proved {A : Type} [AddCommGroup A] (T : Set A) (hT0 : (0 : A) ∉ T) (hTneg : ∀ t ∈ T, -t ∈ T)
    (hT1 : CondT1 T) (hT2 : CondT2 T)
    (𝒢 : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E], MGraph V E → Prop)
    (h_even : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      𝒢 V E G → G.IsEven)
    (h_loop : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E) (l : E),
      𝒢 V E G → G.IsLoop l → 𝒢 V {x : E // x ≠ l} (G.deleteEdge l))
    (h_split : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E)
      (v : V) (e e' : E), 𝒢 V E G → G.Loopless → e ≠ e' → G.IsAt e v → G.IsAt e' v →
      𝒢 V (Option {x : E // x ≠ e ∧ x ≠ e'}) (G.splitOff v e e'))
    (h_local : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      𝒢 V E G → Nonempty E → G.Loopless → (∀ v, G.degree v = 0 ∨ 4 ≤ G.degree v) →
      ∀ f : {f : E → A // G.IsNZFlow f}, ∃ f' : {f : E → A // G.IsNZFlow f},
        G.HasBalancedPair f'.1 ∧ (G.tStepGraph T).Reachable f f')
    (G : MGraph V E) (hG : 𝒢 V E G) : (G.tStepGraph T).Preconnected := by
  obtain ⟨a, ha, h2a⟩ := hT2
  exact reduction_preconnected (I := {x | x ≠ 0}) nonzero_neg hT0 hTneg hT1 ⟨a, ha, h2a⟩ 𝒢 h_even h_loop h_split
    h_local V E G hG

/-- (T1) for `(p,q)`-flows (tex l.752-753): the chain `q, q+1, …, p-q` joins any two elements of `I` inside `I`
with differences `1` or `-1`. -/
theorem ipq_chain (p q : ℕ) (a b : ZMod p) (ha : a ∈ Ipq p q) (hb : b ∈ Ipq p q) :
    Relation.ReflTransGen (fun x y : ZMod p => y ∈ Ipq p q ∧ y - x ∈ Tpq p q) a b := by
  obtain ⟨n₁, h₁, h₁', rfl⟩ := ha
  obtain ⟨n₂, h₂, h₂', rfl⟩ := hb
  exact zmod_chain (I := Ipq p q) (T := Tpq p q) (by simp [Tpq]) (by simp [Tpq]) (fun n h h' => ⟨n, h, h', rfl⟩)
    ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩

/-- Lemma 9.3 (the reduction for `(p,q)`-flows, tex l.735-769): Proposition 3.4 for the class of all even graphs
with `(p,q)`-flows in the place of flows. The facts on `I` and `T` used (tex l.745-747) are the hypotheses
`hI, hT0, hTneg, hqI, h2q` = the claims `sec9_I_props`, `sec9_T_props`. -/
theorem lem_9_3_of (p q : ℕ) (hI : ∀ x ∈ Ipq p q, -x ∈ Ipq p q) (hT0 : (0 : ZMod p) ∉ Tpq p q)
    (hTneg : ∀ t ∈ Tpq p q, -t ∈ Tpq p q) (hqI : (q : ZMod p) ∈ Ipq p q) (h2q : 2 • (q : ZMod p) ∈ Tpq p q)
    (h_local : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      G.IsEven → Nonempty E → G.Loopless → (∀ v, G.degree v = 0 ∨ 4 ≤ G.degree v) →
      ∀ f : {f : E → ZMod p // G.IsIFlow (Ipq p q) f}, ∃ f' : {f : E → ZMod p // G.IsIFlow (Ipq p q) f},
        G.HasBalancedPair f'.1 ∧ (G.stepGraph (Ipq p q) (Tpq p q)).Reachable f f')
    (G : MGraph V E) (hev : G.IsEven) : (G.stepGraph (Ipq p q) (Tpq p q)).Preconnected :=
  reduction_preconnected hI hT0 hTneg (ipq_chain p q) ⟨q, hqI, Or.inr h2q⟩
    (fun _ _ _ _ _ _ G => G.IsEven) (fun _ _ _ _ _ _ _ hG => hG)
    (fun _ _ _ _ _ _ _ _ hG hl => isEven_deleteEdge hl hG)
    (fun _ _ _ _ _ _ _ _ _ _ hG hGl hne he he' => isEven_splitOff (SplitData.of hGl hne he he') hG)
    h_local V E G hev

end EulerFlow
