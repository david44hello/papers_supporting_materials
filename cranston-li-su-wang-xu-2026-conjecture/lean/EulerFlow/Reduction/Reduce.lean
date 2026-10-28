/-
EulerFlow/Reduction/Reduce.lean — Proposition 3.4 of paper 002 (the reduction, tex l.294-319), proved ONCE for
`I`-flows, and its two instances: nowhere-zero flows (Proposition 3.4 itself) and `(p,q)`-flows (Lemma 9.3, tex
l.735-769, "the same proof with this rule of replacement"). Also (T1)/(T2) for `A ∖ {0}` and for `{±1, ±2}`.
-/
import EulerFlow.Reduction.Loop
import EulerFlow.Reduction.Const

namespace EulerFlow

open Finset

namespace MGraph

variable {V E : Type} {G : MGraph V E} [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Ends at a vertex of a loopless graph -/

omit [DecidableEq E] in
/-- Kirchhoff's form (2.1) of the flow condition: the outward values at `z` sum to minus the boundary. -/
theorem sum_dirVal_eq_neg_boundary {M : Type} [AddCommGroup M] (x : E → M) (z : V) :
    ∑ i ∈ univ.filter (fun i : E × Bool => G.endVertex i = z), dirVal x i = -G.boundary x z := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, boundary_eq_sum_bdryTerm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hs : G.src e = z <;> by_cases ht : G.tgt e = z <;>
    simp [hs, ht, endVertex, dirVal, bdryTerm, add_comm]

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem isAt_of_endVertex {i : E × Bool} {v : V} (hi : G.endVertex i = v) : G.IsAt i.1 v := by
  unfold endVertex at hi; unfold IsAt; split_ifs at hi <;> simp [hi]

omit [Fintype E] [DecidableEq E] in
/-- In a loopless graph the end of `i.1` at `v` is `i`. -/
theorem endAt_eq_of_endVertex (hG : G.Loopless) {i : E × Bool} {v : V} (hi : G.endVertex i = v) :
    G.endAt i.1 v = i := by
  obtain ⟨e, b⟩ := i
  have hl := hG e; unfold IsLoop at hl
  cases b <;> simp_all [endVertex, endAt]

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
/-- In a loopless graph two different ends at one vertex lie on different edges. -/
theorem fst_ne_of_ends (hG : G.Loopless) {i j : E × Bool} {v : V} (hij : i ≠ j) (hi : G.endVertex i = v)
    (hj : G.endVertex j = v) : i.1 ≠ j.1 := by
  intro h
  obtain ⟨e, b⟩ := i; obtain ⟨e', b'⟩ := j
  simp only at h; subst h
  have hl := hG e; unfold IsLoop at hl
  cases b <;> cases b' <;> simp_all [endVertex]

omit [Fintype E] [DecidableEq E] in
/-- A balanced pair at `v` of a loopless graph puts `f` in `B(v; e, e')` for the two edges of the pair. -/
theorem splitData_of_balanced (hG : G.Loopless) {A : Type} [AddCommGroup A] {f : E → A} {v : V}
    (h : G.HasBalancedPairAt f v) :
    ∃ e e', SplitData G v e e' ∧ dirVal f (G.endAt e v) + dirVal f (G.endAt e' v) = 0 := by
  obtain ⟨i, j, hij, hi, hj, hsum⟩ := h
  refine ⟨i.1, j.1, SplitData.of hG (fst_ne_of_ends hG hij hi hj) (isAt_of_endVertex hi) (isAt_of_endVertex hj),
    ?_⟩
  rw [endAt_eq_of_endVertex hG hi, endAt_eq_of_endVertex hG hj]; exact hsum

/-- At a vertex of degree `2` of a loopless graph, the two ends are a balanced pair of every flow (tex l.308-309). -/
theorem splitData_of_degree_two (hG : G.Loopless) {v : V} (hv : G.degree v = 2) :
    ∃ e e', SplitData G v e e' ∧ ∀ {A : Type} [AddCommGroup A] (f : E → A), G.IsFlow f →
      dirVal f (G.endAt e v) + dirVal f (G.endAt e' v) = 0 := by
  obtain ⟨i, j, hij, hset⟩ := Finset.card_eq_two.1 hv
  have hi : G.endVertex i = v := by
    have : i ∈ univ.filter (fun i : E × Bool => G.endVertex i = v) := by rw [hset]; simp
    simpa using this
  have hj : G.endVertex j = v := by
    have : j ∈ univ.filter (fun i : E × Bool => G.endVertex i = v) := by rw [hset]; simp
    simpa using this
  refine ⟨i.1, j.1, SplitData.of hG (fst_ne_of_ends hG hij hi hj) (isAt_of_endVertex hi) (isAt_of_endVertex hj),
    fun f hf => ?_⟩
  rw [endAt_eq_of_endVertex hG hi, endAt_eq_of_endVertex hG hj]
  have := sum_dirVal_eq_neg_boundary (G := G) f v
  rw [hset, Finset.sum_pair hij, (isFlow_iff_boundary G f).1 hf v, neg_zero] at this
  exact this

/-! ### The flows in `B(v; e, e')` -/

variable {A : Type} [AddCommGroup A] {I T : Set A}

/-- If any two `I`-flows of `G'` are `T`-joined, then any two `I`-flows of `G` in `B(v; e, e')` are `T`-joined
(tex l.313-314: induction hypothesis for `G'` and Lemma 3.2). -/
theorem reachable_of_balanced (hI : ∀ y ∈ I, -y ∈ I) {v : V} {e e' : E} (hd : SplitData G v e e')
    (hpre : ((G.splitOff v e e').stepGraph I T).Preconnected) (f₁ f₂ : {f // G.IsIFlow I f})
    (h₁ : dirVal f₁.1 (G.endAt e v) + dirVal f₁.1 (G.endAt e' v) = 0)
    (h₂ : dirVal f₂.1 (G.endAt e v) + dirVal f₂.1 (G.endAt e' v) = 0) :
    (G.stepGraph I T).Reachable f₁ f₂ := by
  have k : ∀ (f : {f // G.IsIFlow I f}), dirVal f.1 (G.endAt e v) + dirVal f.1 (G.endAt e' v) = 0 →
      ∃ g : {g // (G.splitOff v e e').IsIFlow I g}, splitLiftV hI hd g = f := by
    intro f hf
    refine ⟨⟨G.splitRes v e e' f.1, ?_⟩, Subtype.ext (splitLift_splitRes hd f.1 hf)⟩
    rw [← isIFlow_splitLift_iff hI hd, splitLift_splitRes hd f.1 hf]; exact f.2
  obtain ⟨g₁, rfl⟩ := k f₁ h₁
  obtain ⟨g₂, rfl⟩ := k f₂ h₂
  exact splitLift_reachable hI hd (hpre g₁ g₂)

/-- All constant flows `a 𝟙_D` are `T`-joined (tex l.314-316, with (T2)). -/
theorem reachable_constFlow (hI : ∀ y ∈ I, -y ∈ I) (hT0 : (0 : A) ∉ T) (hTneg : ∀ t ∈ T, -t ∈ T) {a : A}
    (ha : a ∈ I) (h2a : 2 • a = 0 ∨ 2 • a ∈ T) {D D₂ : E → Bool} (hD : G.IsEulerOrient D)
    (hD₂ : G.IsEulerOrient D₂) :
    (G.stepGraph I T).Reachable ⟨_, isIFlow_constFlow hI hD ha⟩ ⟨_, isIFlow_constFlow hI hD₂ ha⟩ := by
  rcases h2a with h0 | hT
  · have : constFlow a D₂ = constFlow a D := by
      rw [constFlow_eq_add a D D₂, h0, neg_zero]; funext e; simp
    have e₂ : (⟨_, isIFlow_constFlow hI hD₂ ha⟩ : {f // G.IsIFlow I f}) = ⟨_, isIFlow_constFlow hI hD ha⟩ :=
      Subtype.ext this
    rw [e₂]
  · refine reachable_of_circ _ _ _ (reversedSign_mem D D₂) (isFlow_reversedSign hD hD₂) _ (hTneg _ hT) ?_
      (constFlow_eq_add a D D₂)
    intro h0; exact hT0 (by rw [← neg_neg (2 • a), h0, neg_zero] at hT; exact hT)

end MGraph

/-! ### The reduction for `I`-flows -/

open MGraph

/-- A class of graphs, as in Proposition 3.4. -/
abbrev GraphClass := ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E], MGraph V E → Prop

theorem card_deleteEdge_lt {E : Type} [Fintype E] [DecidableEq E] (l : E) :
    Fintype.card {x : E // x ≠ l} < Fintype.card E :=
  Fintype.card_subtype_lt (p := fun x => x ≠ l) (not_not.2 rfl)

theorem card_splitOff_lt {E : Type} [Fintype E] [DecidableEq E] {e e' : E} (hne : e ≠ e') :
    Fintype.card (Option {x : E // x ≠ e ∧ x ≠ e'}) < Fintype.card E := by
  rw [Fintype.card_option, Fintype.card_subtype]
  have h := Finset.card_filter_add_card_filter_not (s := univ) (fun x : E => x ≠ e ∧ x ≠ e')
  have hpair : univ.filter (fun x : E => ¬(x ≠ e ∧ x ≠ e')) = {e, e'} := by
    ext x; simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]; tauto
  rw [hpair, Finset.card_pair hne, Finset.card_univ] at h
  omega

/-- Proposition 3.4 for `I`-flows (tex l.294-319). `(T1)` for `I`: any two elements of `I` are joined by a chain
in `I` whose neighbours differ by an element of `T`; `(T2)` for `I`: some `a ∈ I` has `2a = 0` or `2a ∈ T`. -/
theorem reduction_preconnected {A : Type} [AddCommGroup A] {I T : Set A} (hI : ∀ y ∈ I, -y ∈ I)
    (hT0 : (0 : A) ∉ T) (hTneg : ∀ t ∈ T, -t ∈ T)
    (hT1 : ∀ a b, a ∈ I → b ∈ I → Relation.ReflTransGen (fun x y : A => y ∈ I ∧ y - x ∈ T) a b)
    (hT2 : ∃ a ∈ I, 2 • a = 0 ∨ 2 • a ∈ T) (𝒢 : GraphClass)
    (h_even : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      𝒢 V E G → G.IsEven)
    (h_loop : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E) (l : E),
      𝒢 V E G → G.IsLoop l → 𝒢 V {x : E // x ≠ l} (G.deleteEdge l))
    (h_split : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E)
      (v : V) (e e' : E), 𝒢 V E G → G.Loopless → e ≠ e' → G.IsAt e v → G.IsAt e' v →
      𝒢 V (Option {x : E // x ≠ e ∧ x ≠ e'}) (G.splitOff v e e'))
    (h_local : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      𝒢 V E G → Nonempty E → G.Loopless → (∀ v, G.degree v = 0 ∨ 4 ≤ G.degree v) →
      ∀ f : {f : E → A // G.IsIFlow I f}, ∃ f' : {f : E → A // G.IsIFlow I f},
        G.HasBalancedPair f'.1 ∧ (G.stepGraph I T).Reachable f f')
    (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E) (hG : 𝒢 V E G) :
    (G.stepGraph I T).Preconnected := by
  suffices H : ∀ n, ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      Fintype.card E = n → 𝒢 V E G → (G.stepGraph I T).Preconnected from H _ V E G rfl hG
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V E _ _ _ _ G hn hG
  -- a loop: Lemma 3.1 and the induction hypothesis for `G - l`
  by_cases hloop : ∃ l, G.IsLoop l
  · obtain ⟨l, hl⟩ := hloop
    exact loop_preconnected hT0 hT1 hl
      (ih _ (hn ▸ card_deleteEdge_lt l) V _ (G.deleteEdge l) rfl (h_loop V E G l hG hl))
  have hGl : G.Loopless := fun e he => hloop ⟨e, he⟩
  -- the induction hypothesis for a splitting off
  have ihsplit : ∀ (v : V) (e e' : E), SplitData G v e e' → ((G.splitOff v e e').stepGraph I T).Preconnected :=
    fun v e e' hd => ih _ (hn ▸ card_splitOff_lt hd.ne) V _ (G.splitOff v e e') rfl
      (h_split V E G v e e' hG hGl hd.ne hd.at₁ hd.at₂)
  -- a vertex of degree 2: every flow is in `B(v; e, e')`
  by_cases hdeg2 : ∃ v, G.degree v = 2
  · obtain ⟨v, hv⟩ := hdeg2
    obtain ⟨e, e', hd, hbal⟩ := splitData_of_degree_two hGl hv
    intro f₁ f₂
    exact reachable_of_balanced hI hd (ihsplit v e e' hd) f₁ f₂ (hbal f₁.1 f₁.2.1) (hbal f₂.1 f₂.2.1)
  -- no edge: exactly one flow
  by_cases hE : IsEmpty E
  · intro f₁ f₂
    have : f₁ = f₂ := Subtype.ext (funext fun e => isEmptyElim e)
    rw [this]
  have hne : Nonempty E := not_isEmpty_iff.1 hE
  -- otherwise every degree is `0` or at least `4`, and (LOCAL) applies
  have hdeg : ∀ v, G.degree v = 0 ∨ 4 ≤ G.degree v := by
    intro v
    obtain ⟨k, hk⟩ := h_even V E G hG v
    have : G.degree v ≠ 2 := fun h => hdeg2 ⟨v, h⟩
    omega
  obtain ⟨a, haI, h2a⟩ := hT2
  obtain ⟨D₀, hD₀⟩ := exists_eulerOrient (h_even V E G hG)
  let c₀ : {f // G.IsIFlow I f} := ⟨_, isIFlow_constFlow hI hD₀ haI⟩
  -- every flow with a balanced pair is joined to `c₀` (tex l.312-318)
  have hbal : ∀ f : {f // G.IsIFlow I f}, G.HasBalancedPair f.1 → (G.stepGraph I T).Reachable f c₀ := by
    intro f ⟨v, hv⟩
    obtain ⟨e, e', hd, hfb⟩ := splitData_of_balanced hGl hv
    obtain ⟨D, hD, hDb⟩ := exists_eulerOrient_balanced hd (h_even V E G hG) a
    exact (reachable_of_balanced hI hd (ihsplit v e e' hd) f ⟨_, isIFlow_constFlow hI hD haI⟩ hfb hDb).trans
      (reachable_constFlow hI hT0 hTneg haI h2a hD hD₀)
  have hall : ∀ f : {f // G.IsIFlow I f}, (G.stepGraph I T).Reachable f c₀ := by
    intro f
    obtain ⟨f', hf'b, hff'⟩ := h_local V E G hG hne hGl hdeg f
    exact hff'.trans (hbal f' hf'b)
  intro f₁ f₂
  exact (hall f₁).trans (hall f₂).symm

/-! ### (T1) for chains of residues -/

/-- A chain of residues `n, n ± 1, …` inside `[lo, hi]` joins any two of them by steps `±1`. -/
theorem zmod_chain {p : ℕ} {I T : Set (ZMod p)} (h1 : (1 : ZMod p) ∈ T) (hm1 : (-1 : ZMod p) ∈ T) {lo hi : ℕ}
    (hI : ∀ n, lo ≤ n → n ≤ hi → (n : ZMod p) ∈ I) {n₁ n₂ : ℕ} (h₁ : lo ≤ n₁ ∧ n₁ ≤ hi)
    (h₂ : lo ≤ n₂ ∧ n₂ ≤ hi) :
    Relation.ReflTransGen (fun x y : ZMod p => y ∈ I ∧ y - x ∈ T) (n₁ : ZMod p) (n₂ : ZMod p) := by
  have up : ∀ n k, lo ≤ n → n + k ≤ hi →
      Relation.ReflTransGen (fun x y : ZMod p => y ∈ I ∧ y - x ∈ T) (n : ZMod p) ((n + k : ℕ) : ZMod p) := by
    intro n k hn hk
    induction k with
    | zero => simpa using Relation.ReflTransGen.refl
    | succ k ih =>
      refine (ih (by omega)).tail ⟨hI _ (by omega) hk, ?_⟩
      push_cast; ring_nf; exact h1
  have down : ∀ n k, lo ≤ n → n + k ≤ hi →
      Relation.ReflTransGen (fun x y : ZMod p => y ∈ I ∧ y - x ∈ T) ((n + k : ℕ) : ZMod p) (n : ZMod p) := by
    intro n k hn hk
    induction k with
    | zero => simpa using Relation.ReflTransGen.refl
    | succ k ih =>
      refine Relation.ReflTransGen.head ⟨hI _ (by omega) (by omega), ?_⟩ (ih (by omega))
      push_cast; ring_nf; exact hm1
  rcases le_total n₁ n₂ with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact up n₁ k h₁.1 h₂.2
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact down n₂ k h₂.1 h₁.2

end EulerFlow
