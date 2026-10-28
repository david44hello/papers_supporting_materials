/-
EulerFlow/Concrete/Dipole.lean — the dipole (two vertices, parallel edges) and the one-loop graph: Theorem 9.2,
the introduction's example, the remark after Lemma 8.6 and the remark after Theorem 2.4 (paper 002).
-/
import EulerFlow.Graph.DirCycleBasic

namespace EulerFlow

open MGraph Finset

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-! ### General facts on the step graph -/

omit [Fintype V] in
/-- An edge of a step graph is a step `g = f + t χ_Q` with `t ≠ 0` (in one of its two directions). -/
theorem stepGraph_adj_step {A : Type} [AddCommGroup A] {G : MGraph V E} {I T : Set A}
    {f g : {f : E → A // G.IsIFlow I f}} (h : (G.stepGraph I T).Adj f g) :
    ∃ Q : G.DirCycle, ∃ t : A, t ≠ 0 ∧ g.1 = f.1 + fun e => Q.chi e • t := by
  rw [stepGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨_, ⟨Q, t, _, ht, h⟩ | ⟨Q, t, _, ht, h⟩⟩ := h
  · exact ⟨Q, t, ht, h⟩
  · refine ⟨Q, -t, neg_ne_zero.mpr ht, ?_⟩
    funext e
    have he := congrFun h e
    simp only [Pi.add_apply] at he ⊢
    rw [he, smul_neg]
    abel

/-- A property that passes along every edge of a graph passes along every walk. -/
theorem reachable_invariant {α : Type} {Gr : SimpleGraph α} (P : α → Prop)
    (hP : ∀ x y, Gr.Adj x y → P x → P y) {u v : α} (h : Gr.Reachable u v) (hu : P u) : P v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hP _ _ hadj hu)

/-! ### The dipole -/

/-- Every vertex of the dipole with `n` edges has degree `n`. -/
theorem dipole_degree (n : ℕ) (v : Fin 2) : (dipole n).degree v = n := by
  have h : (univ.filter fun i : Fin n × Bool => (dipole n).endVertex i = v) =
      (univ : Finset (Fin n)) ×ˢ (univ.filter fun b : Bool => (if b then (1 : Fin 2) else 0) = v) := by
    rw [← Finset.filter_product_right, Finset.univ_product_univ]
    rfl
  unfold MGraph.degree
  have h1 : (univ.filter fun b : Bool => (if b then (1 : Fin 2) else 0) = v).card = 1 := by
    fin_cases v <;> decide
  rw [h, Finset.card_product, Finset.card_univ, Fintype.card_fin, h1, mul_one]

/-- The constant map `a` on the dipole with `n` edges is a flow when `n • a = 0`. -/
theorem dipole_isFlow_const {A : Type} [AddCommGroup A] (n : ℕ) (a : A) (h : n • a = 0) :
    (dipole n).IsFlow fun _ => a := by
  intro v
  fin_cases v <;> simp [dipole, h]

/-- Every directed cycle `Q` of the dipole passes an edge `e` in its reference direction (`χ_Q(e) = 1`) and an
edge `e'` in the other direction (`χ_Q(e') = -1`): it leaves each of the two vertices once. -/
theorem dipole_cycle_chi {n : ℕ} (Q : (dipole n).DirCycle) : ∃ e e', Q.chi e = 1 ∧ Q.chi e' = -1 := by
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil Q.darts Q.ne_nil
  obtain ⟨d', hd', h⟩ := Q.exists_leave hd
  have h1 := Q.chi_of_mem hd
  have h2 := Q.chi_of_mem hd'
  obtain ⟨e, b⟩ := d
  obtain ⟨e', b'⟩ := d'
  cases b <;> cases b'
  · simp [dartTail, dartHead, endVertex, dipole] at h
  · exact ⟨e, e', by simpa [dartSign] using h1, by simpa [dartSign] using h2⟩
  · exact ⟨e', e, by simpa [dartSign] using h2, by simpa [dartSign] using h1⟩
  · simp [dartTail, dartHead, endVertex, dipole] at h

/-- The constant flow `a` is isolated in the step graph of the dipole when no `t ≠ 0` has both `a + t` and `a - t`
in `I`; so, if `-a` is another `I`-flow, the step graph is not connected. -/
theorem dipole_not_preconnected {A : Type} [AddCommGroup A] (n : ℕ) (hn0 : 0 < n) (I T : Set A) (a : A)
    (hn : n • a = 0) (ha : a ∈ I) (hna : -a ∈ I) (hne : a ≠ -a)
    (hstep : ∀ t : A, t ≠ 0 → a + t ∈ I → a - t ∈ I → False) :
    ¬ ((dipole n).stepGraph I T).Preconnected := by
  intro hconn
  let f0 : {f : Fin n → A // (dipole n).IsIFlow I f} := ⟨fun _ => a, dipole_isFlow_const n a hn, fun _ => ha⟩
  let f1 : {f : Fin n → A // (dipole n).IsIFlow I f} :=
    ⟨fun _ => -a, dipole_isFlow_const n (-a) (by rw [smul_neg, hn, neg_zero]), fun _ => hna⟩
  have key := reachable_invariant (fun g : {f : Fin n → A // (dipole n).IsIFlow I f} => g.1 = fun _ => a)
    ?_ (hconn f0 f1) rfl
  · exact hne (congrFun key ⟨0, hn0⟩).symm
  intro x y hadj hx
  obtain ⟨Q, t, ht, hy⟩ := stepGraph_adj_step hadj
  obtain ⟨e, e', he, he'⟩ := dipole_cycle_chi Q
  exfalso
  apply hstep t ht
  · have hmem := y.2.2 e
    rw [hy] at hmem
    simpa [hx, he] using hmem
  · have hmem := y.2.2 e'
    rw [hy] at hmem
    simpa [hx, he', sub_eq_add_neg] using hmem

/-! ### Theorem 9.2 -/

/-- An integer that is divisible by `p` and lies strictly between `-p` and `p` is `0`. -/
theorem int_eq_zero_of_dvd_of_bounds {p : ℕ} {x : ℤ} (h : (p : ℤ) ∣ x) (h1 : -(p : ℤ) < x) (h2 : x < p) :
    x = 0 :=
  Int.eq_zero_of_abs_lt_dvd h (abs_lt.mpr ⟨h1, h2⟩)

/-- The arithmetic of Theorem 9.2 (tex l.848-853): for `2q < p < 4q`, no `t ≠ 0` in `ℤ_p` has both `q + t` and
`q - t` in `I(p, q)` (`q + t ∈ I` needs `t ≤ p - 2q`, `q - t ∈ I` needs `t ≥ 2q`). -/
theorem Ipq_no_step (p q : ℕ) (hpq : 2 * q < p) (hp : p < 4 * q) (t : ZMod p) (ht : t ≠ 0)
    (h1 : (q : ZMod p) + t ∈ Ipq p q) (h2 : (q : ZMod p) - t ∈ Ipq p q) : False := by
  have : NeZero p := ⟨by omega⟩
  obtain ⟨n, hn1, hn2, hn⟩ := h1
  obtain ⟨m, hm1, hm2, hm⟩ := h2
  set s := t.val with hs
  have hts : (s : ZMod p) = t := ZMod.natCast_zmod_val t
  have hslt : s < p := ZMod.val_lt t
  have hs0 : s ≠ 0 := by
    intro h0
    apply ht
    rw [← hts, h0, Nat.cast_zero]
  rw [← hts] at hn hm
  have hn' : ((n : ℤ) : ZMod p) = (((q : ℤ) + s : ℤ) : ZMod p) := by push_cast; exact hn
  have hm' : ((m : ℤ) : ZMod p) = (((q : ℤ) - s : ℤ) : ZMod p) := by push_cast; exact hm
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hn' hm'
  have hn0 := int_eq_zero_of_dvd_of_bounds hn' (by omega) (by omega)
  have hm0 := int_eq_zero_of_dvd_of_bounds (dvd_add hm' (dvd_refl (p : ℤ))) (by omega) (by omega)
  omega

/-- `2 p q = 0` in `ℤ_p`: the constant map `q` is a flow of the dipole with `2p` edges. -/
theorem two_mul_smul_natCast_eq_zero (p q : ℕ) : (2 * p) • (q : ZMod p) = 0 := by
  rw [nsmul_eq_mul]
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- Theorem 9.2 (tex l.723-726): `2q < p < 4q`; the graph with two vertices and `2p` parallel edges is even and is
not `(p,q)`-flow-connected. -/
theorem thm_9_2_proved (p q : ℕ) (hpq : 2 * q < p) (hp : p < 4 * q) :
    (dipole (2 * p)).IsEven ∧ ¬ (dipole (2 * p)).PQFlowConnected p q := by
  refine ⟨fun v => by rw [dipole_degree]; exact even_two_mul p, ?_⟩
  apply dipole_not_preconnected (2 * p) (by omega) (Ipq p q) {x | x ≠ 0} (q : ZMod p)
    (two_mul_smul_natCast_eq_zero p q) ⟨q, le_rfl, by omega, rfl⟩
  · exact ⟨p - q, by omega, le_rfl, by rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]⟩
  · intro h
    have h2 : ((2 * q : ℕ) : ZMod p) = 0 := by
      push_cast
      rw [two_mul]
      nth_rewrite 1 [h]
      exact neg_add_cancel _
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by omega) h2
    omega
  · exact Ipq_no_step p q hpq hp

/-! ### The introduction's example (tex l.77-80) -/

/-- An integer value of a `3`-flow (`1 ≤ |x| ≤ 2`) is not `0` modulo `3`. -/
theorem Ik3_cast_ne_zero {x : ℤ} (hx : x ∈ Ik 3) : ((x : ℤ) : ZMod 3) ≠ 0 := by
  obtain ⟨h1, h2⟩ := hx
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [abs_le] at h2
  rw [le_abs'] at h1
  push_cast at h2
  omega

/-- The integer `3`-flow with the values `1, 1, 1, 1, -2, -2` on the dipole with six edges. -/
def liftOne : Fin 6 → ℤ := ![1, 1, 1, 1, -2, -2]

theorem liftOne_isIFlow : (dipole 6).IsIFlow (Ik 3) liftOne := by
  refine ⟨?_, ?_⟩
  · intro v
    fin_cases v <;> decide
  · intro e
    fin_cases e <;> simp [liftOne, Ik]

theorem neg_liftOne_isIFlow : (dipole 6).IsIFlow (Ik 3) (-liftOne) := by
  refine ⟨?_, ?_⟩
  · intro v
    fin_cases v <;> decide
  · intro e
    fin_cases e <;> simp [liftOne, Ik]

/-- In `𝓕(G, 3)` of the dipole with six edges, the integer flows `≡ 1 (mod 3)` are joined to no other `3`-flow:
a step `F' = F + λ χ_Q` with `λ ≡ 0 (mod 3)` keeps the residues, and one with `λ ≢ 0` would make `1 + λ` or
`1 - λ` a zero modulo `3`. -/
theorem dipole6_kflow_invariant (x y : {F : Fin 6 → ℤ // (dipole 6).IsIFlow (Ik 3) F})
    (hadj : ((dipole 6).kFlowGraph 3).Adj x y) (hx : ∀ e, ((x.1 e : ℤ) : ZMod 3) = 1) :
    ∀ e, ((y.1 e : ℤ) : ZMod 3) = 1 := by
  obtain ⟨Q, l, _, hy⟩ := stepGraph_adj_step hadj
  have hval : ∀ e, ((y.1 e : ℤ) : ZMod 3) = 1 + (Q.chi e : ZMod 3) * (l : ZMod 3) := by
    intro e
    rw [hy, ← hx e]
    simp
  by_cases hl : (l : ZMod 3) = 0
  · intro e
    rw [hval e, hl, mul_zero, add_zero]
  · exfalso
    obtain ⟨e, e', he, he'⟩ := dipole_cycle_chi Q
    have h1 := Ik3_cast_ne_zero (y.2.2 e)
    have h2 := Ik3_cast_ne_zero (y.2.2 e')
    rw [hval, he] at h1
    rw [hval, he'] at h2
    revert hl h1 h2
    generalize (l : ZMod 3) = t
    push_cast
    revert t
    decide

/-- Introduction (tex l.77-80): the number `4` cannot be replaced by `3`. The graph with two vertices and six
parallel edges is even and is neither `ℤ_3`-flow-connected nor `3`-flow-connected. -/
theorem intro_example_proved :
    (dipole 6).IsEven ∧ ¬ (dipole 6).FlowConnected (ZMod 3) ∧ ¬ (dipole 6).KFlowConnected 3 := by
  refine ⟨fun v => by rw [dipole_degree]; decide, ?_, ?_⟩
  · apply dipole_not_preconnected 6 (by norm_num) {x | x ≠ 0} {x | x ≠ 0} (1 : ZMod 3) (by decide)
      (by decide) (by decide) (by decide)
    show ∀ t : ZMod 3, t ≠ 0 → 1 + t ≠ 0 → 1 - t ≠ 0 → False
    decide
  · intro hconn
    have key := reachable_invariant (fun F : {F : Fin 6 → ℤ // (dipole 6).IsIFlow (Ik 3) F} =>
        ∀ e, ((F.1 e : ℤ) : ZMod 3) = 1) dipole6_kflow_invariant
      (hconn ⟨liftOne, liftOne_isIFlow⟩ ⟨-liftOne, neg_liftOne_isIFlow⟩) (by decide)
    revert key
    decide

/-! ### The remark after Lemma 8.6 (tex l.652) -/

/-- The one-dart directed cycle of the one-loop graph. -/
def loopCycle : (cycleGraph 1).DirCycle where
  darts := [(0, false)]
  ne_nil := by simp
  chain := List.isChain_singleton _
  closes := Subsingleton.elim _ _
  edges_nodup := List.nodup_singleton _
  tails_nodup := List.nodup_singleton _

/-- Every map on the one-loop graph is a flow (its only edge leaves and enters the only vertex). -/
theorem cycleGraph1_isFlow {A : Type} [AddCommGroup A] (x : Fin 1 → A) : (cycleGraph 1).IsFlow x := by
  intro v
  have h : (cycleGraph 1).src = (cycleGraph 1).tgt := funext fun _ => Subsingleton.elim _ _
  rw [h]

/-- After Lemma 8.6 (tex l.652): `f + χ_Q` can have zeros, so Lemma 8.5 cannot be used twice. (An instance: the
one-loop graph, `k ≥ 3`, `f = -1`: `f` and `f + 2χ_Q` are flows, `f + χ_Q` has a zero.) -/
theorem rem_8_6_zeros_proved (k : ℕ) (hk : 3 ≤ k) :
    ∃ (Q : (cycleGraph 1).DirCycle) (f : Fin 1 → ZMod k), (cycleGraph 1).IsNZFlow f ∧
      (cycleGraph 1).IsNZFlow (f + fun e => Q.chi e • (2 : ZMod k)) ∧
      ¬ (cycleGraph 1).IsNZFlow (f + fun e => Q.chi e • (1 : ZMod k)) := by
  have : Fact (1 < k) := ⟨by omega⟩
  have hchi : ∀ e, loopCycle.chi e = 1 := by
    intro e
    rw [Subsingleton.elim e 0]
    simp [DirCycle.chi, loopCycle]
  refine ⟨loopCycle, fun _ => -1, ⟨cycleGraph1_isFlow _, fun _ => ?_⟩, ⟨cycleGraph1_isFlow _, fun _ => ?_⟩, ?_⟩
  · exact neg_ne_zero.mpr one_ne_zero
  · show -1 + loopCycle.chi _ • (2 : ZMod k) ≠ 0
    rw [hchi, one_smul]
    have h1 : (-1 : ZMod k) + 2 = 1 := by ring
    rw [h1]
    exact one_ne_zero
  · intro h
    apply h.2 0
    show -1 + loopCycle.chi 0 • (1 : ZMod k) = 0
    rw [hchi, one_smul, neg_add_cancel]

/-! ### The remark after Theorem 2.4 (tex l.524-527) -/

/-- In `ℤ_3 × ℤ_3`, `-2a = a` for every `a`. -/
theorem z3z3_neg_two (a : ZMod 3 × ZMod 3) : -(2 • a) = a := by revert a; decide

/-- In `ℤ_3 × ℤ_3`, `6a = 0` for every `a`. -/
theorem z3z3_six (a : ZMod 3 × ZMod 3) : (6 : ℕ) • a = 0 := by revert a; decide

/-- Remark after Theorem 2.4 (tex l.525-527): in `ℤ_3 × ℤ_3`, with `S` of any cyclic decomposition, `-2a = a` for
a small `a`, and a vertex can have six ends with the same small outward value `a` (here: vertex `0` of the graph
with two vertices and six parallel edges). -/
theorem sec6_remark_Z3Z3_proved (D : CyclicDecomp (ZMod 3 × ZMod 3)) (a : ZMod 3 × ZMod 3) (ha : a ∈ D.S) :
    -(2 • a) = a ∧ ∃ f : Fin 6 → ZMod 3 × ZMod 3, (dipole 6).IsNZFlow f ∧
      ∀ i : Fin 6 × Bool, (dipole 6).endVertex i = 0 → dirVal f i = a := by
  have ha0 : a ≠ 0 := by
    obtain ⟨k, hk | hk⟩ := ha
    · rw [hk]; exact D.s_ne k
    · rw [hk]; exact neg_ne_zero.mpr (D.s_ne k)
  refine ⟨z3z3_neg_two a, fun _ => a, ⟨dipole_isFlow_const 6 a (z3z3_six a), fun _ => ha0⟩, ?_⟩
  rintro ⟨e, b⟩ hi
  cases b
  · rfl
  · simp [endVertex, dipole] at hi

end EulerFlow
