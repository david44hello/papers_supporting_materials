/-
EulerFlow/Concrete/Small.lean — small claims of paper 002: the sets `I(p,q)`, `T(p,q)` of Section 9 (tex l.701-706,
l.728-729, l.745-747), the one-cycle graph (Remark 9.7, tex l.856-861), edge-disjoint paths at a vertex of degree
at most 4 (tex l.195-196), and the group with one element (tex l.140-142).
-/
import EulerFlow.Graph.DirCycleBasic

namespace EulerFlow

open MGraph Finset Fin.NatCast

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-! ## Section 9: the sets `I(p,q)` and `T(p,q)` -/

/-- A natural number `n` with `0 < n < p` is not `0` in `ℤ_p`. -/
theorem natCast_ne_zero_of_lt {p n : ℕ} (h0 : 0 < n) (hp : n < p) : (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := Nat.le_of_dvd h0 hdvd
  omega

/-- Section 9 (tex l.702): `I = -I`, `0 ∉ I`, and `q ≠ -q` in `ℤ_p` (for `q ≥ 1`, `p > 2q`). -/
theorem sec9_I_props_proved (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) :
    (∀ x ∈ Ipq p q, -x ∈ Ipq p q) ∧ (0 : ZMod p) ∉ Ipq p q ∧ (q : ZMod p) ≠ -(q : ZMod p) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨n, hn1, hn2, rfl⟩
    refine ⟨p - n, by omega, by omega, ?_⟩
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
  · rintro ⟨n, hn1, hn2, hn⟩
    exact natCast_ne_zero_of_lt (by omega) (by omega) hn
  · intro h
    have h2 : ((2 * q : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_mul, Nat.cast_two, two_mul]
      exact add_eq_zero_iff_eq_neg.mpr h
    exact natCast_ne_zero_of_lt (by omega) hpq h2

/-- Section 9 (tex l.705-706, l.728-729): for `q = 1` the `(p,q)`-flows are the nowhere-zero `ℤ_p`-flows, and the
step values of Theorem 9.1 are those of Theorem 2.4. -/
theorem sec9_I_one_proved (p : ℕ) (hp : 2 < p) : Ipq p 1 = {x | x ≠ 0} ∧ Tpq p 1 = Tcyc p := by
  have : NeZero p := ⟨by omega⟩
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Ipq, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn1, hn2, rfl⟩
      exact natCast_ne_zero_of_lt (by omega) (by omega)
    · intro hx
      have hv0 := (ZMod.val_ne_zero x).mpr hx
      have hvp := ZMod.val_lt x
      exact ⟨x.val, by omega, by omega, ZMod.natCast_zmod_val x⟩
  · simp [Tpq, Tcyc]

/-- Section 9 (tex l.745-747): `T` has no zero, `T = -T`, `q ∈ I`, and `2q ∈ T`. -/
theorem sec9_T_props_proved (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) :
    (0 : ZMod p) ∉ Tpq p q ∧ (∀ t ∈ Tpq p q, -t ∈ Tpq p q) ∧ (q : ZMod p) ∈ Ipq p q ∧
      2 • (q : ZMod p) ∈ Tpq p q := by
  have h1 : (1 : ZMod p) ≠ 0 := by
    rw [← Nat.cast_one]
    exact natCast_ne_zero_of_lt one_pos (by omega)
  have h2 : ((2 * q : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by omega) hpq
  refine ⟨?_, ?_, ⟨q, le_rfl, by omega, rfl⟩, ?_⟩
  · simp only [Tpq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h | h | h)
    · exact h1 h.symm
    · exact h1 (neg_eq_zero.mp h.symm)
    · exact h2 h.symm
    · exact h2 (neg_eq_zero.mp h.symm)
  · simp only [Tpq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro t (rfl | rfl | rfl | rfl) <;> simp
  · simp only [Tpq, Set.mem_insert_iff, Set.mem_singleton_iff]
    right; right; left
    rw [nsmul_eq_mul, Nat.cast_mul, Nat.cast_two]

/-! ## Remark 9.7: the graph that is one cycle -/

/-- On the one-cycle graph, the flow condition at the vertex `finRotate n i` says `x (finRotate n i) = x i`. -/
theorem cycleGraph_flow_rotate {M : Type} [AddCommGroup M] (n : ℕ) (x : Fin n → M)
    (hx : (cycleGraph n).IsFlow x) (i : Fin n) : x (finRotate n i) = x i := by
  have h := hx (finRotate n i)
  have hs : (univ.filter fun e => (cycleGraph n).src e = finRotate n i) = {finRotate n i} := by
    ext e
    simp [cycleGraph]
  have ht : (univ.filter fun e => (cycleGraph n).tgt e = finRotate n i) = {i} := by
    ext e
    simp only [cycleGraph, mem_filter_univ, mem_singleton, (finRotate n).apply_eq_iff_eq]
  rw [hs, ht, sum_singleton, sum_singleton] at h
  exact h

/-- A flow of the one-cycle graph is constant along the cycle. -/
theorem cycleGraph_flow_const {M : Type} [AddCommGroup M] (m : ℕ) (x : Fin (m + 1) → M)
    (hx : (cycleGraph (m + 1)).IsFlow x) (i : Fin (m + 1)) : x i = x 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have hrot : finRotate (m + 1) i.castSucc = i.succ :=
      Fin.ext (by rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last i).ne]; simp)
    rw [← ih, ← hrot]
    exact cycleGraph_flow_rotate (m + 1) x hx i.castSucc

/-- The `k`-th dart of the one-cycle graph: edge `k` in its reference direction. -/
def cycleDart (m k : ℕ) : Fin (m + 1) × Bool := ((k : Fin (m + 1)), false)

theorem cycleDart_inj (m : ℕ) : ∀ x ∈ List.range (m + 1), ∀ y ∈ List.range (m + 1),
    ((x : Fin (m + 1))) = (y : Fin (m + 1)) → x = y := by
  intro x hx y hy hxy
  rw [List.mem_range] at hx hy
  have := congrArg Fin.val hxy
  rwa [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

/-- The whole one-cycle graph, as one directed cycle passing every edge in its reference direction. -/
def cycleQ (m : ℕ) : (cycleGraph (m + 1)).DirCycle where
  darts := (List.range (m + 1)).map (cycleDart m)
  ne_nil := by simp
  chain := isChain_range_map _ _ (fun k => by
    simp only [cycleDart, dartHead_mk_false, dartTail_mk_false, cycleGraph, finRotate_apply]
    push_cast; rfl) _
  closes := by
    simp only [List.getLast_map, List.head_map, List.getLast_range, List.head_range, cycleDart,
      dartHead_mk_false, dartTail_mk_false, cycleGraph, finRotate_apply]
    simp
  edges_nodup := by
    rw [List.map_map]
    exact List.Nodup.map_on (cycleDart_inj m) List.nodup_range
  tails_nodup := by
    rw [List.map_map]
    exact List.Nodup.map_on (fun x hx y hy hxy => cycleDart_inj m x hx y hy (by simpa [cycleDart, cycleGraph] using hxy))
      List.nodup_range

theorem cycleQ_mem (m : ℕ) (e : Fin (m + 1)) : (e, false) ∈ (cycleQ m).darts := by
  refine List.mem_map.mpr ⟨e.val, List.mem_range.mpr e.isLt, ?_⟩
  simp [cycleDart]

theorem cycleQ_chi (m : ℕ) (e : Fin (m + 1)) : (cycleQ m).chi e = 1 := by
  simp [DirCycle.chi, cycleQ_mem m e]

/-- Remark 9.7 (tex l.857-861): a graph that is one cycle is `(p,q)`-flow-connected (for `p > 2q`). -/
theorem rem_9_7_proved (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) (n : ℕ) (hn : 1 ≤ n) :
    (cycleGraph n).PQFlowConnected p q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro f f'
  by_cases hff : f = f'
  · subst hff
    exact SimpleGraph.Reachable.refl _
  · have hc : ∀ e, f.1 e = f.1 0 := cycleGraph_flow_const m f.1 f.2.1
    have hc' : ∀ e, f'.1 e = f'.1 0 := cycleGraph_flow_const m f'.1 f'.2.1
    have ht : f'.1 0 - f.1 0 ≠ 0 := by
      intro h
      apply hff
      apply Subtype.ext
      funext e
      rw [hc, hc' e, (sub_eq_zero.mp h)]
    apply SimpleGraph.Adj.reachable
    rw [MGraph.pqFlowGraph, MGraph.stepGraph, SimpleGraph.fromRel_adj]
    refine ⟨hff, Or.inl ⟨cycleQ m, f'.1 0 - f.1 0, ht, ht, ?_⟩⟩
    funext e
    simp only [Pi.add_apply, cycleQ_chi, one_smul]
    rw [hc e, hc' e]
    abel

/-! ## Remark after Theorem 2.5: edge-disjoint paths -/

/-- Remark after Theorem 2.5 (tex l.195-196): an even graph with all degrees at most `4` has no two vertices
joined by more than four edge-disjoint paths. -/
theorem sec2_paths_le_four_proved (G : MGraph V E) (hev : G.IsEven) (hdeg : ∀ v, G.degree v ≤ 4) (u w : V)
    (huw : u ≠ w) (Ps : List (G.Path u w)) (hdisj : Ps.Pairwise Path.EdgeDisjoint) : Ps.length ≤ 4 := by
  have hnd : (Ps.map fun P => P.darts.head P.ne_nil).Nodup := by
    refine List.Pairwise.map _ ?_ hdisj
    intro P P' h heq
    exact h _ (List.head_mem _) _ (List.head_mem _) (congrArg Prod.fst heq)
  have hsub : (Ps.map fun P => P.darts.head P.ne_nil).toFinset ⊆ univ.filter fun i => G.endVertex i = u := by
    intro i hi
    simp only [List.mem_toFinset, List.mem_map] at hi
    obtain ⟨P, _, rfl⟩ := hi
    simp only [mem_filter, mem_univ, true_and]
    exact P.starts
  have hcard := card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map] at hcard
  exact hcard.trans (hdeg u)

/-! ## Section 2: the group with one element -/

/-- Section 2 (tex l.140-142): for the group with one element, a graph with an edge has no flow, a graph with no
edge has one flow, and every graph is flow-connected. -/
theorem sec2_trivial_group_proved (A : Type) [AddCommGroup A] [Fintype A] (hA : Fintype.card A = 1)
    (G : MGraph V E) :
    (Nonempty E → ∀ f : E → A, ¬ G.IsNZFlow f) ∧ (IsEmpty E → ∃! f : E → A, G.IsNZFlow f) ∧
      G.FlowConnected A := by
  have : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp hA.le
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨e⟩ f hf
    exact hf.2 e (Subsingleton.elim _ _)
  · intro hE
    exact ⟨fun _ => 0, ⟨fun _ => Subsingleton.elim _ _, fun e => isEmptyElim e⟩,
      fun g _ => funext fun e => isEmptyElim e⟩
  · intro f f'
    have hff : f = f' := Subtype.ext (funext fun _ => Subsingleton.elim _ _)
    subst hff
    exact SimpleGraph.Reachable.refl _

end EulerFlow
