/-
Cereceda/LB/JMinor.lean — a `K_m` minor forces treewidth at least `m - 1`; `J_ℓ` has `K_4` as a minor, so its treewidth
is at least `3` (short v3.90 l. 718-720).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route. For a minor model `B` of `K_m` in `G` and a tree decomposition `D` of `G`, the nodes whose bag meets `B x` form a
connected node set of the tree (a walk inside `B x` moves from bag to bag along edges of `G`, and each edge of `G` lies
in a bag), and any two such node sets meet (an edge of `G` between `B x` and `B y` lies in a bag). By Helly's theorem
for subtrees (`Subdivision.helly`) one bag meets all `m` disjoint sets `B x`, so it has at least `m` vertices. The
sanity tests: `K_3` has no `K_4` minor (four disjoint nonempty sets do not fit in three vertices); the 4-cycle has no
`K_4` minor (it has a tree decomposition of width `2`, bags `{0, 1, 2}` and `{0, 2, 3}`).
-/
import Cereceda.Defs.Minor
import Cereceda.Defs.Intro
import Cereceda.Intro.Subdivision

namespace Cereceda

open Finset Subdivision

namespace JMinor

section Model

variable {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} {B : W → Set V}

/-- A vertex lies in at most one branch set. -/
lemma eq_of_mem (hB : IsMinorModel H G B) {x y : W} {a : V} (hx : a ∈ B x) (hy : a ∈ B y) : x = y := by
  by_contra hxy
  exact Set.disjoint_left.mp (hB.disjoint x y hxy) hx hy

/-- A set with a root `r` from which every other point descends (to a neighbour in the set with a smaller value of
`f`) induces a connected subgraph. -/
lemma connected_of_descent {S : Set V} {r : V} (hr : r ∈ S) (f : V → ℕ)
    (h : ∀ w ∈ S, w ≠ r → ∃ u ∈ S, G.Adj w u ∧ f u < f w) : (G.induce S).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨r, hr⟩, fun w => ?_⟩
  suffices key : ∀ k, ∀ w (hw : w ∈ S), f w = k → (G.induce S).Reachable ⟨r, hr⟩ ⟨w, hw⟩ from
    key _ w.1 w.2 rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro w hw hfw
    by_cases hwr : w = r
    · subst hwr
      rfl
    · obtain ⟨u, hu, hwu, hfu⟩ := h w hw hwr
      exact (ih (f u) (hfw ▸ hfu) u hu rfl).trans
        (SimpleGraph.Adj.reachable (show (G.induce S).Adj ⟨u, hu⟩ ⟨w, hw⟩ from hwu.symm))

end Model

section Width

variable {V : Type} {G : SimpleGraph V} {ι : Type} [Fintype ι] (D : TreeDecomposition G ι)

/-- The nodes whose bags meet `S`. -/
def nodes (S : Set V) : Set ι := {i | ∃ z ∈ S, z ∈ D.bag i}

/-- Two nodes whose bags hold the same vertex `a ∈ S` are joined inside `nodes D S`. -/
lemma joined_of_mem {S : Set V} {a : V} (ha : a ∈ S) {i j : ι} (hi : a ∈ D.bag i) (hj : a ∈ D.bag j) :
    JoinedIn D.T (nodes D S) i j :=
  (setConn_of_connected (D.subtree a) i hi j hj).mono fun _ hk => ⟨a, ha, hk⟩

/-- A walk inside `S` from `a` to `b` joins, inside `nodes D S`, every node holding `a` to every node holding `b`. -/
lemma joined_of_walk {S : Set V} {a b : S} (p : (G.induce S).Walk a b) :
    ∀ {i j : ι}, (a : V) ∈ D.bag i → (b : V) ∈ D.bag j → JoinedIn D.T (nodes D S) i j := by
  induction p with
  | nil => exact fun hi hj => joined_of_mem D (Subtype.prop _) hi hj
  | @cons a c b h p ih =>
    intro i j hi hj
    obtain ⟨k, hak, hck⟩ := D.cover_edge a c h
    exact (joined_of_mem D a.2 hi hak).trans (ih hck hj)

/-- The nodes whose bags meet a connected set form a connected node set. -/
lemma setConn_nodes {S : Set V} (hS : (G.induce S).Connected) : SetConn D.T (nodes D S) := by
  rintro i ⟨a, ha, hai⟩ j ⟨b, hb, hbj⟩
  obtain ⟨p⟩ := hS.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  exact joined_of_walk D p hai hbj

variable {m : ℕ} {B : Fin m → Set V}

/-- Any two node sets `nodes D (B x)`, `nodes D (B y)` meet. -/
lemma nodes_inter (hB : IsMinorModel (⊤ : SimpleGraph (Fin m)) G B) (x y : Fin m) :
    (nodes D (B x) ∩ nodes D (B y)).Nonempty := by
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨a, ha⟩ := hB.nonempty x
    obtain ⟨i, hi⟩ := D.cover_vertex a
    exact ⟨i, ⟨a, ha, hi⟩, ⟨a, ha, hi⟩⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := hB.adj x y (by simpa using hxy)
    obtain ⟨i, hai, hbi⟩ := D.cover_edge a b hab
    exact ⟨i, ⟨a, ha, hai⟩, ⟨b, hb, hbi⟩⟩

/-- Some bag meets all `m` (disjoint) branch sets, so it has at least `m` vertices. -/
lemma exists_large_bag (hB : IsMinorModel (⊤ : SimpleGraph (Fin m)) G B) : ∃ i, m ≤ (D.bag i).card := by
  obtain ⟨i, hi⟩ := helly D.isTree (fun x => nodes D (B x)) (fun x => setConn_nodes D (hB.connected x))
    (nodes_inter D hB)
  choose z hzB hzi using hi
  refine ⟨i, ?_⟩
  have := card_le_card_of_injOn (s := univ) z (fun x _ => hzi x)
    (fun x _ y _ h => eq_of_mem hB (hzB x) (by rw [h]; exact hzB y))
  simpa using this

lemma le_width (hB : IsMinorModel (⊤ : SimpleGraph (Fin m)) G B) : m - 1 ≤ D.width := by
  obtain ⟨i, hi⟩ := exists_large_bag D hB
  exact Nat.sub_le_sub_right (hi.trans (le_sup (f := fun i => (D.bag i).card) (mem_univ i))) 1

end Width

section Trivial

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- The one-bag decomposition: one node (the tree `starGraph none` on `Option Empty`) whose bag is all of `V`. -/
def trivialDecomp : TreeDecomposition G (Option Empty) where
  T := SimpleGraph.starGraph none
  isTree := SimpleGraph.isTree_starGraph none
  bag := fun _ => univ
  cover_vertex := fun _ => ⟨none, mem_univ _⟩
  cover_edge := fun _ _ _ => ⟨none, mem_univ _, mem_univ _⟩
  subtree := fun _ => connected_of_center (c := none) (by simp) (fun w _ => by
    rcases w with _ | e
    · exact Or.inl rfl
    · exact e.elim)

omit [DecidableEq V] in
/-- Every graph has a tree decomposition, so the set in the definition of `treewidth` is nonempty. -/
lemma widths_nonempty :
    {w | ∃ (ι : Type) (_ : Fintype ι) (D : TreeDecomposition G ι), D.width = w}.Nonempty :=
  ⟨_, Option Empty, inferInstance, trivialDecomp G, rfl⟩

end Trivial

end JMinor

open JMinor

/-- The step "It has `K_4` as a minor, so its treewidth is at least `3`" of Remark 4.8 (i) (v3.90 l. 718), for any
`m`: a graph with a `K_m` minor (a minor model `B` of `K_m`) has treewidth at least `m - 1`. -/
theorem treewidth_ge_of_minorModel {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (m : ℕ)
    (B : Fin m → Set V) (hB : IsMinorModel (⊤ : SimpleGraph (Fin m)) G B) : m - 1 ≤ treewidth G := by
  unfold treewidth
  refine le_csInf (widths_nonempty G) ?_
  rintro w ⟨ι, _, D, rfl⟩
  exact le_width D hB

/-- Sanity test of `IsMinorModel` (Remark 4.8 (i), v3.90 l. 718-720, uses minor models): every complete graph `K_m` is a
minor of itself, with the singletons `{x}` as branch sets. -/
theorem minorModel_complete_self (m : ℕ) :
    IsMinorModel (⊤ : SimpleGraph (Fin m)) (⊤ : SimpleGraph (Fin m)) (fun x => {x}) where
  nonempty x := Set.singleton_nonempty x
  disjoint _ _ h := Set.disjoint_singleton.mpr h
  connected x := connected_of_center (c := x) rfl (fun _ hw => Or.inl hw)
  adj x y h := ⟨x, rfl, y, rfl, h⟩

/-- Sanity test of `HasMinor` (Remark 4.8 (i), v3.90 l. 718-720, uses minors): the triangle `K_3` has no `K_4` minor,
since four disjoint nonempty branch sets do not fit in three vertices. -/
theorem not_hasMinor_K4_of_K3 : ¬ HasMinor (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 4)) := by
  rintro ⟨B, hB⟩
  choose z hz using hB.nonempty
  have hinj : Function.Injective z := fun x y h => eq_of_mem hB (hz x) (by rw [h]; exact hz y)
  have := Fintype.card_le_of_injective z hinj
  simp at this

namespace JMinor

/-- The two bags of a width-`2` tree decomposition of the 4-cycle `0 1 2 3`: `{0, 1, 2}` and `{0, 2, 3}`. -/
def cycleBag : Option Unit → Finset (Fin 4)
  | none => {0, 1, 2}
  | some _ => {0, 2, 3}

/-- Every nonempty node set of the 2-node tree `starGraph none` on `Option Unit` is connected. -/
lemma optionUnit_connected (S : Set (Option Unit)) (h : S.Nonempty) :
    ((SimpleGraph.starGraph none).induce S).Connected := by
  obtain ⟨c, hc⟩ := h
  refine connected_of_center hc fun w _ => ?_
  rcases c with _ | ⟨⟩ <;> rcases w with _ | ⟨⟩ <;> simp

/-- A tree decomposition of the 4-cycle on the 2-node tree, bags `{0, 1, 2}` and `{0, 2, 3}`. -/
def cycleDecomp : TreeDecomposition (SimpleGraph.cycleGraph 4) (Option Unit) where
  T := SimpleGraph.starGraph none
  isTree := SimpleGraph.isTree_starGraph none
  bag := cycleBag
  cover_vertex := by decide
  cover_edge := by decide
  subtree := fun v => optionUnit_connected _ (by
    fin_cases v
    · exact ⟨none, by decide⟩
    · exact ⟨none, by decide⟩
    · exact ⟨none, by decide⟩
    · exact ⟨some (), by decide⟩)

lemma cycleDecomp_width : cycleDecomp.width = 2 := by decide

lemma treewidth_cycle4_le : treewidth (SimpleGraph.cycleGraph 4) ≤ 2 := by
  have hmem : cycleDecomp.width ∈ {w | ∃ (ι : Type) (_ : Fintype ι)
      (D : TreeDecomposition (SimpleGraph.cycleGraph 4) ι), D.width = w} :=
    ⟨Option Unit, inferInstance, cycleDecomp, rfl⟩
  unfold treewidth
  exact (Nat.sInf_le hmem).trans cycleDecomp_width.le

end JMinor

/-- Sanity test of `HasMinor` and of `treewidth_ge_of_minorModel` (Remark 4.8 (i), v3.90 l. 718: "It has `K_4` as a
minor, so its treewidth is at least `3`"): the 4-cycle has a tree decomposition of width `2`, so it has no `K_4`
minor. -/
theorem not_hasMinor_K4_of_cycle4 : ¬ HasMinor (SimpleGraph.cycleGraph 4) (⊤ : SimpleGraph (Fin 4)) := by
  rintro ⟨B, hB⟩
  have h1 := treewidth_ge_of_minorModel _ 4 B hB
  have h2 := treewidth_cycle4_le
  omega

namespace JMinor

variable {n : ℕ}

lemma mem_inl_iff {i : Fin n} {x : Fin 4} :
    Sum.inl i ∈ Jbranch n x ↔ (x.val = 0 ∧ (i.val = 0 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10)) ∨
      (x.val = 1 ∧ i.val = 1) ∨ (x.val = 2 ∧ i.val = 2) ∨ (x.val = 3 ∧ 3 ≤ i.val ∧ i.val ≤ 7) := by
  show ((x = 0 ∧ (i.val = 0 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10)) ∨ (x = 1 ∧ i.val = 1) ∨
        (x = 2 ∧ i.val = 2) ∨ (x = 3 ∧ 3 ≤ i.val ∧ i.val ≤ 7)) ↔ _
  fin_cases x <;> simp

lemma mem_inr_iff {j x : Fin 4} : Sum.inr j ∈ Jbranch n x ↔ j.val = (x.val + 1) % 4 := by
  show ((x = 0 ∧ j = 1) ∨ (x = 1 ∧ j = 2) ∨ (x = 2 ∧ j = 3) ∨ (x = 3 ∧ j = 0)) ↔ _
  revert x j
  decide

lemma adj_inl_inr_iff {i : Fin n} {j : Fin 4} : (Jgraph n).Adj (.inl i) (.inr j) ↔ (i.val + 1) % 4 = j.val :=
  Fin.ext_iff

lemma adj_inl_inl_iff {i k : Fin n} : (Jgraph n).Adj (.inl i) (.inl k) ↔ i.val + 1 = k.val ∨ k.val + 1 = i.val :=
  Iff.rfl

/-- Each of the four sets induces a connected subgraph: every path vertex of `Jbranch n x` descends to the apex
`a_{x+1}` of the set, either directly or through the path vertex just before it. -/
lemma jbranch_connected (x : Fin 4) : ((Jgraph n).induce (Jbranch n x)).Connected := by
  refine connected_of_descent (r := .inr ⟨(x.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩) (mem_inr_iff.mpr rfl)
    (Sum.elim (fun i => i.val + 1) (fun _ => 0)) ?_
  rintro (i | j) hw hne
  · have hx := x.isLt
    rw [mem_inl_iff] at hw
    by_cases hr : (i.val + 1) % 4 = (x.val + 1) % 4
    · exact ⟨.inr ⟨(x.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩, mem_inr_iff.mpr rfl, adj_inl_inr_iff.mpr hr,
        by simp⟩
    · refine ⟨.inl ⟨i.val - 1, by omega⟩, mem_inl_iff.mpr ?_, adj_inl_inl_iff.mpr ?_, ?_⟩
      · simp only
        omega
      · simp only
        omega
      · simp only [Sum.elim_inl]
        omega
  · exact absurd (congrArg Sum.inr (Fin.ext (mem_inr_iff.mp hw))) hne

/-- Any two of the four sets are joined by an edge (for `x < y`): `v_1 v_2`, `v_11 a_3`, `v_9 v_8`, `v_2 v_3`,
`a_2 v_6`, `v_3 v_4`. -/
lemma jbranch_adj_of_lt (hn : 11 ≤ n) (x y : Fin 4) (h : x < y) :
    ∃ a ∈ Jbranch n x, ∃ b ∈ Jbranch n y, (Jgraph n).Adj a b := by
  fin_cases x <;> fin_cases y <;> simp at h
  · exact ⟨.inl ⟨0, by omega⟩, mem_inl_iff.mpr (by simp), .inl ⟨1, by omega⟩, mem_inl_iff.mpr (by simp),
      adj_inl_inl_iff.mpr (by simp)⟩
  · exact ⟨.inl ⟨10, by omega⟩, mem_inl_iff.mpr (by simp), .inr 3, mem_inr_iff.mpr (by simp),
      adj_inl_inr_iff.mpr (by simp)⟩
  · exact ⟨.inl ⟨8, by omega⟩, mem_inl_iff.mpr (by simp), .inl ⟨7, by omega⟩, mem_inl_iff.mpr (by simp),
      adj_inl_inl_iff.mpr (by simp)⟩
  · exact ⟨.inl ⟨1, by omega⟩, mem_inl_iff.mpr (by simp), .inl ⟨2, by omega⟩, mem_inl_iff.mpr (by simp),
      adj_inl_inl_iff.mpr (by simp)⟩
  · exact ⟨.inr 2, mem_inr_iff.mpr (by simp), .inl ⟨5, by omega⟩, mem_inl_iff.mpr (by simp),
      (adj_inl_inr_iff.mpr (by simp)).symm⟩
  · exact ⟨.inl ⟨2, by omega⟩, mem_inl_iff.mpr (by simp), .inl ⟨3, by omega⟩, mem_inl_iff.mpr (by simp),
      adj_inl_inl_iff.mpr (by simp)⟩

/-- The four sets of Remark 4.8 (i) form a minor model of `K_4` in `J_n` (for `n ≥ 11`). -/
lemma jbranch_minorModel (hn : 11 ≤ n) : IsMinorModel (⊤ : SimpleGraph (Fin 4)) (Jgraph n) (Jbranch n) where
  nonempty x := ⟨.inr ⟨(x.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩, mem_inr_iff.mpr rfl⟩
  disjoint x y hxy := by
    rw [Set.disjoint_left]
    rintro (i | j) hx hy
    · rw [mem_inl_iff] at hx hy
      exact hxy (Fin.ext (by omega))
    · rw [mem_inr_iff] at hx hy
      have := x.isLt
      have := y.isLt
      exact hxy (Fin.ext (by omega))
  connected := jbranch_connected
  adj x y h := by
    rcases lt_or_gt_of_ne (show x ≠ y by simpa using h) with hxy | hxy
    · exact jbranch_adj_of_lt hn x y hxy
    · obtain ⟨a, ha, b, hb, hab⟩ := jbranch_adj_of_lt hn y x hxy
      exact ⟨b, hb, a, ha, hab.symm⟩

end JMinor

/-- Remark 4.8 (i) (v3.90 l. 718-720): "(i) It has `K_4` as a minor, so its treewidth is at least `3`: the sets
`{a_1, v_1, v_9, v_10, v_11}`, `{a_2, v_2}`, `{a_3, v_3}` and `{a_0, v_4, ..., v_8}` are disjoint, each induces a
connected subgraph, and any two of them are joined by an edge." (`Jbranch n 0`, ..., `Jbranch n 3` are these four
sets; `ℓ = n ≥ 15`.) -/
theorem rem_4_8_i_proved (n : ℕ) (hn : 15 ≤ n) :
    IsMinorModel (⊤ : SimpleGraph (Fin 4)) (Jgraph n) (Jbranch n) ∧ HasMinor (Jgraph n) (⊤ : SimpleGraph (Fin 4)) ∧
      3 ≤ treewidth (Jgraph n) := by
  have hM := jbranch_minorModel (n := n) (by omega)
  exact ⟨hM, ⟨_, hM⟩, treewidth_ge_of_minorModel (Jgraph n) 4 (Jbranch n) hM⟩

end Cereceda
