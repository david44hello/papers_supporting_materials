/-
LeeDiam/Bridge/Graphs.lean — the bridge between the graphs of the two polytopes and two combinatorial graphs: the
graph of ideals (nested, connected difference) and the graph of antichains (connected symmetric difference).
Paper 004 (short v1.50), Section 1 l. 50 ("whose vertices are the indicator vectors of the ideals / antichains") and
Theorem 2.1 (the cited adjacency criterion, l. 141-144).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

Not trust surface: the claims of the paper are stated with `orderDiam`, `chainDiam`, `dO`, `dC` (Defs); these lemmas let
the proofs work with ideals and antichains instead of polytope vertices.
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Vertices
import LeeDiam.Defs.Walks
import LeeDiam.Cited.Lee26

namespace LeeDiam

section Graphs

variable (P : Type) [PartialOrder P]

def idealGraph : SimpleGraph {I : Set P // IsIdeal I} where
  Adj I J := (I.1 ⊆ J.1 ∧ IsConnSet (J.1 \ I.1)) ∨ (J.1 ⊆ I.1 ∧ IsConnSet (I.1 \ J.1))
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by
    rcases h with ⟨_, hc⟩ | ⟨_, hc⟩ <;>
    · obtain ⟨⟨x, hx⟩⟩ := hc.nonempty
      exact hx.2 hx.1⟩

def antichainGraph : SimpleGraph {A : Set P // IsAntichainSet A} where
  Adj A B := IsConnSet (symmDiff A.1 B.1)
  symm := ⟨fun A B h => by
    rw [symmDiff_comm]
    exact h⟩
  loopless := ⟨fun A h => by
    obtain ⟨⟨x, hx⟩⟩ := h.nonempty
    simp at hx⟩

end Graphs

section Metric

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem graphHom_edist_le (mapping : G →g H) (left right : V) :
    H.edist (mapping left) (mapping right) ≤ G.edist left right := by
  change H.edist (mapping left) (mapping right) ≤ ⨅ walk : G.Walk left right, (walk.length : ℕ∞)
  apply le_iInf
  intro walk
  simpa only [SimpleGraph.Walk.length_map] using (walk.map mapping).edist_le

theorem graphIso_edist (equiv : G ≃g H) (left right : V) :
    H.edist (equiv left) (equiv right) = G.edist left right := by
  apply le_antisymm (graphHom_edist_le equiv.toHom left right)
  change G.edist left right ≤ H.edist (equiv left) (equiv right)
  have opposite := graphHom_edist_le equiv.symm.toHom (equiv left) (equiv right)
  change G.edist (equiv.symm (equiv left)) (equiv.symm (equiv right)) ≤
    H.edist (equiv left) (equiv right) at opposite
  simpa only [RelIso.symm_apply_apply] using opposite

theorem graphIso_ediam (equiv : G ≃g H) : H.ediam = G.ediam := by
  apply le_antisymm
  · rw [SimpleGraph.ediam_le_iff]
    intro left right
    obtain ⟨left, rfl⟩ := equiv.surjective left
    obtain ⟨right, rfl⟩ := equiv.surjective right
    rw [graphIso_edist]
    exact SimpleGraph.edist_le_ediam
  · rw [SimpleGraph.ediam_le_iff]
    intro left right
    rw [← graphIso_edist equiv left right]
    exact SimpleGraph.edist_le_ediam

theorem graph_edist_le_iff_list (left right : V) (bound : ℕ) :
    G.edist left right ≤ bound ↔ ∃ states : List V,
      states.head? = some left ∧ states.getLast? = some right ∧
      states.length ≤ bound + 1 ∧ states.IsChain G.Adj := by
  constructor
  · intro distance
    have finite : G.edist left right ≠ ⊤ := by
      have below : G.edist left right < ⊤ := lt_of_le_of_lt distance (by simp)
      exact ne_of_lt below
    obtain ⟨walk, shortest⟩ := SimpleGraph.exists_walk_of_edist_ne_top finite
    have length_le : walk.length ≤ bound := by exact_mod_cast shortest.trans_le distance
    refine ⟨walk.support, ?_, ?_, ?_, walk.isChain_adj_support⟩
    · simp [List.head?_eq_some_head walk.support_ne_nil]
    · simp [List.getLast?_eq_some_getLast walk.support_ne_nil]
    · rw [SimpleGraph.Walk.length_support]
      omega
  · rintro ⟨states, first, last, length_le, chained⟩
    have nonempty : states ≠ [] := by intro same; simp [same] at first
    have first_eq : states.head nonempty = left :=
      Option.some.inj ((List.head?_eq_some_head nonempty).symm.trans first)
    have last_eq : states.getLast nonempty = right :=
      Option.some.inj ((List.getLast?_eq_some_getLast nonempty).symm.trans last)
    have distance := (SimpleGraph.Walk.ofSupport states nonempty chained).edist_le
    rw [SimpleGraph.Walk.length_ofSupport, first_eq, last_eq] at distance
    exact distance.trans (by exact_mod_cast (show states.length - 1 ≤ bound by omega))

end Metric

section Bridge

variable {P : Type} [Fintype P] [PartialOrder P]

omit [Fintype P] in
theorem orderPolytope_eq_dual : orderPolytope P = HibiLi.orderPolytope Pᵒᵈ := by
  ext point
  constructor
  · rintro ⟨bounds, monotone⟩
    exact ⟨bounds, fun left right relation => monotone right left relation⟩
  · rintro ⟨bounds, monotone⟩
    exact ⟨bounds, fun left right relation => monotone right left relation⟩

theorem order_vertex_iff_ideal (point : P → ℝ) :
    HibiLi.IsFace (orderPolytope P) {point} ↔
      ∃ ideal : Set P, IsIdeal ideal ∧ point = HibiLi.setVector ideal := by
  constructor
  · intro face
    have hull : orderPolytope P =
        convexHull ℝ (orderPolytope P ∩ HibiLi.zeroOneVectors P) := by
      rw [orderPolytope_eq_dual]
      exact HibiLi.orderPolytope_eq_convexHull_zeroOne Pᵒᵈ
    have extreme := isExtreme_singleton.mp face.2.isExtreme
    rw [hull] at extreme
    have member : point ∈ orderPolytope P ∩ HibiLi.zeroOneVectors P :=
      extremePoints_convexHull_subset extreme
    have original : point ∈ orderPolytope P := member.1
    refine ⟨{coord | point coord = 1}, ?_, (HibiLi.setVector_support member.2).symm⟩
    intro upper lower relation upper_mem
    change point lower = 1
    change point upper = 1 at upper_mem
    have bound := (original.1 lower).2
    have compared := original.2 lower upper relation
    linarith
  · rintro ⟨ideal, member, rfl⟩
    exact isFace_ideal ideal member

theorem chain_vertex_iff_antichain (point : P → ℝ) :
    HibiLi.IsFace (chainPolytope P) {point} ↔
      ∃ antichain : Set P, IsAntichainSet antichain ∧ point = HibiLi.setVector antichain := by
  constructor
  · intro face
    have extreme := isExtreme_singleton.mp face.2.isExtreme
    change point ∈ Set.extremePoints ℝ (HibiLi.chainPolytope P) at extreme
    rw [HibiLi.chainPolytope_eq_convexHull_zeroOne] at extreme
    have member : point ∈ HibiLi.chainPolytope P ∩ HibiLi.zeroOneVectors P :=
      extremePoints_convexHull_subset extreme
    exact ⟨{coord | point coord = 1}, HibiLi.support_antichain member.1,
      (HibiLi.setVector_support member.2).symm⟩
  · rintro ⟨antichain, member, rfl⟩
    exact isFace_antichain antichain member

omit [Fintype P] [PartialOrder P] in
theorem indicator_injective : Function.Injective (HibiLi.setVector (P := P)) := by
  intro left right same
  ext coord
  rw [← HibiLi.setVector_eq_one left coord, ← HibiLi.setVector_eq_one right coord, same]

theorem idealGraph_iso :
    ∃ e : idealGraph P ≃g polyGraph (orderPolytope P),
      ∀ I : {I : Set P // IsIdeal I}, e I = oVtx I.1 I.2 := by
  let mapping : {I : Set P // IsIdeal I} → {v : P → ℝ // HibiLi.IsFace (orderPolytope P) {v}} :=
    fun ideal => oVtx ideal.1 ideal.2
  have injective : Function.Injective mapping := by
    intro left right same
    apply Subtype.ext
    exact indicator_injective (congrArg Subtype.val same)
  have surjective : Function.Surjective mapping := by
    intro vertex
    obtain ⟨ideal, valid, same⟩ := (order_vertex_iff_ideal vertex.1).mp vertex.2
    exact ⟨⟨ideal, valid⟩, Subtype.ext same.symm⟩
  have bijective : Function.Bijective mapping := ⟨injective, surjective⟩
  refine ⟨{
    toEquiv := Equiv.ofBijective mapping bijective
    map_rel_iff' := ?_ }, fun _ => rfl⟩
  intro left right
  by_cases same : left = right
  · subst right
    simp
  · have distinct : left.1 ≠ right.1 := fun equality => same (Subtype.ext equality)
    have image_distinct : mapping left ≠ mapping right := fun equality => same (injective equality)
    change (mapping left ≠ mapping right ∧ _) ↔ _
    have criterion := (Cited.lee26_thm4 P).1 left.1 right.1 left.2 right.2 distinct
    exact ⟨fun member => criterion.mp member.2,
      fun member => ⟨image_distinct, criterion.mpr member⟩⟩

theorem antichainGraph_iso :
    ∃ e : antichainGraph P ≃g polyGraph (chainPolytope P),
      ∀ A : {A : Set P // IsAntichainSet A}, e A = cVtx A.1 A.2 := by
  let mapping : {A : Set P // IsAntichainSet A} → {v : P → ℝ // HibiLi.IsFace (chainPolytope P) {v}} :=
    fun antichain => cVtx antichain.1 antichain.2
  have injective : Function.Injective mapping := by
    intro left right same
    apply Subtype.ext
    exact indicator_injective (congrArg Subtype.val same)
  have surjective : Function.Surjective mapping := by
    intro vertex
    obtain ⟨antichain, valid, same⟩ := (chain_vertex_iff_antichain vertex.1).mp vertex.2
    exact ⟨⟨antichain, valid⟩, Subtype.ext same.symm⟩
  have bijective : Function.Bijective mapping := ⟨injective, surjective⟩
  refine ⟨{
    toEquiv := Equiv.ofBijective mapping bijective
    map_rel_iff' := ?_ }, fun _ => rfl⟩
  intro left right
  by_cases same : left = right
  · subst right
    simp
  · have distinct : left.1 ≠ right.1 := fun equality => same (Subtype.ext equality)
    have image_distinct : mapping left ≠ mapping right := fun equality => same (injective equality)
    change (mapping left ≠ mapping right ∧ _) ↔ _
    have criterion := (Cited.lee26_thm4 P).2 left.1 right.1 left.2 right.2 distinct
    exact ⟨fun member => criterion.mp member.2,
      fun member => ⟨image_distinct, criterion.mpr member⟩⟩

theorem dO_eq (I J : Set P) (hI : IsIdeal I) (hJ : IsIdeal J) :
    dO I J hI hJ = (idealGraph P).edist ⟨I, hI⟩ ⟨J, hJ⟩ := by
  obtain ⟨equiv, evaluates⟩ := idealGraph_iso (P := P)
  have same := graphIso_edist equiv ⟨I, hI⟩ ⟨J, hJ⟩
  simpa only [evaluates, dO] using same

theorem dC_eq (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B) :
    dC A B hA hB = (antichainGraph P).edist ⟨A, hA⟩ ⟨B, hB⟩ := by
  obtain ⟨equiv, evaluates⟩ := antichainGraph_iso (P := P)
  have same := graphIso_edist equiv ⟨A, hA⟩ ⟨B, hB⟩
  simpa only [evaluates, dC] using same

theorem orderDiam_eq : orderDiam P = (idealGraph P).ediam := by
  obtain ⟨equiv, _⟩ := idealGraph_iso (P := P)
  exact graphIso_ediam equiv

theorem chainDiam_eq : chainDiam P = (antichainGraph P).ediam := by
  obtain ⟨equiv, _⟩ := antichainGraph_iso (P := P)
  exact graphIso_ediam equiv

theorem orderDiam_le_iff (bound : ℕ∞) :
    orderDiam P ≤ bound ↔
      ∀ (I J : Set P) (hI : IsIdeal I) (hJ : IsIdeal J), dO I J hI hJ ≤ bound := by
  rw [orderDiam_eq, SimpleGraph.ediam_le_iff]
  constructor
  · intro all I J hI hJ
    rw [dO_eq]
    exact all ⟨I, hI⟩ ⟨J, hJ⟩
  · intro all left right
    simpa only [dO_eq] using all left.1 right.1 left.2 right.2

theorem chainDiam_le_iff (bound : ℕ∞) :
    chainDiam P ≤ bound ↔ ∀ (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B),
      dC A B hA hB ≤ bound := by
  rw [chainDiam_eq, SimpleGraph.ediam_le_iff]
  constructor
  · intro all A B hA hB
    rw [dC_eq]
    exact all ⟨A, hA⟩ ⟨B, hB⟩
  · intro all left right
    simpa only [dC_eq] using all left.1 right.1 left.2 right.2

theorem dO_le_iff (I J : Set P) (hI : IsIdeal I) (hJ : IsIdeal J) (bound : ℕ) :
    dO I J hI hJ ≤ bound ↔ ∃ states : List {K : Set P // IsIdeal K},
      states.head? = some ⟨I, hI⟩ ∧ states.getLast? = some ⟨J, hJ⟩ ∧
      states.length ≤ bound + 1 ∧ states.IsChain (idealGraph P).Adj := by
  rw [dO_eq]
  exact graph_edist_le_iff_list _ _ _

theorem dC_le_iff (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B) (bound : ℕ) :
    dC A B hA hB ≤ bound ↔ ∃ states : List (Set P),
      IsWalkFromTo states A B ∧ states.length - 1 ≤ bound := by
  rw [dC_eq, graph_edist_le_iff_list]
  constructor
  · rintro ⟨states, first, last, length_le, chained⟩
    have nonempty : states ≠ [] := by intro same; simp [same] at first
    refine ⟨states.map Subtype.val, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · intro empty
      have lengths := congrArg List.length empty
      simp only [List.length_map, List.length_nil] at lengths
      exact nonempty (List.length_eq_zero_iff.mp lengths)
    · intro state member
      obtain ⟨vertex, _, rfl⟩ := List.mem_map.mp member
      exact vertex.2
    · exact List.isChain_map_of_isChain Subtype.val (fun _ _ adjacent => adjacent) chained
    · simp only [List.head?_map, first, Option.map_some]
    · simp only [List.getLast?_map, last, Option.map_some]
    · simp only [List.length_map]
      omega
  · rintro ⟨states, walk, length_le⟩
    let vertices : List {state : Set P // IsAntichainSet state} :=
      states.attachWith IsAntichainSet walk.1.2.1
    have mapped : vertices.map Subtype.val = states := List.attachWith_map_subtype_val _
    have injective : Function.Injective (Option.map (Subtype.val : {S : Set P // IsAntichainSet S} → Set P)) :=
      Option.map_injective Subtype.val_injective
    refine ⟨vertices, ?_, ?_, ?_, ?_⟩
    · apply injective
      change vertices.head?.map Subtype.val = some A
      rw [← List.head?_map, mapped]
      exact walk.2.1
    · apply injective
      change vertices.getLast?.map Subtype.val = some B
      rw [← List.getLast?_map, mapped]
      exact walk.2.2
    · have same_length : vertices.length = states.length := by
        simpa only [List.length_map] using congrArg List.length mapped
      omega
    · change vertices.IsChain (fun left right => IsConnSet (symmDiff left.1 right.1))
      apply (List.isChain_map (R := fun left right : Set P => IsConnSet (symmDiff left right))
        Subtype.val (l := vertices)).mp
      rw [mapped]
      exact walk.1.2.2

end Bridge

end LeeDiam
