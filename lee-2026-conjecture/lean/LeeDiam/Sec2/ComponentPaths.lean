/-
Component paths and bounds.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Bridge.Graphs
import LeeDiam.Sec4.Comps

namespace LeeDiam

section ComponentBounds

variable {P : Type} [PartialOrder P]

theorem induce_reachable_iff (D : Set P) (x y : D) :
    ((compGraph P).induce D).Reachable x y ↔ y.1 ∈ S4.reach D x.1 := by
  constructor
  · rintro ⟨walk⟩
    induction walk with
    | nil => exact .refl
    | @cons x middle y edge walk ih =>
      exact Relation.ReflTransGen.head ⟨x.2, middle.2, edge⟩ ih
  · intro reached
    change Relation.ReflTransGen _ _ _ at reached
    have key : ∀ (u v : P) (path : Relation.ReflTransGen
        (fun a b => a ∈ D ∧ b ∈ D ∧ Comp a b) u v),
        ∀ (hu : u ∈ D) (hv : v ∈ D),
        ((compGraph P).induce D).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
      intro u v path
      induction path with
      | refl => intro _ _; exact .rfl
      | @tail middle endpoint path edge ih =>
        intro hu hv
        exact (ih hu edge.1).trans (SimpleGraph.Adj.reachable edge.2.2)
    exact key _ _ reached x.2 y.2

def componentSet (D : Set P) (C : ((compGraph P).induce D).ConnectedComponent) : Set P :=
  {x | ∃ hx : x ∈ D, ((compGraph P).induce D).connectedComponentMk ⟨x, hx⟩ = C}

theorem componentSet_mk (D : Set P) (x : D) :
    componentSet D (((compGraph P).induce D).connectedComponentMk x) = S4.reach D x.1 := by
  ext y
  constructor
  · rintro ⟨hy, equal⟩
    exact (induce_reachable_iff D x ⟨y, hy⟩).mp
      (SimpleGraph.ConnectedComponent.exact equal).symm
  · intro reached
    have hy := (S4.isComponent_reach x.2).2.1 reached
    exact ⟨hy, SimpleGraph.ConnectedComponent.sound
      ((induce_reachable_iff D x ⟨y, hy⟩).mpr reached).symm⟩

theorem componentSet_component (D : Set P)
    (C : ((compGraph P).induce D).ConnectedComponent) : IsComponent (componentSet D C) D := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h x => rw [componentSet_mk]; exact S4.isComponent_reach x.2

theorem componentSet_injective (D : Set P) : Function.Injective (componentSet D) := by
  intro C C' equal
  obtain ⟨x⟩ := (componentSet_component D C).1.nonempty
  have hx' : x.1 ∈ componentSet D C' := equal ▸ x.2
  obtain ⟨member, equation⟩ := x.2
  obtain ⟨member', equation'⟩ := hx'
  exact equation.symm.trans equation'

theorem componentSet_surjective (D : Set P) {K : Set P} (hK : IsComponent K D) :
    ∃ C, componentSet D C = K := by
  obtain ⟨x⟩ := hK.1.nonempty
  let vertex : D := ⟨x.1, hK.2.1 x.2⟩
  refine ⟨((compGraph P).induce D).connectedComponentMk vertex, ?_⟩
  apply S4.comp_eq_of_mem (componentSet_component _ _) hK
  · exact ⟨vertex.2, rfl⟩
  · exact x.2

theorem component_enumeration [Fintype P] (D : Set P) :
    ∃ L : List (Set P), L.Nodup ∧ (∀ K, K ∈ L ↔ IsComponent K D) ∧ L.length = numComp D := by
  classical
  let : Fintype ((compGraph P).induce D).ConnectedComponent := Fintype.ofFinite _
  let vertices := (Finset.univ : Finset ((compGraph P).induce D).ConnectedComponent).toList
  refine ⟨vertices.map (componentSet D), ?_, ?_, ?_⟩
  · exact (Finset.nodup_toList _).map (componentSet_injective D)
  · intro K
    constructor
    · rintro member
      obtain ⟨C, _, rfl⟩ := List.mem_map.mp member
      exact componentSet_component D C
    · intro component
      obtain ⟨C, rfl⟩ := componentSet_surjective D component
      exact List.mem_map.mpr ⟨C, by simp [vertices], rfl⟩
  · simp [vertices, numComp, Nat.card_eq_fintype_card]

theorem numComp_le_width [Fintype P] (D : Set P) : numComp D ≤ width P := by
  classical
  let G := (compGraph P).induce D
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let representative : G.ConnectedComponent → P := fun C => C.out.1
  have injective : Function.Injective representative := by
    intro C C' same
    have equal : C.out = C'.out := Subtype.ext same
    exact C.out_eq.symm.trans ((congrArg G.connectedComponentMk equal).trans C'.out_eq)
  let A := Finset.univ.image representative
  have antichain : IsAntichainSet (A : Set P) := by
    rw [S4.isAntichainSet_iff_comp]
    intro x hx y hy comparable
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨C', _, rfl⟩ := Finset.mem_image.mp hy
    have same : C = C' := C.out_eq.symm.trans
      ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj comparable).trans C'.out_eq)
    subst C'
    exact comparable.elim (lt_irrefl _) (lt_irrefl _)
  have cardinal : A.card = numComp D := by
    simp [A, Finset.card_image_of_injective _ injective, numComp, Nat.card_eq_fintype_card, G]
  apply le_csSup
  · refine ⟨Fintype.card P, ?_⟩
    rintro n ⟨B, _, rfl⟩
    exact Finset.card_le_univ B
  · exact ⟨A, antichain, cardinal⟩

theorem antichain_distance_le_numComp [Fintype P] (A B : Set P)
    (hA : IsAntichainSet A) (hB : IsAntichainSet B) : dC A B hA hB ≤ numComp (symmDiff A B) := by
  obtain ⟨L, nodup, components, length⟩ := component_enumeration (symmDiff A B)
  apply (dC_le_iff A B hA hB _).mpr
  refine ⟨L.scanl symmDiff A, S4.components_walk A B hA hB L nodup components, ?_⟩
  simp only [List.length_scanl, Nat.add_sub_cancel, length, le_refl]

theorem chain_diameter_le_width [Fintype P] : chainDiam P ≤ width P := by
  apply (chainDiam_le_iff _).mpr
  intro A B hA hB
  exact (antichain_distance_le_numComp A B hA hB).trans
    (by exact_mod_cast numComp_le_width (symmDiff A B))

end ComponentBounds

end LeeDiam


namespace LeeDiam

section IdealComponents

variable {P : Type} [PartialOrder P]

theorem ideal_difference_closed (I J : Set P) (hI : IsIdeal I) (hJ : IsIdeal J) :
    IsCompUnion (I \ J) (symmDiff I J) := by
  refine ⟨fun _ member => Set.mem_symmDiff.mpr (Or.inl member), ?_⟩
  intro x hx y hy comparable
  rcases Set.mem_symmDiff.mp hy with hy | hy
  · exact hy
  · rcases comparable with below | above
    · exact False.elim (hx.2 (hJ below.le hy.1))
    · exact False.elim (hy.2 (hI above.le hx.1))

theorem ideal_adj_of_connected_difference {I J : Set P} (hI : IsIdeal I) (hJ : IsIdeal J)
    (connected : IsConnSet (symmDiff I J)) : (idealGraph P).Adj ⟨I, hI⟩ ⟨J, hJ⟩ := by
  classical
  by_cases subset : I ⊆ J
  · left
    refine ⟨subset, ?_⟩
    have difference : symmDiff I J = J \ I := by
      ext x
      simp only [Set.mem_symmDiff, Set.mem_sdiff]
      have := @subset x
      tauto
    rwa [difference] at connected
  · obtain ⟨x, hxI, hxJ⟩ := Set.not_subset.mp subset
    have hx : x ∈ symmDiff I J := Set.mem_symmDiff.mpr (Or.inl ⟨hxI, hxJ⟩)
    have closed := ideal_difference_closed I J hI hJ
    have all : symmDiff I J ⊆ I \ J := by
      intro y hy
      have reaches := S4.rtg_of_isConnSet connected Set.Subset.rfl hx hy
      clear hy
      induction reaches with
      | refl => exact ⟨hxI, hxJ⟩
      | tail _ edge ih => exact closed.2 _ ih _ edge.2.1 edge.2.2
    have subset' : J ⊆ I := by
      intro y hy
      by_contra outside
      exact (all (Set.mem_symmDiff.mpr (Or.inr ⟨hy, outside⟩))).2 hy
    right
    refine ⟨subset', ?_⟩
    have difference : symmDiff I J = I \ J := by
      ext y
      simp only [Set.mem_symmDiff, Set.mem_sdiff]
      have := @subset' y
      tauto
    rwa [difference] at connected

theorem ideal_exchange_ideal (I J Q : Set P) (hI : IsIdeal I) (hJ : IsIdeal J)
    (hQ : IsCompUnion Q (symmDiff I J)) : IsIdeal (symmDiff I Q) := by
  intro x y relation hx
  rw [Set.mem_symmDiff] at hx ⊢
  by_cases equal : y = x
  · simpa only [equal] using hx
  have comparable : Comp x y := Or.inr (lt_of_le_of_ne relation equal)
  rcases hx with hx | hx
  · left
    refine ⟨hI relation hx.1, ?_⟩
    intro hyQ
    have hyD := Set.mem_symmDiff.mp (hQ.1 hyQ)
    have hyJ : y ∉ J := by
      rcases hyD with hyD | hyD
      · exact hyD.2
      · exact False.elim (hyD.2 (hI relation hx.1))
    have hxJ : x ∉ J := fun member => hyJ (hJ relation member)
    exact hx.2 (hQ.2 y hyQ x (Set.mem_symmDiff.mpr (Or.inl ⟨hx.1, hxJ⟩))
      (S4.comp_symm comparable))
  · have hxJ : x ∈ J := by
      rcases Set.mem_symmDiff.mp (hQ.1 hx.1) with member | member
      · exact False.elim (hx.2 member.1)
      · exact member.1
    have hyJ := hJ relation hxJ
    by_cases hyI : y ∈ I
    · left
      refine ⟨hyI, ?_⟩
      intro hyQ
      rcases Set.mem_symmDiff.mp (hQ.1 hyQ) with member | member
      · exact member.2 hyJ
      · exact member.2 hyI
    · right
      exact ⟨hQ.2 x hx.1 y (Set.mem_symmDiff.mpr (Or.inr ⟨hyJ, hyI⟩)) comparable, hyI⟩

theorem ideal_component_states (I J : Set P) (hI : IsIdeal I) (hJ : IsIdeal J)
    (L : List (Set P)) (nodup : L.Nodup)
    (components : ∀ C, C ∈ L ↔ IsComponent C (symmDiff I J)) :
    ∀ X ∈ L.scanl symmDiff I, IsIdeal X := by
  intro X member
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem member
  let Q : Set P := {x | ∃ C ∈ L.take i, x ∈ C}
  have closed : IsCompUnion Q (symmDiff I J) := by
    constructor
    · rintro x ⟨C, hC, hx⟩
      exact ((components C).mp (List.mem_of_mem_take hC)).2.1 hx
    · rintro x ⟨C, hC, hx⟩ y hy comparable
      exact ⟨C, hC, S4.comp_closed ((components C).mp (List.mem_of_mem_take hC)) hx hy comparable⟩
  have equal : (L.scanl symmDiff I)[i] = symmDiff I Q := by
    ext x
    rw [S4.mem_scanl_symmDiff I L (S4.comps_pairwise nodup components) hi x]
    change (x ∈ I ↔ x ∉ Q) ↔ x ∈ symmDiff I Q
    rw [Set.mem_symmDiff]
    tauto
  rw [equal]
  exact ideal_exchange_ideal I J Q hI hJ closed

theorem ideal_components_distance [Fintype P] (I J : Set P) (hI : IsIdeal I) (hJ : IsIdeal J)
    (L : List (Set P)) (nodup : L.Nodup)
    (components : ∀ C, C ∈ L ↔ IsComponent C (symmDiff I J)) :
    dO I J hI hJ ≤ L.length := by
  let states := L.scanl symmDiff I
  have ideals : ∀ X ∈ states, IsIdeal X := ideal_component_states I J hI hJ L nodup components
  let lifted := states.attachWith IsIdeal ideals
  apply (dO_le_iff I J hI hJ _).mpr
  refine ⟨lifted, ?_, ?_, ?_, ?_⟩
  · apply Option.map_injective Subtype.val_injective
    simp [lifted, states]
  · have endpoint : states.getLast? = some J := by
      rw [List.getLast?_scanl, Option.some_inj]
      ext x
      rw [S4.mem_foldl_symmDiff I L (S4.comps_pairwise nodup components) x,
        S4.comps_cover components x, Set.mem_symmDiff]
      tauto
    apply Option.map_injective Subtype.val_injective
    simpa [lifted] using endpoint
  · simp [lifted, states]
  · apply List.isChain_iff_getElem.mpr
    intro i hi
    apply ideal_adj_of_connected_difference
    change IsConnSet (symmDiff (lifted[i]).1 (lifted[i + 1]).1)
    simp only [lifted, List.getElem_attachWith]
    rw [List.getElem_succ_scanl, symmDiff_symmDiff_cancel_left]
    exact ((components _).mp (List.getElem_mem (by simpa [lifted, states] using hi))).1

end IdealComponents

end LeeDiam

namespace LeeDiam

theorem ideal_distance_le_numComp {P : Type} [Fintype P] [PartialOrder P]
    (I J : Set P) (hI : IsIdeal I) (hJ : IsIdeal J) : dO I J hI hJ ≤ numComp (symmDiff I J) := by
  obtain ⟨L, nodup, components, length⟩ := component_enumeration (symmDiff I J)
  rw [← length]
  exact ideal_components_distance I J hI hJ L nodup components

theorem order_diameter_le_width {P : Type} [Fintype P] [PartialOrder P] : orderDiam P ≤ width P := by
  apply (orderDiam_le_iff _).mpr
  intro I J hI hJ
  exact (ideal_distance_le_numComp I J hI hJ).trans
    (by exact_mod_cast numComp_le_width (symmDiff I J))

theorem component_bounds_all (P : Type) [Fintype P] [PartialOrder P] :
    (∀ (I J : Set P) (hI : IsIdeal I) (hJ : IsIdeal J), dO I J hI hJ ≤ numComp (symmDiff I J)) ∧
    (∀ (A B : Set P), IsAntichainSet A → IsAntichainSet B → ∀ L : List (Set P), L.Nodup →
      (∀ C, C ∈ L ↔ IsComponent C (symmDiff A B)) → IsWalkFromTo (L.scanl symmDiff A) A B) ∧
    (∀ (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B), dC A B hA hB ≤ numComp (symmDiff A B)) ∧
    orderDiam P ≤ width P ∧ chainDiam P ≤ width P :=
  ⟨ideal_distance_le_numComp, S4.components_walk, antichain_distance_le_numComp,
    order_diameter_le_width, chain_diameter_le_width⟩

end LeeDiam


