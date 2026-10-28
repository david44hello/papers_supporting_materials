/-
LeeDiam/Sec4/Comps.lean — components of a set (sec 2 of paper 004): closure, disjointness, existence, and the walk
that exchanges the components of `A △ B` one at a time, in any order (Proposition 2.3, the walk claim).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Walks
import LeeDiam.Sec4.Merge

namespace LeeDiam.S4

section Components

variable {P : Type} [PartialOrder P]

/-- A component is closed under comparability inside its set. -/
theorem comp_closed {D S : Set P} (hD : IsComponent D S) {x y : P} (hx : x ∈ D) (hy : y ∈ S) (hxy : Comp x y) :
    y ∈ D := by
  have hconn : IsConnSet (insert y D) := isConnSet_insert hD.1 hx (comp_symm hxy)
  have hsub : insert y D ⊆ S := Set.insert_subset hy hD.2.1
  rw [← hD.2.2 _ hconn (Set.subset_insert y D) hsub]
  exact Set.mem_insert y D

/-- Two components that meet are equal. -/
theorem comp_eq_of_mem {D D' S : Set P} (hD : IsComponent D S) (hD' : IsComponent D' S) {x : P} (hx : x ∈ D)
    (hx' : x ∈ D') : D = D' := by
  have hconn : IsConnSet (D ∪ D') := isConnSet_union_of_inter hD.1 hD'.1 ⟨x, hx, hx'⟩
  have hsub : D ∪ D' ⊆ S := Set.union_subset hD.2.1 hD'.2.1
  have h1 := hD.2.2 _ hconn Set.subset_union_left hsub
  have h2 := hD'.2.2 _ hconn Set.subset_union_right hsub
  rw [← h1, h2]

theorem comp_disjoint {D D' S : Set P} (hD : IsComponent D S) (hD' : IsComponent D' S) (hne : D ≠ D') :
    Disjoint D D' :=
  Set.disjoint_left.2 fun _ hx hx' => hne (comp_eq_of_mem hD hD' hx hx')

/-- The elements reached from `x` through comparable pairs inside `S`. -/
def reach (S : Set P) (x : P) : Set P := {y | Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ Comp u v) x y}

theorem mem_reach_self (S : Set P) (x : P) : x ∈ reach S x := Relation.ReflTransGen.refl

/-- For `x ∈ S`, `reach S x` is the component of `S` that contains `x`. -/
theorem isComponent_reach {S : Set P} {x : P} (hx : x ∈ S) : IsComponent (reach S x) S := by
  have hKS : reach S x ⊆ S := by
    intro y hy
    induction hy with
    | refl => exact hx
    | tail _ huv _ => exact huv.2.1
  have hconn : IsConnSet (reach S x) := by
    refine isConnSet_of_rtg (mem_reach_self S x) fun y hy => ?_
    induction hy with
    | refl => exact Relation.ReflTransGen.refl
    | @tail u v hu huv ih => exact ih.tail ⟨hu, hu.tail huv, huv.2.2⟩
  refine ⟨hconn, hKS, fun C' hC' hKC' hC'S => ?_⟩
  refine Set.Subset.antisymm (fun y hy => ?_) hKC'
  exact rtg_of_isConnSet hC' hC'S (hKC' (mem_reach_self S x)) hy

/-- Every element of `S` lies in a component of `S`. -/
theorem comp_exists {S : Set P} {x : P} (hx : x ∈ S) : ∃ D, IsComponent D S ∧ x ∈ D :=
  ⟨reach S x, isComponent_reach hx, mem_reach_self S x⟩

end Components

section ScanWalk

variable {P : Type} [PartialOrder P]

omit [PartialOrder P] in
/-- Membership in an iterated symmetric difference with pairwise disjoint sets. -/
theorem mem_foldl_symmDiff (A : Set P) (L : List (Set P)) (hL : L.Pairwise Disjoint) (x : P) :
    x ∈ L.foldl symmDiff A ↔ (x ∈ A ↔ ¬ ∃ D ∈ L, x ∈ D) := by
  induction L generalizing A with
  | nil => simp
  | cons D L ih =>
    rw [List.foldl_cons, ih _ (List.pairwise_cons.1 hL).2, Set.mem_symmDiff]
    have hdis := (List.pairwise_cons.1 hL).1
    by_cases hxD : x ∈ D
    · have : ¬ ∃ D' ∈ L, x ∈ D' := fun ⟨D', hD', hxD'⟩ => Set.disjoint_left.1 (hdis D' hD') hxD hxD'
      simp only [List.mem_cons, exists_eq_or_imp, hxD, this]
      tauto
    · simp [hxD]

omit [PartialOrder P] in
theorem mem_scanl_symmDiff (A : Set P) (L : List (Set P)) (hL : L.Pairwise Disjoint) {i : ℕ}
    (hi : i < (L.scanl symmDiff A).length) (x : P) :
    x ∈ (L.scanl symmDiff A)[i] ↔ (x ∈ A ↔ ¬ ∃ D ∈ L.take i, x ∈ D) := by
  rw [List.getElem_scanl, mem_foldl_symmDiff A _ (hL.sublist (List.take_sublist i L)) x]

/-- The components of `S` listed by `L` (without repetition) are pairwise disjoint. -/
theorem comps_pairwise {S : Set P} {L : List (Set P)} (hnd : L.Nodup) (hL : ∀ C, C ∈ L ↔ IsComponent C S) :
    L.Pairwise Disjoint :=
  hnd.pairwise_of_forall_ne fun D hD D' hD' hne => comp_disjoint ((hL D).1 hD) ((hL D').1 hD') hne

/-- The components listed by `L` cover `S`. -/
theorem comps_cover {S : Set P} {L : List (Set P)} (hL : ∀ C, C ∈ L ↔ IsComponent C S) (x : P) :
    (∃ D ∈ L, x ∈ D) ↔ x ∈ S := by
  constructor
  · rintro ⟨D, hD, hxD⟩
    exact ((hL D).1 hD).2.1 hxD
  · intro hx
    obtain ⟨D, hD, hxD⟩ := comp_exists hx
    exact ⟨D, (hL D).2 hD, hxD⟩

/-- Proposition 2.3, the walk claim: exchanging the components of `A △ B` one at a time, in the order of `L`, gives a
walk from `A` to `B`. -/
theorem components_walk (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B) (L : List (Set P))
    (hnd : L.Nodup) (hL : ∀ C, C ∈ L ↔ IsComponent C (symmDiff A B)) : IsWalkFromTo (L.scanl symmDiff A) A B := by
  have hpw := comps_pairwise hnd hL
  refine ⟨⟨List.scanl_ne_nil, ?_, ?_⟩, by simp, ?_⟩
  · intro X hX
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hX
    rw [isAntichainSet_iff_comp]
    intro x hx y hy hxy
    rw [mem_scanl_symmDiff A L hpw hi] at hx hy
    rw [isAntichainSet_iff_comp] at hA hB
    have hU : ∀ z, (∃ D ∈ L.take i, z ∈ D) → z ∈ symmDiff A B ∧ ∀ w ∈ symmDiff A B, Comp z w →
        ∃ D ∈ L.take i, w ∈ D := by
      rintro z ⟨D, hD, hzD⟩
      have hDc := (hL D).1 (List.mem_of_mem_take hD)
      exact ⟨hDc.2.1 hzD, fun w hw hzw => ⟨D, hD, comp_closed hDc hzD hw hzw⟩⟩
    by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
    · exact hA x hxA y hyA hxy
    · have hyU := (not_not.1 (mt hy.2 hyA))
      have hyB : y ∈ B := by
        have := (hU y hyU).1
        rw [Set.mem_symmDiff] at this
        tauto
      have hxB : x ∉ B := fun hxB => hB x hxB y hyB hxy
      have hxS : x ∈ symmDiff A B := Set.mem_symmDiff.2 (Or.inl ⟨hxA, hxB⟩)
      exact hx.1 hxA ((hU y hyU).2 x hxS (comp_symm hxy))
    · have hxU := (not_not.1 (mt hx.2 hxA))
      have hxB : x ∈ B := by
        have := (hU x hxU).1
        rw [Set.mem_symmDiff] at this
        tauto
      have hyB : y ∉ B := fun hyB => hB x hxB y hyB hxy
      have hyS : y ∈ symmDiff A B := Set.mem_symmDiff.2 (Or.inl ⟨hyA, hyB⟩)
      exact hy.1 hyA ((hU x hxU).2 y hyS hxy)
    · have hxU := (not_not.1 (mt hx.2 hxA))
      have hyU := (not_not.1 (mt hy.2 hyA))
      have hxB : x ∈ B := by
        have := (hU x hxU).1
        rw [Set.mem_symmDiff] at this
        tauto
      have hyB : y ∈ B := by
        have := (hU y hyU).1
        rw [Set.mem_symmDiff] at this
        tauto
      exact hB x hxB y hyB hxy
  · rw [List.isChain_iff_getElem]
    intro i hi
    rw [List.getElem_succ_scanl, symmDiff_symmDiff_cancel_left]
    have hi' : i < L.length := by
      rw [List.length_scanl] at hi
      omega
    exact ((hL _).1 (List.getElem_mem hi')).1
  · rw [List.getLast?_scanl, Option.some_inj]
    ext x
    rw [mem_foldl_symmDiff A L hpw x, comps_cover hL x, Set.mem_symmDiff]
    tauto

end ScanWalk

end LeeDiam.S4

