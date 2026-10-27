/-
HibiLi — coordinate transport for the center switch.
-/
import HibiLi.Example21.CenterSwitch
import HibiLi.Example21.CenterRegions
import HibiLi.Example21.CenterDimension
import HibiLi.Polytope.Affine
import HibiLi.Polytope.IntersectionFaces

namespace HibiLi.Example21.CenterGeometry

open Finset CenterSwitch

local instance : DecidableLT XElem := decidableLTOfDecidableLE

abbrev center := canonical.toSwitch
abbrev Coord := center.P'

def coordinateIndex : Fin 4 ≃ Coord where
  toFun := ![canonical.pa, canonical.pb, canonical.pg, canonical.ph]
  invFun := fun coord => match coord.1 with
    | .a => 0 | .b => 1 | .c => 0 | .g => 2 | .h => 3
  left_inv := by intro index; fin_cases index <;> rfl
  right_inv := by
    rintro ⟨coord, valid⟩
    cases coord <;> try rfl
    exact False.elim (valid rfl)

noncomputable def canonicalEquiv : (Coord → ℝ) ≃ᵃ[ℝ] (Fin 4 → ℝ) :=
  (LinearEquiv.piCongrLeft' ℝ (fun _ : Coord => ℝ) coordinateIndex.symm).toAffineEquiv

@[simp] theorem canonicalEquiv_apply (point : Coord → ℝ) (index : Fin 4) :
    canonicalEquiv point index = point (coordinateIndex index) := rfl

theorem coord_cases (coord : Coord) : coord = canonical.pa ∨ coord = canonical.pb ∨
    coord = canonical.pg ∨ coord = canonical.ph := by
  rcases coord with ⟨coord, valid⟩
  cases coord
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact False.elim (valid rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem mem_ideal_iff (coord : Coord) : coord ∈ center.I' ↔
    coord = canonical.pa ∨ coord = canonical.pb := by
  change (¬ XElem.c ≤ coord.1) ↔ _
  rcases coord_cases coord with rfl | rfl | rfl | rfl <;> decide

theorem off_lower (point : Coord → ℝ) :
    ∀ coord : Coord, coord.1 ∈ center.I → coord.1 ≠ canonical.a →
      coord.1 ≠ canonical.b → point coord = 0 := by
  intro coord member ne_a ne_b
  rcases (mem_ideal_iff coord).mp member with rfl | rfl
  · exact False.elim (ne_a rfl)
  · exact False.elim (ne_b rfl)

theorem off_upper (point : Coord → ℝ) :
    ∀ coord : Coord, coord.1 ∉ center.I → coord.1 ≠ canonical.g' →
      coord.1 ≠ canonical.h' → point coord = 1 := by
  intro coord member ne_g ne_h
  rcases coord_cases coord with rfl | rfl | rfl | rfl
  · exact False.elim (member (show ¬ XElem.c ≤ XElem.a by decide))
  · exact False.elim (member (show ¬ XElem.c ≤ XElem.b by decide))
  · exact False.elim (ne_g rfl)
  · exact False.elim (ne_h rfl)

theorem mem_B_iff (point : Coord → ℝ) : point ∈ center.B ↔
    0 ≤ point canonical.pa ∧ 0 ≤ point canonical.pb ∧
    max (point canonical.pa) (point canonical.pb) ≤ min (point canonical.pg) (point canonical.ph) ∧
    point canonical.pg ≤ 1 ∧ point canonical.ph ≤ 1 := by
  constructor
  · intro member
    exact Proofs.Lemma44.E0_subset canonical rfl rfl rfl rfl
      (by rwa [E0_eq_B])
  · rintro ⟨ha, hb, hm, hg, hh⟩
    exact Proofs.Lemma44.mem_B_of_system canonical rfl rfl rfl rfl
      (off_lower point) (off_upper point) ha hb hm hg hh

theorem mem_base_iff (point : Coord → ℝ) :
    canonicalEquiv point ∈ CenterRegions.base ↔ point ∈ center.B := by
  rw [mem_B_iff]
  simp only [CenterRegions.base, CenterRegions.body, Set.mem_ofPred_eq,
    canonicalEquiv_apply, coordinateIndex, Equiv.coe_fn_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, and_true,
    max_le_iff, le_min_iff]
  tauto

theorem image_B : canonicalEquiv '' center.B = CenterRegions.base := by
  ext point
  obtain ⟨point, rfl⟩ := canonicalEquiv.surjective point
  constructor
  · rintro ⟨original, member, same⟩
    obtain rfl := canonicalEquiv.injective same
    exact (mem_base_iff _).mpr member
  · intro member
    exact ⟨point, (mem_base_iff _).mp member, rfl⟩

theorem lowBranches_cases {branch : Finset Coord} (valid : branch ∈ center.lowBranches) :
    branch = ∅ ∨ branch = {canonical.pa} ∨ branch = {canonical.pb} := by
  classical
  simp only [Switch.lowBranches, mem_filter, mem_univ, true_and] at valid
  have info := valid
  have members : ∀ coord ∈ branch, coord = canonical.pa ∨ coord = canonical.pb :=
    fun coord member => (mem_ideal_iff coord).mp (info.1 member)
  by_cases ha : canonical.pa ∈ branch
  · right; left
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨ha, fun coord member => ?_⟩
    rcases members coord member with rfl | rfl
    · rfl
    · exfalso
      have comparable := info.2.1 ha member (by decide : canonical.pa ≠ canonical.pb)
      rcases comparable with impossible | impossible <;> revert impossible <;> decide
  · by_cases hb : canonical.pb ∈ branch
    · right; right
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hb, fun coord member => (members coord member).resolve_left (fun same => ha (same ▸ member))⟩
    · left
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro coord member
      rcases members coord member with rfl | rfl <;> contradiction

theorem upBranches_cases {branch : Option Coord} (valid : branch ∈ center.upBranches) :
    branch = none ∨ branch = some canonical.pg ∨ branch = some canonical.ph := by
  classical
  simp only [Switch.upBranches, mem_insert, mem_image, mem_filter, mem_univ, true_and] at valid
  rcases valid with rfl | ⟨coord, above, rfl⟩
  · exact Or.inl rfl
  · rcases coord_cases coord with rfl | rfl | rfl | rfl
    · exact False.elim ((by decide : ¬ center.q < canonical.pa.1) above)
    · exact False.elim ((by decide : ¬ center.q < canonical.pb.1) above)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem L_eq {point : Coord → ℝ} (member : point ∈ center.B) :
    center.L point = max (point canonical.pa) (point canonical.pb) := by
  classical
  unfold Switch.L
  apply le_antisymm
  · apply Finset.sup'_le
    intro branch valid
    rcases lowBranches_cases valid with rfl | rfl | rfl
    · simpa [Switch.chainSum] using le_max_of_le_left (mem_B_iff point |>.mp member).1
    · simp [Switch.chainSum]
    · simp [Switch.chainSum]
  · apply max_le
    · simpa only [Switch.chainSum, Finset.sum_singleton] using
        Finset.le_sup' (center.chainSum · point) canonical.singleton_pa_mem
    · simpa only [Switch.chainSum, Finset.sum_singleton] using
        Finset.le_sup' (center.chainSum · point) canonical.singleton_pb_mem

theorem upper_valid (cut : Bool) :
    (some (if cut then canonical.ph else canonical.pg)) ∈ center.upBranches := by
  classical
  cases cut <;> simp [Switch.upBranches] <;> decide

theorem U_eq {point : Coord → ℝ} (member : point ∈ center.B) :
    center.U point = min (point canonical.pg) (point canonical.ph) := by
  classical
  apply le_antisymm
  · apply le_min
    · exact Finset.inf'_le (center.upVal · point) (upper_valid false)
    · exact Finset.inf'_le (center.upVal · point) (upper_valid true)
  · apply Finset.le_inf'
    intro branch valid
    rcases upBranches_cases valid with rfl | rfl | rfl
    · exact (min_le_left _ _).trans (mem_B_iff point |>.mp member).2.2.2.1
    · exact min_le_left _ _
    · exact min_le_right _ _

noncomputable def lowerBranch (cut : Bool) : Finset Coord :=
  {if cut then canonical.pa else canonical.pb}

def upperBranch (cut : Bool) : Option Coord :=
  some (if cut then canonical.ph else canonical.pg)

theorem lower_valid (cut : Bool) : lowerBranch cut ∈ center.lowBranches := by
  cases cut
  · exact canonical.singleton_pb_mem
  · exact canonical.singleton_pa_mem

theorem image_domL (cut : Bool) :
    canonicalEquiv '' center.domL (lowerBranch cut) = CenterRegions.body (some cut) none := by
  ext point
  obtain ⟨point, rfl⟩ := canonicalEquiv.surjective point
  rw [Set.mem_image_iff_of_inverse canonicalEquiv.symm_apply_apply canonicalEquiv.apply_symm_apply,
    canonicalEquiv.symm_apply_apply]
  change (point ∈ center.B ∧ center.L point = _) ↔ _
  by_cases member : point ∈ center.B
  · have base := (mem_base_iff point).mpr member
    simp only [member, true_and, L_eq member]
    cases cut <;>
      simp_all [lowerBranch, Switch.chainSum, CenterRegions.base, CenterRegions.body,
        canonicalEquiv_apply, coordinateIndex]
  · have outside := (mem_base_iff point).not.mpr member
    cases cut <;>
      simp_all [CenterRegions.base, CenterRegions.body, canonicalEquiv_apply, coordinateIndex]

theorem image_domU (cut : Bool) :
    canonicalEquiv '' center.domU (upperBranch cut) = CenterRegions.body none (some cut) := by
  ext point
  obtain ⟨point, rfl⟩ := canonicalEquiv.surjective point
  rw [Set.mem_image_iff_of_inverse canonicalEquiv.symm_apply_apply canonicalEquiv.apply_symm_apply,
    canonicalEquiv.symm_apply_apply]
  change (point ∈ center.B ∧ center.U point = _) ↔ _
  by_cases member : point ∈ center.B
  · have base := (mem_base_iff point).mpr member
    simp only [member, true_and, U_eq member]
    cases cut <;>
      simp_all [upperBranch, Switch.upVal, CenterRegions.base, CenterRegions.body,
        canonicalEquiv_apply, coordinateIndex]
  · have outside := (mem_base_iff point).not.mpr member
    cases cut <;>
      simp_all [CenterRegions.base, CenterRegions.body, canonicalEquiv_apply, coordinateIndex]

theorem zero_mem_B : (0 : Coord → ℝ) ∈ center.B := by
  rw [mem_B_iff]
  norm_num

theorem one_mem_B : (1 : Coord → ℝ) ∈ center.B := by
  rw [mem_B_iff]
  norm_num

theorem domL_empty_not_full : adim (center.domL ∅) ≠ Fintype.card Coord := by
  classical
  intro dimension
  have nonempty : (center.domL ∅).Nonempty := by
    refine ⟨0, zero_mem_B, ?_⟩
    simp [L_eq zero_mem_B, Switch.chainSum]
  have spans := affineSpan_eq_of_subset_of_adim_eq nonempty
    (show center.domL ∅ ⊆ center.B from fun _ member => member.1)
    (dimension.trans (chainOrderPolytope_adim Coord center.I').symm)
  let coordinate : (Coord → ℝ) →ᵃ[ℝ] ℝ :=
    (ContinuousLinearMap.proj canonical.pa : StrongDual ℝ (Coord → ℝ)).toLinearMap.toAffineMap
  have agree : (center.domL ∅).EqOn coordinate (AffineMap.const ℝ _ 0) := by
    intro point member
    change point canonical.pa = 0
    have bound := le_max_left (point canonical.pa) (point canonical.pb)
    have equal := member.2
    rw [L_eq member.1] at equal
    simp only [Switch.chainSum, Finset.sum_empty] at equal
    rw [equal] at bound
    exact le_antisymm bound (mem_B_iff _ |>.mp member.1).1
  have in_span : (1 : Coord → ℝ) ∈ affineSpan ℝ (center.domL ∅) := by
    rw [spans]
    exact subset_affineSpan ℝ _ one_mem_B
  have impossible := AffineMap.eqOn_affineSpan agree in_span
  norm_num [coordinate] at impossible

theorem domU_none_not_full : adim (center.domU none) ≠ Fintype.card Coord := by
  classical
  intro dimension
  have nonempty : (center.domU none).Nonempty := by
    refine ⟨1, one_mem_B, ?_⟩
    simp [U_eq one_mem_B, Switch.upVal]
  have spans := affineSpan_eq_of_subset_of_adim_eq nonempty
    (show center.domU none ⊆ center.B from fun _ member => member.1)
    (dimension.trans (chainOrderPolytope_adim Coord center.I').symm)
  let coordinate : (Coord → ℝ) →ᵃ[ℝ] ℝ :=
    (ContinuousLinearMap.proj canonical.pg : StrongDual ℝ (Coord → ℝ)).toLinearMap.toAffineMap
  have agree : (center.domU none).EqOn coordinate (AffineMap.const ℝ _ 1) := by
    intro point member
    change point canonical.pg = 1
    have bound := min_le_left (point canonical.pg) (point canonical.ph)
    have equal := member.2
    rw [U_eq member.1] at equal
    change min (point canonical.pg) (point canonical.ph) = 1 at equal
    rw [equal] at bound
    exact le_antisymm (mem_B_iff _ |>.mp member.1).2.2.2.1 bound
  have in_span : (0 : Coord → ℝ) ∈ affineSpan ℝ (center.domU none) := by
    rw [spans]
    exact subset_affineSpan ℝ _ zero_mem_B
  have impossible := AffineMap.eqOn_affineSpan agree in_span
  norm_num [coordinate] at impossible

theorem card_coord : Fintype.card Coord = 4 := by
  rw [← Fintype.card_congr coordinateIndex]
  rfl

theorem domL_full (cut : Bool) : adim (center.domL (lowerBranch cut)) = Fintype.card Coord := by
  rw [← adim_image_affineEquiv canonicalEquiv, image_domL, CenterRegions.body_adim, card_coord]

theorem domU_full (cut : Bool) : adim (center.domU (upperBranch cut)) = Fintype.card Coord := by
  rw [← adim_image_affineEquiv canonicalEquiv, image_domU, CenterRegions.body_adim, card_coord]

theorem cellsS_iff (cell : Set (Coord → ℝ)) :
    cell ∈ center.cellsS ↔ ∃ cut : Bool, IsFace (center.domL (lowerBranch cut)) cell := by
  constructor
  · rintro ⟨branch, valid, dimension, hface⟩
    rcases lowBranches_cases valid with rfl | rfl | rfl
    · exact False.elim (domL_empty_not_full dimension)
    · exact ⟨true, hface⟩
    · exact ⟨false, hface⟩
  · rintro ⟨cut, hface⟩
    exact ⟨lowerBranch cut, lower_valid cut, domL_full cut, hface⟩

theorem cellsT_iff (cell : Set (Coord → ℝ)) :
    cell ∈ center.cellsT ↔ ∃ cut : Bool, IsFace (center.domU (upperBranch cut)) cell := by
  constructor
  · rintro ⟨branch, valid, dimension, hface⟩
    rcases upBranches_cases valid with rfl | rfl | rfl
    · exact False.elim (domU_none_not_full dimension)
    · exact ⟨false, hface⟩
    · exact ⟨true, hface⟩
  · rintro ⟨cut, hface⟩
    exact ⟨upperBranch cut, upper_valid cut, domU_full cut, hface⟩

theorem image_cellsS : (fun cell => canonicalEquiv '' cell) '' center.cellsS =
    CenterRegions.familyS := by
  ext cell
  constructor
  · rintro ⟨original, member, rfl⟩
    obtain ⟨cut, hface⟩ := (cellsS_iff original).mp member
    refine ⟨cut, ?_⟩
    simpa only [image_domL] using hface.image_affineEquiv canonicalEquiv
  · rintro ⟨cut, hface⟩
    refine ⟨canonicalEquiv.symm '' cell, (cellsS_iff _).mpr ⟨cut, ?_⟩, ?_⟩
    · rw [← image_domL cut] at hface
      have pulled := hface.image_affineEquiv canonicalEquiv.symm
      simpa only [Set.image_image, Function.comp_def, AffineEquiv.symm_apply_apply,
        Set.image_id'] using pulled
    · simp only [Set.image_image, AffineEquiv.apply_symm_apply, Set.image_id']

theorem image_cellsT : (fun cell => canonicalEquiv '' cell) '' center.cellsT =
    CenterRegions.familyT := by
  ext cell
  constructor
  · rintro ⟨original, member, rfl⟩
    obtain ⟨cut, hface⟩ := (cellsT_iff original).mp member
    refine ⟨cut, ?_⟩
    simpa only [image_domU] using hface.image_affineEquiv canonicalEquiv
  · rintro ⟨cut, hface⟩
    refine ⟨canonicalEquiv.symm '' cell, (cellsT_iff _).mpr ⟨cut, ?_⟩, ?_⟩
    · rw [← image_domU cut] at hface
      have pulled := hface.image_affineEquiv canonicalEquiv.symm
      simpa only [Set.image_image, Function.comp_def, AffineEquiv.symm_apply_apply,
        Set.image_id'] using pulled
    · simp only [Set.image_image, AffineEquiv.apply_symm_apply, Set.image_id']

theorem body_inter (lower upper : Bool) :
    CenterRegions.body (some lower) none ∩ CenterRegions.body none (some upper) =
      CenterRegions.body (some lower) (some upper) := by
  ext point
  cases lower <;> cases upper <;> simp only [CenterRegions.body, Set.mem_inter_iff,
    Set.mem_ofPred_eq] <;> tauto

theorem image_dom_inter (lower upper : Bool) :
    canonicalEquiv '' (center.domL (lowerBranch lower) ∩ center.domU (upperBranch upper)) =
      CenterRegions.body (some lower) (some upper) := by
  rw [Set.image_inter canonicalEquiv.injective, image_domL, image_domU, body_inter]

private theorem faces_inter {leftBody rightBody left right : Set (Coord → ℝ)}
    (left_face : IsFace leftBody left) (right_face : IsFace rightBody right)
    (nonempty : (left ∩ right).Nonempty) : IsFace (leftBody ∩ rightBody) (left ∩ right) := by
  have first := left_face.inter_subset
    (show leftBody ∩ rightBody ⊆ leftBody from Set.inter_subset_left)
    (nonempty.mono fun _ member => ⟨⟨left_face.subset member.1, right_face.subset member.2⟩, member.1⟩)
  have second := right_face.inter_subset
    (show leftBody ∩ rightBody ⊆ rightBody from Set.inter_subset_right)
    (nonempty.mono fun _ member => ⟨⟨left_face.subset member.1, right_face.subset member.2⟩, member.2⟩)
  have both := first.inter second (nonempty.mono fun _ member =>
    ⟨⟨⟨left_face.subset member.1, right_face.subset member.2⟩, member.1⟩,
      ⟨left_face.subset member.1, right_face.subset member.2⟩, member.2⟩)
  have same : ((leftBody ∩ rightBody) ∩ left) ∩ ((leftBody ∩ rightBody) ∩ right) = left ∩ right := by
    ext point
    constructor
    · exact fun member => ⟨member.1.2, member.2.2⟩
    · exact fun member => ⟨⟨⟨left_face.subset member.1, right_face.subset member.2⟩, member.1⟩,
        ⟨left_face.subset member.1, right_face.subset member.2⟩, member.2⟩
  rwa [same] at both

theorem image_cellsR : (fun cell => canonicalEquiv '' cell) '' center.cellsR =
    CenterRegions.familyR := by
  ext cell
  constructor
  · rintro ⟨original, ⟨nonempty, left, left_mem, right, right_mem, rfl⟩, rfl⟩
    obtain ⟨lower, left_face⟩ := (cellsS_iff left).mp left_mem
    obtain ⟨upper, right_face⟩ := (cellsT_iff right).mp right_mem
    refine ⟨lower, upper, ?_⟩
    have hface := (faces_inter left_face right_face nonempty).image_affineEquiv canonicalEquiv
    simpa only [image_dom_inter] using hface
  · rintro ⟨lower, upper, hface⟩
    rw [← image_dom_inter lower upper] at hface
    have pulled := hface.image_affineEquiv canonicalEquiv.symm
    simp only [Set.image_image, AffineEquiv.symm_apply_apply,
      Set.image_id'] at pulled
    obtain ⟨left, right, left_face, right_face, same⟩ := pulled.inter_decomposition
      (center.domL_isPolytope _ (lower_valid lower))
      (center.domU_isPolytope _ (upper_valid upper))
      (center.domL_halfspaces _ (lower_valid lower))
      (center.domU_halfspaces _ (upper_valid upper))
    refine ⟨canonicalEquiv.symm '' cell,
      ⟨pulled.1, left, (cellsS_iff _).mpr ⟨lower, left_face⟩,
        right, (cellsT_iff _).mpr ⟨upper, right_face⟩, same⟩, ?_⟩
    simp only [Set.image_image, AffineEquiv.apply_symm_apply, Set.image_id']

end HibiLi.Example21.CenterGeometry
