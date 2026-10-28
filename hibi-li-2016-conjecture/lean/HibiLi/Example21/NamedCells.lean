/-
HibiLi/Example21/NamedCells.lean — Proposition 5.1, switch of c in X: the cells with carrier B by name, the maximal cells of S and T, the
Figure 2 slices, and L, U not affine across the walls (local model CenterRegions, then transported).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.CenterResult
import HibiLi.Polytope.RefinementCover
import HibiLi.Polytope.SharedFacet

namespace HibiLi.Example21.NamedCells

open CenterRegions Filter Topology

/-- Evaluates explicit points against the inequalities of `body`. -/
macro "point_tac" : tactic =>
  `(tactic| (simp only [body, base, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons] <;> norm_num))

/-- The interior point `u₀ = (1/4, 1/4, 3/4, 3/4)` of `B` (paper, Figure 2). -/
noncomputable def u0 : Fin 4 → ℝ := ![1/4, 1/4, 3/4, 3/4]

theorem u0_mem_body (lower upper : Option Bool) : u0 ∈ body lower upper := by
  rcases lower with _ | _ | _ <;> rcases upper with _ | _ | _ <;> unfold u0 <;> point_tac

theorem body_subset_base (lower upper : Option Bool) : body lower upper ⊆ base := fun _ hv =>
  ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2.1, hv.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.1,
    trivial, trivial⟩

theorem u0_mem_interior : u0 ∈ intrinsicInterior ℝ base := by
  refine mem_intrinsicInterior_of_eventually (subset_affineSpan ℝ base (u0_mem_body none none)) ?_
  have lt (f g : (Fin 4 → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) (h : f u0 < g u0) :
      ∀ᶠ y in 𝓝 u0, f y < g y := (isOpen_lt hf hg).mem_nhds h
  have c (i : Fin 4) : Continuous fun y : Fin 4 → ℝ => y i := continuous_apply i
  have e1 := lt (fun _ => 0) (fun y => y 0) continuous_const (c 0) (by unfold u0; norm_num)
  have e2 := lt (fun _ => 0) (fun y => y 1) continuous_const (c 1) (by unfold u0; norm_num)
  have e3 := lt (fun y => y 0) (fun y => y 2) (c 0) (c 2) (by unfold u0; norm_num)
  have e4 := lt (fun y => y 0) (fun y => y 3) (c 0) (c 3) (by unfold u0; norm_num)
  have e5 := lt (fun y => y 1) (fun y => y 2) (c 1) (c 2) (by unfold u0; norm_num)
  have e6 := lt (fun y => y 1) (fun y => y 3) (c 1) (c 3) (by unfold u0; norm_num)
  have e7 := lt (fun y => y 2) (fun _ => 1) (c 2) continuous_const (by unfold u0; norm_num)
  have e8 := lt (fun y => y 3) (fun _ => 1) (c 3) continuous_const (by unfold u0; norm_num)
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8] with y h1 h2 h3 h4 h5 h6 h7 h8 _
  exact ⟨h1.le, h2.le, h3.le, h4.le, h5.le, h6.le, h7.le, h8.le, trivial, trivial⟩

/-- A set cut out of `A` by a linear functional `l ≤ 0` on `A` (attained) is a face of `A`. -/
theorem isFace_level {A : Set (Fin 4 → ℝ)} (l : StrongDual ℝ (Fin 4 → ℝ)) (hle : ∀ y ∈ A, l y ≤ 0)
    {p : Fin 4 → ℝ} (hpA : p ∈ A) (hp : l p = 0) : IsFace A {x | x ∈ A ∧ l x = 0} := by
  refine ⟨⟨p, hpA, hp⟩, fun _ => ⟨l, ?_⟩⟩
  ext x
  constructor
  · rintro ⟨hxA, hx0⟩
    exact ⟨hxA, fun y hy => by rw [hx0]; exact hle y hy⟩
  · rintro ⟨hxA, hmax⟩
    refine ⟨hxA, le_antisymm (hle x hxA) ?_⟩
    rw [← hp]
    exact hmax p hpA

/-- `v ↦ v i − v j`. -/
noncomputable def diff (i j : Fin 4) : StrongDual ℝ (Fin 4 → ℝ) :=
  (ContinuousLinearMap.proj i : (Fin 4 → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj j

@[simp] theorem diff_apply (i j : Fin 4) (v : Fin 4 → ℝ) : diff i j v = v i - v j := by
  simp [diff]

theorem carrier_base {C : Set (Fin 4 → ℝ)} (hC : C ⊆ base) (hu0 : u0 ∈ C) : IsCarrier base base C :=
  isCarrier_of_subset_of_intrinsicInterior (IsFace.refl ⟨u0, u0_mem_body none none⟩) hC ⟨u0, hu0, u0_mem_interior⟩

/-! ### The named cells (local coordinates `v = (α, β, γ, η)`) -/

/-- `B ∩ {α = β}`. -/
def wallS : Set (Fin 4 → ℝ) := {v | v ∈ base ∧ v 0 = v 1}
/-- `B ∩ {γ = η}`. -/
def wallT : Set (Fin 4 → ℝ) := {v | v ∈ base ∧ v 2 = v 3}

theorem wallS_eq_level : wallS = {x | x ∈ body (some false) none ∧ diff 0 1 x = 0} := by
  ext v
  simp only [wallS, base, body, Set.mem_ofPred_eq, diff_apply, sub_eq_zero]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩, h⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h.le, trivial⟩, h⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩, h⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, trivial, trivial⟩, h⟩

theorem wallT_eq_level : wallT = {x | x ∈ body none (some false) ∧ diff 2 3 x = 0} := by
  ext v
  simp only [wallT, base, body, Set.mem_ofPred_eq, diff_apply, sub_eq_zero]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩, h⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, trivial, h.le⟩, h⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩, h⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, trivial, trivial⟩, h⟩

theorem wallS_face : IsFace (body (some false) none) wallS := by
  rw [wallS_eq_level]
  refine isFace_level (diff 0 1) (fun y hy => ?_) (u0_mem_body _ _) (by unfold u0; simp)
  have := hy.2.2.2.2.2.2.2.2.1
  simp only [diff_apply]
  linarith

theorem wallT_face : IsFace (body none (some false)) wallT := by
  rw [wallT_eq_level]
  refine isFace_level (diff 2 3) (fun y hy => ?_) (u0_mem_body _ _) (by unfold u0; simp)
  have := hy.2.2.2.2.2.2.2.2.2
  simp only [diff_apply]
  linarith

theorem u0_mem_wallS : u0 ∈ wallS := ⟨u0_mem_body none none, by unfold u0; simp⟩
theorem u0_mem_wallT : u0 ∈ wallT := ⟨u0_mem_body none none, by unfold u0; simp⟩

/-! ### Counting: cells with carrier `B` of a finite family, from the checked counts -/

/-- The cells of `F` with carrier `B` of dimension `d` (the set counted by `carriedCount`). -/
def carried (F : Set (Set (Fin 4 → ℝ))) (d : ℕ) : Set (Set (Fin 4 → ℝ)) :=
  {cell | cell ∈ F ∧ adim cell = d ∧ IsCarrier base base cell}

theorem carried_ncard (F : Set (Set (Fin 4 → ℝ))) (d : ℕ) :
    (carried F d).ncard = carriedCount base F base d := rfl

theorem familyS_finite : familyS.Finite := by
  rw [sFaces_geometry]
  exact (Finset.finite_toSet _).image _

theorem familyT_finite : familyT.Finite := by
  rw [tFaces_geometry]
  exact (Finset.finite_toSet _).image _

theorem familyR_finite : familyR.Finite := by
  rw [rFaces_geometry]
  exact (Finset.finite_toSet _).image _

/-- A member of a finite set with `ncard = 0` is impossible. -/
theorem not_mem_of_ncard_zero {s : Set (Set (Fin 4 → ℝ))} (hs : s.Finite) (h0 : s.ncard = 0) {C : Set (Fin 4 → ℝ)}
    (hC : C ∈ s) : False := by
  rw [Set.ncard_eq_zero hs] at h0
  rw [h0] at hC
  exact hC

/-- Two-plus-one classification: if the carried cells of `F` number 2 in dimension 4, 1 in dimension 3 and 0 otherwise,
and `b₀ ≠ b₁` are carried 4-dimensional members and `w` is a carried member that is a face of `b₀` different from
`b₀`, then the carried cells are exactly `b₀, b₁, w`, and `w` has dimension 3. -/
theorem classify_two_one {F : Set (Set (Fin 4 → ℝ))} (hF : F.Finite)
    (hcount : ∀ d, (carried F d).ncard = if d = 4 then 2 else if d = 3 then 1 else 0)
    {b₀ b₁ w : Set (Fin 4 → ℝ)} (hb₀ : b₀ ∈ carried F 4) (hb₁ : b₁ ∈ carried F 4) (hne : b₀ ≠ b₁)
    (hwF : w ∈ F) (hwcar : IsCarrier base base w) (hwface : IsFace b₀ w) (hwne : w ≠ b₀) :
    {C | C ∈ F ∧ IsCarrier base base C} = {b₀, b₁, w} ∧ adim w = 3 := by
  have hfin (d : ℕ) : (carried F d).Finite := hF.subset fun _ hc => hc.1
  have h4 : carried F 4 = {b₀, b₁} := by
    refine (Set.eq_of_subset_of_ncard_le (Set.insert_subset_iff.2 ⟨hb₀, Set.singleton_subset_iff.2 hb₁⟩) ?_
      (hfin 4)).symm
    rw [hcount, Set.ncard_pair hne]
    rfl
  have hwlt : adim w < 4 := by
    have hle : adim w ≤ adim b₀ := Submodule.finrank_mono (vectorSpan_mono ℝ hwface.subset)
    rcases hle.lt_or_eq with hlt | heq
    · rw [hb₀.2.1] at hlt
      exact hlt
    · exact absurd (hwface.eq_of_adim_eq heq) hwne
  have hw3 : adim w = 3 := by
    by_contra h3
    exact not_mem_of_ncard_zero (C := w) (hfin (adim w))
      (by rw [hcount, ite_eq_right hwlt.ne, ite_eq_right h3]) ⟨hwF, rfl, hwcar⟩
  have hwmem : w ∈ carried F 3 := ⟨hwF, hw3, hwcar⟩
  have h3 : carried F 3 = {w} := by
    refine (Set.eq_of_subset_of_ncard_le (Set.singleton_subset_iff.2 hwmem) ?_ (hfin 3)).symm
    rw [hcount, Set.ncard_singleton]
    rfl
  refine ⟨?_, hw3⟩
  ext C
  constructor
  · rintro ⟨hCF, hCcar⟩
    by_cases hd4 : adim C = 4
    · have : C ∈ carried F 4 := ⟨hCF, hd4, hCcar⟩
      rw [h4] at this
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · by_cases hd3 : adim C = 3
      · have : C ∈ carried F 3 := ⟨hCF, hd3, hCcar⟩
        rw [h3] at this
        exact Or.inr (Or.inr this)
      · exact (not_mem_of_ncard_zero (C := C) (hfin (adim C)) (by rw [hcount, ite_eq_right hd4, ite_eq_right hd3])
          ⟨hCF, rfl, hCcar⟩).elim
  · rintro (rfl | rfl | rfl)
    · exact ⟨hb₀.1, hb₀.2.2⟩
    · exact ⟨hb₁.1, hb₁.2.2⟩
    · exact ⟨hwF, hwcar⟩

theorem body_carried_S (cut : Bool) : body (some cut) none ∈ carried familyS 4 :=
  ⟨⟨cut, IsFace.refl ⟨u0, u0_mem_body _ _⟩⟩, body_adim _ _, carrier_base (body_subset_base _ _) (u0_mem_body _ _)⟩

theorem body_carried_T (cut : Bool) : body none (some cut) ∈ carried familyT 4 :=
  ⟨⟨cut, IsFace.refl ⟨u0, u0_mem_body _ _⟩⟩, body_adim _ _, carrier_base (body_subset_base _ _) (u0_mem_body _ _)⟩

/-- Witness points: `(1/8, 3/8, 3/4, 3/4)` has `α < β`, `(3/8, 1/8, 3/4, 3/4)` has `α > β`; similarly for `γ, η`. -/
theorem body_S_ne : body (some false) none ≠ body (some true) none := by
  intro h
  have hp : (![1/8, 3/8, 3/4, 3/4] : Fin 4 → ℝ) ∈ body (some false) none := by point_tac
  rw [h] at hp
  revert hp
  point_tac

theorem body_T_ne : body none (some false) ≠ body none (some true) := by
  intro h
  have hp : (![1/4, 1/4, 5/8, 7/8] : Fin 4 → ℝ) ∈ body none (some false) := by point_tac
  rw [h] at hp
  revert hp
  point_tac

theorem wallS_ne : wallS ≠ body (some false) none := by
  intro h
  have hp : (![1/8, 3/8, 3/4, 3/4] : Fin 4 → ℝ) ∈ body (some false) none := by point_tac
  rw [← h] at hp
  revert hp
  simp only [wallS]
  point_tac

theorem wallT_ne : wallT ≠ body none (some false) := by
  intro h
  have hp : (![1/4, 1/4, 5/8, 7/8] : Fin 4 → ℝ) ∈ body none (some false) := by point_tac
  rw [← h] at hp
  revert hp
  simp only [wallT]
  point_tac

theorem counts_S (d : ℕ) : (carried familyS d).ncard = if d = 4 then 2 else if d = 3 then 1 else 0 :=
  (geometric_base_counts d).1

theorem counts_T (d : ℕ) : (carried familyT d).ncard = if d = 4 then 2 else if d = 3 then 1 else 0 :=
  (geometric_base_counts d).2.1

/-- Local form, S and T. -/
theorem local_S_T :
    ({C | C ∈ familyS ∧ IsCarrier base base C} = {body (some false) none, body (some true) none, wallS} ∧
      adim wallS = 3) ∧
    ({C | C ∈ familyT ∧ IsCarrier base base C} = {body none (some false), body none (some true), wallT} ∧
      adim wallT = 3) :=
  ⟨classify_two_one familyS_finite counts_S (body_carried_S false) (body_carried_S true) body_S_ne
      ⟨false, wallS_face⟩ (carrier_base (fun _ h => h.1) u0_mem_wallS) wallS_face wallS_ne,
    classify_two_one familyT_finite counts_T (body_carried_T false) (body_carried_T true) body_T_ne
      ⟨false, wallT_face⟩ (carrier_base (fun _ h => h.1) u0_mem_wallT) wallT_face wallT_ne⟩

/-! ### R: four 4-cells (quadrants), four 3-cells (half-walls), one 2-cell -/

/-- The quadrant `B ∩ {cut of α, β} ∩ {cut of γ, η}` (a body with both cuts). -/
def quad (lower upper : Bool) : Set (Fin 4 → ℝ) := body (some lower) (some upper)
/-- The half-wall `B ∩ {α = β} ∩ {cut of γ, η}`. -/
def halfS (upper : Bool) : Set (Fin 4 → ℝ) := {v | v ∈ body none (some upper) ∧ v 0 = v 1}
/-- The half-wall `B ∩ {γ = η} ∩ {cut of α, β}`. -/
def halfT (lower : Bool) : Set (Fin 4 → ℝ) := {v | v ∈ body (some lower) none ∧ v 2 = v 3}
/-- The 2-cell `B ∩ {α = β, γ = η}`. -/
def corner : Set (Fin 4 → ℝ) := {v | v ∈ base ∧ v 0 = v 1 ∧ v 2 = v 3}

/-- The four half-walls, indexed by `Bool ⊕ Bool`. -/
def half : Bool ⊕ Bool → Set (Fin 4 → ℝ)
  | .inl upper => halfS upper
  | .inr lower => halfT lower

/-- Witness coordinates: `false ↦ (1/8, 3/8)` (first < second), `true ↦ (3/8, 1/8)`; `5/8, 7/8` for `γ, η`. -/
noncomputable def lowPair : Bool → ℝ × ℝ
  | false => (1/8, 3/8)
  | true => (3/8, 1/8)
noncomputable def upPair : Bool → ℝ × ℝ
  | false => (5/8, 7/8)
  | true => (7/8, 5/8)

/-- A point strictly inside the quadrant `quad l u`. -/
noncomputable def qpt (lower upper : Bool) : Fin 4 → ℝ :=
  ![(lowPair lower).1, (lowPair lower).2, (upPair upper).1, (upPair upper).2]

theorem qpt_mem (lower upper : Bool) : qpt lower upper ∈ quad lower upper := by
  cases lower <;> cases upper <;> simp only [qpt, quad, lowPair, upPair] <;> point_tac

theorem quad_injective : Function.Injective fun p : Bool × Bool => quad p.1 p.2 := by
  rintro ⟨l, u⟩ ⟨l', u'⟩ h
  have hp := qpt_mem l u
  simp only at h
  rw [h] at hp
  revert hp
  cases l <;> cases u <;> cases l' <;> cases u' <;> simp only [qpt, quad, lowPair, upPair] <;> point_tac

/-- A point of each half-wall: `(1/4, 1/4, upPair)` and `(lowPair, 3/4, 3/4)`. -/
noncomputable def hpt : Bool ⊕ Bool → Fin 4 → ℝ
  | .inl upper => ![1/4, 1/4, (upPair upper).1, (upPair upper).2]
  | .inr lower => ![(lowPair lower).1, (lowPair lower).2, 3/4, 3/4]

theorem hpt_mem (i : Bool ⊕ Bool) : hpt i ∈ half i := by
  rcases i with u | l <;> cases_type* Bool <;> simp only [hpt, half, halfS, halfT, upPair, lowPair] <;>
    point_tac

theorem half_injective : Function.Injective half := by
  intro i j h
  have hp := hpt_mem i
  rw [h] at hp
  revert hp
  rcases i with u | l <;> rcases j with u' | l' <;> cases_type* Bool <;>
    simp only [hpt, half, halfS, halfT, upPair, lowPair] <;> point_tac

theorem half_ne_corner (i : Bool ⊕ Bool) : half i ≠ corner := by
  intro h
  have hp := hpt_mem i
  rw [h] at hp
  revert hp
  rcases i with u | l <;> cases_type* Bool <;> simp only [hpt, corner, upPair, lowPair] <;> point_tac

/-- Each half-wall is a face of a quadrant, different from it. -/
theorem halfS_face (upper : Bool) : IsFace (quad false upper) (halfS upper) := by
  have heq : halfS upper = {x | x ∈ quad false upper ∧ diff 0 1 x = 0} := by
    ext v
    simp only [halfS, quad, body, Set.mem_ofPred_eq, diff_apply, sub_eq_zero]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, -, h10⟩, h⟩
      exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h.le, h10⟩, h⟩
    · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, -, h10⟩, h⟩
      exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, trivial, h10⟩, h⟩
  rw [heq]
  refine isFace_level (diff 0 1) (fun y hy => ?_) (u0_mem_body _ _) (by unfold u0; simp)
  have := hy.2.2.2.2.2.2.2.2.1
  simp only [diff_apply]
  linarith

theorem halfT_face (lower : Bool) : IsFace (quad lower false) (halfT lower) := by
  have heq : halfT lower = {x | x ∈ quad lower false ∧ diff 2 3 x = 0} := by
    ext v
    simp only [halfT, quad, body, Set.mem_ofPred_eq, diff_apply, sub_eq_zero]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩, h⟩
      exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h.le⟩, h⟩
    · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩, h⟩
      exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, trivial⟩, h⟩
  rw [heq]
  refine isFace_level (diff 2 3) (fun y hy => ?_) (u0_mem_body _ _) (by unfold u0; simp)
  have := hy.2.2.2.2.2.2.2.2.2
  simp only [diff_apply]
  linarith

theorem half_face (i : Bool ⊕ Bool) :
    ∃ l u, IsFace (quad l u) (half i) ∧ half i ≠ quad l u := by
  rcases i with u | l
  · refine ⟨false, u, halfS_face u, fun h => ?_⟩
    have hp := qpt_mem false u
    rw [← h] at hp
    revert hp
    cases u <;> simp only [qpt, half, halfS, lowPair, upPair] <;> point_tac
  · refine ⟨l, false, halfT_face l, fun h => ?_⟩
    have hp := qpt_mem l false
    rw [← h] at hp
    revert hp
    cases l <;> simp only [qpt, half, halfT, lowPair, upPair] <;> point_tac

/-- The 2-cell is a face of the quadrant `(false, false)` and of the half-wall `halfS false`. -/
theorem corner_face_quad : IsFace (quad false false) corner := by
  have heq : corner = {x | x ∈ quad false false ∧ (diff 0 1 + diff 2 3) x = 0} := by
    ext v
    simp only [corner, base, quad, body, Set.mem_ofPred_eq, add_apply, diff_apply]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩, ha, hb⟩
      exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, ha.le, hb.le⟩, by rw [ha, hb]; ring⟩
    · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, h⟩
      exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, trivial, trivial⟩, by linarith, by linarith⟩
  rw [heq]
  refine isFace_level _ (fun y hy => ?_) (u0_mem_body _ _) (by unfold u0; simp)
  have h9 := hy.2.2.2.2.2.2.2.2.1
  have h10 := hy.2.2.2.2.2.2.2.2.2
  simp only [add_apply, diff_apply]
  linarith

theorem corner_face_half : IsFace (halfS false) corner := by
  have heq : corner = {x | x ∈ halfS false ∧ diff 2 3 x = 0} := by
    ext v
    simp only [corner, base, halfS, body, Set.mem_ofPred_eq, diff_apply, sub_eq_zero]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩, ha, hb⟩
      exact ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, trivial, hb.le⟩, ha⟩, hb⟩
    · rintro ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩, ha⟩, hb⟩
      exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, trivial, trivial⟩, ha, hb⟩
  rw [heq]
  refine isFace_level (diff 2 3) (fun y hy => ?_) ⟨u0_mem_body _ _, by unfold u0; simp⟩ (by unfold u0; simp)
  have := hy.1.2.2.2.2.2.2.2.2.2
  simp only [diff_apply]
  linarith

theorem u0_mem_half (i : Bool ⊕ Bool) : u0 ∈ half i := by
  rcases i with u | l
  · exact ⟨u0_mem_body _ _, by unfold u0; simp⟩
  · exact ⟨u0_mem_body _ _, by unfold u0; simp⟩

theorem u0_mem_corner : u0 ∈ corner := ⟨u0_mem_body none none, by unfold u0; simp, by unfold u0; simp⟩

theorem half_subset_base (i : Bool ⊕ Bool) : half i ⊆ base := by
  rcases i with u | l
  · exact fun v hv => body_subset_base _ _ hv.1
  · exact fun v hv => body_subset_base _ _ hv.1

theorem adim_le_of_subset {X Y : Set (Fin 4 → ℝ)} (h : X ⊆ Y) : adim X ≤ adim Y :=
  Submodule.finrank_mono (vectorSpan_mono ℝ h)

theorem adim_lt_of_face {X Y : Set (Fin 4 → ℝ)} (hface : IsFace Y X) (hne : X ≠ Y) : adim X < adim Y := by
  rcases (adim_le_of_subset hface.subset).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd (hface.eq_of_adim_eq heq) hne

theorem counts_R (d : ℕ) :
    (carried familyR d).ncard = if d = 4 then 4 else if d = 3 then 4 else if d = 2 then 1 else 0 :=
  (geometric_base_counts d).2.2

theorem local_R :
    {C | C ∈ familyR ∧ IsCarrier base base C} = Set.range (fun p : Bool × Bool => quad p.1 p.2) ∪
      Set.range half ∪ {corner} ∧
    (∀ l u, adim (quad l u) = 4) ∧ (∀ i, adim (half i) = 3) ∧ adim corner = 2 := by
  have hfin (d : ℕ) : (carried familyR d).Finite := familyR_finite.subset fun _ hc => hc.1
  have hquad (l u : Bool) : quad l u ∈ carried familyR 4 :=
    ⟨⟨l, u, IsFace.refl ⟨u0, u0_mem_body _ _⟩⟩, body_adim _ _,
      carrier_base (body_subset_base _ _) (u0_mem_body _ _)⟩
  have hhalfR (i : Bool ⊕ Bool) : half i ∈ familyR ∧ IsCarrier base base (half i) := by
    obtain ⟨l, u, hf, -⟩ := half_face i
    exact ⟨⟨l, u, hf⟩, carrier_base (half_subset_base i) (u0_mem_half i)⟩
  have hcornerR : corner ∈ familyR ∧ IsCarrier base base corner :=
    ⟨⟨false, false, corner_face_quad⟩, carrier_base (fun _ h => h.1) u0_mem_corner⟩
  have h4 : carried familyR 4 = Set.range (fun p : Bool × Bool => quad p.1 p.2) := by
    refine (Set.eq_of_subset_of_ncard_le (Set.range_subset_iff.2 fun p : Bool × Bool => hquad p.1 p.2) ?_ (hfin 4)).symm
    rw [counts_R, Set.ncard_range_of_injective quad_injective]
    simp
  have hhalf_lt (i : Bool ⊕ Bool) : adim (half i) < 4 := by
    obtain ⟨l, u, hf, hne⟩ := half_face i
    have := adim_lt_of_face hf hne
    rwa [show adim (quad l u) = 4 from body_adim _ _] at this
  have hcorner_le : adim corner ≤ 2 := by
    have h1 := adim_lt_of_face corner_face_half (half_ne_corner (.inl false)).symm
    have h2 := hhalf_lt (.inl false)
    simp only [half] at h2
    omega
  have hcorner2 : adim corner = 2 := by
    by_contra h2
    exact not_mem_of_ncard_zero (C := corner) (hfin (adim corner))
      (by rw [counts_R, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h2])
      ⟨hcornerR.1, rfl, hcornerR.2⟩
  have hcmem : corner ∈ carried familyR 2 := ⟨hcornerR.1, hcorner2, hcornerR.2⟩
  have h2 : carried familyR 2 = {corner} := by
    refine (Set.eq_of_subset_of_ncard_le (Set.singleton_subset_iff.2 hcmem) ?_ (hfin 2)).symm
    rw [counts_R, Set.ncard_singleton]
    rfl
  have hhalf3 (i : Bool ⊕ Bool) : adim (half i) = 3 := by
    by_contra h3
    by_cases hd2 : adim (half i) = 2
    · have : half i ∈ carried familyR 2 := ⟨(hhalfR i).1, hd2, (hhalfR i).2⟩
      rw [h2] at this
      exact half_ne_corner i this
    · exact not_mem_of_ncard_zero (C := half i) (hfin (adim (half i)))
        (by rw [counts_R, ite_eq_right (hhalf_lt i).ne, ite_eq_right h3, ite_eq_right hd2])
        ⟨(hhalfR i).1, rfl, (hhalfR i).2⟩
  have hhalfmem (i : Bool ⊕ Bool) : half i ∈ carried familyR 3 := ⟨(hhalfR i).1, hhalf3 i, (hhalfR i).2⟩
  have h3 : carried familyR 3 = Set.range half := by
    refine (Set.eq_of_subset_of_ncard_le (Set.range_subset_iff.2 hhalfmem) ?_ (hfin 3)).symm
    rw [counts_R, Set.ncard_range_of_injective half_injective]
    simp
  refine ⟨?_, fun l u => body_adim _ _, hhalf3, hcorner2⟩
  ext C
  constructor
  · rintro ⟨hCF, hCcar⟩
    by_cases hd4 : adim C = 4
    · have : C ∈ carried familyR 4 := ⟨hCF, hd4, hCcar⟩
      rw [h4] at this
      exact Or.inl (Or.inl this)
    · by_cases hd3 : adim C = 3
      · have : C ∈ carried familyR 3 := ⟨hCF, hd3, hCcar⟩
        rw [h3] at this
        exact Or.inl (Or.inr this)
      · by_cases hd2 : adim C = 2
        · have : C ∈ carried familyR 2 := ⟨hCF, hd2, hCcar⟩
          rw [h2] at this
          exact Or.inr this
        · exact (not_mem_of_ncard_zero (C := C) (hfin (adim C))
            (by rw [counts_R, ite_eq_right hd4, ite_eq_right hd3, ite_eq_right hd2]) ⟨hCF, rfl, hCcar⟩).elim
  · rintro ((⟨p, rfl⟩ | ⟨i, rfl⟩) | hC)
    · exact ⟨(hquad p.1 p.2).1, (hquad p.1 p.2).2.2⟩
    · exact hhalfR i
    · rw [Set.mem_singleton_iff.1 hC]
      exact hcornerR

/-! ### The maximal cells of S and T (paper v2.10 l. 921-922: "The maximal cells of S are B ∩ {α ≥ β} and
B ∩ {α ≤ β}, and those of T are B ∩ {γ ≥ η} and B ∩ {γ ≤ η}") -/

theorem familyS_subset_base {C : Set (Fin 4 → ℝ)} (hC : C ∈ familyS) : C ⊆ base := by
  obtain ⟨cut, hface⟩ := hC
  exact hface.subset.trans (body_subset_base _ _)

theorem familyT_subset_base {C : Set (Fin 4 → ℝ)} (hC : C ∈ familyT) : C ⊆ base := by
  obtain ⟨cut, hface⟩ := hC
  exact hface.subset.trans (body_subset_base _ _)

theorem local_maximal_S_T :
    {C | C ∈ familyS ∧ adim C = 4} = {body (some false) none, body (some true) none} ∧
    {C | C ∈ familyT ∧ adim C = 4} = {body none (some false), body none (some true)} := by
  have hbase : adim base = 4 := body_adim none none
  have hrefl : IsFace base base := IsFace.refl ⟨u0, u0_mem_body none none⟩
  constructor
  · ext C
    constructor
    · rintro ⟨hC, h4⟩
      obtain ⟨cut, hface⟩ := hC
      have hcar : IsCarrier base base C :=
        isCarrier_of_subset_of_adim_eq hrefl hface.1 (familyS_subset_base ⟨cut, hface⟩) (h4.trans hbase.symm)
      have hmem : C ∈ {C | C ∈ familyS ∧ IsCarrier base base C} := ⟨⟨cut, hface⟩, hcar⟩
      rw [local_S_T.1.1] at hmem
      rcases hmem with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · rw [h, local_S_T.1.2] at h4
        exact absurd h4 (by norm_num)
    · rintro (rfl | rfl)
      · exact ⟨⟨false, IsFace.refl ⟨u0, u0_mem_body _ _⟩⟩, body_adim _ _⟩
      · exact ⟨⟨true, IsFace.refl ⟨u0, u0_mem_body _ _⟩⟩, body_adim _ _⟩
  · ext C
    constructor
    · rintro ⟨hC, h4⟩
      obtain ⟨cut, hface⟩ := hC
      have hcar : IsCarrier base base C :=
        isCarrier_of_subset_of_adim_eq hrefl hface.1 (familyT_subset_base ⟨cut, hface⟩) (h4.trans hbase.symm)
      have hmem : C ∈ {C | C ∈ familyT ∧ IsCarrier base base C} := ⟨⟨cut, hface⟩, hcar⟩
      rw [local_S_T.2.1] at hmem
      rcases hmem with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · rw [h, local_S_T.2.2] at h4
        exact absurd h4 (by norm_num)
    · rintro (rfl | rfl)
      · exact ⟨⟨false, IsFace.refl ⟨u0, u0_mem_body _ _⟩⟩, body_adim _ _⟩
      · exact ⟨⟨true, IsFace.refl ⟨u0, u0_mem_body _ _⟩⟩, body_adim _ _⟩

/-! ### Transport to the switch of `c` itself (`CenterGeometry.center`, coordinates `u ↦ (x_a, x_b, y_g, y_h)`) -/

open CenterGeometry in
/-- The coordinate map is `u ↦ (α, β, γ, η) = (x_a, x_b, y_g, y_h)`. -/
theorem canonicalEquiv_coords (u : Coord → ℝ) :
    canonicalEquiv u = ![u CenterSwitch.canonical.pa, u CenterSwitch.canonical.pb, u CenterSwitch.canonical.pg,
      u CenterSwitch.canonical.ph] := by
  ext i
  fin_cases i <;> rfl

open CenterGeometry in
/-- Cells with carrier `B` correspond, under the coordinate map, to the local cells with carrier `base`. -/
theorem transport_carried (F : Set (Set (Coord → ℝ))) (G : Set (Set (Fin 4 → ℝ)))
    (hFG : (fun C => canonicalEquiv '' C) '' F = G) :
    (fun C => canonicalEquiv '' C) '' {C | C ∈ F ∧ IsCarrier center.B center.B C} =
      {D | D ∈ G ∧ IsCarrier base base D} := by
  ext D
  constructor
  · rintro ⟨C, ⟨hC, hcar⟩, rfl⟩
    refine ⟨by rw [← hFG]; exact ⟨C, hC, rfl⟩, ?_⟩
    have h := (carrier_image_affineEquiv_iff canonicalEquiv center.B center.B C).2 hcar
    rwa [image_B] at h
  · rintro ⟨hD, hcar⟩
    rw [← hFG] at hD
    obtain ⟨C, hC, rfl⟩ := hD
    refine ⟨C, ⟨hC, ?_⟩, rfl⟩
    have h := (carrier_image_affineEquiv_iff canonicalEquiv center.B center.B C).1
    rw [image_B] at h
    exact h hcar

open CenterGeometry in
/-- **The cells with carrier `B`** for the switch of `c` in `X` (the paper's sentence, v2.10 l. 925-929, all three
families), in the coordinates `(α, β, γ, η)`; with their dimensions (an affine bijection keeps dimensions). -/
theorem center_cells_with_carrier_B :
    (fun C => canonicalEquiv '' C) '' {C | C ∈ center.cellsS ∧ IsCarrier center.B center.B C} =
      {body (some false) none, body (some true) none, wallS} ∧
    (fun C => canonicalEquiv '' C) '' {C | C ∈ center.cellsT ∧ IsCarrier center.B center.B C} =
      {body none (some false), body none (some true), wallT} ∧
    (fun C => canonicalEquiv '' C) '' {C | C ∈ center.cellsR ∧ IsCarrier center.B center.B C} =
      Set.range (fun p : Bool × Bool => quad p.1 p.2) ∪ Set.range half ∪ {corner} ∧
    adim wallS = 3 ∧ adim wallT = 3 ∧ (∀ l u, adim (quad l u) = 4) ∧ (∀ i, adim (half i) = 3) ∧
      adim corner = 2 ∧ (∀ C : Set (Coord → ℝ), adim (canonicalEquiv '' C) = adim C) := by
  refine ⟨?_, ?_, ?_, local_S_T.1.2, local_S_T.2.2, local_R.2.1, local_R.2.2.1, local_R.2.2.2,
    fun C => adim_image_affineEquiv canonicalEquiv C⟩
  · rw [transport_carried _ _ image_cellsS]
    exact local_S_T.1.1
  · rw [transport_carried _ _ image_cellsT]
    exact local_S_T.2.1
  · rw [transport_carried _ _ image_cellsR]
    exact local_R.1

/-! ### Figure 2 (v2.10 l. 665-667: "The function L is affine on no neighborhood of a point with ξ = 0 …, and U is
affine on no neighborhood of a point with ω = 0"), here in the weaker band form: L is not affine across ξ = 0, nor U
across ω = 0 -/

open CenterGeometry in
theorem coords_symm (v : Fin 4 → ℝ) :
    canonicalEquiv.symm v CenterSwitch.canonical.pa = v 0 ∧ canonicalEquiv.symm v CenterSwitch.canonical.pb = v 1 ∧
      canonicalEquiv.symm v CenterSwitch.canonical.pg = v 2 ∧ canonicalEquiv.symm v CenterSwitch.canonical.ph = v 3 := by
  have h := canonicalEquiv_coords (canonicalEquiv.symm v)
  rw [AffineEquiv.apply_symm_apply] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrFun h 0
    simp only [Matrix.cons_val_zero] at this
    exact this.symm
  · have := congrFun h 1
    simp only [Matrix.cons_val_one] at this
    exact this.symm
  · have := congrFun h 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
    exact this.symm
  · have := congrFun h 3
    simp only [Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at this
    exact this.symm

open CenterGeometry in
/-- If an affine function agrees on `p`, `q` and a point `m` whose coordinates are the averages, then its value at `m`
is the average. -/
theorem affine_mid (g : (Coord → ℝ) →ᵃ[ℝ] ℝ) (p q m : Coord → ℝ) (hm : ∀ c, m c = (p c + q c) / 2) :
    g m = (g p + g q) / 2 := by
  have hline : m = AffineMap.lineMap p q (1 / 2 : ℝ) := by
    funext c
    rw [AffineMap.lineMap_apply_module, hm c]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hline, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
  ring

open CenterGeometry in
/-- `L = max(α, β)` is not affine on any band `|α − β| ≤ t` (`t > 0`) of the slice `{α + β = 1/2, γ + η = 3/2}` of `B`:
the points `ξ = α − β = −t, 0, t` (with `ω = 0`) carry the values `1/4 + t/2, 1/4, 1/4 + t/2`. -/
theorem center_L_not_affine_across (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    ¬ AffineOn center.L {u | u ∈ center.B ∧ u CenterSwitch.canonical.pa + u CenterSwitch.canonical.pb = 1 / 2 ∧
      u CenterSwitch.canonical.pg + u CenterSwitch.canonical.ph = 3 / 2 ∧
      |u CenterSwitch.canonical.pa - u CenterSwitch.canonical.pb| ≤ t} := by
  rintro ⟨g, hg⟩
  obtain ⟨pa, pb, pg, ph⟩ := coords_symm ![1/4 - t/2, 1/4 + t/2, 3/4, 3/4]
  obtain ⟨qa, qb, qg, qh⟩ := coords_symm ![1/4 + t/2, 1/4 - t/2, 3/4, 3/4]
  obtain ⟨ma, mb, mg, mh⟩ := coords_symm ![1/4, 1/4, 3/4, 3/4]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at pa pb pg ph qa qb qg qh ma mb mg mh
  set p := canonicalEquiv.symm ![1/4 - t/2, 1/4 + t/2, 3/4, 3/4]
  set q := canonicalEquiv.symm ![1/4 + t/2, 1/4 - t/2, 3/4, 3/4]
  set m := canonicalEquiv.symm ![1/4, 1/4, 3/4, 3/4]
  have hpB : p ∈ center.B := by
    rw [mem_B_iff, pa, pb, pg, ph]
    refine ⟨by linarith, by linarith, ?_, by norm_num, by norm_num⟩
    rw [max_le_iff, le_min_iff, le_min_iff]
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hqB : q ∈ center.B := by
    rw [mem_B_iff, qa, qb, qg, qh]
    refine ⟨by linarith, by linarith, ?_, by norm_num, by norm_num⟩
    rw [max_le_iff, le_min_iff, le_min_iff]
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hmB : m ∈ center.B := by
    rw [mem_B_iff, ma, mb, mg, mh]
    norm_num
  have hp := hg p ⟨hpB, by rw [pa, pb]; ring, by rw [pg, ph]; norm_num,
    by rw [pa, pb, show 1/4 - t/2 - (1/4 + t/2) = -t by ring, abs_neg, abs_of_pos ht]⟩
  have hq := hg q ⟨hqB, by rw [qa, qb]; ring, by rw [qg, qh]; norm_num,
    by rw [qa, qb, show 1/4 + t/2 - (1/4 - t/2) = t by ring, abs_of_pos ht]⟩
  have hmm := hg m ⟨hmB, by rw [ma, mb]; norm_num, by rw [mg, mh]; norm_num,
    by rw [ma, mb, sub_self, abs_zero]; exact ht.le⟩
  rw [L_eq hpB, pa, pb, max_eq_right (by linarith)] at hp
  rw [L_eq hqB, qa, qb, max_eq_left (by linarith)] at hq
  rw [L_eq hmB, ma, mb, max_self] at hmm
  have hmid := affine_mid g p q m (fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl
    · rw [ma, pa, qa]; ring
    · rw [mb, pb, qb]; ring
    · rw [mg, pg, qg]; ring
    · rw [mh, ph, qh]; ring)
  linarith

open CenterGeometry in
/-- `U = min(γ, η)` is not affine on any band `|γ − η| ≤ t` of the slice (points `ω = −t, 0, t` with `ξ = 0`). -/
theorem center_U_not_affine_across (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    ¬ AffineOn center.U {u | u ∈ center.B ∧ u CenterSwitch.canonical.pa + u CenterSwitch.canonical.pb = 1 / 2 ∧
      u CenterSwitch.canonical.pg + u CenterSwitch.canonical.ph = 3 / 2 ∧
      |u CenterSwitch.canonical.pg - u CenterSwitch.canonical.ph| ≤ t} := by
  rintro ⟨g, hg⟩
  obtain ⟨pa, pb, pg, ph⟩ := coords_symm ![1/4, 1/4, 3/4 - t/2, 3/4 + t/2]
  obtain ⟨qa, qb, qg, qh⟩ := coords_symm ![1/4, 1/4, 3/4 + t/2, 3/4 - t/2]
  obtain ⟨ma, mb, mg, mh⟩ := coords_symm ![1/4, 1/4, 3/4, 3/4]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at pa pb pg ph qa qb qg qh ma mb mg mh
  set p := canonicalEquiv.symm ![1/4, 1/4, 3/4 - t/2, 3/4 + t/2]
  set q := canonicalEquiv.symm ![1/4, 1/4, 3/4 + t/2, 3/4 - t/2]
  set m := canonicalEquiv.symm ![1/4, 1/4, 3/4, 3/4]
  have hpB : p ∈ center.B := by
    rw [mem_B_iff, pa, pb, pg, ph]
    refine ⟨by norm_num, by norm_num, ?_, by linarith, by linarith⟩
    simp only [max_le_iff, le_min_iff]
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hqB : q ∈ center.B := by
    rw [mem_B_iff, qa, qb, qg, qh]
    refine ⟨by norm_num, by norm_num, ?_, by linarith, by linarith⟩
    simp only [max_le_iff, le_min_iff]
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hmB : m ∈ center.B := by
    rw [mem_B_iff, ma, mb, mg, mh]
    norm_num
  have hp := hg p ⟨hpB, by rw [pa, pb]; norm_num, by rw [pg, ph]; ring,
    by rw [pg, ph, show 3/4 - t/2 - (3/4 + t/2) = -t by ring, abs_neg, abs_of_pos ht]⟩
  have hq := hg q ⟨hqB, by rw [qa, qb]; norm_num, by rw [qg, qh]; ring,
    by rw [qg, qh, show 3/4 + t/2 - (3/4 - t/2) = t by ring, abs_of_pos ht]⟩
  have hmm := hg m ⟨hmB, by rw [ma, mb]; norm_num, by rw [mg, mh]; norm_num,
    by rw [mg, mh, sub_self, abs_zero]; exact ht.le⟩
  rw [U_eq hpB, pg, ph, min_eq_left (by linarith)] at hp
  rw [U_eq hqB, qg, qh, min_eq_right (by linarith)] at hq
  rw [U_eq hmB, mg, mh, min_self] at hmm
  have hmid := affine_mid g p q m (fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl
    · rw [ma, pa, qa]; ring
    · rw [mb, pb, qb]; ring
    · rw [mg, pg, qg]; ring
    · rw [mh, ph, qh]; ring)
  linarith



/-! ### Figure 2: the slices through `u₀`

Paper (Figure 2 caption, v2.10 l. 661-669): "The figure shows the slice of B by the plane {α+β = 1/2,
γ+η = 3/2} through u₀ = (1/4,1/4,3/4,3/4), in the coordinates ξ = α − β, ω = γ − η (|ξ|, |ω| ≤ 1/2). ... The point u₀,
the four half-axes and the four quadrants are the slices of the 2-, 3- and 4-dimensional cells of R with carrier B".
Route: on the plane, `sliceLift (ξ, ω) = (1/4 + ξ/2, 1/4 − ξ/2, 3/4 + ω/2, 3/4 − ω/2)` inverts `sliceCoords`, so the image
of `C ∩ Π` is `{x | sliceLift x ∈ C}`; on `sliceLift x` the inequalities of `B` become `|ξ| ≤ 1/2`, `|ω| ≤ 1/2`, and the
cuts become sign conditions on `ξ` and `ω`.
-/

/-- The slice plane `Π = {α + β = 1/2, γ + η = 3/2}` and the slice coordinates `(ξ, ω) = (α − β, γ − η)`. -/
def slicePlane : Set (Fin 4 → ℝ) := {v | v 0 + v 1 = 1/2 ∧ v 2 + v 3 = 3/2}
def sliceCoords (v : Fin 4 → ℝ) : ℝ × ℝ := (v 0 - v 1, v 2 - v 3)

/-- The inverse of `sliceCoords` on the plane `Π`. -/
noncomputable def sliceLift (x : ℝ × ℝ) : Fin 4 → ℝ := ![1/4 + x.1/2, 1/4 - x.1/2, 3/4 + x.2/2, 3/4 - x.2/2]

theorem sliceLift_zero (x : ℝ × ℝ) : sliceLift x 0 = 1/4 + x.1/2 := rfl
theorem sliceLift_one (x : ℝ × ℝ) : sliceLift x 1 = 1/4 - x.1/2 := rfl
theorem sliceLift_two (x : ℝ × ℝ) : sliceLift x 2 = 3/4 + x.2/2 := rfl
theorem sliceLift_three (x : ℝ × ℝ) : sliceLift x 3 = 3/4 - x.2/2 := rfl

theorem sliceCoords_lift (x : ℝ × ℝ) : sliceCoords (sliceLift x) = x := by
  rcases x with ⟨a, b⟩
  simp only [sliceCoords, sliceLift_zero, sliceLift_one, sliceLift_two, sliceLift_three, Prod.mk.injEq]
  constructor <;> ring

theorem lift_mem_plane (x : ℝ × ℝ) : sliceLift x ∈ slicePlane := by
  show sliceLift x 0 + sliceLift x 1 = 1/2 ∧ sliceLift x 2 + sliceLift x 3 = 3/2
  rw [sliceLift_zero, sliceLift_one, sliceLift_two, sliceLift_three]
  constructor <;> ring

theorem lift_sliceCoords {v : Fin 4 → ℝ} (hv : v ∈ slicePlane) : sliceLift (sliceCoords v) = v := by
  obtain ⟨h01, h23⟩ := hv
  funext i
  fin_cases i
  · show 1/4 + (v 0 - v 1)/2 = v 0
    linarith
  · show 1/4 - (v 0 - v 1)/2 = v 1
    linarith
  · show 3/4 + (v 2 - v 3)/2 = v 2
    linarith
  · show 3/4 - (v 2 - v 3)/2 = v 3
    linarith

/-- The slice of `C` by `Π`, in the coordinates `(ξ, ω)`. -/
theorem image_slice (C : Set (Fin 4 → ℝ)) : sliceCoords '' (C ∩ slicePlane) = {x | sliceLift x ∈ C} := by
  ext x
  constructor
  · rintro ⟨v, ⟨hvC, hvP⟩, rfl⟩
    show sliceLift (sliceCoords v) ∈ C
    rw [lift_sliceCoords hvP]
    exact hvC
  · intro hx
    exact ⟨sliceLift x, ⟨hx, lift_mem_plane x⟩, sliceCoords_lift x⟩

/-- On `sliceLift x`, the inequalities of `B` are `|ξ| ≤ 1/2`, `|ω| ≤ 1/2`, and the cuts are signs of `ξ`, `ω`. -/
theorem lift_mem_body (x : ℝ × ℝ) (lower upper : Option Bool) :
    sliceLift x ∈ body lower upper ↔
      |x.1| ≤ 1/2 ∧ |x.2| ≤ 1/2 ∧
      (match lower with | none => True | some false => x.1 ≤ 0 | some true => 0 ≤ x.1) ∧
      (match upper with | none => True | some false => x.2 ≤ 0 | some true => 0 ≤ x.2) := by
  rcases lower with _ | _ | _ <;> rcases upper with _ | _ | _ <;>
  ( simp only [body, Set.mem_ofPred_eq, sliceLift_zero, sliceLift_one, sliceLift_two, sliceLift_three, abs_le]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by first | trivial | linarith,
        by first | trivial | linarith⟩
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h9, h10⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by first | trivial | linarith, by first | trivial | linarith⟩ )

theorem fig2_slices :
    u0 ∈ slicePlane ∧ sliceCoords u0 = (0, 0) ∧
    sliceCoords '' (base ∩ slicePlane) = {x | |x.1| ≤ 1/2 ∧ |x.2| ≤ 1/2} ∧
    (∀ l u : Bool, sliceCoords '' (quad l u ∩ slicePlane) =
      {x | |x.1| ≤ 1/2 ∧ |x.2| ≤ 1/2 ∧ (if l then 0 ≤ x.1 else x.1 ≤ 0) ∧ (if u then 0 ≤ x.2 else x.2 ≤ 0)}) ∧
    (∀ u : Bool, sliceCoords '' (halfS u ∩ slicePlane) =
      {x | x.1 = 0 ∧ |x.2| ≤ 1/2 ∧ (if u then 0 ≤ x.2 else x.2 ≤ 0)}) ∧
    (∀ l : Bool, sliceCoords '' (halfT l ∩ slicePlane) =
      {x | x.2 = 0 ∧ |x.1| ≤ 1/2 ∧ (if l then 0 ≤ x.1 else x.1 ≤ 0)}) ∧
    sliceCoords '' (corner ∩ slicePlane) = {(0, 0)} := by
  have hP : u0 ∈ slicePlane := by
    show (1/4 : ℝ) + 1/4 = 1/2 ∧ (3/4 : ℝ) + 3/4 = 3/2
    constructor <;> norm_num
  have hC : sliceCoords u0 = (0, 0) := by
    show ((1/4 : ℝ) - 1/4, (3/4 : ℝ) - 3/4) = (0, 0)
    norm_num
  refine ⟨hP, hC, ?_, ?_, ?_, ?_, ?_⟩
  · rw [image_slice]
    ext x
    exact (lift_mem_body x none none).trans (by simp)
  · intro l u
    rw [image_slice]
    ext x
    refine (lift_mem_body x (some l) (some u)).trans ?_
    cases l <;> cases u <;> simp
  · intro u
    rw [image_slice]
    ext x
    show sliceLift x ∈ body none (some u) ∧ sliceLift x 0 = sliceLift x 1 ↔
      x.1 = 0 ∧ |x.2| ≤ 1/2 ∧ (if u then 0 ≤ x.2 else x.2 ≤ 0)
    rw [lift_mem_body, sliceLift_zero, sliceLift_one]
    have e : (1/4 + x.1/2 = 1/4 - x.1/2) ↔ x.1 = 0 := ⟨fun h => by linarith, fun h => by rw [h]; ring⟩
    constructor
    · rintro ⟨⟨-, h2, -, h4⟩, h5⟩
      exact ⟨e.mp h5, h2, by cases u <;> simpa using h4⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by rw [h1, abs_zero]; norm_num, h2, trivial, by cases u <;> simpa using h3⟩, e.mpr h1⟩
  · intro l
    rw [image_slice]
    ext x
    show sliceLift x ∈ body (some l) none ∧ sliceLift x 2 = sliceLift x 3 ↔
      x.2 = 0 ∧ |x.1| ≤ 1/2 ∧ (if l then 0 ≤ x.1 else x.1 ≤ 0)
    rw [lift_mem_body, sliceLift_two, sliceLift_three]
    have e : (3/4 + x.2/2 = 3/4 - x.2/2) ↔ x.2 = 0 := ⟨fun h => by linarith, fun h => by rw [h]; ring⟩
    constructor
    · rintro ⟨⟨h1, -, h3, -⟩, h5⟩
      exact ⟨e.mp h5, h1, by cases l <;> simpa using h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h2, by rw [h1, abs_zero]; norm_num, by cases l <;> simpa using h3, trivial⟩, e.mpr h1⟩
  · rw [image_slice]
    ext x
    show sliceLift x ∈ body none none ∧ sliceLift x 0 = sliceLift x 1 ∧ sliceLift x 2 = sliceLift x 3 ↔
      x = (0, 0)
    rw [lift_mem_body, sliceLift_zero, sliceLift_one, sliceLift_two, sliceLift_three]
    constructor
    · rintro ⟨-, h5, h6⟩
      exact Prod.ext (show x.1 = 0 by linarith) (show x.2 = 0 by linarith)
    · rintro rfl
      exact ⟨⟨by norm_num, by norm_num, trivial, trivial⟩, by norm_num, by norm_num⟩


end HibiLi.Example21.NamedCells
