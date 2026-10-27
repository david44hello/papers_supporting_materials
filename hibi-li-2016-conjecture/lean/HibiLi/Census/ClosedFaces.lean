/-
HibiLi/Census/ClosedFaces.lean — the faces of a polytope that is cut out by finitely many integer inequalities and is
the hull of finitely many points: they are exactly the hulls of the CLOSED point sets (general tool for the census).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Setting: `Q = polyOf rows = {x | rowForm row x ≤ rhs for every row}` and `Q = conv (range pt)`, `pt : Fin nv → ℝ^d`.
A set `S` of point indices is closed if every point that is tight on all rows tight on all of `S` lies in `S`.
* `isFace_of_closed`, `mem_hull_iff_of_closed`: a nonempty closed `S` spans a face, and the only points in it are `S`.
* `exists_closed_of_isFace`: every face is spanned by a nonempty closed set (perturbation argument).
* `adim_lt_of_ssubset`: a strictly smaller closed set spans a face of strictly smaller dimension.
-/
import HibiLi.Example21.Argmax

namespace HibiLi.Census

open Finset

/-- An integer inequality `∑ j, coef j * x j ≤ rhs` on `Fin d → ℝ`, as the pair `(coef, rhs)`. -/
abbrev Row (d : ℕ) := (Fin d → ℤ) × ℤ

variable {d nv : ℕ}

/-- The linear form `x ↦ ∑ j, coef j * x j` of a row. -/
noncomputable def rowForm (row : Row d) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ j, ((row.1 j : ℤ) : ℝ) • ContinuousLinearMap.proj j

theorem rowForm_apply (row : Row d) (x : Fin d → ℝ) : rowForm row x = ∑ j, (row.1 j : ℝ) * x j := by
  simp [rowForm, smul_eq_mul]

/-- The polyhedron cut out by a list of rows. -/
def polyOf (rows : List (Row d)) : Set (Fin d → ℝ) := {x | ∀ row ∈ rows, rowForm row x ≤ row.2}

variable (rows : List (Row d)) (pt : Fin nv → Fin d → ℝ)

/-- The point `pt k` is tight on `row`. -/
def Tight (row : Row d) (k : Fin nv) : Prop := rowForm row (pt k) = row.2

/-- `S` is closed: every point that is tight on every row tight on all of `S` lies in `S`. -/
def IsClosedSet (S : Finset (Fin nv)) : Prop :=
  ∀ k, (∀ row ∈ rows, (∀ s ∈ S, Tight pt row s) → Tight pt row k) → k ∈ S

variable {rows pt}

section Exposing

variable (rows pt)

/-- Every point lies in the polytope. -/
theorem pt_mem (hQ : polyOf rows = convexHull ℝ (Set.range pt)) (k : Fin nv) : pt k ∈ polyOf rows := by
  rw [hQ]; exact subset_convexHull ℝ _ (Set.mem_range_self k)

open Classical in
/-- The rows tight on all of `S`. -/
noncomputable def selRows (S : Finset (Fin nv)) : Finset (Row d) :=
  rows.toFinset.filter fun row => ∀ s ∈ S, Tight pt row s

/-- The exposing functional of `S`: the sum of the rows tight on all of `S`. -/
noncomputable def expoForm (S : Finset (Fin nv)) : (Fin d → ℝ) →L[ℝ] ℝ := ∑ row ∈ selRows rows pt S, rowForm row

/-- Its maximum on the polytope: the sum of the right-hand sides of those rows. -/
noncomputable def expoBound (S : Finset (Fin nv)) : ℝ := ∑ row ∈ selRows rows pt S, (row.2 : ℝ)

theorem mem_selRows {S : Finset (Fin nv)} {row : Row d} :
    row ∈ selRows rows pt S ↔ row ∈ rows ∧ ∀ s ∈ S, Tight pt row s := by
  classical
  simp only [selRows, Finset.mem_filter, List.mem_toFinset]

theorem expoForm_apply (S : Finset (Fin nv)) (x : Fin d → ℝ) :
    expoForm rows pt S x = ∑ row ∈ selRows rows pt S, rowForm row x := by
  simp [expoForm]

theorem expoForm_le {S : Finset (Fin nv)} {x : Fin d → ℝ} (hx : x ∈ polyOf rows) :
    expoForm rows pt S x ≤ expoBound rows pt S := by
  rw [expoForm_apply, expoBound]
  exact Finset.sum_le_sum fun row hrow => hx row ((mem_selRows rows pt).1 hrow).1

theorem expoForm_pt_eq_iff (hQ : polyOf rows = convexHull ℝ (Set.range pt)) (S : Finset (Fin nv)) (k : Fin nv) :
    expoForm rows pt S (pt k) = expoBound rows pt S ↔ ∀ row ∈ selRows rows pt S, Tight pt row k := by
  rw [expoForm_apply, expoBound]
  exact Finset.sum_eq_sum_iff_of_le fun row hrow => pt_mem rows pt hQ k row ((mem_selRows rows pt).1 hrow).1

variable {rows pt}

theorem expoForm_pt_eq_iff_mem (hQ : polyOf rows = convexHull ℝ (Set.range pt)) {S : Finset (Fin nv)}
    (hS : IsClosedSet rows pt S) (k : Fin nv) :
    expoForm rows pt S (pt k) = expoBound rows pt S ↔ k ∈ S := by
  rw [expoForm_pt_eq_iff rows pt hQ]
  constructor
  · intro h
    exact hS k fun row hrow hall => h row ((mem_selRows rows pt).2 ⟨hrow, hall⟩)
  · intro hk row hrow
    exact ((mem_selRows rows pt).1 hrow).2 k hk

theorem argmax_expoForm (hQ : polyOf rows = convexHull ℝ (Set.range pt)) {S : Finset (Fin nv)}
    (hS : IsClosedSet rows pt S) (hne : S.Nonempty) :
    generatorArgmax (Set.range pt) (expoForm rows pt S) = pt '' (S : Set (Fin nv)) := by
  obtain ⟨s, hs⟩ := hne
  have hsM := (expoForm_pt_eq_iff_mem hQ hS s).2 hs
  ext x
  constructor
  · rintro ⟨⟨k, rfl⟩, hmax⟩
    have hle : expoForm rows pt S (pt s) ≤ expoForm rows pt S (pt k) := hmax _ ⟨s, rfl⟩
    have hk : expoForm rows pt S (pt k) = expoBound rows pt S :=
      le_antisymm (expoForm_le rows pt (pt_mem rows pt hQ k)) (hsM ▸ hle)
    exact ⟨k, (expoForm_pt_eq_iff_mem hQ hS k).1 hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k, rfl⟩, ?_⟩
    rintro _ ⟨j, rfl⟩
    rw [(expoForm_pt_eq_iff_mem hQ hS k).2 hk]
    exact expoForm_le rows pt (pt_mem rows pt hQ j)

end Exposing

/-- A nonempty closed set spans a face. -/
theorem isFace_of_closed (hQ : polyOf rows = convexHull ℝ (Set.range pt)) {S : Finset (Fin nv)}
    (hS : IsClosedSet rows pt S) (hne : S.Nonempty) :
    IsFace (polyOf rows) (convexHull ℝ (pt '' (S : Set (Fin nv)))) := by
  obtain ⟨s, hs⟩ := hne
  rw [hQ, ← argmax_expoForm hQ hS ⟨s, hs⟩]
  exact isFace_convexHull_generatorArgmax (Set.finite_range pt) ⟨pt s, s, rfl⟩ _

/-- The points in the face spanned by a nonempty closed set `S` are exactly those of `S`. -/
theorem mem_hull_iff_of_closed (hQ : polyOf rows = convexHull ℝ (Set.range pt)) {S : Finset (Fin nv)}
    (hS : IsClosedSet rows pt S) (hne : S.Nonempty) (k : Fin nv) :
    pt k ∈ convexHull ℝ (pt '' (S : Set (Fin nv))) ↔ k ∈ S := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := hne
    have hexp := toExposed_convexHull_eq (Set.finite_range pt) ⟨pt s, s, rfl⟩ (expoForm rows pt S)
    rw [argmax_expoForm hQ hS ⟨s, hs⟩] at hexp
    rw [← hexp] at h
    have h2 : pt k ∈ Set.range pt ∩ (expoForm rows pt S).toExposed (convexHull ℝ (Set.range pt)) :=
      ⟨⟨k, rfl⟩, h⟩
    rw [inter_toExposed_convexHull, argmax_expoForm hQ hS ⟨s, hs⟩] at h2
    obtain ⟨j, hj, hjk⟩ := h2
    rw [← expoForm_pt_eq_iff_mem hQ hS k, ← hjk]
    exact (expoForm_pt_eq_iff_mem hQ hS j).2 hj
  · intro hk
    exact subset_convexHull ℝ _ ⟨k, hk, rfl⟩

section Perturb

open Classical in
/-- **Perturbation.** The points maximizing a linear form form a closed set. Proof: let `p` be the centroid of the
maximizers and `k` a point tight on every row tight on all maximizers. Rows tight on all maximizers stay tight along
`ε ↦ p + ε • (p − pt k)`; the others are strict at `p`, so stay valid for small `ε > 0`. That point lies in the
polytope, so the form is at most its maximum there, which forces the form at `pt k` to be at least the maximum. -/
theorem argmax_closed (hQ : polyOf rows = convexHull ℝ (Set.range pt)) (ell : (Fin d → ℝ) →L[ℝ] ℝ)
    (hne : (Finset.univ.filter fun k => pt k ∈ generatorArgmax (Set.range pt) ell).Nonempty) :
    IsClosedSet rows pt (Finset.univ.filter fun k => pt k ∈ generatorArgmax (Set.range pt) ell) := by
  set S := Finset.univ.filter fun k => pt k ∈ generatorArgmax (Set.range pt) ell with hSdef
  intro k hk
  obtain ⟨s0, hs0⟩ := hne
  have hs0' : pt s0 ∈ generatorArgmax (Set.range pt) ell := (Finset.mem_filter.1 hs0).2
  set M := ell (pt s0) with hM
  have hleQ : ∀ x ∈ polyOf rows, ell x ≤ M := by
    rw [hQ]
    exact linear_le_on_convexHull _ ell M (by rintro _ ⟨j, rfl⟩; exact hs0'.2 _ ⟨j, rfl⟩)
  have hSM : ∀ s ∈ S, ell (pt s) = M := fun s hs =>
    le_antisymm (hs0'.2 _ ⟨s, rfl⟩) ((Finset.mem_filter.1 hs).2.2 _ ⟨s0, rfl⟩)
  have hcardpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.2 ⟨s0, hs0⟩
  set c : ℝ := (S.card : ℝ)⁻¹ with hc
  set p : Fin d → ℝ := c • ∑ s ∈ S, pt s with hp
  have hlin : ∀ f : (Fin d → ℝ) →L[ℝ] ℝ, f p = c * ∑ s ∈ S, f (pt s) := by
    intro f
    simp [hp, map_sum, smul_eq_mul]
  have hp_ell : ell p = M := by
    rw [hlin, Finset.sum_congr rfl hSM, Finset.sum_const, nsmul_eq_mul, hc]
    field_simp
  have hrow_p : ∀ row ∈ rows, (∀ s ∈ S, Tight pt row s) → rowForm row p = row.2 := by
    intro row _ hall
    rw [hlin, Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, hc]
    field_simp
  have hrow_p_lt : ∀ row ∈ rows, ¬ (∀ s ∈ S, Tight pt row s) → rowForm row p < row.2 := by
    intro row hrow hall
    push Not at hall
    obtain ⟨s1, hs1, hns1⟩ := hall
    have hlt : ∑ s ∈ S, rowForm row (pt s) < ∑ s ∈ S, (row.2 : ℝ) :=
      Finset.sum_lt_sum (fun s _ => pt_mem rows pt hQ s row hrow)
        ⟨s1, hs1, lt_of_le_of_ne (pt_mem rows pt hQ s1 row hrow) hns1⟩
    rw [Finset.sum_const, nsmul_eq_mul] at hlt
    rw [hlin, hc]
    rw [inv_mul_lt_iff₀ hcardpos]
    exact hlt
  have hy_row : ∀ (f : (Fin d → ℝ) →L[ℝ] ℝ) (ε : ℝ),
      f (p + ε • (p - pt k)) = f p + ε * (f p - f (pt k)) := by
    intro f ε
    simp [map_add, map_smul, map_sub, smul_eq_mul]
  have hev : ∀ᶠ ε in nhds (0 : ℝ), ∀ row ∈ rows.toFinset, rowForm row (p + ε • (p - pt k)) ≤ row.2 := by
    refine (Filter.eventually_all_finset _).2 fun row hrow => ?_
    have hrow' := List.mem_toFinset.1 hrow
    by_cases hall : ∀ s ∈ S, Tight pt row s
    · refine Filter.Eventually.of_forall fun ε => ?_
      have hk' : rowForm row (pt k) = row.2 := hk row hrow' hall
      rw [hy_row, hrow_p row hrow' hall, hk']
      simp
    · have hcont : Continuous fun ε : ℝ => rowForm row p + ε * (rowForm row p - rowForm row (pt k)) := by
        fun_prop
      have h0 : rowForm row p + (0 : ℝ) * (rowForm row p - rowForm row (pt k)) < (row.2 : ℝ) := by
        simpa using hrow_p_lt row hrow' hall
      filter_upwards [hcont.continuousAt.eventually_lt continuousAt_const h0] with ε hε
      rw [hy_row]
      exact hε.le
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hεpos : (0 : ℝ) < δ / 2 := half_pos hδ
  have hdist : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hεpos]
    linarith
  have hyQ : p + (δ / 2) • (p - pt k) ∈ polyOf rows := fun row hrow =>
    hball hdist row (List.mem_toFinset.2 hrow)
  have hyle := hleQ _ hyQ
  rw [hy_row, hp_ell] at hyle
  have hMk : M ≤ ell (pt k) := by nlinarith
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨k, rfl⟩, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact (hs0'.2 _ ⟨j, rfl⟩).trans hMk

end Perturb

/-- Every face is spanned by a nonempty closed set. -/
theorem exists_closed_of_isFace (hQ : polyOf rows = convexHull ℝ (Set.range pt)) {F : Set (Fin d → ℝ)}
    (hF : IsFace (polyOf rows) F) :
    ∃ S : Finset (Fin nv), S.Nonempty ∧ IsClosedSet rows pt S ∧ F = convexHull ℝ (pt '' (S : Set (Fin nv))) := by
  classical
  rw [hQ] at hF
  obtain ⟨ell, hell⟩ := hF.exists_generatorArgmax (Set.finite_range pt)
  have hVN : (Set.range pt).Nonempty := by
    obtain ⟨x, hx⟩ := hF.1
    rw [hell] at hx
    obtain ⟨y, hy⟩ := convexHull_nonempty_iff.1 ⟨x, hx⟩
    exact ⟨y, hy.1⟩
  set S := Finset.univ.filter fun k => pt k ∈ generatorArgmax (Set.range pt) ell with hSdef
  have himage : pt '' (S : Set (Fin nv)) = generatorArgmax (Set.range pt) ell := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (Finset.mem_filter.1 hk).2
    · intro hx
      obtain ⟨k, rfl⟩ := hx.1
      exact ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩, rfl⟩
  have hne : S.Nonempty := by
    obtain ⟨x, hx⟩ := generatorArgmax_nonempty (Set.finite_range pt) hVN ell
    obtain ⟨k, rfl⟩ := hx.1
    exact ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩⟩
  exact ⟨S, hne, argmax_closed hQ ell hne, by rw [himage]; exact hell⟩

/-- A strictly smaller nonempty closed set spans a face of strictly smaller dimension. -/
theorem adim_lt_of_ssubset (hQ : polyOf rows = convexHull ℝ (Set.range pt)) {S T : Finset (Fin nv)}
    (hS : IsClosedSet rows pt S) (_hT : IsClosedSet rows pt T) (hne : S.Nonempty) (hST : S ⊂ T) :
    adim (pt '' (S : Set (Fin nv))) < adim (pt '' (T : Set (Fin nv))) := by
  classical
  obtain ⟨s, hs⟩ := hne
  obtain ⟨k, hkT, hkS⟩ := Finset.exists_of_ssubset hST
  have hsM := (expoForm_pt_eq_iff_mem hQ hS s).2 hs
  have hkM : expoForm rows pt S (pt k) ≠ expoBound rows pt S := fun h =>
    hkS ((expoForm_pt_eq_iff_mem hQ hS k).1 h)
  have hle : vectorSpan ℝ (pt '' (S : Set (Fin nv))) ≤ vectorSpan ℝ (pt '' (T : Set (Fin nv))) :=
    vectorSpan_mono ℝ (Set.image_mono (Finset.coe_subset.2 hST.subset))
  unfold adim
  by_contra hnot
  push Not at hnot
  have heq := Submodule.eq_of_le_of_finrank_le hle hnot
  have hker : vectorSpan ℝ (pt '' (S : Set (Fin nv))) ≤
      LinearMap.ker ((expoForm rows pt S : (Fin d → ℝ) →L[ℝ] ℝ) : (Fin d → ℝ) →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨a, ⟨i, hi, rfl⟩, b, ⟨j, hj, rfl⟩, rfl⟩
    have hi' := (expoForm_pt_eq_iff_mem hQ hS i).2 hi
    have hj' := (expoForm_pt_eq_iff_mem hQ hS j).2 hj
    simp [vsub_eq_sub, map_sub, hi', hj']
  have hmem : pt k -ᵥ pt s ∈ vectorSpan ℝ (pt '' (S : Set (Fin nv))) := by
    rw [heq]
    exact vsub_mem_vectorSpan ℝ ⟨k, hkT, rfl⟩ ⟨s, Finset.mem_coe.2 (hST.subset hs), rfl⟩
  have hzero := hker hmem
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, vsub_eq_sub, map_sub] at hzero
  exact hkM (by rw [← hsM]; linarith)

end HibiLi.Census
