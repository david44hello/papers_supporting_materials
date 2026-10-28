/-
HibiLi/Example21/ProperFacesAffine.lean — Proposition 5.1, switch of c in X: on every proper face of B, L or U is affine
(paper v2.10 lines 908-914; helpers; the row prop_5_1_proper_faces_affine is in Statements.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.CenterResult
import HibiLi.Proofs.Lemma36
import HibiLi.Polytope.SubdivisionPurity

namespace HibiLi

namespace B2

open Example21 CenterGeometry CenterSwitch

/-- The coordinate `u ↦ u i`, as an affine map. -/
noncomputable def coord (i : Coord) : (Coord → ℝ) →ᵃ[ℝ] ℝ :=
  (LinearMap.proj (R := ℝ) (φ := fun _ : Coord => ℝ) i).toAffineMap

@[simp] theorem coord_apply (i : Coord) (u : Coord → ℝ) : coord i u = u i := rfl

theorem affineOn_coord {f : (Coord → ℝ) → ℝ} {D : Set (Coord → ℝ)} (i : Coord)
    (h : ∀ u ∈ D, f u = u i) : AffineOn f D :=
  ⟨coord i, fun u hu => (h u hu).trans (coord_apply i u).symm⟩

theorem affineOn_mono {f : (Coord → ℝ) → ℝ} {D D' : Set (Coord → ℝ)} (h : AffineOn f D) (sub : D' ⊆ D) :
    AffineOn f D' := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun u hu => hg u (sub hu)⟩

/-- The eight inequalities of `B`, in the paper's order (v2.10 lines 908-909). -/
theorem ineqs {u : Coord → ℝ} (hu : u ∈ center.B) :
    0 ≤ u canonical.pa ∧ 0 ≤ u canonical.pb ∧ u canonical.pg ≤ 1 ∧ u canonical.ph ≤ 1 ∧
    u canonical.pa ≤ u canonical.pg ∧ u canonical.pa ≤ u canonical.ph ∧
    u canonical.pb ≤ u canonical.pg ∧ u canonical.pb ≤ u canonical.ph := by
  obtain ⟨ha, hb, hm, hg, hh⟩ := (mem_B_iff u).mp hu
  rw [max_le_iff, le_min_iff, le_min_iff] at hm
  exact ⟨ha, hb, hg, hh, hm.1.1, hm.1.2, hm.2.1, hm.2.2⟩

/-- A point where all eight inequalities are strict is an interior point of `B`. -/
theorem mem_interior_B {w : Coord → ℝ} (ha : 0 < w canonical.pa) (hb : 0 < w canonical.pb)
    (hg : w canonical.pg < 1) (hh : w canonical.ph < 1) (hag : w canonical.pa < w canonical.pg)
    (hah : w canonical.pa < w canonical.ph) (hbg : w canonical.pb < w canonical.pg)
    (hbh : w canonical.pb < w canonical.ph) : w ∈ interior center.B := by
  have cts (i : Coord) : Continuous fun u : Coord → ℝ => u i := continuous_apply i
  have hopen : IsOpen {u : Coord → ℝ | 0 < u canonical.pa ∧ 0 < u canonical.pb ∧ u canonical.pg < 1 ∧
      u canonical.ph < 1 ∧ u canonical.pa < u canonical.pg ∧ u canonical.pa < u canonical.ph ∧
      u canonical.pb < u canonical.pg ∧ u canonical.pb < u canonical.ph} :=
    (isOpen_lt continuous_const (cts _)).and <| (isOpen_lt continuous_const (cts _)).and <|
      (isOpen_lt (cts _) continuous_const).and <| (isOpen_lt (cts _) continuous_const).and <|
      (isOpen_lt (cts _) (cts _)).and <| (isOpen_lt (cts _) (cts _)).and <|
      (isOpen_lt (cts _) (cts _)).and (isOpen_lt (cts _) (cts _))
  refine interior_maximal ?_ hopen ⟨ha, hb, hg, hh, hag, hah, hbg, hbh⟩
  rintro u ⟨ha, hb, hg, hh, hag, hah, hbg, hbh⟩
  exact (mem_B_iff u).mpr
    ⟨ha.le, hb.le, max_le (le_min hag.le hah.le) (le_min hbg.le hbh.le), hg.le, hh.le⟩

/-- If `f ≤ g` on `B` (affine `f`, `g`) with equality at a relative-interior point of a face `E`, then `f = g` on `E`. -/
theorem tight {E : Set (Coord → ℝ)} (hE : IsFace center.B E) {w : Coord → ℝ} (hw : w ∈ intrinsicInterior ℝ E)
    (f g : (Coord → ℝ) →ᵃ[ℝ] ℝ) (hle : ∀ u ∈ center.B, f u ≤ g u) (heq : f w = g w) :
    ∀ u ∈ E, f u = g u := by
  intro u hu
  have key := Proofs.affine_eq_of_intrinsicInterior_min hw (g - f)
    (fun y hy => by
      simp only [AffineMap.coe_sub, Pi.sub_apply, heq, sub_self, sub_nonneg]
      exact hle y (hE.2.subset hy)) u hu
  simp only [AffineMap.coe_sub, Pi.sub_apply, heq, sub_self, sub_eq_zero] at key
  exact key.symm

/-- Conjunct 1: every proper face of `B` lies in one of the eight hyperplanes. -/
theorem proper_face_hyperplane {E : Set (Coord → ℝ)} (hE : IsFace center.B E) (hne : E ≠ center.B) :
    E ⊆ {u | u canonical.pa = 0} ∨ E ⊆ {u | u canonical.pb = 0} ∨ E ⊆ {u | u canonical.pg = 1} ∨
    E ⊆ {u | u canonical.ph = 1} ∨ E ⊆ {u | u canonical.pa = u canonical.pg} ∨
    E ⊆ {u | u canonical.pa = u canonical.ph} ∨ E ⊆ {u | u canonical.pb = u canonical.pg} ∨
    E ⊆ {u | u canonical.pb = u canonical.ph} := by
  obtain ⟨w, hw⟩ := Set.Nonempty.intrinsicInterior (hE.2.convex center.B_isPolytope.convex) hE.1
  have hwB : w ∈ center.B := hE.2.subset (intrinsicInterior_subset hw)
  obtain ⟨ha, hb, hg, hh, hag, hah, hbg, hbh⟩ := ineqs hwB
  rcases ha.lt_or_eq with ha | ha
  swap
  · exact Or.inl fun u hu => by
      simpa using (tight hE hw (AffineMap.const ℝ _ 0) (coord canonical.pa)
        (fun v hv => by simpa using (ineqs hv).1) (by simpa using ha) u hu).symm
  rcases hb.lt_or_eq with hb | hb
  swap
  · exact Or.inr <| Or.inl fun u hu => by
      simpa using (tight hE hw (AffineMap.const ℝ _ 0) (coord canonical.pb)
        (fun v hv => by simpa using (ineqs hv).2.1) (by simpa using hb) u hu).symm
  rcases hg.lt_or_eq with hg | hg
  swap
  · exact Or.inr <| Or.inr <| Or.inl fun u hu => by
      simpa using tight hE hw (coord canonical.pg) (AffineMap.const ℝ _ 1)
        (fun v hv => by simpa using (ineqs hv).2.2.1) (by simpa using hg) u hu
  rcases hh.lt_or_eq with hh | hh
  swap
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl fun u hu => by
      simpa using tight hE hw (coord canonical.ph) (AffineMap.const ℝ _ 1)
        (fun v hv => by simpa using (ineqs hv).2.2.2.1) (by simpa using hh) u hu
  rcases hag.lt_or_eq with hag | hag
  swap
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl fun u hu => by
      simpa using tight hE hw (coord canonical.pa) (coord canonical.pg)
        (fun v hv => by simpa using (ineqs hv).2.2.2.2.1) (by simpa using hag) u hu
  rcases hah.lt_or_eq with hah | hah
  swap
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl fun u hu => by
      simpa using tight hE hw (coord canonical.pa) (coord canonical.ph)
        (fun v hv => by simpa using (ineqs hv).2.2.2.2.2.1) (by simpa using hah) u hu
  rcases hbg.lt_or_eq with hbg | hbg
  swap
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl fun u hu => by
      simpa using tight hE hw (coord canonical.pb) (coord canonical.pg)
        (fun v hv => by simpa using (ineqs hv).2.2.2.2.2.2.1) (by simpa using hbg) u hu
  rcases hbh.lt_or_eq with hbh | hbh
  swap
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr fun u hu => by
      simpa using tight hE hw (coord canonical.pb) (coord canonical.ph)
        (fun v hv => by simpa using (ineqs hv).2.2.2.2.2.2.2) (by simpa using hbh) u hu
  exact absurd (hE.eq_of_mem_intrinsicInterior (intrinsicInterior_subset hw)
    (interior_subset_intrinsicInterior (mem_interior_B ha hb hg hh hag hah hbg hbh))) hne

/-! ### `L` or `U` on the first four hyperplanes -/

theorem L_alpha : AffineOn center.L {u | u ∈ center.B ∧ u canonical.pa = 0} :=
  affineOn_coord canonical.pb fun u ⟨hu, h⟩ => by
    rw [L_eq hu, h]; exact max_eq_right (ineqs hu).2.1

theorem L_beta : AffineOn center.L {u | u ∈ center.B ∧ u canonical.pb = 0} :=
  affineOn_coord canonical.pa fun u ⟨hu, h⟩ => by
    rw [L_eq hu, h]; exact max_eq_left (ineqs hu).1

theorem U_gamma : AffineOn center.U {u | u ∈ center.B ∧ u canonical.pg = 1} :=
  affineOn_coord canonical.ph fun u ⟨hu, h⟩ => by
    rw [U_eq hu, h]; exact min_eq_right (ineqs hu).2.2.2.1

theorem U_eta : AffineOn center.U {u | u ∈ center.B ∧ u canonical.ph = 1} :=
  affineOn_coord canonical.pg fun u ⟨hu, h⟩ => by
    rw [U_eq hu, h]; exact min_eq_left (ineqs hu).2.2.1

/-! ### `L = U` on the other four, and both are affine there -/

theorem L_eq_U {u : Coord → ℝ} (hu : u ∈ center.B)
    (h : u canonical.pa = u canonical.pg ∨ u canonical.pa = u canonical.ph ∨
      u canonical.pb = u canonical.pg ∨ u canonical.pb = u canonical.ph) : center.L u = center.U u := by
  rw [L_eq hu, U_eq hu]
  refine le_antisymm ((mem_B_iff u).mp hu).2.2.1 ?_
  rcases h with h | h | h | h
  · exact (min_le_left _ _).trans (by rw [← h]; exact le_max_left _ _)
  · exact (min_le_right _ _).trans (by rw [← h]; exact le_max_left _ _)
  · exact (min_le_left _ _).trans (by rw [← h]; exact le_max_right _ _)
  · exact (min_le_right _ _).trans (by rw [← h]; exact le_max_right _ _)

theorem LU_alpha_gamma : AffineOn center.L {u | u ∈ center.B ∧ u canonical.pa = u canonical.pg} ∧
    AffineOn center.U {u | u ∈ center.B ∧ u canonical.pa = u canonical.pg} := by
  constructor
  · refine affineOn_coord canonical.pa fun u hu' => ?_
    obtain ⟨hu, h⟩ := hu'
    obtain ⟨-, -, -, -, -, -, hbg, -⟩ := ineqs hu
    rw [L_eq hu]; exact max_eq_left (by linarith)
  · refine affineOn_coord canonical.pg fun u hu' => ?_
    obtain ⟨hu, h⟩ := hu'
    obtain ⟨-, -, -, -, -, hah, -, -⟩ := ineqs hu
    rw [U_eq hu]; exact min_eq_left (by linarith)

theorem LU_alpha_eta : AffineOn center.L {u | u ∈ center.B ∧ u canonical.pa = u canonical.ph} ∧
    AffineOn center.U {u | u ∈ center.B ∧ u canonical.pa = u canonical.ph} := by
  constructor
  · refine affineOn_coord canonical.pa fun u hu' => ?_
    obtain ⟨hu, h⟩ := hu'
    obtain ⟨-, -, -, -, -, -, -, hbh⟩ := ineqs hu
    rw [L_eq hu]; exact max_eq_left (by linarith)
  · refine affineOn_coord canonical.ph fun u hu' => ?_
    obtain ⟨hu, h⟩ := hu'
    obtain ⟨-, -, -, -, hag, -, -, -⟩ := ineqs hu
    rw [U_eq hu]; exact min_eq_right (by linarith)

theorem LU_beta_gamma : AffineOn center.L {u | u ∈ center.B ∧ u canonical.pb = u canonical.pg} ∧
    AffineOn center.U {u | u ∈ center.B ∧ u canonical.pb = u canonical.pg} := by
  constructor
  · refine affineOn_coord canonical.pb fun u hu' => ?_
    obtain ⟨hu, h⟩ := hu'
    obtain ⟨-, -, -, -, hag, -, -, -⟩ := ineqs hu
    rw [L_eq hu]; exact max_eq_right (by linarith)
  · refine affineOn_coord canonical.pg fun u hu' => ?_
    obtain ⟨hu, h⟩ := hu'
    obtain ⟨-, -, -, -, -, -, -, hbh⟩ := ineqs hu
    rw [U_eq hu]; exact min_eq_left (by linarith)

theorem LU_beta_eta : AffineOn center.L {u | u ∈ center.B ∧ u canonical.pb = u canonical.ph} ∧
    AffineOn center.U {u | u ∈ center.B ∧ u canonical.pb = u canonical.ph} := by
  constructor
  · refine affineOn_coord canonical.pb fun u hu' => ?_
    obtain ⟨hu, h⟩ := hu'
    obtain ⟨-, -, -, -, -, hah, -, -⟩ := ineqs hu
    rw [L_eq hu]; exact max_eq_right (by linarith)
  · refine affineOn_coord canonical.ph fun u hu' => ?_
    obtain ⟨hu, h⟩ := hu'
    obtain ⟨-, -, -, -, -, -, hbg, -⟩ := ineqs hu
    rw [U_eq hu]; exact min_eq_right (by linarith)

/-- The conclusion: on every proper face of `B`, `L` or `U` is affine. -/
theorem proper_face_affine {E : Set (Coord → ℝ)} (hE : IsFace center.B E) (hne : E ≠ center.B) :
    AffineOn center.L E ∨ AffineOn center.U E := by
  have sub {p : (Coord → ℝ) → Prop} (h : E ⊆ {u | p u}) : E ⊆ {u | u ∈ center.B ∧ p u} :=
    fun u hu => ⟨hE.2.subset hu, h hu⟩
  rcases proper_face_hyperplane hE hne with h | h | h | h | h | h | h | h
  · exact Or.inl (affineOn_mono L_alpha (sub h))
  · exact Or.inl (affineOn_mono L_beta (sub h))
  · exact Or.inr (affineOn_mono U_gamma (sub h))
  · exact Or.inr (affineOn_mono U_eta (sub h))
  · exact Or.inl (affineOn_mono LU_alpha_gamma.1 (sub h))
  · exact Or.inl (affineOn_mono LU_alpha_eta.1 (sub h))
  · exact Or.inl (affineOn_mono LU_beta_gamma.1 (sub h))
  · exact Or.inl (affineOn_mono LU_beta_eta.1 (sub h))

end B2

end HibiLi
