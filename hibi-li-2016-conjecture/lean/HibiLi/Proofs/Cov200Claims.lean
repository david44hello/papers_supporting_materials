/-
HibiLi/Proofs/Cov200Claims.lean — proofs of seven in-text claims of paper v2.10 found by the last delta reader (valid
inequalities cut out a face, carrier = intersection of faces, strictness at u0, a facet and a vertex outside it, carrier
of S n T, the two cells on opposite sides of aff(D), L not affine near the wall); rows in Statements.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Polytope.CarrierInterior
import HibiLi.Proofs.Lemma48
import HibiLi.Proofs.Lemma45
import HibiLi.Example21.CenterGeometry
import HibiLi.Polytope.SharedFacet

namespace HibiLi.Proofs.Cov200

open HibiLi HibiLi.Proofs

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Q1: finitely many valid inequalities `l i ≤ c i`: their sum is valid and cuts out the same set; if that set is
nonempty, it is a face. -/
theorem valid_tight_face_proved {ι : Type*} (Q : Set E) (s : Finset ι) (l : ι → StrongDual ℝ E) (c : ι → ℝ)
    (hvalid : ∀ i ∈ s, ∀ x ∈ Q, l i x ≤ c i) :
    (∀ x ∈ Q, (∑ i ∈ s, l i) x ≤ ∑ i ∈ s, c i) ∧
      {x ∈ Q | ∀ i ∈ s, l i x = c i} = {x ∈ Q | (∑ i ∈ s, l i) x = ∑ i ∈ s, c i} ∧
      ({x ∈ Q | ∀ i ∈ s, l i x = c i}.Nonempty → IsFace Q {x ∈ Q | ∀ i ∈ s, l i x = c i}) := by
  have hsum : ∀ x, (∑ i ∈ s, l i) x = ∑ i ∈ s, l i x := fun x => by simp
  have hvalidSum : ∀ x ∈ Q, (∑ i ∈ s, l i) x ≤ ∑ i ∈ s, c i := fun x hx => by
    rw [hsum]
    exact Finset.sum_le_sum fun i hi => hvalid i hi x hx
  have hcut : {x ∈ Q | ∀ i ∈ s, l i x = c i} = {x ∈ Q | (∑ i ∈ s, l i) x = ∑ i ∈ s, c i} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, by rw [hsum]; exact Finset.sum_congr rfl h⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, (Finset.sum_eq_sum_iff_of_le fun i hi => hvalid i hi x hx).1 (by rw [← hsum]; exact h)⟩
  refine ⟨hvalidSum, hcut, fun hne => ⟨hne, fun _ => ⟨∑ i ∈ s, l i, ?_⟩⟩⟩
  obtain ⟨x₀, hx₀Q, hx₀⟩ := hne
  have hx₀C : (∑ i ∈ s, l i) x₀ = ∑ i ∈ s, c i := by
    rw [hsum]
    exact Finset.sum_congr rfl hx₀
  rw [hcut]
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hxC⟩
    exact ⟨hx, fun y hy => (hvalidSum y hy).trans hxC.ge⟩
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, le_antisymm (hvalidSum x hx) (hx₀C.symm.le.trans (hmax x₀ hx₀Q))⟩

/-- Q3: a carrier is the intersection of all faces that contain the cell. -/
theorem carrier_eq_sInter {B C K : Set E} (h : IsCarrier B K C) : K = ⋂₀ {G | IsFace B G ∧ C ⊆ G} :=
  Set.Subset.antisymm (Set.subset_sInter fun G hG => h.2.2 G hG.1 hG.2) (Set.sInter_subset_of_mem ⟨h.1, h.2.1⟩)

/-- Q6, general form: if `A' ⊆ A ⊆ B` and `A'` has carrier `B`, then so does `A`. -/
theorem carrier_self_of_subset {B A A' : Set E} (hA : A ⊆ B) (hA' : A' ⊆ A) (h : IsCarrier B B A') :
    IsCarrier B B A :=
  ⟨h.1, hA, fun G hG hAG => h.2.2 G hG (hA'.trans hAG)⟩

end General

/-- Cells of `S` lie in `B`. -/
theorem cellsS_subset_B {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) {C : Set (s.P' → ℝ)}
    (hC : C ∈ s.cellsS) : C ⊆ s.B := by
  obtain ⟨K, -, -, hF⟩ := hC
  exact fun u hu => (hF.subset hu).1

/-- Cells of `T` lie in `B`. -/
theorem cellsT_subset_B {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) {C : Set (s.P' → ℝ)}
    (hC : C ∈ s.cellsT) : C ⊆ s.B := by
  obtain ⟨j, -, -, hF⟩ := hC
  exact fun u hu => (hF.subset hu).1

/-- Q3 for the cells of `S`, `T`, `R`: the intersection of all faces of `B` containing the cell is its carrier. -/
theorem carrier_sInter_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (C : Set (s.P' → ℝ))
    (hC : C ∈ s.cellsS ∨ C ∈ s.cellsT ∨ C ∈ s.cellsR) :
    IsCarrier s.B (⋂₀ {G | IsFace s.B G ∧ C ⊆ G}) C ∧ ∀ K, IsCarrier s.B K C → K = ⋂₀ {G | IsFace s.B G ∧ C ⊆ G} := by
  obtain ⟨⟨K, hK, -⟩, -⟩ := sec3_carrier_proved s C hC
  refine ⟨?_, fun K' hK' => carrier_eq_sInter hK'⟩
  rwa [← carrier_eq_sInter hK]

/-- Q6: a cell `S ∩ T` has carrier `B` only if `S` and `T` do. -/
theorem RT_carrier_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) {S T : Set (s.P' → ℝ)}
    (hS : S ∈ s.cellsS) (hT : T ∈ s.cellsT) (h : IsCarrier s.B s.B (S ∩ T)) :
    IsCarrier s.B s.B S ∧ IsCarrier s.B s.B T :=
  ⟨carrier_self_of_subset (cellsS_subset_B s hS) Set.inter_subset_left h,
    carrier_self_of_subset (cellsT_subset_B s hT) Set.inter_subset_right h⟩

/-- Q5, first part: a polytope of dimension `t + 1` has a facet (a face of dimension `t`). -/
theorem exists_facet_proved {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (hne : Q.Nonempty)
    (t : ℕ) (hs : adim Q = t + 1) : ∃ F, IsFace Q F ∧ adim F + 1 = adim Q := by
  obtain ⟨v₀, -, hv₀⟩ := exists_vertex_mem hQ (IsFace.refl hne)
  let proper : Set (Set (ι → ℝ)) := {G | IsFace Q G ∧ G ≠ Q}
  obtain ⟨F, ⟨hF, hFQ⟩, hFmax⟩ := (hQ.finite_faces.subset fun G (hG : G ∈ proper) => hG.1).exists_maximal
    ⟨{v₀}, hv₀, fun h => by have := adim_singleton v₀; rw [h, hs] at this; omega⟩
  obtain ⟨m, QF, hQF, hQFe, hQFdim, φ, -⟩ := Cited.ziegler_face_figure Q hQ F hF
  have hQFne : QF.Nonempty := Set.nonempty_iff_ne_empty.mpr fun h => hFQ (hQFe.mp h)
  have hdimF := hQFdim hQFne
  have htop : ∀ G : {G // IsFace Q G ∧ F ⊂ G}, G.1 = Q := fun G => by
    by_contra h
    exact G.2.2.not_subset (hFmax ⟨G.2.1, h⟩ G.2.2.subset)
  have hle1 : fNum QF 0 ≤ 1 := by
    refine (Set.ncard_le_one (hQF.faces_finite 0)).mpr fun a ha b hb => ?_
    have := φ.symm.injective
      (Subtype.ext ((htop _).trans (htop _).symm) : φ.symm ⟨a, ha.1⟩ = φ.symm ⟨b, hb.1⟩)
    exact congrArg Subtype.val this
  have hQF0 := lemma_4_8_simplex_proved QF hQF hQFne 0 (Nat.zero_le _)
  rw [Nat.choose_one_right] at hQF0
  exact ⟨F, hF, by omega⟩

/-- Q5, second part: a polytope has a vertex outside each of its proper faces. -/
theorem exists_vertex_not_mem_proved {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q)
    (hne : Q.Nonempty) (F : Set (ι → ℝ)) (hF : IsFace Q F) (hFQ : F ≠ Q) : ∃ v, IsFace Q {v} ∧ v ∉ F := by
  obtain ⟨l, hl⟩ := hF.2 hF.1
  obtain ⟨S, hS⟩ := id hQ
  have hcomp : IsCompact Q := hS ▸ S.finite_toSet.isCompact_convexHull ℝ
  obtain ⟨x, hx, hxmin⟩ := hcomp.exists_isMinOn hne l.continuous.continuousOn
  have hGface : IsFace Q {y ∈ Q | ∀ z ∈ Q, l y ≤ l z} := by
    refine ⟨⟨x, hx, fun z hz => hxmin hz⟩, fun _ => ⟨-l, ?_⟩⟩
    ext y
    simp
  obtain ⟨v, ⟨-, hvmin⟩, hv⟩ := exists_vertex_mem hQ hGface
  refine ⟨v, hv, fun hvF => ?_⟩
  rw [hl] at hvF
  apply hFQ
  refine Set.Subset.antisymm hF.subset fun y hy => ?_
  rw [hl]
  exact ⟨hy, fun z hz => (hvF.2 z hz).trans (hvmin y hy)⟩

section Q4

variable {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)

/-- The four special coordinates of `u₀` are `1/4` or `3/4`. -/
lemma u0_special_bounds {p : x.toSwitch.P'} (hs : p ∈ x.special) : 0 < x.u0 p ∧ x.u0 p ≤ 3 / 4 := by
  simp only [XSwitch.special, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · rw [Lemma45.u0_pa]; norm_num
  · rw [Lemma45.u0_pb]; norm_num
  · rw [Lemma45.u0_pg]; norm_num
  · rw [Lemma45.u0_ph]; norm_num

/-- Every order coordinate `y_r` (`r ∉ I`) of `u₀` is `3/4` or `1`. -/
lemma u0_J_ge {r : x.toSwitch.P'} (hr : r ∉ x.toSwitch.I') : 3 / 4 ≤ x.u0 r := by
  by_cases hs : r ∈ x.special
  · rcases Lemma45.special_J x hs hr with rfl | rfl
    · exact (Lemma45.u0_pg x).ge
    · exact (Lemma45.u0_ph x).ge
  · rw [Lemma45.u0_J x hs hr]
    norm_num

/-- At `u₀` every chain sum of `I` is at most `1/4` (a chain meets at most one of `a, b`). -/
lemma chain_u0 {K : Finset x.toSwitch.P'} (hKI : ↑K ⊆ x.toSwitch.I') (hK : IsChainSet x.toSwitch.P' K) :
    ∑ p ∈ K, x.u0 p ≤ 1 / 4 := by
  have h0 := Lemma44.chainSum_le_max x (u := x.u0) (pa := x.pa) (pb := x.pb) rfl rfl
    (fun p hp ha hb => Lemma45.u0_I x (Lemma45.not_special_I x hp (fun e => ha (congrArg Subtype.val e))
      (fun e => hb (congrArg Subtype.val e))) hp) (by rw [Lemma45.u0_pa]; norm_num) hKI hK
  rw [Lemma45.u0_pa, Lemma45.u0_pb, max_self] at h0
  exact h0

/-- Q4: the inequalities of `B` that involve `α, β, γ, η` are strict at `u₀` (and so are all chain inequalities). -/
theorem u0_strict_proved :
    (∀ p ∈ x.special, 0 < x.u0 p ∧ x.u0 p < 1) ∧
    (∀ r r', r ∉ x.toSwitch.I' → r' ∉ x.toSwitch.I' → r < r' → (r ∈ x.special ∨ r' ∈ x.special) →
      x.u0 r < x.u0 r') ∧
    (∀ r ∉ x.toSwitch.I', ∀ K : Finset x.toSwitch.P', ↑K ⊆ x.toSwitch.I' → IsChainSet x.toSwitch.P' K →
      (∀ p ∈ K, p < r) → ∑ p ∈ K, x.u0 p < x.u0 r) ∧
    (∀ K : Finset x.toSwitch.P', ↑K ⊆ x.toSwitch.I' → IsChainSet x.toSwitch.P' K → ∑ p ∈ K, x.u0 p < 1) := by
  refine ⟨fun p hs => ?_, fun r r' hr hr' hlt hspec => ?_, fun r hr K hKI hK _ => ?_, fun K hKI hK => ?_⟩
  · have h := u0_special_bounds x hs
    exact ⟨h.1, by linarith [h.2]⟩
  · have hr'ns : r' ∉ x.special := fun hs' =>
      hlt.ne (Lemma45.eq_of_le_special x hr (Lemma45.special_J x hs' hr') hlt.le)
    rw [Lemma45.u0_J x hr'ns hr']
    rcases hspec with hs | hs'
    · linarith [(u0_special_bounds x hs).2]
    · exact absurd hs' hr'ns
  · linarith [chain_u0 x hKI hK, u0_J_ge x hr]
  · linarith [chain_u0 x hKI hK]

end Q4

section Q8

open HibiLi.Example21 HibiLi.Example21.CenterGeometry

/-- The coordinates `(α, β, γ, η)` of a point (copied from the Figure 2 draft). -/
theorem canonicalEquiv_coords (u : Coord → ℝ) :
    canonicalEquiv u = ![u CenterSwitch.canonical.pa, u CenterSwitch.canonical.pb, u CenterSwitch.canonical.pg,
      u CenterSwitch.canonical.ph] := by
  ext i
  fin_cases i <;> rfl

/-- The point with coordinates `(α, β, γ, η) = v` (copied from the Figure 2 draft). -/
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

/-- An affine function at the midpoint is the average (copied from the Figure 2 draft). -/
theorem affine_mid (g : (Coord → ℝ) →ᵃ[ℝ] ℝ) (p q m : Coord → ℝ) (hm : ∀ c, m c = (p c + q c) / 2) :
    g m = (g p + g q) / 2 := by
  have hline : m = AffineMap.lineMap p q (1 / 2 : ℝ) := by
    funext c
    rw [AffineMap.lineMap_apply_module, hm c]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hline, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
  ring

/-- A point whose four coordinates are within `t/2` of those of `v` lies in `ball(v, ε)` when `t ≤ ε`. -/
theorem dist_lt_of_coords {v w : Coord → ℝ} {t ε : ℝ} (ht : 0 < t) (htε : t ≤ ε)
    (h : ∀ c, |w c - v c| ≤ t / 2) : dist w v < ε := by
  have h1 : dist w v ≤ t / 2 := (dist_pi_le_iff (by linarith)).2 fun c => by rw [Real.dist_eq]; exact h c
  linarith

/-- Q8, `L`: at a slice point with `ξ = 0`, `L` is affine on no neighbourhood within the slice. -/
theorem L_not_affine_near_proved (v : Coord → ℝ) (hv : v ∈ center.B)
    (hPa : v CenterSwitch.canonical.pa + v CenterSwitch.canonical.pb = 1 / 2)
    (hPg : v CenterSwitch.canonical.pg + v CenterSwitch.canonical.ph = 3 / 2)
    (hξ : v CenterSwitch.canonical.pa = v CenterSwitch.canonical.pb) {ε : ℝ} (hε : 0 < ε) :
    ¬ AffineOn center.L {u | u ∈ center.B ∧ u CenterSwitch.canonical.pa + u CenterSwitch.canonical.pb = 1 / 2 ∧
      u CenterSwitch.canonical.pg + u CenterSwitch.canonical.ph = 3 / 2 ∧ dist u v < ε} := by
  rintro ⟨g, hg⟩
  have hvB := hv
  rw [mem_B_iff] at hv
  obtain ⟨-, -, -, hvg, hvh⟩ := hv
  have ha : v CenterSwitch.canonical.pa = 1 / 4 := by linarith
  have hb : v CenterSwitch.canonical.pb = 1 / 4 := by linarith
  have hg1 : 1 / 2 ≤ v CenterSwitch.canonical.pg := by linarith
  have hh1 : 1 / 2 ≤ v CenterSwitch.canonical.ph := by linarith
  obtain ⟨t, ht0, ht1, htε⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧ t ≤ ε :=
    ⟨min (1 / 2) ε, lt_min (by norm_num) hε, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨pa, pb, pg, ph⟩ := coords_symm
    ![1 / 4 - t / 2, 1 / 4 + t / 2, v CenterSwitch.canonical.pg, v CenterSwitch.canonical.ph]
  obtain ⟨qa, qb, qg, qh⟩ := coords_symm
    ![1 / 4 + t / 2, 1 / 4 - t / 2, v CenterSwitch.canonical.pg, v CenterSwitch.canonical.ph]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at pa pb pg ph qa qb qg qh
  set p := canonicalEquiv.symm
    ![1 / 4 - t / 2, 1 / 4 + t / 2, v CenterSwitch.canonical.pg, v CenterSwitch.canonical.ph]
  set q := canonicalEquiv.symm
    ![1 / 4 + t / 2, 1 / 4 - t / 2, v CenterSwitch.canonical.pg, v CenterSwitch.canonical.ph]
  have hpB : p ∈ center.B := by
    rw [mem_B_iff, pa, pb, pg, ph, max_le_iff, le_min_iff, le_min_iff]
    exact ⟨by linarith, by linarith, ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, hvg, hvh⟩
  have hqB : q ∈ center.B := by
    rw [mem_B_iff, qa, qb, qg, qh, max_le_iff, le_min_iff, le_min_iff]
    exact ⟨by linarith, by linarith, ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, hvg, hvh⟩
  have hpd : dist p v < ε := dist_lt_of_coords ht0 htε fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl
    · rw [pa, ha, abs_le]; constructor <;> linarith
    · rw [pb, hb, abs_le]; constructor <;> linarith
    · rw [pg, sub_self, abs_zero]; linarith
    · rw [ph, sub_self, abs_zero]; linarith
  have hqd : dist q v < ε := dist_lt_of_coords ht0 htε fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl
    · rw [qa, ha, abs_le]; constructor <;> linarith
    · rw [qb, hb, abs_le]; constructor <;> linarith
    · rw [qg, sub_self, abs_zero]; linarith
    · rw [qh, sub_self, abs_zero]; linarith
  have hp := hg p ⟨hpB, by rw [pa, pb]; ring, by rw [pg, ph]; exact hPg, hpd⟩
  have hq := hg q ⟨hqB, by rw [qa, qb]; ring, by rw [qg, qh]; exact hPg, hqd⟩
  have hm := hg v ⟨hvB, hPa, hPg, by rw [dist_self]; exact hε⟩
  rw [L_eq hpB, pa, pb, max_eq_right (by linarith)] at hp
  rw [L_eq hqB, qa, qb, max_eq_left (by linarith)] at hq
  rw [L_eq hvB, ha, hb, max_self] at hm
  have hmid := affine_mid g p q v fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl
    · rw [pa, qa, ha]; ring
    · rw [pb, qb, hb]; ring
    · rw [pg, qg]; ring
    · rw [ph, qh]; ring
  linarith

/-- Q8, `U`: at a slice point with `ω = 0`, `U` is affine on no neighbourhood within the slice. -/
theorem U_not_affine_near_proved (v : Coord → ℝ) (hv : v ∈ center.B)
    (hPa : v CenterSwitch.canonical.pa + v CenterSwitch.canonical.pb = 1 / 2)
    (hPg : v CenterSwitch.canonical.pg + v CenterSwitch.canonical.ph = 3 / 2)
    (hω : v CenterSwitch.canonical.pg = v CenterSwitch.canonical.ph) {ε : ℝ} (hε : 0 < ε) :
    ¬ AffineOn center.U {u | u ∈ center.B ∧ u CenterSwitch.canonical.pa + u CenterSwitch.canonical.pb = 1 / 2 ∧
      u CenterSwitch.canonical.pg + u CenterSwitch.canonical.ph = 3 / 2 ∧ dist u v < ε} := by
  rintro ⟨g, hg⟩
  have hvB := hv
  rw [mem_B_iff] at hv
  obtain ⟨hva, hvb, -, -, -⟩ := hv
  have hgv : v CenterSwitch.canonical.pg = 3 / 4 := by linarith
  have hhv : v CenterSwitch.canonical.ph = 3 / 4 := by linarith
  have ha1 : v CenterSwitch.canonical.pa ≤ 1 / 2 := by linarith
  have hb1 : v CenterSwitch.canonical.pb ≤ 1 / 2 := by linarith
  obtain ⟨t, ht0, ht1, htε⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧ t ≤ ε :=
    ⟨min (1 / 2) ε, lt_min (by norm_num) hε, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨pa, pb, pg, ph⟩ := coords_symm
    ![v CenterSwitch.canonical.pa, v CenterSwitch.canonical.pb, 3 / 4 - t / 2, 3 / 4 + t / 2]
  obtain ⟨qa, qb, qg, qh⟩ := coords_symm
    ![v CenterSwitch.canonical.pa, v CenterSwitch.canonical.pb, 3 / 4 + t / 2, 3 / 4 - t / 2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at pa pb pg ph qa qb qg qh
  set p := canonicalEquiv.symm
    ![v CenterSwitch.canonical.pa, v CenterSwitch.canonical.pb, 3 / 4 - t / 2, 3 / 4 + t / 2]
  set q := canonicalEquiv.symm
    ![v CenterSwitch.canonical.pa, v CenterSwitch.canonical.pb, 3 / 4 + t / 2, 3 / 4 - t / 2]
  have hpB : p ∈ center.B := by
    rw [mem_B_iff, pa, pb, pg, ph, max_le_iff, le_min_iff, le_min_iff]
    exact ⟨hva, hvb, ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by linarith, by linarith⟩
  have hqB : q ∈ center.B := by
    rw [mem_B_iff, qa, qb, qg, qh, max_le_iff, le_min_iff, le_min_iff]
    exact ⟨hva, hvb, ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by linarith, by linarith⟩
  have hpd : dist p v < ε := dist_lt_of_coords ht0 htε fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl
    · rw [pa, sub_self, abs_zero]; linarith
    · rw [pb, sub_self, abs_zero]; linarith
    · rw [pg, hgv, abs_le]; constructor <;> linarith
    · rw [ph, hhv, abs_le]; constructor <;> linarith
  have hqd : dist q v < ε := dist_lt_of_coords ht0 htε fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl
    · rw [qa, sub_self, abs_zero]; linarith
    · rw [qb, sub_self, abs_zero]; linarith
    · rw [qg, hgv, abs_le]; constructor <;> linarith
    · rw [qh, hhv, abs_le]; constructor <;> linarith
  have hp := hg p ⟨hpB, by rw [pa, pb]; exact hPa, by rw [pg, ph]; ring, hpd⟩
  have hq := hg q ⟨hqB, by rw [qa, qb]; exact hPa, by rw [qg, qh]; ring, hqd⟩
  have hm := hg v ⟨hvB, hPa, hPg, by rw [dist_self]; exact hε⟩
  rw [U_eq hpB, pg, ph, min_eq_left (by linarith)] at hp
  rw [U_eq hqB, qg, qh, min_eq_right (by linarith)] at hq
  rw [U_eq hvB, hgv, hhv, min_self] at hm
  have hmid := affine_mid g p q v fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl
    · rw [pa, qa]; ring
    · rw [pb, qb]; ring
    · rw [pg, qg, hgv]; ring
    · rw [ph, qh, hhv]; ring
  linarith

end Q8

section Q7

open Set Filter
open scoped Topology

/-- Q7: two cells `A, B` of the dimension of `E` meeting in a common face `A ∩ B` of dimension `dim E - 1` lie on
opposite sides of the hyperplane `aff(A ∩ B)` of `aff(E)`, and near each point of `relint(A ∩ B)`, within `aff(E)`,
each coincides with its closed half-space. (Steps copied from `interior_shared_facet`.) -/
theorem opposite_sides_proved {ι : Type*} [Fintype ι] {E A B : Set (ι → ℝ)}
    (hA : IsPolytope A) (hB : IsPolytope B) (hAE : A ⊆ E) (hBE : B ⊆ E)
    (hAdim : adim A = adim E) (hBdim : adim B = adim E)
    (hfA : IsFace A (A ∩ B)) (hdim : adim (A ∩ B) + 1 = adim E) :
    ∃ h : (ι → ℝ) →ᵃ[ℝ] ℝ, (∀ x ∈ affineSpan ℝ E, h x = 0 ↔ x ∈ affineSpan ℝ (A ∩ B)) ∧
      (∀ x ∈ A, h x ≤ 0) ∧ (∀ x ∈ B, 0 ≤ h x) ∧ (∃ x ∈ A, h x < 0) ∧ (∃ x ∈ B, 0 < h x) ∧
      ∀ x₀ ∈ intrinsicInterior ℝ (A ∩ B), ∀ᶠ y in 𝓝 x₀, y ∈ affineSpan ℝ E →
        ((y ∈ A ↔ h y ≤ 0) ∧ (y ∈ B ↔ 0 ≤ h y)) := by
  have convexA : Convex ℝ A := by
    obtain ⟨vertices, rfl⟩ := hA
    exact convex_convexHull ℝ _
  have convexB : Convex ℝ B := by
    obtain ⟨vertices, rfl⟩ := hB
    exact convex_convexHull ℝ _
  obtain ⟨point, interior⟩ := hfA.1.intrinsicInterior (convexA.inter convexB)
  have point_mem : point ∈ A ∩ B := intrinsicInterior_subset interior
  have spanE : ∀ other ∈ E, other ∈ affineSpan ℝ E := fun _ member => subset_affineSpan ℝ E member
  -- the exposing functional of the face `A ∩ B` of `A`, with level `functional point`
  obtain ⟨functional, exposed⟩ := hfA.2 ⟨point, point_mem⟩
  have top : ∀ other ∈ A, functional other ≤ functional point := by
    have member := point_mem
    rw [exposed] at member
    exact member.2
  have level : ∀ other ∈ A ∩ B, functional other = functional point := by
    intro other member
    have maximal := member
    rw [exposed] at maximal
    exact le_antisymm (top other member.1) (maximal.2 point point_mem.1)
  have small_of_subset : ∀ body : Set (ι → ℝ), body ⊆ affineSpan ℝ (A ∩ B) → adim body ≤ adim (A ∩ B) := by
    intro body subset
    have directions := AffineSubspace.direction_le (affineSpan_le.mpr subset)
    rw [direction_affineSpan, direction_affineSpan] at directions
    exact Submodule.finrank_mono directions
  -- `A` has a point strictly below the level
  obtain ⟨low, low_mem, low_lt⟩ : ∃ low ∈ A, functional low < functional point := by
    by_contra none
    push Not at none
    have inside : A ⊆ affineSpan ℝ (A ∩ B) := by
      intro other member
      have in_face : other ∈ A ∩ B := by
        rw [exposed]
        exact ⟨member, fun third third_mem =>
          (top third third_mem).trans (none other member)⟩
      exact subset_affineSpan ℝ _ in_face
    have := small_of_subset A inside
    omega
  -- inside `aff E`, the level set of `functional` through `point` is exactly `aff (A ∩ B)`
  have span_le : vectorSpan ℝ (A ∩ B) ≤
      vectorSpan ℝ E ⊓ LinearMap.ker (functional : (ι → ℝ) →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨first, first_mem, second, second_mem, rfl⟩
    refine ⟨vsub_mem_vectorSpan ℝ (hAE first_mem.1) (hAE second_mem.1), ?_⟩
    simp [LinearMap.mem_ker, level first first_mem, level second second_mem]
  have proper : vectorSpan ℝ E ⊓ LinearMap.ker (functional : (ι → ℝ) →ₗ[ℝ] ℝ) < vectorSpan ℝ E := by
    refine lt_of_le_of_ne inf_le_left fun same => ?_
    have step : low -ᵥ point ∈ vectorSpan ℝ E := vsub_mem_vectorSpan ℝ (hAE low_mem) (hAE point_mem.1)
    rw [← same] at step
    have flat := step.2
    simp [LinearMap.mem_ker] at flat
    linarith
  have span_eq := Submodule.eq_of_le_of_finrank_eq span_le
    (le_antisymm (Submodule.finrank_mono span_le)
      (by have := Submodule.finrank_lt_finrank_of_lt proper; unfold adim at hdim; omega))
  have slice : ∀ other ∈ affineSpan ℝ E, functional other = functional point →
      other ∈ affineSpan ℝ (A ∩ B) := by
    intro other span same
    have step : other -ᵥ point ∈ vectorSpan ℝ (A ∩ B) := by
      rw [span_eq]
      refine ⟨?_, ?_⟩
      · rw [← direction_affineSpan]
        exact AffineSubspace.vsub_mem_direction span (spanE point (hAE point_mem.1))
      · simp [LinearMap.mem_ker, same]
    have moved := AffineSubspace.vadd_mem_of_mem_direction (by rwa [direction_affineSpan])
      (subset_affineSpan ℝ (A ∩ B) point_mem)
    simpa using moved
  -- the level is constant on `aff (A ∩ B)`
  have level_span : ∀ x ∈ affineSpan ℝ (A ∩ B), functional x = functional point := by
    intro x hx
    have step : x -ᵥ point ∈ vectorSpan ℝ (A ∩ B) := by
      rw [← direction_affineSpan]
      exact AffineSubspace.vsub_mem_direction hx (subset_affineSpan ℝ _ point_mem)
    have hker := (span_le step).2
    simp [LinearMap.mem_ker] at hker
    linarith
  have slice_near : ∀ x₀ ∈ intrinsicInterior ℝ (A ∩ B), ∀ᶠ other in 𝓝 x₀, other ∈ affineSpan ℝ E →
      functional other = functional point → other ∈ A ∩ B := fun x₀ hx₀ =>
    (eventually_mem_of_mem_intrinsicInterior hx₀).mono fun other near span same => near (slice other span same)
  -- `B` has no point below the level (else `A` and `B` would share points below it near `point`)
  have below_none : ∀ y ∈ B, functional point ≤ functional y := by
    by_contra hbad
    push Not at hbad
    obtain ⟨lowB, lowB_mem, lowB_lt⟩ := hbad
    have nearB := eventually_mem_of_slice convexB (affineSpan ℝ E) functional lowB_mem
      (spanE lowB (hBE lowB_mem)) lowB_lt
      ((slice_near point interior).mono fun _ near span same => (near span same).2)
    have path : Tendsto (fun scalar : ℝ => AffineMap.lineMap point low scalar) (𝓝 0) (𝓝 point) := by
      have continuous : Continuous (fun scalar : ℝ => AffineMap.lineMap point low scalar) := by fun_prop
      simpa using continuous.tendsto 0
    obtain ⟨scalar, inB, scalar_pos, scalar_lt⟩ :=
      (((path.eventually nearB).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi 0))).and
        (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
    have value : functional (AffineMap.lineMap point low scalar) =
        functional point + scalar * (functional low - functional point) := by
      simp [AffineMap.lineMap_apply_module]
      ring
    have strict : functional (AffineMap.lineMap point low scalar) < functional point := by
      rw [value]
      nlinarith
    have memA := convexA.lineMap_mem point_mem.1 low_mem ⟨scalar_pos.le, scalar_lt.le⟩
    have memB := inB (AffineMap.lineMap_mem scalar (spanE point (hAE point_mem.1)) (spanE low (hAE low_mem)))
      strict.le
    have := level _ ⟨memA, memB⟩
    linarith
  -- `B` has a point above the level (else `B ⊆ aff (A ∩ B)` would be too small)
  obtain ⟨high, high_mem, high_gt⟩ : ∃ high ∈ B, functional point < functional high := by
    by_contra none
    push Not at none
    have inside : B ⊆ affineSpan ℝ (A ∩ B) := fun other member =>
      slice other (spanE other (hBE member)) (le_antisymm (none other member) (below_none other member))
    have := small_of_subset B inside
    omega
  -- `h = functional - functional point`
  obtain ⟨h, hh⟩ : ∃ h : (ι → ℝ) →ᵃ[ℝ] ℝ, ∀ x, h x = functional x - functional point :=
    ⟨(functional : (ι → ℝ) →ₗ[ℝ] ℝ).toAffineMap - AffineMap.const ℝ (ι → ℝ) (functional point), fun _ => rfl⟩
  refine ⟨h, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, ⟨low, low_mem, ?_⟩, ⟨high, high_mem, ?_⟩, ?_⟩
  · rw [hh, sub_eq_zero]
    exact ⟨slice x hx, level_span x⟩
  · rw [hh]
    linarith [top x hx]
  · rw [hh]
    linarith [below_none x hx]
  · rw [hh]
    linarith
  · rw [hh]
    linarith
  · intro x₀ hx₀
    have hx₀c : functional x₀ = functional point := level x₀ (intrinsicInterior_subset hx₀)
    have lowA₀ := eventually_mem_of_slice convexA (affineSpan ℝ E) functional low_mem (spanE low (hAE low_mem))
      (by rw [hx₀c]; exact low_lt)
      ((slice_near x₀ hx₀).mono fun _ near span same => (near span (same.trans hx₀c)).1)
    have highB₀ := eventually_mem_of_slice convexB (affineSpan ℝ E) (-functional) high_mem
      (spanE high (hBE high_mem))
      (by show -(functional high) < -(functional x₀); linarith)
      ((slice_near x₀ hx₀).mono fun other near span same =>
        (near span (by have h2 : -(functional other) = -(functional x₀) := same; linarith)).2)
    filter_upwards [lowA₀, highB₀] with y inA inB span
    rw [hh]
    refine ⟨⟨fun hy => by linarith [top y hy], fun hy => inA span (by linarith)⟩,
      ⟨fun hy => by linarith [below_none y hy], fun hy => inB span ?_⟩⟩
    show -(functional y) ≤ -(functional x₀)
    linarith

end Q7

end HibiLi.Proofs.Cov200
