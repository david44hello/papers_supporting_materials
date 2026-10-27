/-
HibiLi — rational vertices of all nine center-switch regions.
-/
import HibiLi.Example21.CenterRegions
import HibiLi.Example21.RationalFaces
import HibiLi.Example21.ZeroOne

namespace HibiLi.Example21.CenterRegions

open Finset

def points : Fin 8 → Fin 4 → ℚ :=
  ![![0,0,0,0], ![0,0,1,0], ![0,0,0,1], ![0,0,1,1],
    ![1,0,1,1], ![0,1,1,1], ![1,1,1,1], ![1,0,0,0]]

def normals (lower upper : Option Bool) : Fin 10 → Fin 4 → ℚ :=
  ![![-1,0,0,0], ![0,-1,0,0], ![1,0,-1,0], ![1,0,0,-1],
    ![0,1,-1,0], ![0,1,0,-1], ![0,0,1,0], ![0,0,0,1],
    (match lower with | none => ![0,0,0,0] | some false => ![1,-1,0,0] | some true => ![-1,1,0,0]),
    (match upper with | none => ![0,0,0,0] | some false => ![0,0,1,-1] | some true => ![0,0,-1,1])]

def bounds : Fin 10 → ℚ := ![0,0,0,0,0,0,1,1,0,0]

def vertices (lower upper : Option Bool) : Finset (Fin 8) :=
  univ.filter fun idx => ∀ index, rationalScore points (normals lower upper index) idx ≤ bounds index

theorem body_halfspaces (lower upper : Option Bool) : body lower upper =
    {point | ∀ index, normalFunctional (normals lower upper index) point ≤ (bounds index : ℝ)} := by
  ext point
  fin_cases lower <;> fin_cases upper <;>
    simp [body, normals, bounds, normalFunctional, Fin.forall_fin_succ,
      Fin.sum_univ_succ, smul_eq_mul]

theorem body_convex (lower upper : Option Bool) : Convex ℝ (body lower upper) := by
  rw [body_halfspaces]
  have eq : {point : Fin 4 → ℝ | ∀ index, normalFunctional (normals lower upper index) point ≤
      (bounds index : ℝ)} = ⋂ index, {point | normalFunctional (normals lower upper index) point ≤
        (bounds index : ℝ)} := by ext point; simp
  rw [eq]
  exact convex_iInter fun index => (convex_Iic _).linear_preimage (normalFunctional _).toLinearMap

theorem body_coordinate_bounds (lower upper : Option Bool) {v : Fin 4 → ℝ} (hv : v ∈ body lower upper) :
    ∀ idx, 0 ≤ v idx ∧ v idx ≤ 1 := by
  intro idx
  obtain ⟨ha, hb, hag, hah, hbg, hbh, hg, hh, _⟩ := hv
  fin_cases idx
  · exact ⟨ha, hag.trans hg⟩
  · exact ⟨hb, hbg.trans hg⟩
  · exact ⟨ha.trans hag, hg⟩
  · exact ⟨ha.trans hah, hh⟩

private theorem indicator_le {v : Fin 4 → ℝ} {time : ℝ} (positive : 0 < time) {left right : Fin 4}
    (ordered : v left ≤ v right) :
    intervalVector (fun _ => 0) v time left ≤ intervalVector (fun _ => 0) v time right := by
  classical
  by_cases hp : time ≤ v left
  · have hq := hp.trans ordered
    simp [intervalVector, Set.mem_Ioc, positive, hp, hq]
  · simp [intervalVector, Set.mem_Ioc, hp]
    by_cases hq : time ∈ Set.Ioc 0 (v right) <;> simp [hq]

theorem body_eq_zeroOne_hull (lower upper : Option Bool) :
    body lower upper = convexHull ℝ (body lower upper ∩ zeroOneVectors (Fin 4)) := by
  classical
  apply Set.Subset.antisymm
  · intro v hv
    have hb := body_coordinate_bounds lower upper hv
    have hh := intervalVector_convexHull (fun _ : Fin 4 => 0) v (fun _ => le_rfl)
      (fun idx => (hb idx).1) (fun idx => (hb idx).2)
      ((zeroOneVectors_finite (Fin 4)).inter_of_right (body lower upper))
    simp only [sub_zero] at hh
    apply hh
    intro time htime
    have hbits := intervalVector_mem_zeroOne (fun _ : Fin 4 => 0) v time
    have hbound : ∀ idx, 0 ≤ intervalVector (fun _ : Fin 4 => 0) v time idx ∧
        intervalVector (fun _ : Fin 4 => 0) v time idx ≤ 1 := by
      intro idx
      rcases hbits idx with heq | heq <;> rw [heq] <;> norm_num
    refine ⟨⟨(hbound 0).1, (hbound 1).1, indicator_le htime.1 hv.2.2.1,
      indicator_le htime.1 hv.2.2.2.1, indicator_le htime.1 hv.2.2.2.2.1,
      indicator_le htime.1 hv.2.2.2.2.2.1, (hbound 2).2, (hbound 3).2, ?_, ?_⟩, hbits⟩
    · have cut := hv.2.2.2.2.2.2.2.2.1
      fin_cases lower
      · trivial
      · exact indicator_le htime.1 cut
      · exact indicator_le htime.1 cut
    · have cut := hv.2.2.2.2.2.2.2.2.2
      fin_cases upper
      · trivial
      · exact indicator_le htime.1 cut
      · exact indicator_le htime.1 cut
  · exact convexHull_min Set.inter_subset_left (body_convex lower upper)

theorem realPoint_mem_body_iff (lower upper : Option Bool) (idx : Fin 8) :
    realPoints points idx ∈ body lower upper ↔ idx ∈ vertices lower upper := by
  rw [body_halfspaces]
  simp only [Set.mem_ofPred_eq, vertices, mem_filter, mem_univ, true_and]
  apply forall_congr'
  intro index
  rw [normalFunctional_apply]
  exact Rat.cast_le

theorem points_zeroOne (idx : Fin 8) : realPoints points idx ∈ zeroOneVectors (Fin 4) := by
  intro row
  fin_cases idx <;> fin_cases row <;> norm_num [realPoints, points]

theorem body_zeroOne_eq_vertices (lower upper : Option Bool) :
    body lower upper ∩ zeroOneVectors (Fin 4) =
      realPoints points '' (vertices lower upper : Set (Fin 8)) := by
  ext v
  constructor
  · rintro ⟨hv, hz⟩
    have vertex : ∃ idx : Fin 8, realPoints points idx = v := by
      rcases hz 0 with h0 | h0 <;> rcases hz 1 with h1 | h1 <;>
        rcases hz 2 with h2 | h2 <;> rcases hz 3 with h3 | h3 <;>
        simp_all [body, Fin.exists_fin_succ, realPoints, points, funext_iff, Fin.forall_fin_succ] <;>
        norm_num at hv
    obtain ⟨idx, rfl⟩ := vertex
    exact ⟨idx, (realPoint_mem_body_iff lower upper idx).mp hv, rfl⟩
  · rintro ⟨idx, hi, rfl⟩
    exact ⟨(realPoint_mem_body_iff lower upper idx).mpr hi, points_zeroOne idx⟩

theorem body_eq_hull (lower upper : Option Bool) :
    body lower upper = supportHull points (vertices lower upper) := by
  rw [body_eq_zeroOne_hull lower upper, body_zeroOne_eq_vertices]
  rfl

theorem faces_eq_supports (lower upper : Option Bool) :
    {F | IsFace (body lower upper) F} = supportHull points ''
      (faceSupports points (vertices lower upper) (normals lower upper) bounds : Set (Finset (Fin 8))) := by
  rw [body_eq_hull]
  exact allFaces_eq_supports points _ _ _ ((body_eq_hull lower upper).symm.trans (body_halfspaces lower upper))

end HibiLi.Example21.CenterRegions
