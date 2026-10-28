/- Empty-base case tested separately; intrinsic AffineMap requires
Nonempty affineSpan. Singleton base and apex faces
are included below; IsFace excludes the empty face throughout the project. -/
import HibiLi.Proofs.PyramidRows

namespace HibiLi.Proofs

/-- l.262-263: an affine function on aff(Q) extends with any prescribed value at o. -/
theorem sec2_pyramid_extend {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ))
    [Nonempty (affineSpan ℝ Q)] (o : ι → ℝ) (ho : o ∉ affineSpan ℝ Q)
    (f : affineSpan ℝ Q →ᵃ[ℝ] ℝ) (c : ℝ) :
    ∃ g : (ι → ℝ) →ᵃ[ℝ] ℝ, (∀ y : affineSpan ℝ Q, g y = f y) ∧ g o = c := by
  classical
  let p : affineSpan ℝ Q := Classical.choice inferInstance
  have outside : o - (p : ι → ℝ) ∉ (affineSpan ℝ Q).direction := by
    intro h
    exact ho ((AffineSubspace.vsub_right_mem_direction_iff_mem p.2 o).mp h)
  obtain ⟨L, hL, hLo⟩ := f.linear.exists_extend_of_notMem outside (c - f p)
  let g : (ι → ℝ) →ᵃ[ℝ] ℝ := AffineMap.mk'
    (fun y => L (y - p) + f p) L (p : ι → ℝ) (by intro y; simp)
  refine ⟨g, ?_, ?_⟩
  · intro y
    have hy := congrArg (fun M : (affineSpan ℝ Q).direction →ₗ[ℝ] ℝ => M (y -ᵥ p)) hL
    change L ((y : ι → ℝ) - p) = f.linear (y -ᵥ p) at hy
    change L ((y : ι → ℝ) - p) + f p = f y
    rw [hy, f.linear_apply_vsub]
    exact sub_add_cancel _ _
  · change L (o - p) + f p = c
    rw [hLo, sub_add_cancel]

/-- l.263-265: each cut is valid on the entire pyramid, with the stated tight set. -/
theorem sec2_pyramid_cut_valid {ι : Type*} (Q : Set (ι → ℝ)) (V : Finset (ι → ℝ))
    (hQ : Q = convexHull ℝ ↑V) (o : ι → ℝ) (ho : o ∉ affineSpan ℝ Q)
    (G : Set (ι → ℝ)) (g : (ι → ℝ) →ᵃ[ℝ] ℝ) (hg : ∀ x ∈ Q, 0 ≤ g x)
    (hG : {x ∈ Q | g x = 0} = G) (hGface : IsFace Q G) :
    (g o = 1 → (∀ x ∈ convexHull ℝ (insert o Q), 0 ≤ g x) ∧
      {x ∈ convexHull ℝ (insert o Q) | g x = 0} = G) ∧
    (g o = 0 → (∀ x ∈ convexHull ℝ (insert o Q), 0 ≤ g x) ∧
      {x ∈ convexHull ℝ (insert o Q) | g x = 0} = convexHull ℝ (insert o G)) := by
  have valid (hgo : 0 ≤ g o) : ∀ x ∈ convexHull ℝ (insert o Q), 0 ≤ g x := by
    apply convexHull_min
    · rintro x (rfl | hx)
      · exact hgo
      · exact hg x hx
    · exact (convex_Ici (0 : ℝ)).affine_preimage g
  have old := sec2_pyramid_cut Q V hQ o ho G g hg hG hGface
  exact ⟨fun h => ⟨valid (by rw [h]; norm_num), old.1 h⟩,
    fun h => ⟨valid (by rw [h]), old.2 h⟩⟩

/-- l.266-268: F intersect Q is a pyramid face with precisely the non-apex vertices;
the membership of the apex and emptiness of the intersection determine each case. -/
theorem sec2_pyramid_face_cases {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ))
    (V : Finset (ι → ℝ)) (hQ : Q = convexHull ℝ ↑V) (o : ι → ℝ)
    (ho : o ∉ affineSpan ℝ Q) (F : Set (ι → ℝ))
    (hF : IsFace (convexHull ℝ (insert o Q)) F) :
    ((F ∩ Q).Nonempty → IsFace (convexHull ℝ (insert o Q)) (F ∩ Q) ∧
      ∀ v, IsFace (F ∩ Q) {v} ↔ IsFace F {v} ∧ v ≠ o) ∧
    (o ∉ F → F = F ∩ Q) ∧ (F ∩ Q = ∅ → F = {o}) ∧
    (o ∈ F → (F ∩ Q).Nonempty → F = convexHull ℝ (insert o (F ∩ Q))) := by
  have hQp : IsPolytope Q := ⟨V, hQ⟩
  have hoQ : o ∉ Q := fun h => ho (subset_affineSpan ℝ Q h)
  have classification := (sec2_pyramid_faces_proved Q hQp o ho F).mp hF
  have hsubQ : Q ⊆ convexHull ℝ (insert o Q) :=
    fun _ h => subset_convexHull ℝ _ (Set.mem_insert_of_mem _ h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hne
    have hGQ := (sec2_pyramid_face_parts Q V hQ o ho F hF).2 hne
    have hbase := (pyramid_base_and_apex_faces hQp (hne.mono Set.inter_subset_right) o ho).1
    have hGP := IsFace.trans (hQp.convexHull_insert o) hbase hGQ
    have hGF := hGP.mono hF.subset Set.inter_subset_left
    refine ⟨hGP, fun v => ⟨?_, ?_⟩⟩
    · intro hv
      exact ⟨IsFace.trans ((hQp.convexHull_insert o).face hF) hGF hv,
        fun h => hoQ (h ▸ (hv.subset (Set.mem_singleton v)).2)⟩
    · rintro ⟨hv, hvo⟩
      have hvQ : IsFace Q {v} := by
        rcases (sec2_pyramid_face_parts Q V hQ o ho F hF).1 v hv with h | h
        · exact (hvo h).elim
        · exact h
      exact hv.mono Set.inter_subset_left
        (fun y hy => ⟨hv.subset hy, hvQ.subset hy⟩)
  · intro hno
    have subset : F ⊆ Q := by
      rcases classification with h | rfl | ⟨G, _, rfl⟩
      · exact h.subset
      · exact (hno (Set.mem_singleton o)).elim
      · exact (hno (subset_convexHull ℝ _ (Set.mem_insert o G))).elim
    exact (Set.inter_eq_left.mpr subset).symm
  · intro hempty
    rcases classification with h | h | ⟨G, hG, rfl⟩
    · have same := Set.inter_eq_left.mpr h.subset
      exact (h.1.ne_empty (same.symm.trans hempty)).elim
    · exact h
    · have same := pyramid_join_inter_base hQp hG o ho
      exact (hG.1.ne_empty (same.symm.trans hempty)).elim
  · intro hoF hne
    rcases classification with h | rfl | ⟨G, hG, rfl⟩
    · exact (hoQ (h.subset hoF)).elim
    · obtain ⟨y, hy, hyQ⟩ := hne
      exact (hoQ ((Set.mem_singleton_iff.mp hy) ▸ hyQ)).elim
    · rw [pyramid_join_inter_base hQp hG o ho]

end HibiLi.Proofs

#print axioms HibiLi.Proofs.sec2_pyramid_extend
#print axioms HibiLi.Proofs.sec2_pyramid_cut_valid
#print axioms HibiLi.Proofs.sec2_pyramid_face_cases
