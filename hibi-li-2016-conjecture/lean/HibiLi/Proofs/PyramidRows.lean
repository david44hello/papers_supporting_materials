/-
HibiLi/Proofs/PyramidRows.lean — the pyramid facts of Section 2 (l. 257-267): review 006 coverage item B10, rows c, d.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

The pyramid is over a polytope `Q = conv V` with apex `o ∉ aff Q` (l. 257-258). Every point of `conv(Q ∪ {o})` is
`a • o + b • q` with `q ∈ Q`, `a, b ≥ 0`, `a + b = 1` (`pyr_seg`); an affine `g` is `a g(o) + b g(q)` there. Row d uses
the face classification `sec2_pyramid_faces_proved` (twice) and the exposing functional of `F` for `F ∩ Q`.
-/
import HibiLi.Proofs.PyramidFacesIff
import HibiLi.Polytope.Transitivity
import HibiLi.Polytope.FiniteFaces

namespace HibiLi.Proofs

variable {ι : Type*}

/-- A point of `conv(Q ∪ {o})`, for `Q` convex and nonempty, lies on a segment from `o` to a point of `Q`. -/
theorem pyr_seg {Q : Set (ι → ℝ)} (hQc : Convex ℝ Q) (hQne : Q.Nonempty) (o : ι → ℝ) {x : ι → ℝ}
    (hx : x ∈ convexHull ℝ (insert o Q)) :
    ∃ q ∈ Q, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • o + b • q = x := by
  rw [convexHull_insert hQne, hQc.convexHull_eq, mem_convexJoin] at hx
  obtain ⟨o', ho', q, hq, a, b, ha, hb, hab, rfl⟩ := hx
  rw [Set.mem_singleton_iff.1 ho']
  exact ⟨q, hq, a, b, ha, hb, hab, rfl⟩

/-- An affine function vanishing on `T` vanishes on `conv T`. -/
theorem affine_zero_hull (g : (ι → ℝ) →ᵃ[ℝ] ℝ) {T : Set (ι → ℝ)} (hT : ∀ x ∈ T, g x = 0) :
    ∀ x ∈ convexHull ℝ T, g x = 0 :=
  fun _ hx => convexHull_min hT ((convex_singleton (0 : ℝ)).affine_preimage g) hx

/-- B10 c, l. 262-265: if the affine `g` is `≥ 0` on `Q` and vanishes exactly on the face `G`, then `g ≥ 0` cuts out
`G` from the pyramid when `g(o) = 1`, and `conv(G ∪ {o})` when `g(o) = 0`. -/
theorem sec2_pyramid_cut (Q : Set (ι → ℝ)) (V : Finset (ι → ℝ)) (hQ : Q = convexHull ℝ ↑V) (o : ι → ℝ)
    (_ho : o ∉ affineSpan ℝ Q) (G : Set (ι → ℝ)) (g : (ι → ℝ) →ᵃ[ℝ] ℝ) (hg : ∀ x ∈ Q, 0 ≤ g x)
    (hG : {x ∈ Q | g x = 0} = G) (hGface : IsFace Q G) :
    (g o = 1 → {x ∈ convexHull ℝ (insert o Q) | g x = 0} = G) ∧
      (g o = 0 → {x ∈ convexHull ℝ (insert o Q) | g x = 0} = convexHull ℝ (insert o G)) := by
  have hQc : Convex ℝ Q := hQ ▸ convex_convexHull ℝ _
  have hGQ : G ⊆ Q := fun x hx => by
    rw [← hG] at hx
    exact hx.1
  have hQne : Q.Nonempty := hGface.1.mono hGQ
  refine ⟨fun h1 => ?_, fun h0 => ?_⟩
  · ext x
    constructor
    · rintro ⟨hx, hgx⟩
      obtain ⟨q, hq, a, b, ha, hb, hab, rfl⟩ := pyr_seg hQc hQne o hx
      rw [Convex.combo_affine_apply hab, h1, smul_eq_mul, smul_eq_mul] at hgx
      have hbg := mul_nonneg hb (hg q hq)
      have ha0 : a = 0 := by linarith
      have hb1 : b = 1 := by linarith
      subst ha0 hb1
      have hgq : g q = 0 := by linarith
      rw [← hG, zero_smul, one_smul, zero_add]
      exact ⟨hq, hgq⟩
    · intro hx
      rw [← hG] at hx
      exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx.1), hx.2⟩
  · ext x
    constructor
    · rintro ⟨hx, hgx⟩
      obtain ⟨q, hq, a, b, ha, hb, hab, rfl⟩ := pyr_seg hQc hQne o hx
      rw [Convex.combo_affine_apply hab, h0, smul_eq_mul, smul_eq_mul, mul_zero, zero_add] at hgx
      rcases mul_eq_zero.1 hgx with hb0 | hgq
      · subst hb0
        have ha1 : a = 1 := by linarith
        subst ha1
        rw [one_smul, zero_smul, add_zero]
        exact subset_convexHull ℝ _ (Set.mem_insert _ _)
      · have hqG : q ∈ G := by
          rw [← hG]
          exact ⟨hq, hgq⟩
        exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ (Set.mem_insert _ _))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hqG)) ha hb hab
    · intro hx
      refine ⟨convexHull_mono (Set.insert_subset_insert hGQ) hx, affine_zero_hull g ?_ x hx⟩
      rintro y (rfl | hy)
      · exact h0
      · rw [← hG] at hy
        exact hy.2

/-- B10 c (last clause), l. 265: for `g ≡ 1` on `Q` and `g(o) = 0`, the inequality `g ≥ 0` cuts out the apex. -/
theorem sec2_pyramid_apex_cut (Q : Set (ι → ℝ)) (V : Finset (ι → ℝ)) (hQ : Q = convexHull ℝ ↑V) (o : ι → ℝ)
    (_ho : o ∉ affineSpan ℝ Q) (g : (ι → ℝ) →ᵃ[ℝ] ℝ) (hg1 : ∀ x ∈ Q, g x = 1) (hgo : g o = 0) :
    {x ∈ convexHull ℝ (insert o Q) | g x = 0} = {o} := by
  have hQc : Convex ℝ Q := hQ ▸ convex_convexHull ℝ _
  ext x
  constructor
  · rintro ⟨hx, hgx⟩
    rcases Q.eq_empty_or_nonempty with hQe | hQne
    · rw [hQe, insert_empty_eq, convexHull_singleton] at hx
      exact hx
    · obtain ⟨q, hq, a, b, ha, hb, hab, rfl⟩ := pyr_seg hQc hQne o hx
      rw [Convex.combo_affine_apply hab, hgo, hg1 q hq, smul_eq_mul, smul_eq_mul, mul_zero, zero_add,
        mul_one] at hgx
      subst hgx
      have ha1 : a = 1 := by linarith
      subst ha1
      rw [one_smul, zero_smul, add_zero]
      exact Set.mem_singleton _
  · intro hx
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨subset_convexHull ℝ _ (Set.mem_insert _ _), hgo⟩

/-- B10 d, l. 265-267: the vertices of a face `F` of the pyramid are among `o` and the vertices of `Q`, and `F ∩ Q`,
when nonempty, is a face of `Q`. -/
theorem sec2_pyramid_face_parts [Fintype ι] (Q : Set (ι → ℝ)) (V : Finset (ι → ℝ)) (hQ : Q = convexHull ℝ ↑V)
    (o : ι → ℝ) (ho : o ∉ affineSpan ℝ Q) (F : Set (ι → ℝ)) :
    IsFace (convexHull ℝ (insert o Q)) F →
      (∀ v, IsFace F {v} → v = o ∨ IsFace Q {v}) ∧ ((F ∩ Q).Nonempty → IsFace Q (F ∩ Q)) := by
  intro hF
  have hQp : IsPolytope Q := ⟨V, hQ⟩
  refine ⟨fun v hv => ?_, fun hne => ?_⟩
  · rcases (sec2_pyramid_faces_proved Q hQp o ho F).1 hF with hG | rfl | ⟨G, hG, rfl⟩
    · exact Or.inr (IsFace.trans hQp hG hv)
    · exact Or.inl (Set.singleton_eq_singleton_iff.1 ((isFace_singleton_iff o {v}).1 hv))
    · have hGp : IsPolytope G := hQp.face hG
      have hoG : o ∉ affineSpan ℝ G := fun h => ho (affineSpan_mono ℝ hG.subset h)
      rcases (sec2_pyramid_faces_proved G hGp o hoG {v}).1 hv with h | h | ⟨G', -, h⟩
      · exact Or.inr (IsFace.trans hQp hG h)
      · exact Or.inl (Set.singleton_eq_singleton_iff.1 h)
      · have hov : o ∈ ({v} : Set (ι → ℝ)) := by
          rw [h]
          exact subset_convexHull ℝ _ (Set.mem_insert o G')
        exact Or.inl (Set.mem_singleton_iff.1 hov).symm
  · obtain ⟨hFne, hexp⟩ := hF
    obtain ⟨l, hl⟩ := hexp hFne
    refine ⟨hne, fun _ => ⟨l, ?_⟩⟩
    have hQsub : Q ⊆ convexHull ℝ (insert o Q) := (Set.subset_insert o Q).trans (subset_convexHull ℝ _)
    obtain ⟨z, hzF, hzQ⟩ := hne
    rw [hl] at hzF
    ext x
    constructor
    · rintro ⟨hxF, hxQ⟩
      rw [hl] at hxF
      exact ⟨hxQ, fun y hy => hxF.2 y (hQsub hy)⟩
    · rintro ⟨hxQ, hmax⟩
      refine ⟨?_, hxQ⟩
      rw [hl]
      exact ⟨hQsub hxQ, fun y hy => (hzF.2 y hy).trans (hmax z hzQ)⟩

end HibiLi.Proofs
