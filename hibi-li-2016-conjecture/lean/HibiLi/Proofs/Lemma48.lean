/-
HibiLi/Proofs/Lemma48.lean — proof of paper Lemma 4.8: the simplex lower bound on face numbers, and cofaces of a face.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Polytope.Transitivity
import HibiLi.Cited.Others

namespace HibiLi.Proofs

open HibiLi

theorem adim_singleton {ι : Type*} (v : ι → ℝ) : adim ({v} : Set (ι → ℝ)) = 0 := by
  simp [adim, vectorSpan_singleton]

/-- Every nonempty face `G` of a polytope contains a vertex (a one-point face): a minimal face inside `G` is a point,
since a coordinate that differs on two of its points would expose a smaller face. -/
theorem exists_vertex_mem {ι : Type*} [Fintype ι] {Q G : Set (ι → ℝ)} (hQ : IsPolytope Q) (hG : IsFace Q G) :
    ∃ v ∈ G, IsFace Q {v} := by
  let below : Set (Set (ι → ℝ)) := {H | IsFace Q H ∧ H ⊆ G}
  obtain ⟨H, ⟨hH, hHG⟩, hmin⟩ :=
    (hQ.finite_faces.subset fun H (hH : H ∈ below) => hH.1).exists_minimal ⟨G, hG, subset_rfl⟩
  obtain ⟨v, hv⟩ := hH.1
  have hsingle : H = {v} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hv, fun w hw => ?_⟩
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    obtain ⟨S, hS⟩ := hQ.face hH
    have hcomp : IsCompact H := hS ▸ S.finite_toSet.isCompact_convexHull ℝ
    obtain ⟨x, hx, hxmax⟩ := hcomp.exists_isMaxOn ⟨v, hv⟩ (continuous_apply i).continuousOn
    let l : StrongDual ℝ (ι → ℝ) := ContinuousLinearMap.proj i
    have hface : IsFace H (l.toExposed H) :=
      ⟨⟨x, hx, fun y hy => hxmax hy⟩, ContinuousLinearMap.toExposed.isExposed⟩
    have hsub : H ⊆ l.toExposed H :=
      hmin ⟨IsFace.trans hQ hH hface, hface.subset.trans hHG⟩ hface.subset
    have hwv : w i ≤ v i := (hsub hv).2 w hw
    have hvw : v i ≤ w i := (hsub hw).2 v hv
    exact hi (le_antisymm hwv hvw)
  exact ⟨v, hHG hv, hsingle ▸ hH⟩

/-- Under a face figure of `E`, the faces of dimension `dim E + j + 1` containing `E` correspond to the `j`-faces of
the figure. -/
theorem ncard_cofaces_eq {ι : Type*} [Fintype ι] {m : ℕ} {B E : Set (ι → ℝ)} {Q : Set (Fin m → ℝ)}
    (φ : {G // IsFace B G ∧ E ⊂ G} ≃ {G' // IsFace Q G'})
    (hφ : ∀ G, adim G.1 = adim (φ G).1 + adim E + 1) (j : ℕ) :
    {G | IsFace B G ∧ E ⊆ G ∧ adim G = adim E + j + 1}.ncard = fNum Q j := by
  have hss : ∀ G, E ⊆ G → adim G = adim E + j + 1 → E ⊂ G := fun G hEG hdim =>
    hEG.ssubset_of_ne (by rintro rfl; omega)
  refine Set.ncard_congr (fun G hG => (φ ⟨G, hG.1, hss G hG.2.1 hG.2.2⟩).1) ?_ ?_ ?_
  · intro G hG
    have := hφ ⟨G, hG.1, hss G hG.2.1 hG.2.2⟩
    have hGdim := hG.2.2
    exact ⟨(φ _).2, by simp only at this; omega⟩
  · intro G G' hG hG' h
    simpa using φ.injective (Subtype.ext h)
  · intro G' hG'
    have := hφ (φ.symm ⟨G', hG'.1⟩)
    rw [Equiv.apply_symm_apply] at this
    refine ⟨(φ.symm ⟨G', hG'.1⟩).1, ⟨(φ.symm _).2.1, (φ.symm _).2.2.subset, ?_⟩, by simp⟩
    rw [this, hG'.2]
    omega

/-- The simplex bound: `Q` has at least `C(dim Q + 1, κ + 1)` faces of each dimension `κ ≤ dim Q`. -/
def SimplexBound {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) : Prop :=
  ∀ κ ≤ adim Q, (adim Q + 1).choose (κ + 1) ≤ fNum Q κ

/-- Induction step for the simplex bound (paper, Lemma 4.8, first part): a facet `F` and a vertex `v ∉ F` split the
`κ`-faces into those inside `F` and those containing `v` (the latter via the face figure of `v`). -/
theorem simplexBound_step {ι : Type*} [Fintype ι] (s : ℕ)
    (ihι : ∀ Q' : Set (ι → ℝ), IsPolytope Q' → Q'.Nonempty → adim Q' < s → SimplexBound Q')
    (ihfin : ∀ (m : ℕ) (Q' : Set (Fin m → ℝ)), IsPolytope Q' → Q'.Nonempty → adim Q' < s → SimplexBound Q')
    (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (hne : Q.Nonempty) (hs : adim Q = s) : SimplexBound Q := by
  intro κ hκ
  have hfin := hQ.faces_finite κ
  rcases s with _ | t
  · obtain rfl : κ = 0 := by omega
    rw [hs]
    exact (Set.ncard_pos hfin).mpr ⟨Q, IsFace.refl hne, hs⟩
  -- a maximal proper face `F`
  obtain ⟨v₀, -, hv₀⟩ := exists_vertex_mem hQ (IsFace.refl hne)
  let proper : Set (Set (ι → ℝ)) := {G | IsFace Q G ∧ G ≠ Q}
  obtain ⟨F, ⟨hF, hFQ⟩, hFmax⟩ := (hQ.finite_faces.subset fun G (hG : G ∈ proper) => hG.1).exists_maximal
    ⟨{v₀}, hv₀, fun h => by have := adim_singleton v₀; rw [h, hs] at this; omega⟩
  -- face figure at `F`: only `Q` lies strictly above `F`, so the figure has one face, is a point, and `dim F = t`
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
  have hQF0 := ihfin m QF hQF hQFne (by omega) 0 (Nat.zero_le _)
  rw [Nat.choose_one_right] at hQF0
  have hFt : adim F = t := by omega
  -- a vertex `v ∉ F`: minimize the functional exposing `F`
  obtain ⟨l, hl⟩ := hF.2 hF.1
  obtain ⟨S, hS⟩ := id hQ
  have hcomp : IsCompact Q := hS ▸ S.finite_toSet.isCompact_convexHull ℝ
  obtain ⟨x, hx, hxmin⟩ := hcomp.exists_isMinOn hne l.continuous.continuousOn
  have hGface : IsFace Q {y ∈ Q | ∀ z ∈ Q, l y ≤ l z} := by
    refine ⟨⟨x, hx, fun z hz => hxmin hz⟩, fun _ => ⟨-l, ?_⟩⟩
    ext y
    simp
  obtain ⟨v, ⟨-, hvmin⟩, hv⟩ := exists_vertex_mem hQ hGface
  have hvF : v ∉ F := by
    intro hvF
    rw [hl] at hvF
    apply hFQ
    refine Set.Subset.antisymm hF.subset fun y hy => ?_
    rw [hl]
    exact ⟨hy, fun z hz => (hvF.2 z hz).trans (hvmin y hy)⟩
  -- face figure at the vertex `v`: dimension `t`
  have hvQ : ({v} : Set (ι → ℝ)) ≠ Q := fun h => by have := adim_singleton v; rw [h, hs] at this; omega
  obtain ⟨m', Qv, hQv, hQve, hQvdim, ψ, hψ⟩ := Cited.ziegler_face_figure Q hQ {v} hv
  have hQvne : Qv.Nonempty := Set.nonempty_iff_ne_empty.mpr fun h => hvQ (hQve.mp h)
  have hQvt : adim Qv = t := by have := hQvdim hQvne; rw [adim_singleton, hs] at this; omega
  -- the `κ`-faces of `F` avoid `v`
  have hA : (t + 1).choose (κ + 1) ≤ (faces Q κ \ {G | v ∈ G}).ncard := by
    rcases Nat.lt_or_ge t κ with h | h
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      exact Nat.zero_le _
    · have := ihι F (hQ.face hF) hF.1 (by omega) κ (by omega)
      rw [hFt] at this
      refine this.trans (Set.ncard_le_ncard ?_ hfin.sdiff)
      intro G hG
      exact ⟨⟨IsFace.trans hQ hF hG.1, hG.2⟩, fun hvG => hvF (hG.1.subset hvG)⟩
  -- the `κ`-faces containing `v`: `{v}` itself, or `(κ-1)`-faces of the figure of `v`
  have hB : (t + 1).choose κ ≤ (faces Q κ ∩ {G | v ∈ G}).ncard := by
    rcases κ with _ | κ
    · rw [Nat.choose_zero_right]
      exact (Set.ncard_pos (hfin.inter_of_left _)).mpr ⟨{v}, ⟨hv, adim_singleton v⟩, rfl⟩
    · have hset : faces Q (κ + 1) ∩ {G | v ∈ G} =
          {G | IsFace Q G ∧ {v} ⊆ G ∧ adim G = adim ({v} : Set (ι → ℝ)) + κ + 1} := by
        ext G
        simp only [faces, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.singleton_subset_iff, adim_singleton]
        constructor
        · rintro ⟨⟨hG, hdim⟩, hvG⟩
          exact ⟨hG, hvG, by omega⟩
        · rintro ⟨hG, hvG, hdim⟩
          exact ⟨⟨hG, by omega⟩, hvG⟩
      rw [hset, ncard_cofaces_eq ψ hψ κ]
      have := ihfin m' Qv hQv hQvne (by omega) κ (by omega)
      rwa [hQvt] at this
  show _ ≤ (faces Q κ).ncard
  rw [hs, ← Set.ncard_inter_add_ncard_sdiff_eq_ncard (faces Q κ) {G | v ∈ G} hfin, Nat.choose_succ_succ']
  omega

/-- The simplex bound for polytopes in the coordinate spaces `Fin m → ℝ` (where face figures live). -/
theorem simplexBound_fin (s : ℕ) : ∀ (m : ℕ) (Q : Set (Fin m → ℝ)), IsPolytope Q → Q.Nonempty → adim Q = s →
    SimplexBound Q := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro m Q hQ hne hs
    exact simplexBound_step s (fun Q' hQ' hne' hlt => ih _ hlt m Q' hQ' hne' rfl)
      (fun m' Q' hQ' hne' hlt => ih _ hlt m' Q' hQ' hne' rfl) Q hQ hne hs

/-- **Lemma 4.8**, first part: an `s`-polytope has at least `C(s+1, κ+1)` faces of dimension `κ` (`0 ≤ κ ≤ s`). -/
theorem lemma_4_8_simplex_proved {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (hne : Q.Nonempty)
    (κ : ℕ) (hκ : κ ≤ adim Q) : Nat.choose (adim Q + 1) (κ + 1) ≤ fNum Q κ := by
  suffices h : ∀ s (Q : Set (ι → ℝ)), IsPolytope Q → Q.Nonempty → adim Q = s → SimplexBound Q from
    h _ Q hQ hne rfl κ hκ
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro Q hQ hne hs
    exact simplexBound_step s (fun Q' hQ' hne' hlt => ih _ hlt Q' hQ' hne' rfl)
      (fun m Q' hQ' hne' _ => simplexBound_fin _ m Q' hQ' hne' rfl) Q hQ hne hs

/-- **Lemma 4.8**: a nonempty `e`-face `E` of an `m`-polytope `B` lies in at least `C(m−e, j)` faces of dimension
`e + j`, for `0 ≤ j ≤ m − e`. -/
theorem lemma_4_8_proved {ι : Type*} [Fintype ι] (B : Set (ι → ℝ)) (hB : IsPolytope B) (E : Set (ι → ℝ))
    (hE : IsFace B E) (j : ℕ) (hj : j ≤ adim B - adim E) :
    Nat.choose (adim B - adim E) j ≤ {G | IsFace B G ∧ E ⊆ G ∧ adim G = adim E + j}.ncard := by
  rcases j with _ | j
  · rw [Nat.choose_zero_right]
    have hfin : {G | IsFace B G ∧ E ⊆ G ∧ adim G = adim E + 0}.Finite :=
      hB.finite_faces.subset fun _ hG => hG.1
    exact (Set.ncard_pos hfin).mpr ⟨E, hE, subset_rfl, rfl⟩
  obtain ⟨m, Q, hQ, hQe, hQdim, φ, hφ⟩ := Cited.ziegler_face_figure B hB E hE
  have hEB : E ≠ B := by
    rintro rfl
    omega
  have hQne : Q.Nonempty := Set.nonempty_iff_ne_empty.mpr fun h => hEB (hQe.mp h)
  have hdim := hQdim hQne
  rw [← add_assoc, ncard_cofaces_eq φ hφ j]
  have := lemma_4_8_simplex_proved Q hQ hQne j (by omega)
  rwa [show adim Q + 1 = adim B - adim E by omega] at this

end HibiLi.Proofs
