/-
HibiLi/Example21/ZeroOneFaces.lean — zero-one points and zero-dimensional geometric faces.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.ZeroOneResult

namespace HibiLi

variable {P : Type*} [Fintype P]

noncomputable def cubeFunctional (v : P → ℝ) : (P → ℝ) →L[ℝ] ℝ :=
  ∑ pp, (2 * v pp - 1) • ContinuousLinearMap.proj pp

theorem cubeFunctional_apply (v w : P → ℝ) :
    cubeFunctional v w = ∑ pp, (2 * v pp - 1) * w pp := by
  simp [cubeFunctional, smul_eq_mul]

theorem cubeFunctional_term_le {v w : P → ℝ} (hv : v ∈ zeroOneVectors P)
    (hw : ∀ pp, 0 ≤ w pp ∧ w pp ≤ 1) (pp : P) :
    (2 * v pp - 1) * w pp ≤ (2 * v pp - 1) * v pp := by
  rcases hv pp with hz | ho
  · rw [hz]; nlinarith [(hw pp).1]
  · rw [ho]; nlinarith [(hw pp).2]

theorem cubeFunctional_le {v w : P → ℝ} (hv : v ∈ zeroOneVectors P)
    (hw : ∀ pp, 0 ≤ w pp ∧ w pp ≤ 1) : cubeFunctional v w ≤ cubeFunctional v v := by
  simp only [cubeFunctional_apply]
  exact Finset.sum_le_sum fun pp _ => cubeFunctional_term_le hv hw pp

theorem cubeFunctional_eq_iff {v w : P → ℝ} (hv : v ∈ zeroOneVectors P)
    (hw : ∀ pp, 0 ≤ w pp ∧ w pp ≤ 1) : cubeFunctional v w = cubeFunctional v v ↔ w = v := by
  constructor
  · intro hh
    simp only [cubeFunctional_apply] at hh
    have hterms := (Finset.sum_eq_sum_iff_of_le
      (fun pp (_ : pp ∈ (Finset.univ : Finset P)) => cubeFunctional_term_le hv hw pp)).mp hh
    ext pp
    have hp := hterms pp (Finset.mem_univ pp)
    rcases hv pp with hz | ho
    · rw [hz] at hp ⊢; linarith
    · rw [ho] at hp ⊢; linarith
  · rintro rfl
    rfl

theorem zeroOne_isFace_singleton {Q : Set (P → ℝ)} {v : P → ℝ}
    (hQ : ∀ w ∈ Q, ∀ pp, 0 ≤ w pp ∧ w pp ≤ 1)
    (hv : v ∈ Q) (hzero : v ∈ zeroOneVectors P) : IsFace Q {v} := by
  refine ⟨Set.singleton_nonempty _, fun _ => ⟨cubeFunctional v, ?_⟩⟩
  ext w
  constructor
  · rintro rfl
    exact ⟨hv, fun other hother => cubeFunctional_le hzero (hQ other hother)⟩
  · intro hw
    have heq := le_antisymm (cubeFunctional_le hzero (hQ w hw.1)) (hw.2 v hv)
    exact (cubeFunctional_eq_iff hzero (hQ w hw.1)).mp heq

theorem faces_zero_eq_singletons {Q V : Set (P → ℝ)}
    (hV : V ⊆ zeroOneVectors P) (hQ : Q = convexHull ℝ V)
    (hcube : ∀ w ∈ Q, ∀ pp, 0 ≤ w pp ∧ w pp ≤ 1) :
    faces Q 0 = (fun v => ({v} : Set (P → ℝ))) '' V := by
  ext F
  constructor
  · rintro ⟨hface, hdim⟩
    obtain ⟨v, hv⟩ := hface.1
    have hspan : vectorSpan ℝ F = ⊥ := Submodule.finrank_eq_zero.mp hdim
    have hsub : F.Subsingleton := (vectorSpan_eq_bot_iff_subsingleton ℝ).mp hspan
    have hf : F = {v} := Set.eq_singleton_iff_unique_mem.mpr ⟨hv, fun w hw => hsub hw hv⟩
    have hext : v ∈ Set.extremePoints ℝ Q := by
      apply isExtreme_singleton.mp
      simpa only [hf] using hface.2.isExtreme
    rw [hQ] at hext
    exact ⟨v, extremePoints_convexHull_subset hext, hf.symm⟩
  · rintro ⟨v, hv, rfl⟩
    have hvQ : v ∈ Q := hQ ▸ subset_convexHull ℝ V hv
    exact ⟨zeroOne_isFace_singleton hcube hvQ (hV hv), by simp [adim]⟩

theorem fNum_zero_eq_ncard {Q V : Set (P → ℝ)}
    (hV : V ⊆ zeroOneVectors P) (hQ : Q = convexHull ℝ V)
    (hcube : ∀ w ∈ Q, ∀ pp, 0 ≤ w pp ∧ w pp ≤ 1) : fNum Q 0 = V.ncard := by
  rw [fNum, faces_zero_eq_singletons hV hQ hcube]
  exact Set.ncard_image_of_injective V Set.singleton_injective

end HibiLi
