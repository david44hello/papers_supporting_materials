/-
HibiLi/Example21/Catalog.lean — certified subset catalogs count geometric faces.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.Nonface

namespace HibiLi.Example21

variable {rows : Type*} [Fintype rows]

def catalogMasks (catalog : Fin 256 → Option (RankCertificate rows × ExposureCertificate rows))
    (dim : ℕ) : Finset (Fin 256) :=
  Finset.univ.filter fun mask => (catalog mask).any (fun cert => cert.1.dim == dim)

def CatalogValid (points : Fin 8 → rows → ℚ)
    (catalog : Fin 256 → Option (RankCertificate rows × ExposureCertificate rows))
    (exclusion : Fin 256 → NonfaceCertificate) : Prop :=
  ∀ mask, match catalog mask with
    | some cert => cert.1.Valid points (maskFinset mask) ∧
        cert.2.Valid points (maskFinset mask)
    | none => mask.val = 0 ∨ (exclusion mask).Valid points (maskFinset mask)

def catalogFace (points : Fin 8 → rows → ℚ) (mask : Fin 256) : Set (rows → ℝ) :=
  convexHull ℝ (realPoints points '' (maskFinset mask : Set (Fin 8)))

theorem ExposureCertificate.mem_hull_iff (cert : ExposureCertificate rows)
    (points : Fin 8 → rows → ℚ) (subset : Finset (Fin 8))
    (hcert : cert.Valid points subset) (hn : subset.Nonempty) (idx : Fin 8) :
    realPoints points idx ∈ convexHull ℝ (realPoints points '' (subset : Set (Fin 8))) ↔
      idx ∈ subset := by
  constructor
  · intro hmem
    have heq := toExposed_convexHull_eq (Set.finite_range (realPoints points))
      (Set.range_nonempty _) (normalFunctional cert.normal)
    rw [cert.generatorArgmax_eq points subset hcert hn] at heq
    rw [← heq] at hmem
    by_contra hout
    obtain ⟨base, hbase⟩ := hn
    have hle := hmem.2 (realPoints points base) (subset_convexHull ℝ _ (Set.mem_range_self base))
    rw [normalFunctional_apply, normalFunctional_apply] at hle
    have hle' : rationalScore points cert.normal base ≤ rationalScore points cert.normal idx :=
      by exact_mod_cast hle
    rw [(hcert base).1 hbase] at hle'
    exact (not_lt_of_ge hle') ((hcert idx).2 hout)
  · intro hi
    exact subset_convexHull ℝ _ (Set.mem_image_of_mem (realPoints points) hi)

theorem generatorArgmax_range_eq_image (points : Fin 8 → rows → ℚ)
    (ell : (rows → ℝ) →L[ℝ] ℝ) (subset : Finset (Fin 8))
    (hsubset : ∀ idx, idx ∈ subset ↔ ∀ other,
      ell (realPoints points other) ≤ ell (realPoints points idx)) :
    generatorArgmax (Set.range (realPoints points)) ell =
      realPoints points '' (subset : Set (Fin 8)) := by
  ext point
  constructor
  · rintro ⟨⟨idx, rfl⟩, hh⟩
    exact ⟨idx, (hsubset idx).mpr (fun other => hh _ (Set.mem_range_self other)), rfl⟩
  · rintro ⟨idx, hi, rfl⟩
    refine ⟨Set.mem_range_self idx, ?_⟩
    rintro _ ⟨other, rfl⟩
    exact (hsubset idx).mp hi other

theorem catalogFace_isFace {points : Fin 8 → rows → ℚ}
    {catalog : Fin 256 → Option (RankCertificate rows × ExposureCertificate rows)}
    {exclusion : Fin 256 → NonfaceCertificate} (hvalid : CatalogValid points catalog exclusion)
    {mask : Fin 256} {cert : RankCertificate rows × ExposureCertificate rows}
    (hc : catalog mask = some cert) :
    IsFace (convexHull ℝ (Set.range (realPoints points))) (catalogFace points mask) ∧
      adim (catalogFace points mask) = cert.1.dim := by
  have hh : cert.1.Valid points (maskFinset mask) ∧ cert.2.Valid points (maskFinset mask) := by
    simpa [CatalogValid, hc] using hvalid mask
  have hn : (maskFinset mask).Nonempty := ⟨cert.1.base, hh.1.1⟩
  exact ⟨cert.2.isFace points _ hh.2 hn,
    (adim_convexHull _).trans (cert.1.adim_eq points _ hh.1)⟩

theorem catalog_complete {points : Fin 8 → rows → ℚ}
    {catalog : Fin 256 → Option (RankCertificate rows × ExposureCertificate rows)}
    {exclusion : Fin 256 → NonfaceCertificate} (hvalid : CatalogValid points catalog exclusion)
    {F : Set (rows → ℝ)} (hF : IsFace (convexHull ℝ (Set.range (realPoints points))) F) :
    ∃ mask cert, catalog mask = some cert ∧ F = catalogFace points mask := by
  classical
  obtain ⟨ell, hell⟩ := hF.exists_generatorArgmax (Set.finite_range _)
  let subset := Finset.univ.filter fun idx =>
    ∀ other, ell (realPoints points other) ≤ ell (realPoints points idx)
  have hsubset : ∀ idx, idx ∈ subset ↔ ∀ other,
      ell (realPoints points other) ≤ ell (realPoints points idx) := by
    intro idx
    simp [subset]
  have harg := generatorArgmax_range_eq_image points ell subset hsubset
  have hn : subset.Nonempty := by
    obtain ⟨point, hpoint⟩ := generatorArgmax_nonempty (Set.finite_range (realPoints points))
      (Set.range_nonempty _) ell
    rw [harg] at hpoint
    obtain ⟨idx, hi, _⟩ := hpoint
    exact ⟨idx, hi⟩
  obtain ⟨mask, hmask⟩ := maskFinset_surjective subset
  have hh := hvalid mask
  cases hc : catalog mask with
  | some cert =>
    refine ⟨mask, cert, hc, ?_⟩
    simpa only [catalogFace, hmask, harg] using hell
  | none =>
    have hh' : mask.val = 0 ∨ (exclusion mask).Valid points (maskFinset mask) := by
      simpa [CatalogValid, hc] using hh
    rcases hh' with hz | hexclude
    · have hzero : maskFinset mask = ∅ := by simp [maskFinset, hz]
      rw [hmask] at hzero
      exact False.elim (hn.ne_empty hzero)
    · rw [hmask] at hexclude
      exact False.elim ((exclusion mask).not_maximizers points subset hexclude hn ell hsubset)

theorem catalogFace_injOn {points : Fin 8 → rows → ℚ}
    {catalog : Fin 256 → Option (RankCertificate rows × ExposureCertificate rows)}
    {exclusion : Fin 256 → NonfaceCertificate} (hvalid : CatalogValid points catalog exclusion)
    (dim : ℕ) : Set.InjOn (catalogFace points) (catalogMasks catalog dim : Set (Fin 256)) := by
  intro first hfirst second hsecond heq
  obtain ⟨cert₁, hc₁, _⟩ : ∃ cert, catalog first = some cert ∧ cert.1.dim = dim := by
    simpa [catalogMasks, Option.any_eq_true] using hfirst
  obtain ⟨cert₂, hc₂, _⟩ : ∃ cert, catalog second = some cert ∧ cert.1.dim = dim := by
    simpa [catalogMasks, Option.any_eq_true] using hsecond
  have hv₁ : cert₁.1.Valid points (maskFinset first) ∧ cert₁.2.Valid points (maskFinset first) := by
    simpa [CatalogValid, hc₁] using hvalid first
  have hv₂ : cert₂.1.Valid points (maskFinset second) ∧ cert₂.2.Valid points (maskFinset second) := by
    simpa [CatalogValid, hc₂] using hvalid second
  apply maskFinset_injective
  ext idx
  rw [← cert₁.2.mem_hull_iff points _ hv₁.2 ⟨cert₁.1.base, hv₁.1.1⟩ idx,
    ← cert₂.2.mem_hull_iff points _ hv₂.2 ⟨cert₂.1.base, hv₂.1.1⟩ idx]
  change realPoints points idx ∈ catalogFace points first ↔
    realPoints points idx ∈ catalogFace points second
  rw [heq]

theorem faces_eq_catalog_image {points : Fin 8 → rows → ℚ}
    {catalog : Fin 256 → Option (RankCertificate rows × ExposureCertificate rows)}
    {exclusion : Fin 256 → NonfaceCertificate} (hvalid : CatalogValid points catalog exclusion)
    (dim : ℕ) : faces (convexHull ℝ (Set.range (realPoints points))) dim =
      catalogFace points '' (catalogMasks catalog dim : Set (Fin 256)) := by
  ext F
  constructor
  · rintro ⟨hF, hdim⟩
    obtain ⟨mask, cert, hc, hface⟩ := catalog_complete hvalid hF
    have hd : cert.1.dim = dim := by
      rw [hface, (catalogFace_isFace hvalid hc).2] at hdim
      exact hdim
    refine ⟨mask, ?_, hface.symm⟩
    simp [catalogMasks, hc, hd]
  · rintro ⟨mask, hmask, rfl⟩
    obtain ⟨cert, hc, hd⟩ : ∃ cert, catalog mask = some cert ∧ cert.1.dim = dim := by
      simpa [catalogMasks, Option.any_eq_true] using hmask
    exact ⟨(catalogFace_isFace hvalid hc).1, (catalogFace_isFace hvalid hc).2.trans hd⟩

theorem fNum_eq_catalog_card {points : Fin 8 → rows → ℚ}
    {catalog : Fin 256 → Option (RankCertificate rows × ExposureCertificate rows)}
    {exclusion : Fin 256 → NonfaceCertificate} (hvalid : CatalogValid points catalog exclusion)
    (dim : ℕ) : fNum (convexHull ℝ (Set.range (realPoints points))) dim =
      (catalogMasks catalog dim).card := by
  rw [fNum, faces_eq_catalog_image hvalid dim,
    (catalogFace_injOn hvalid dim).ncard_image, Set.ncard_coe_finset]

end HibiLi.Example21
