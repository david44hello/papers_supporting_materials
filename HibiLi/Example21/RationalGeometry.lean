/-
HibiLi/Example21/RationalGeometry.lean — rational data checked against real geometry.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.Masks
import HibiLi.Example21.Argmax

namespace HibiLi.Example21

variable {rows : Type*} [Fintype rows]

def realPoints (points : Fin 8 → rows → ℚ) (idx : Fin 8) : rows → ℝ :=
  fun row => (points idx row : ℝ)

def rationalDifference (points : Fin 8 → rows → ℚ) (subset : Finset (Fin 8))
    (base : Fin 8) : Matrix rows (Fin 8) ℚ :=
  fun row col => if col ∈ subset then points col row - points base row else 0

structure RankCertificate (rows : Type*) where
  base : Fin 8
  dim : ℕ
  pivot : Fin dim → Fin 8
  dual : Matrix (Fin dim) rows ℚ
  coeff : Matrix (Fin dim) (Fin 8) ℚ

def RankCertificate.Valid (cert : RankCertificate rows) (points : Fin 8 → rows → ℚ)
    (subset : Finset (Fin 8)) : Prop :=
  cert.base ∈ subset ∧
    cert.dual * (rationalDifference points subset cert.base).submatrix id cert.pivot = 1 ∧
    rationalDifference points subset cert.base =
      (rationalDifference points subset cert.base).submatrix id cert.pivot * cert.coeff

instance (cert : RankCertificate rows) (points : Fin 8 → rows → ℚ)
    (subset : Finset (Fin 8)) : Decidable (cert.Valid points subset) := by
  unfold RankCertificate.Valid
  infer_instance

theorem RankCertificate.adim_eq (cert : RankCertificate rows) (points : Fin 8 → rows → ℚ)
    (subset : Finset (Fin 8)) (hcert : cert.Valid points subset) :
    adim (realPoints points '' (subset : Set (Fin 8))) = cert.dim := by
  rw [adim_image_eq_rank (realPoints points) subset cert.base hcert.1]
  have hmap : differenceMatrix (realPoints points) subset cert.base =
      (rationalDifference points subset cert.base).map (Rat.castHom ℝ) := by
    ext row col
    by_cases hc : col ∈ subset <;> simp [differenceMatrix, rationalDifference, realPoints, hc]
  rw [hmap]
  exact rational_matrix_rank_certificate _ cert.pivot cert.dual cert.coeff hcert.2.1 hcert.2.2

def rationalScore (points : Fin 8 → rows → ℚ) (normal : rows → ℚ) (idx : Fin 8) : ℚ :=
  ∑ row, normal row * points idx row

noncomputable def normalFunctional (normal : rows → ℚ) : (rows → ℝ) →L[ℝ] ℝ :=
  ∑ row, (normal row : ℝ) • ContinuousLinearMap.proj row

theorem normalFunctional_apply (points : Fin 8 → rows → ℚ) (normal : rows → ℚ) (idx : Fin 8) :
    normalFunctional normal (realPoints points idx) = (rationalScore points normal idx : ℝ) := by
  simp [normalFunctional, realPoints, rationalScore, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

structure ExposureCertificate (rows : Type*) where
  normal : rows → ℚ
  level : ℚ

def ExposureCertificate.Valid (cert : ExposureCertificate rows) (points : Fin 8 → rows → ℚ)
    (subset : Finset (Fin 8)) : Prop :=
  ∀ idx, (idx ∈ subset → rationalScore points cert.normal idx = cert.level) ∧
    (idx ∉ subset → rationalScore points cert.normal idx < cert.level)

instance (cert : ExposureCertificate rows) (points : Fin 8 → rows → ℚ)
    (subset : Finset (Fin 8)) : Decidable (cert.Valid points subset) := by
  unfold ExposureCertificate.Valid
  infer_instance

theorem ExposureCertificate.generatorArgmax_eq (cert : ExposureCertificate rows)
    (points : Fin 8 → rows → ℚ) (subset : Finset (Fin 8))
    (hcert : cert.Valid points subset) (hn : subset.Nonempty) :
    generatorArgmax (Set.range (realPoints points)) (normalFunctional cert.normal) =
      realPoints points '' (subset : Set (Fin 8)) := by
  have heq : ∀ idx ∈ subset, normalFunctional cert.normal (realPoints points idx) =
      (cert.level : ℝ) := by
    intro idx hi
    rw [normalFunctional_apply, (hcert idx).1 hi]
  have hlt : ∀ idx ∉ subset, normalFunctional cert.normal (realPoints points idx) <
      (cert.level : ℝ) := by
    intro idx hi
    rw [normalFunctional_apply]
    exact_mod_cast (hcert idx).2 hi
  ext point
  constructor
  · rintro ⟨⟨idx, rfl⟩, hmax⟩
    have hi : idx ∈ subset := by
      by_contra hnidx
      obtain ⟨base, hbase⟩ := hn
      have hle := hmax (realPoints points base) (Set.mem_range_self base)
      rw [heq base hbase] at hle
      exact (not_lt_of_ge hle) (hlt idx hnidx)
    exact Set.mem_image_of_mem (realPoints points) hi
  · rintro ⟨idx, hi, rfl⟩
    refine ⟨Set.mem_range_self idx, ?_⟩
    rintro _ ⟨other, rfl⟩
    rw [heq idx hi]
    by_cases ho : other ∈ subset
    · exact (heq other ho).le
    · exact (hlt other ho).le

theorem ExposureCertificate.isFace (cert : ExposureCertificate rows)
    (points : Fin 8 → rows → ℚ) (subset : Finset (Fin 8))
    (hcert : cert.Valid points subset) (hn : subset.Nonempty) :
    IsFace (convexHull ℝ (Set.range (realPoints points)))
      (convexHull ℝ (realPoints points '' (subset : Set (Fin 8)))) := by
  rw [← cert.generatorArgmax_eq points subset hcert hn]
  exact isFace_convexHull_generatorArgmax (Set.finite_range _) (Set.range_nonempty _)
    (normalFunctional cert.normal)

end HibiLi.Example21
