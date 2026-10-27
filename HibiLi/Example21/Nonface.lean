/-
HibiLi/Example21/Nonface.lean — exact affine-dependence certificates excluding faces.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.RationalGeometry

namespace HibiLi.Example21

variable {rows : Type*} [Fintype rows]

structure NonfaceCertificate where
  weights : Fin 8 → ℚ
  witness : Fin 8

def NonfaceCertificate.Valid (cert : NonfaceCertificate) (points : Fin 8 → rows → ℚ)
    (subset : Finset (Fin 8)) : Prop :=
  (∑ idx, cert.weights idx) = 0 ∧
  (∀ row, ∑ idx, cert.weights idx * points idx row = 0) ∧
  (∀ idx, 0 < cert.weights idx → idx ∈ subset) ∧
  cert.weights cert.witness < 0 ∧ cert.witness ∉ subset

instance (cert : NonfaceCertificate) (points : Fin 8 → rows → ℚ)
    (subset : Finset (Fin 8)) : Decidable (cert.Valid points subset) := by
  unfold NonfaceCertificate.Valid
  infer_instance

theorem NonfaceCertificate.not_maximizers (cert : NonfaceCertificate)
    (points : Fin 8 → rows → ℚ) (subset : Finset (Fin 8))
    (hcert : cert.Valid points subset) (hn : subset.Nonempty)
    (ell : (rows → ℝ) →L[ℝ] ℝ)
    (hmax : ∀ idx, idx ∈ subset ↔
      ∀ other, ell (realPoints points other) ≤ ell (realPoints points idx)) : False := by
  obtain ⟨base, hbase⟩ := hn
  let level := ell (realPoints points base)
  have hle (idx : Fin 8) : ell (realPoints points idx) ≤ level :=
    (hmax base).mp hbase idx
  have heq (idx : Fin 8) (hi : idx ∈ subset) : ell (realPoints points idx) = level :=
    le_antisymm (hle idx) ((hmax idx).mp hi base)
  have hsumweights : ∑ idx, (cert.weights idx : ℝ) = 0 := by exact_mod_cast hcert.1
  have hsumvectors : ∑ idx, (cert.weights idx : ℝ) • realPoints points idx = 0 := by
    ext row
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, realPoints]
    exact_mod_cast hcert.2.1 row
  have hsumscores : ∑ idx, (cert.weights idx : ℝ) * ell (realPoints points idx) = 0 := by
    have hh := congrArg ell hsumvectors
    simpa only [map_sum, map_smul, map_zero, smul_eq_mul] using hh
  let summand := fun idx => (cert.weights idx : ℝ) * (ell (realPoints points idx) - level)
  have hnonneg (idx : Fin 8) : 0 ≤ summand idx := by
    by_cases hw : 0 < cert.weights idx
    · dsimp [summand]
      rw [heq idx (hcert.2.2.1 idx hw), sub_self, mul_zero]
    · have hw' : (cert.weights idx : ℝ) ≤ 0 := by exact_mod_cast le_of_not_gt hw
      exact mul_nonneg_of_nonpos_of_nonpos hw' (sub_nonpos.mpr (hle idx))
  have hwitness : ell (realPoints points cert.witness) < level := by
    by_contra hnlt
    have hh : cert.witness ∈ subset := (hmax cert.witness).mpr fun idx =>
      (hle idx).trans (le_of_not_gt hnlt)
    exact hcert.2.2.2.2 hh
  have hnegative : (cert.weights cert.witness : ℝ) < 0 := by
    exact_mod_cast hcert.2.2.2.1
  have hpositive : 0 < summand cert.witness :=
    mul_pos_of_neg_of_neg hnegative (sub_neg.mpr hwitness)
  have hsumpositive : 0 < ∑ idx, summand idx :=
    Finset.sum_pos' (fun idx _ => hnonneg idx) ⟨cert.witness, Finset.mem_univ _, hpositive⟩
  have hsumzero : (∑ idx, summand idx) = 0 := by
    simp only [summand, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hsumscores, hsumweights, zero_mul, sub_zero]
  linarith

end HibiLi.Example21
