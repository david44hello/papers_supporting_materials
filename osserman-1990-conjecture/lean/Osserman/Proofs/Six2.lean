/-
Osserman/Proofs/Six2.lean — proofs of the rows of Lemma 24.5 of paper 013 (sec_singular_integral_extraction.tex
l. 155-169), statements in Osserman/Paper/StatementsSix.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.SixPieces
namespace Osserman.Proofs.Six2
open Osserman Matrix

/-
Six2.lean — proofs of the rows of Lemma 24.5 of paper 013 (sec_singular_integral_extraction.tex l. 155-169), rows of
Osserman/Paper/StatementsSix.lean copied verbatim with suffix `_proved`.
-/

lemma sym_entry {T : Type*} [CommRing T] (Bm : Matrix (Fin 2) (Fin 2) T) (hsym : Bmᵀ = Bm) : Bm 1 0 = Bm 0 1 := by
  have h := congrFun (congrFun hsym 0) 1
  simpa [transpose_apply] using h

lemma eta_sym {T : Type*} [CommRing T] (Bm : Matrix (Fin 2) (Fin 2) T) (hsym : Bmᵀ = Bm) :
    Bm = !![Bm 0 0, Bm 0 1; Bm 0 1, Bm 1 1] := by
  have h10 := sym_entry Bm hsym
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10]

theorem lem_24_5_entries_max_proved {T : Type*} [CommRing T] [IsLocalRing T] (h2 : IsUnit (2 : T))
    (Bm : Matrix (Fin 2) (Fin 2) T) (hsym : Bmᵀ = Bm)
    (hall : ∀ v : Fin 2 → T, v ⬝ᵥ (Bm *ᵥ v) ∈ IsLocalRing.maximalIdeal T) :
    (∀ i j, Bm i j ∈ IsLocalRing.maximalIdeal T) ∧ Bm.det ∈ IsLocalRing.maximalIdeal T := by
  have h10 := sym_entry Bm hsym
  have e0 := hall ![1, 0]
  have e1 := hall ![0, 1]
  have e01 := hall ![1, 1]
  simp [dotProduct, mulVec, Fin.sum_univ_two] at e0 e1 e01
  have h2b : 2 * Bm 0 1 ∈ IsLocalRing.maximalIdeal T := by
    have h := (IsLocalRing.maximalIdeal T).sub_mem ((IsLocalRing.maximalIdeal T).sub_mem e01 e0) e1
    convert h using 1
    rw [h10]
    ring
  have hb : Bm 0 1 ∈ IsLocalRing.maximalIdeal T := by
    obtain ⟨u, hu⟩ := h2
    have h := (IsLocalRing.maximalIdeal T).mul_mem_left (↑u⁻¹ : T) h2b
    rwa [← hu, ← mul_assoc, Units.inv_mul, one_mul] at h
  have hall' : ∀ i j, Bm i j ∈ IsLocalRing.maximalIdeal T := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact e0
    · exact hb
    · simpa [h10] using hb
    · exact e1
  refine ⟨hall', ?_⟩
  rw [det_fin_two]
  exact (IsLocalRing.maximalIdeal T).sub_mem ((IsLocalRing.maximalIdeal T).mul_mem_right _ (hall' 0 0))
    ((IsLocalRing.maximalIdeal T).mul_mem_right _ (hall' 0 1))

theorem lem_24_5_unit_norm_proved {T : Type*} [CommRing T] [IsLocalRing T] (h2 : IsUnit (2 : T))
    (Bm : Matrix (Fin 2) (Fin 2) T) (hsym : Bmᵀ = Bm) (hunimod : IsUnit Bm.det) :
    ∃ v : Fin 2 → T, IsUnit (v ⬝ᵥ (Bm *ᵥ v)) := by
  by_contra h
  push Not at h
  have hall : ∀ v : Fin 2 → T, v ⬝ᵥ (Bm *ᵥ v) ∈ IsLocalRing.maximalIdeal T :=
    fun v => (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (h v))
  have hdet := (lem_24_5_entries_max_proved h2 Bm hsym hall).2
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hdet) hunimod

theorem lem_24_5_split_off_proved {T : Type*} [CommRing T] (Bm : Matrix (Fin 2) (Fin 2) T) (hsym : Bmᵀ = Bm)
    (hunimod : IsUnit Bm.det) :
    ∀ v : Fin 2 → T, IsUnit (v ⬝ᵥ (Bm *ᵥ v)) → ∃ w : Fin 2 → T, v ⬝ᵥ (Bm *ᵥ w) = 0 ∧
      IsUnit (Matrix.of ![v, w]).det ∧ IsUnit (w ⬝ᵥ (Bm *ᵥ w)) ∧
      (∀ u : Fin 2 → T, v ⬝ᵥ (Bm *ᵥ u) = 0 ↔ ∃ c : T, u = c • w) ∧
      Matrix.of ![v, w] * Bm * (Matrix.of ![v, w])ᵀ = diagonal ![v ⬝ᵥ (Bm *ᵥ v), w ⬝ᵥ (Bm *ᵥ w)] := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c : T, Bm = !![a, b; b, c] := ⟨_, _, _, eta_sym Bm hsym⟩
  intro v hv
  have hq : v ⬝ᵥ (!![a, b; b, c] *ᵥ v) = v 0 * (a * v 0 + b * v 1) + v 1 * (b * v 0 + c * v 1) := by
    simp [dotProduct, mulVec, Fin.sum_univ_two]
  set w : Fin 2 → T := ![-(b * v 0 + c * v 1), a * v 0 + b * v 1] with hw
  have hvw : v ⬝ᵥ (!![a, b; b, c] *ᵥ w) = 0 := by
    simp [hw, dotProduct, mulVec, Fin.sum_univ_two]
    ring
  have hdet : (Matrix.of ![v, w]).det = v ⬝ᵥ (!![a, b; b, c] *ᵥ v) := by
    rw [hq, det_fin_two]
    simp [hw]
    ring
  have hww : w ⬝ᵥ (!![a, b; b, c] *ᵥ w) = !![a, b; b, c].det * v ⬝ᵥ (!![a, b; b, c] *ᵥ v) := by
    rw [hq, det_fin_two_of]
    simp [hw, dotProduct, mulVec, Fin.sum_univ_two]
    ring
  refine ⟨w, hvw, by rw [hdet]; exact hv, by rw [hww]; exact hunimod.mul hv, ?_, ?_⟩
  · intro u
    constructor
    · intro hu
      have hu' : v 0 * (a * u 0 + b * u 1) + v 1 * (b * u 0 + c * u 1) = 0 := by
        simpa [dotProduct, mulVec, Fin.sum_univ_two] using hu
      obtain ⟨dinv, hd⟩ := hv.exists_right_inv
      rw [hq] at hd
      refine ⟨(u 1 * v 0 - u 0 * v 1) * dinv, funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
      · simp only [hw, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
        linear_combination (-u 0) * hd + dinv * v 0 * hu'
      · simp only [hw, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        linear_combination (-u 1) * hd + dinv * v 1 * hu'
    · rintro ⟨k, rfl⟩
      rw [mulVec_smul, dotProduct_smul, hvw, smul_zero]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hw, Matrix.mul_apply, Fin.sum_univ_two, dotProduct, mulVec, diagonal, Matrix.vecHead,
        Matrix.vecTail] <;> ring

theorem lem_24_5_root_proved {T : Type*} [CommRing T] [IsDomain T] (a b : T) (ha : IsUnit a) (hb : IsUnit b)
    (hhyp : IsHyperbolic2 ((diagonal ![a, b]).map (algebraMap T (FractionRing T)))) :
    ∃ r : FractionRing T, r ^ 2 = -(algebraMap T (FractionRing T) b / algebraMap T (FractionRing T) a) := by
  obtain ⟨P, hP, hPB⟩ := hhyp
  have ha' : algebraMap T (FractionRing T) a ≠ 0 := (ha.map (algebraMap T (FractionRing T))).ne_zero
  have h00 := congrFun (congrFun hPB 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, diagonal, transpose_apply] at h00
  have hdet := hP.ne_zero
  rw [det_fin_two] at hdet
  have hP10 : P 1 0 ≠ 0 := by
    intro h
    have h' : algebraMap T (FractionRing T) a * (P 0 0 * P 0 0) = 0 := by
      rw [h] at h00
      linear_combination h00
    have hP00 : P 0 0 = 0 := by
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' ha'
      · exact mul_self_eq_zero.mp h''
    apply hdet
    rw [hP00, h]
    ring
  refine ⟨P 0 0 / P 1 0, ?_⟩
  rw [div_pow, eq_neg_iff_add_eq_zero, div_add_div _ _ (pow_ne_zero 2 hP10) ha', div_eq_zero_iff]
  left
  linear_combination h00

theorem lem_24_5_integral_proved {T : Type*} [CommRing T] [IsDomain T] [IsIntegrallyClosed T] (a b : T)
    (ha : IsUnit a) (hb : IsUnit b) (r : FractionRing T)
    (hr : r ^ 2 = -(algebraMap T (FractionRing T) b / algebraMap T (FractionRing T) a)) :
    IsIntegral T r ∧ ∃ r' : T, algebraMap T (FractionRing T) r' = r ∧ IsUnit r' ∧ a * r' ^ 2 + b = 0 := by
  obtain ⟨u, rfl⟩ := ha
  have ha' : algebraMap T (FractionRing T) ↑u ≠ 0 := (u.isUnit.map (algebraMap T (FractionRing T))).ne_zero
  have hr' : r ^ 2 = algebraMap T (FractionRing T) (-(b * ↑u⁻¹)) := by
    rw [hr, map_neg, map_mul, map_units_inv, div_eq_mul_inv]
  have hint : IsIntegral T r := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (-(b * ↑u⁻¹)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hr', sub_self]
  refine ⟨hint, ?_⟩
  obtain ⟨r', hr'eq⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hrel : ↑u * r' ^ 2 + b = 0 := by
    apply IsFractionRing.injective T (FractionRing T)
    rw [map_add, map_mul, map_pow, hr'eq, hr, map_zero]
    field_simp
    ring
  refine ⟨r', hr'eq, ?_, hrel⟩
  have h1 : IsUnit (↑u * r' ^ 2) := by
    rw [show (↑u : T) * r' ^ 2 = -b by linear_combination hrel]
    exact hb.neg
  exact (isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_right h1)

theorem lem_24_5_basis_proved {T : Type*} [CommRing T] (h2 : IsUnit (2 : T)) (a b r : T) (hr : IsUnit r)
    (hab : a * r ^ 2 + b = 0) :
    ![r, 1] ⬝ᵥ (diagonal ![a, b] *ᵥ ![r, 1]) = 0 ∧ ![-r, 1] ⬝ᵥ (diagonal ![a, b] *ᵥ ![-r, 1]) = 0 ∧
      IsUnit (Matrix.of ![![r, 1], ![-r, 1]]).det := by
  refine ⟨?_, ?_, ?_⟩
  · simp [dotProduct, mulVec, Fin.sum_univ_two, diagonal]
    linear_combination hab
  · simp [dotProduct, mulVec, Fin.sum_univ_two, diagonal]
    linear_combination hab
  · rw [det_fin_two_of, show r * 1 - 1 * -r = 2 * r by ring]
    exact h2.mul hr

/-- Hyperbolicity is invariant under congruence `B ↦ QBQᵀ` by an invertible `Q`. -/
lemma hyp_transport {K : Type*} [Field K] (B Q : Matrix (Fin 2) (Fin 2) K) (hQ : IsUnit Q.det)
    (h : IsHyperbolic2 B) : IsHyperbolic2 (Q * B * Qᵀ) := by
  obtain ⟨P, hP, hPB⟩ := h
  have hQt : IsUnit Qᵀ.det := by rwa [det_transpose]
  refine ⟨Qᵀ⁻¹ * P, ?_, ?_⟩
  · rw [det_mul]
    exact (isUnit_nonsing_inv_det (A := Qᵀ) hQt).mul hP
  · rw [transpose_mul, transpose_nonsing_inv, transpose_transpose]
    calc Pᵀ * Q⁻¹ * (Q * B * Qᵀ) * (Qᵀ⁻¹ * P) = Pᵀ * (Q⁻¹ * Q) * B * (Qᵀ * Qᵀ⁻¹) * P := by
          simp only [Matrix.mul_assoc]
      _ = Pᵀ * B * P := by
          rw [nonsing_inv_mul (A := Q) hQ, mul_nonsing_inv (A := Qᵀ) hQt, Matrix.mul_one, Matrix.mul_one]
      _ = !![0, 1; 1, 0] := hPB

/-- The basis `P = Qᵀ Nᵀ` (`N` with rows `(r,1), (-r,1)`) is isotropic when `QBQᵀ = diag(a,b)` and `ar² + b = 0`. -/
lemma iso_of_diag {T : Type*} [CommRing T] (Bm Qm : Matrix (Fin 2) (Fin 2) T) (a b r : T)
    (hdiag : Qm * Bm * Qmᵀ = diagonal ![a, b]) (hab : a * r ^ 2 + b = 0) :
    ((Qmᵀ * (Matrix.of ![![r, 1], ![-r, 1]])ᵀ)ᵀ * Bm * (Qmᵀ * (Matrix.of ![![r, 1], ![-r, 1]])ᵀ)) 0 0 = 0 ∧
    ((Qmᵀ * (Matrix.of ![![r, 1], ![-r, 1]])ᵀ)ᵀ * Bm * (Qmᵀ * (Matrix.of ![![r, 1], ![-r, 1]])ᵀ)) 1 1 = 0 := by
  have e : (Qmᵀ * (Matrix.of ![![r, 1], ![-r, 1]])ᵀ)ᵀ * Bm * (Qmᵀ * (Matrix.of ![![r, 1], ![-r, 1]])ᵀ) =
      Matrix.of ![![r, 1], ![-r, 1]] * (Qm * Bm * Qmᵀ) * (Matrix.of ![![r, 1], ![-r, 1]])ᵀ := by
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [e, hdiag]
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul_diagonal] <;>
    linear_combination hab

theorem lem_24_5_proved {T : Type*} [CommRing T] [IsDomain T] [IsLocalRing T] [IsIntegrallyClosed T]
    (h2 : IsUnit (2 : T))
    (Bm : Matrix (Fin 2) (Fin 2) T) (hsym : Bmᵀ = Bm) (hunimod : IsUnit Bm.det)
    (hhyp : IsHyperbolic2 (Bm.map (algebraMap T (FractionRing T)))) :
    ∃ P : Matrix (Fin 2) (Fin 2) T, IsUnit P.det ∧ (Pᵀ * Bm * P) 0 0 = 0 ∧ (Pᵀ * Bm * P) 1 1 = 0 := by
  obtain ⟨v, hv⟩ := lem_24_5_unit_norm_proved h2 Bm hsym hunimod
  obtain ⟨w, -, hdetvw, hw, -, hdiag⟩ := lem_24_5_split_off_proved Bm hsym hunimod v hv
  have hhypD : IsHyperbolic2
      ((diagonal ![v ⬝ᵥ (Bm *ᵥ v), w ⬝ᵥ (Bm *ᵥ w)]).map (algebraMap T (FractionRing T))) := by
    rw [← hdiag, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    refine hyp_transport _ _ ?_ hhyp
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdetvw.map _
  obtain ⟨r, hr⟩ := lem_24_5_root_proved _ _ hv hw hhypD
  obtain ⟨-, r', -, hr'u, hr'⟩ := lem_24_5_integral_proved _ _ hv hw r hr
  obtain ⟨-, -, hdetN⟩ := lem_24_5_basis_proved h2 _ _ r' hr'u hr'
  refine ⟨(Matrix.of ![v, w])ᵀ * (Matrix.of ![![r', 1], ![-r', 1]])ᵀ, ?_, iso_of_diag Bm _ _ _ r' hdiag hr'⟩
  rw [det_mul, det_transpose, det_transpose]
  exact hdetvw.mul hdetN

/-! ### Saturation -/

/-- Coordinates in the basis of the columns of `P`: `det P · v = X·(col 0) + Y·(col 1)`. -/
lemma coord_identity {R : Type*} [CommRing R] (P : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) (i : Fin 2) :
    P.det * v i = (v 0 * P 1 1 - v 1 * P 0 1) * P i 0 + (P 0 0 * v 1 - P 1 0 * v 0) * P i 1 := by
  rw [det_fin_two]
  fin_cases i <;> simp <;> ring

/-- The form in the coordinates `X, Y` of `coord_identity`. -/
lemma quad_identity {R : Type*} [CommRing R] (P B : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) :
    P.det ^ 2 * (v ⬝ᵥ (B *ᵥ v)) =
      (v 0 * P 1 1 - v 1 * P 0 1) ^ 2 * (Pᵀ * B * P) 0 0 +
      (v 0 * P 1 1 - v 1 * P 0 1) * (P 0 0 * v 1 - P 1 0 * v 0) * ((Pᵀ * B * P) 0 1 + (Pᵀ * B * P) 1 0) +
      (P 0 0 * v 1 - P 1 0 * v 0) ^ 2 * (Pᵀ * B * P) 1 1 := by
  simp [det_fin_two, dotProduct, mulVec, Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma gram_entry {R : Type*} [CommRing R] (P B : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    (fun k => P k i) ⬝ᵥ (B *ᵥ fun k => P k j) = (Pᵀ * B * P) i j := by
  simp [dotProduct, mulVec, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Over a field: for a basis `P` of two isotropic vectors with `(col 0)ᵀB(col 1)` nonzero, every nonzero isotropic
vector is a nonzero multiple of one of the two columns. -/
lemma iso_on_axis {K : Type*} [Field K] (P B : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) (hdet : P.det ≠ 0)
    (h00 : (Pᵀ * B * P) 0 0 = 0) (h11 : (Pᵀ * B * P) 1 1 = 0) (hsym : (Pᵀ * B * P) 1 0 = (Pᵀ * B * P) 0 1)
    (hβ : (Pᵀ * B * P) 0 1 ≠ 0) (h2 : (2 : K) ≠ 0) (hv0 : v ≠ 0) (hiso : v ⬝ᵥ (B *ᵥ v) = 0) :
    (∃ c : K, c ≠ 0 ∧ v = c • fun i => P i 0) ∨ (∃ c : K, c ≠ 0 ∧ v = c • fun i => P i 1) := by
  have key := quad_identity P B v
  rw [hiso, h00, h11, hsym] at key
  have hXY : (v 0 * P 1 1 - v 1 * P 0 1) * (P 0 0 * v 1 - P 1 0 * v 0) = 0 := by
    have h : 2 * (Pᵀ * B * P) 0 1 * ((v 0 * P 1 1 - v 1 * P 0 1) * (P 0 0 * v 1 - P 1 0 * v 0)) = 0 := by
      linear_combination -key
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero h2 hβ)
  have hc0 := coord_identity P v 0
  have hc1 := coord_identity P v 1
  have hzero : v 0 * P 1 1 - v 1 * P 0 1 = 0 → P 0 0 * v 1 - P 1 0 * v 0 = 0 → False := by
    intro hX hY
    apply hv0
    refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · have h : P.det * v 0 = 0 := by rw [hc0, hX, hY]; ring
      simpa [hdet] using h
    · have h : P.det * v 1 = 0 := by rw [hc1, hX, hY]; ring
      simpa [hdet] using h
  rcases mul_eq_zero.mp hXY with hX | hY
  · right
    refine ⟨(P 0 0 * v 1 - P 1 0 * v 0) / P.det, ?_, funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
    · intro h
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · exact hzero hX h
      · exact hdet h
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff hdet]
      linear_combination hc0 + P 0 0 * hX
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff hdet]
      linear_combination hc1 + P 1 0 * hX
  · left
    refine ⟨(v 0 * P 1 1 - v 1 * P 0 1) / P.det, ?_, funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
    · intro h
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · exact hzero h hY
      · exact hdet h
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff hdet]
      linear_combination hc0 + P 0 1 * hY
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff hdet]
      linear_combination hc1 + P 1 1 * hY

/-- The saturation of the line `Frac(T)·e` (with `e` part of a `T`-basis) is the free line `T·e`. -/
lemma sat_line {T : Type*} [CommRing T] [IsDomain T] (e f : Fin 2 → T) (hdet : IsUnit (Matrix.of ![e, f]).det)
    (v : Fin 2 → FractionRing T) (c : FractionRing T) (hc : c ≠ 0)
    (hv : v = c • fun i => algebraMap T (FractionRing T) (e i)) (u : Fin 2 → T) :
    (∃ c' : FractionRing T, (fun i => algebraMap T (FractionRing T) (u i)) = c' • v) ↔ ∃ t : T, u = t • e := by
  constructor
  · rintro ⟨c', hc'⟩
    have h0 := congrFun hc' 0
    have h1 := congrFun hc' 1
    rw [hv] at h0 h1
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
    have ht' : e 0 * u 1 - e 1 * u 0 = 0 := by
      apply IsFractionRing.injective T (FractionRing T)
      rw [map_sub, map_mul, map_mul, h0, h1, map_zero]
      ring
    rw [det_fin_two] at hdet
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hdet
    obtain ⟨dinv, hd⟩ := hdet.exists_right_inv
    refine ⟨dinv * (u 0 * f 1 - u 1 * f 0), funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      linear_combination (-u 0) * hd + dinv * f 0 * ht'
    · simp only [Pi.smul_apply, smul_eq_mul]
      linear_combination (-u 1) * hd + dinv * f 1 * ht'
  · rintro ⟨t, rfl⟩
    refine ⟨algebraMap T (FractionRing T) t / c, ?_⟩
    rw [hv]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    field_simp

theorem lem_24_5_saturation_proved {T : Type*} [CommRing T] [IsDomain T] [IsLocalRing T] [IsIntegrallyClosed T]
    (h2 : IsUnit (2 : T)) (Bm : Matrix (Fin 2) (Fin 2) T) (hsym : Bmᵀ = Bm) (hunimod : IsUnit Bm.det)
    (hhyp : IsHyperbolic2 (Bm.map (algebraMap T (FractionRing T)))) :
    ∀ v : Fin 2 → FractionRing T, v ≠ 0 → v ⬝ᵥ (Bm.map (algebraMap T (FractionRing T)) *ᵥ v) = 0 →
      ∃ e f : Fin 2 → T, IsUnit (Matrix.of ![e, f]).det ∧ e ⬝ᵥ (Bm *ᵥ e) = 0 ∧ f ⬝ᵥ (Bm *ᵥ f) = 0 ∧
        ∀ u : Fin 2 → T, (∃ c : FractionRing T, (fun i => algebraMap T (FractionRing T) (u i)) = c • v) ↔
          ∃ t : T, u = t • e := by
  intro v hv0 hviso
  obtain ⟨P, hP, hG00, hG11⟩ := lem_24_5_proved h2 Bm hsym hunimod hhyp
  have hGsym : (Pᵀ * Bm * P) 1 0 = (Pᵀ * Bm * P) 0 1 := by
    have hT : (Pᵀ * Bm * P)ᵀ = Pᵀ * Bm * P := by
      rw [transpose_mul, transpose_mul, transpose_transpose, hsym, Matrix.mul_assoc]
    have h := congrFun (congrFun hT 0) 1
    simpa [transpose_apply] using h
  have hβ : IsUnit ((Pᵀ * Bm * P) 0 1) := by
    have hd : IsUnit (Pᵀ * Bm * P).det := by
      rw [det_mul, det_mul, det_transpose]
      exact (hP.mul hunimod).mul hP
    rw [det_fin_two, hG00, hG11, hGsym, zero_mul, zero_sub] at hd
    have hd' := hd.neg
    rw [neg_neg] at hd'
    exact isUnit_of_mul_isUnit_left hd'
  have hGK : (P.map (algebraMap T (FractionRing T)))ᵀ * Bm.map (algebraMap T (FractionRing T)) *
      P.map (algebraMap T (FractionRing T)) = (Pᵀ * Bm * P).map (algebraMap T (FractionRing T)) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hK : (P.map (algebraMap T (FractionRing T))).det = algebraMap T (FractionRing T) P.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have h2K : (2 : FractionRing T) ≠ 0 := by
    have h := (h2.map (algebraMap T (FractionRing T))).ne_zero
    rwa [map_ofNat] at h
  have hiso := iso_on_axis (P.map (algebraMap T (FractionRing T))) (Bm.map (algebraMap T (FractionRing T))) v
    (by rw [hK]; exact (hP.map _).ne_zero)
    (by rw [hGK, Matrix.map_apply, hG00, map_zero]) (by rw [hGK, Matrix.map_apply, hG11, map_zero])
    (by rw [hGK, Matrix.map_apply, Matrix.map_apply, hGsym])
    (by rw [hGK, Matrix.map_apply]; exact (hβ.map _).ne_zero) h2K hv0 hviso
  have hisoe : (fun k => P k 0) ⬝ᵥ (Bm *ᵥ fun k => P k 0) = 0 := by rw [gram_entry]; exact hG00
  have hisof : (fun k => P k 1) ⬝ᵥ (Bm *ᵥ fun k => P k 1) = 0 := by rw [gram_entry]; exact hG11
  have hdetef : (Matrix.of ![fun k => P k 0, fun k => P k 1]).det = P.det := by
    rw [det_fin_two, det_fin_two]
    simp
    ring
  have hdetfe : (Matrix.of ![fun k => P k 1, fun k => P k 0]).det = -P.det := by
    rw [det_fin_two, det_fin_two]
    simp
    ring
  rcases hiso with ⟨c, hc, hvc⟩ | ⟨c, hc, hvc⟩
  · refine ⟨fun k => P k 0, fun k => P k 1, by rw [hdetef]; exact hP, hisoe, hisof, fun u => ?_⟩
    exact sat_line _ _ (by rw [hdetef]; exact hP) v c hc (by rw [hvc]; rfl) u
  · refine ⟨fun k => P k 1, fun k => P k 0, by rw [hdetfe]; exact hP.neg, hisof, hisoe, fun u => ?_⟩
    exact sat_line _ _ (by rw [hdetfe]; exact hP.neg) v c hc (by rw [hvc]; rfl) u

end Osserman.Proofs.Six2
