/-
Osserman/Proofs/S86.lean — §8.6 of paper 013: multiplicities at most two besides one of 7 or 8, [Nik2006, Lemma 3.3]
with up to eight columns (rows s8_6_shift, s8_6_fields, s8_6_normalize, s8_6_identities, s8_6_diag, s8_6_d_one,
s8_6_clifford_form, s8_6_clifford; statements copied verbatim from Osserman/Paper/Statements8.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Identities. At a unit `x`, the `r = 15 - M` fields are orthonormal reduced eigenvectors `p_j` of `Λ_j ≠ 0`; with
`W = E_0(x) ⊕ ℝx` (dimension `M + 1`) they fill `ℝ^16`, so a matrix `F` with `Fp_j = c_jp_j` and `F = 0` on `W` is
`∑ c_jp_jp_jᵀ` (`F = A`, `c = Λ`; `F = A²`, `c = Λ²`). Homogeneity of degree `d` gives the identities at every `x`.
Diagonal: entry `(a,a)` of the third identity, as polynomials, is `q·∑(Λ_jP_{ja})² = q^{d-1}(A²)_{aa}`; cancel `q`.
`d = 1`: for `d ≥ 3` Lemma 3.11 (`sos_dvd`) makes every component divisible by `q`. Clifford form: linear fields
`J_jx`, orthonormal and tangent, form a Clifford structure (`thm_E_frame_clifford`), and `A = ∑ Λ_j(J_jx)(J_jx)ᵀ`.
Fields: the reduced spectrum at one unit point (`card_eig_jacobi`), [Nik2006, Lemma 3.1] for each nonzero eigenvalue,
indexed by `Σ t, Fin (m t)` (fields of different eigenvalues are orthogonal). Normalize: strip the largest power of
`q` from each field, multiply by `q^((d - e_j)/2)` for the largest remaining degree `d`.
-/
import Osserman.Proofs.S8Gen
import Osserman.Proofs.ThmEElementary
import Osserman.Proofs.ThmEFrames
import Osserman.Proofs.Rem72b

namespace Osserman.Proofs.S86

open Osserman Matrix MvPolynomial

/-- Row `s8_6_shift`. -/
theorem s8_6_shift_proved (R : CurvTensor 16) (μ0 : ℝ) (M : ℕ) (h : SmallMultHyp R μ0 M) :
    ∃ R0 : CurvTensor 16, (∀ u v z, R0.op u v z = R.op u v z - μ0 • R1fun u v z) ∧ SmallMultHyp R0 0 M ∧
      (R0.IsClifford ↔ R.IsClifford) := by
  obtain ⟨R0, hop, -, hO, hC⟩ := Rem72a.shift_R1_proved R μ0
  obtain ⟨hOss, hM, hmult, hle⟩ := h
  have shift := ThmEElementary.thm_E_shift_proved R R0 μ0 hop
  refine ⟨R0, hop, ⟨hO.mpr hOss, hM, fun x hx => ?_, fun x hx μ hμ => ?_⟩, hC⟩
  · have e := shift x hx μ0
    rw [sub_self] at e
    rw [e, hmult x hx]
  · have e := shift x hx (μ + μ0)
    rw [add_sub_cancel_right] at e
    rw [e]
    exact hle x hx _ fun h' => hμ (by linarith)

/-! ### Filling `ℝ^16` -/

/-- Orthonormal `p_j` and a subspace `W ⊥ p_j` of complementary dimension: a matrix `F` with `Fp_j = c_jp_j` and
`F = 0` on `W` is `∑ c_jp_jp_jᵀ`. -/
lemma fill {r : ℕ} {p : Fin r → Vec 16} (hpo : ∀ j l, p j ⬝ᵥ p l = if j = l then 1 else 0)
    {W : Submodule ℝ (Vec 16)} (hWp : ∀ w ∈ W, ∀ j, p j ⬝ᵥ w = 0) (hdim : Module.finrank ℝ W + r = 16)
    {F : Matrix (Fin 16) (Fin 16) ℝ} (c : Fin r → ℝ) (hFp : ∀ j, F *ᵥ p j = c j • p j)
    (hFW : ∀ w ∈ W, F *ᵥ w = 0) : ∑ j, c j • vecMulVec (p j) (p j) = F := by
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ j, c j • vecMulVec (p j) (p j) - F := ⟨_, rfl⟩
  have hQv : ∀ v, (∑ j, c j • vecMulVec (p j) (p j)) *ᵥ v = ∑ j, (c j * (p j ⬝ᵥ v)) • p j := fun v => by
    rw [Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec, Spectral.vecMulVec_self_mulVec, smul_smul]
  have hspan : Submodule.span ℝ (Set.range p) ≤ LinearMap.ker (Matrix.toLin' D) := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.toLin'_apply, hD, Matrix.sub_mulVec, hQv, hFp,
      Finset.sum_eq_single l]
    · rw [hpo, ite_eq_left rfl, mul_one, sub_self]
    · intro j _ hj
      rw [hpo, ite_eq_right hj, mul_zero, zero_smul]
    · intro hl
      exact absurd (Finset.mem_univ l) hl
  have hW : W ≤ LinearMap.ker (Matrix.toLin' D) := fun w hw => by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, hD, Matrix.sub_mulVec, hQv, hFW w hw, sub_zero]
    exact Finset.sum_eq_zero fun j _ => by rw [hWp w hw j, mul_zero, zero_smul]
  have hinf : Submodule.span ℝ (Set.range p) ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvp, hvW⟩ := Submodule.mem_inf.mp hv
    have hle : Submodule.span ℝ (Set.range p) ≤ LinearMap.ker (Spectral.dotL v) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      show v ⬝ᵥ p j = 0
      rw [dotProduct_comm]
      exact hWp v hvW j
    rw [Submodule.mem_bot]
    exact dotProduct_self_eq_zero.mp (LinearMap.mem_ker.mp (hle hvp))
  have htop : Submodule.span ℝ (Set.range p) ⊔ W = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℝ (Set.range p)) W
    rw [hinf, finrank_bot, add_zero, finrank_span_eq_card (S8Gen.orthonormal_li hpo), Fintype.card_fin] at h
    rw [h, Module.finrank_fin_fun]
    omega
  have hker : (⊤ : Submodule ℝ (Vec 16)) ≤ LinearMap.ker (Matrix.toLin' D) := by
    rw [← htop]
    exact sup_le hspan hW
  have hall : ∀ v, D *ᵥ v = 0 := fun v => by
    have h := hker (Submodule.mem_top (x := v))
    rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at h
  rw [← sub_eq_zero, ← hD]
  exact Matrix.ext_iff_mulVec.mpr fun v => by rw [hall v, Matrix.zero_mulVec]

/-- `PΛPᵀ = ∑ Λ_j P_jP_jᵀ` for the matrix of fields `P`. -/
lemma fieldMat_diag {r : ℕ} (P : Fin r → Fin 16 → MvPolynomial (Fin 16) ℝ) (w : Fin r → ℝ) (x : Vec 16) :
    fieldMat P x * diagonal w * (fieldMat P x)ᵀ =
      ∑ j, w j • vecMulVec (evalField (P j) x) (evalField (P j) x) := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, fieldMat, Matrix.of_apply, Matrix.sum_apply,
    Matrix.smul_apply, vecMulVec_apply, evalField, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `PᵀP = q^d I`. -/
lemma gram {r : ℕ} (P : Fin r → Fin 16 → MvPolynomial (Fin 16) ℝ) {d : ℕ}
    (hPo : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ d else 0)
    (x : Vec 16) : (fieldMat P x)ᵀ * fieldMat P x = (x ⬝ᵥ x) ^ d • (1 : Matrix (Fin r) (Fin r) ℝ) := by
  ext j l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, fieldMat, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact hPo x j l

/-- At a unit `u`: `∑ Λ_jp_jp_jᵀ = A` and `∑ Λ_j²p_jp_jᵀ = A²`. -/
lemma unit_sums {R : CurvTensor 16} {M : ℕ} (h : SmallMultHyp R 0 M) {Λ : Fin (15 - M) → ℝ}
    {P : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ} {d : ℕ} (hΛ : ∀ j, Λ j ≠ 0)
    (hPe : ∀ j, IsEigenfield R (Λ j) (P j))
    (hPo : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ d else 0)
    {u : Vec 16} (hu : u ⬝ᵥ u = 1) :
    ∑ j, Λ j • vecMulVec (evalField (P j) u) (evalField (P j) u) = R.jacobi u ∧
      ∑ j, (Λ j ^ 2) • vecMulVec (evalField (P j) u) (evalField (P j) u) = R.jacobi u * R.jacobi u := by
  have hpe := fun j => S8Gen.unit_eig (hPe j) hu
  have hpo : ∀ j l, evalField (P j) u ⬝ᵥ evalField (P l) u = if j = l then 1 else 0 := fun j l => by
    rw [hPo, hu, one_pow]
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hWp : ∀ w ∈ Spectral.Esp R u 0 ⊔ Submodule.span ℝ {u}, ∀ j, evalField (P j) u ⬝ᵥ w = 0 := by
    have hle : Spectral.Esp R u 0 ⊔ Submodule.span ℝ {u} ≤
        ⨅ j, LinearMap.ker (Spectral.dotL (evalField (P j) u)) := by
      refine sup_le (fun y hy => (Submodule.mem_iInf _).mpr fun j => LinearMap.mem_ker.mpr ?_) ?_
      · show evalField (P j) u ⬝ᵥ y = 0
        rw [dotProduct_comm]
        exact S83.esp_dot_eig (hΛ j).symm hy (hpe j).1
      · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
        refine (Submodule.mem_iInf _).mpr fun j => LinearMap.mem_ker.mpr ?_
        show evalField (P j) u ⬝ᵥ u = 0
        rw [dotProduct_comm]
        exact (hpe j).2
    intro w hw j
    exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp (hle hw) j)
  have hdim : Module.finrank ℝ ↥(Spectral.Esp R u 0 ⊔ Submodule.span ℝ {u}) + (15 - M) = 16 := by
    rw [S83.dim_add_one hu0 fun y hy => by rw [dotProduct_comm]; exact (S8Gen.mem_Esp'.mp hy).2]
    have hM : Module.finrank ℝ ↥(Spectral.Esp R u 0) = M := h.2.2.1 u hu
    rcases h.2.1 with rfl | rfl <;> omega
  have hW0 : ∀ w ∈ Spectral.Esp R u 0 ⊔ Submodule.span ℝ {u}, R.jacobi u *ᵥ w = 0 := by
    have hle : Spectral.Esp R u 0 ⊔ Submodule.span ℝ {u} ≤ LinearMap.ker (Matrix.toLin' (R.jacobi u)) := by
      refine sup_le (fun y hy => ?_) ?_
      · rw [LinearMap.mem_ker, Matrix.toLin'_apply, (S8Gen.mem_Esp'.mp hy).1, zero_smul]
      · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker, Matrix.toLin'_apply,
          Spectral.jacobi_self]
    intro w hw
    have e := hle hw
    rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at e
  refine ⟨fill hpo hWp hdim Λ (fun j => (hpe j).1) hW0, fill hpo hWp hdim (fun j => Λ j ^ 2) (fun j => ?_)
    (fun w hw => ?_)⟩
  · show (R.jacobi u * R.jacobi u) *ᵥ evalField (P j) u = (Λ j ^ 2) • evalField (P j) u
    rw [← Matrix.mulVec_mulVec, (hpe j).1, Matrix.mulVec_smul, (hpe j).1, smul_smul, sq]
  · rw [← Matrix.mulVec_mulVec, hW0 w hw, Matrix.mulVec_zero]

/-- Row `s8_6_identities`. -/
theorem s8_6_identities_proved (R : CurvTensor 16) (M : ℕ) (h : SmallMultHyp R 0 M) (Λ : Fin (15 - M) → ℝ)
    (P : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ) (d : ℕ) (hd : Odd d)
    (hhom : ∀ j a, (P j a).IsHomogeneous d) (hΛ : ∀ j, Λ j ≠ 0) (hPe : ∀ j, IsEigenfield R (Λ j) (P j))
    (hPo : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ d else 0) :
    ∀ x : Vec 16, (fieldMat P x)ᵀ * fieldMat P x = (x ⬝ᵥ x) ^ d • (1 : Matrix (Fin (15 - M)) (Fin (15 - M)) ℝ) ∧
      fieldMat P x * diagonal Λ * (fieldMat P x)ᵀ = (x ⬝ᵥ x) ^ (d - 1) • R.jacobi x ∧
      (x ⬝ᵥ x) • (fieldMat P x * diagonal (fun j => Λ j ^ 2) * (fieldMat P x)ᵀ) =
        (x ⬝ᵥ x) ^ (d - 1) • (R.jacobi x * R.jacobi x) := by
  intro x
  refine ⟨gram P hPo x, ?_⟩
  obtain ⟨s, u, hu, rfl⟩ := Spectral.exists_unit_scale x
  obtain ⟨hA, hA2⟩ := unit_sums h hΛ hPe hPo hu
  have hev : ∀ j, evalField (P j) (s • u) = s ^ d • evalField (P j) u := fun j =>
    S8Tools.evalField_smul (hhom j) s u
  have hq : (s • u) ⬝ᵥ (s • u) = s * s := by
    rw [smul_dotProduct, dotProduct_smul, hu, smul_eq_mul, smul_eq_mul, mul_one]
  obtain ⟨t, rfl⟩ := hd
  have hd1 : 2 * t + 1 - 1 = 2 * t := by omega
  rw [fieldMat_diag, fieldMat_diag, hq, hd1, Spectral.jacobi_smul, Matrix.smul_mul, Matrix.mul_smul, ← hA2, ← hA]
  simp only [hev, smul_vecMulVec, vecMulVec_smul, smul_smul, Finset.smul_sum]
  constructor
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring

/-! ### `d = 1` -/

lemma sqP_ne_zero : sqP 16 ≠ 0 := by
  intro h
  have e := congrArg (MvPolynomial.eval (Pi.single 0 1 : Vec 16)) h
  rw [Poly.eval_sqP, map_zero] at e
  simp at e

/-- Row `s8_6_diag`. -/
theorem s8_6_diag_proved (R : CurvTensor 16) (M : ℕ) (h : SmallMultHyp R 0 M) (Λ : Fin (15 - M) → ℝ)
    (P : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ) (d : ℕ) (hd : Odd d) (hd3 : 3 ≤ d)
    (hhom : ∀ j a, (P j a).IsHomogeneous d) (hΛ : ∀ j, Λ j ≠ 0) (hPe : ∀ j, IsEigenfield R (Λ j) (P j))
    (hPo : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ d else 0) :
    15 - M ≤ 8 ∧ ∀ a : Fin 16, sqP 16 ∣ ∑ j, (MvPolynomial.C (Λ j) * P j a) ^ 2 := by
  refine ⟨by rcases h.2.1 with rfl | rfl <;> norm_num, fun a => ?_⟩
  have hid := fun x => (s8_6_identities_proved R M h Λ P d hd hhom hΛ hPe hPo x).2.2
  have hpoly : sqP 16 * ∑ j, (MvPolynomial.C (Λ j) * P j a) ^ 2 =
      sqP 16 ^ (d - 1) * ∑ k, S8Tools.jacP R a k * S8Tools.jacP R k a := by
    refine MvPolynomial.funext fun x => ?_
    have e := congrFun (congrFun (hid x) a) a
    rw [fieldMat_diag] at e
    simp only [Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, Matrix.mul_apply, smul_eq_mul, evalField] at e
    simp only [map_mul, map_sum, map_pow, MvPolynomial.eval_C, Poly.eval_sqP, S8Tools.eval_jacP]
    rw [← e]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨e2, rfl⟩ : ∃ e2, d = e2 + 3 := ⟨d - 3, by omega⟩
  have hpow : sqP 16 ^ (e2 + 3 - 1) = sqP 16 * (sqP 16 * sqP 16 ^ e2) := by
    rw [show e2 + 3 - 1 = e2 + 2 by omega]
    ring
  rw [hpow, mul_assoc] at hpoly
  rw [mul_left_cancel₀ sqP_ne_zero hpoly]
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

/-- Row `s8_6_d_one`. -/
theorem s8_6_d_one_proved (R : CurvTensor 16) (M : ℕ) (h : SmallMultHyp R 0 M) (Λ : Fin (15 - M) → ℝ)
    (P : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ) (d : ℕ) (hd : Odd d)
    (hhom : ∀ j a, (P j a).IsHomogeneous d) (hΛ : ∀ j, Λ j ≠ 0) (hPe : ∀ j, IsEigenfield R (Λ j) (P j))
    (hPo : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ d else 0)
    (hnd : ∃ j a, ¬ sqP 16 ∣ P j a) : d = 1 := by
  by_contra hne
  have hd3 : 3 ≤ d := by
    obtain ⟨t, rfl⟩ := hd
    omega
  obtain ⟨hr, hdiv⟩ := s8_6_diag_proved R M h Λ P d hd hd3 hhom hΛ hPe hPo
  obtain ⟨j, a, hja⟩ := hnd
  apply hja
  have hsos := S8Tools.sos_dvd hr (fun j => MvPolynomial.C (Λ j) * P j a) (fun _ => 1) (Or.inl fun _ => one_pos)
    (by simpa using hdiv a) j
  exact S8Tools.dvd_of_C_mul (hΛ j) hsos

/-- Row `s8_6_clifford_form`. -/
theorem s8_6_clifford_form_proved (R : CurvTensor 16) (M : ℕ) (h : SmallMultHyp R 0 M) (Λ : Fin (15 - M) → ℝ)
    (P : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ) (hhom : ∀ j a, (P j a).IsHomogeneous 1)
    (hΛ : ∀ j, Λ j ≠ 0) (hPe : ∀ j, IsEigenfield R (Λ j) (P j))
    (hPo : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then x ⬝ᵥ x else 0) :
    ∃ J : Fin (15 - M) → Matrix (Fin 16) (Fin 16) ℝ, IsCliffordStr J ∧ (∀ j, (J j)ᵀ * J j = 1) ∧
      (∀ j (x : Vec 16), evalField (P j) x = J j *ᵥ x) ∧ (∀ x, R.jacobi x = ∑ j, Λ j • jfam (J j) x) ∧
      R.IsClifford := by
  choose J hJ using fun j => ThmEFrames.thm_E_linear_fields_proved (P j) 1 odd_one (by norm_num) (hhom j)
  have horth : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ a b, (J a *ᵥ x) ⬝ᵥ (J b *ᵥ x) = if a = b then 1 else 0 :=
    fun x hx a b => by rw [← hJ a x, ← hJ b x, hPo, hx]
  have hperp : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ a, x ⬝ᵥ (J a *ᵥ x) = 0 := fun x _ a => by
    rw [← hJ a x]
    exact (S8Gen.mem_Esp'.mp (hPe a x)).2
  obtain ⟨hC, hO⟩ := ThmEFrames.thm_E_frame_clifford_proved J horth hperp
  have hPo1 : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ 1 else 0 :=
    fun x j l => by rw [pow_one]; exact hPo x j l
  have hjac : ∀ x, R.jacobi x = ∑ j, Λ j • jfam (J j) x := fun x => by
    have e := (s8_6_identities_proved R M h Λ P 1 odd_one hhom hΛ hPe hPo1 x).2.1
    rw [fieldMat_diag, Nat.sub_self, pow_zero, one_smul] at e
    rw [← e]
    simp only [hJ, jfam]
  exact ⟨J, hC, hO, hJ, hjac, ⟨15 - M, J, hC, 0, Λ, fun x => by rw [hjac, zero_smul, zero_add]; rfl⟩⟩

/-! ### The fields: [Nik2006, Lemma 3.1] for each nonzero eigenvalue -/

/-- The reduced spectrum of an Osserman `R` with `0` a reduced eigenvalue: distinct values `ev`, multiplicities `m`. -/
lemma spectrum (R : CurvTensor 16) (hO : R.IsOsserman) {M : ℕ} (hM : 0 < M)
    (h0 : ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x 0 = M) :
    ∃ (k : ℕ) (ev : Fin k → ℝ) (m : Fin k → ℕ), Function.Injective ev ∧ (∀ i, 0 < m i) ∧ ∑ i, m i = 15 ∧
      (∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i, R.redMult x (ev i) = m i) ∧ ∃ j, ev j = 0 := by
  classical
  obtain ⟨x0, hx0⟩ : ∃ x0 : Vec 16, x0 ⬝ᵥ x0 = 1 := ⟨Pi.single 0 1, by simp⟩
  let S : Finset ℝ := Finset.univ.image (OssTop.jacobi_isHermitian R x0).eigenvalues
  have hcard := Rem72b.card_eig_jacobi R hx0
  have h0S : (0 : ℝ) ∈ S := by
    have hc := hcard 0
    rw [ite_eq_left rfl] at hc
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter fun i =>
      (OssTop.jacobi_isHermitian R x0).eigenvalues i = 0).card by omega)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  refine ⟨S.card, fun i => (S.equivFin.symm i : ℝ), fun i => R.redMult x0 (S.equivFin.symm i),
    fun i i' hii => S.equivFin.symm.injective (Subtype.ext hii), fun i => ?_, ?_,
    fun x hx i => hO x x0 hx hx0 _, ⟨S.equivFin ⟨0, h0S⟩, by simp⟩⟩
  · show 0 < R.redMult x0 (S.equivFin.symm i)
    obtain ⟨i', -, hi'⟩ := Finset.mem_image.mp (S.equivFin.symm i).2
    by_cases hs : (S.equivFin.symm i : ℝ) = 0
    · rw [hs, h0 x0 hx0]
      exact hM
    · have hc := hcard (S.equivFin.symm i)
      rw [ite_eq_right hs, add_zero] at hc
      rw [← hc]
      exact Finset.card_pos.mpr ⟨i', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩⟩
  · show ∑ i : Fin S.card, R.redMult x0 (S.equivFin.symm i) = 15
    have h1 : ∑ i : Fin S.card, R.redMult x0 (S.equivFin.symm i) = ∑ s ∈ S, R.redMult x0 s := by
      rw [← Finset.sum_coe_sort S]
      exact Equiv.sum_comp S.equivFin.symm (fun s : S => R.redMult x0 s)
    have h16 : ∑ s ∈ S, (R.redMult x0 s + if s = 0 then 1 else 0) = 16 := by
      rw [Finset.sum_congr rfl fun s _ => (hcard s).symm, ← Finset.card_eq_sum_card_image]
      simp
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' S 0 (fun _ => 1), ite_eq_left h0S] at h16
    omega

/-- Row `s8_6_fields`. -/
theorem s8_6_fields_proved (R : CurvTensor 16) (M : ℕ) (h : SmallMultHyp R 0 M) :
    15 - M ≤ 8 ∧ ∃ (Λ : Fin (15 - M) → ℝ) (P : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ)
      (dg : Fin (15 - M) → ℕ), (∀ j, Odd (dg j)) ∧ (∀ j a, (P j a).IsHomogeneous (dg j)) ∧ (∀ j, Λ j ≠ 0) ∧
      (∀ j, IsEigenfield R (Λ j) (P j)) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then 1 else 0 := by
  classical
  refine ⟨by rcases h.2.1 with rfl | rfl <;> norm_num, ?_⟩
  obtain ⟨hO, hM, h0, hle⟩ := h
  obtain ⟨x0, hx0⟩ : ∃ x0 : Vec 16, x0 ⬝ᵥ x0 = 1 := ⟨Pi.single 0 1, by simp⟩
  obtain ⟨k, ev, m, hev, hpos, hsum, hpat, jz, hjz⟩ :=
    spectrum R hO (by rcases hM with rfl | rfl <;> norm_num) h0
  have hsmall : ∀ t : {i // ev i ≠ 0}, m t.1 = 1 ∨ m t.1 = 2 := fun t => by
    have h1 := hpos t.1
    have h2 := hle x0 hx0 (ev t.1) t.2
    rw [hpat x0 hx0] at h2
    omega
  choose dT ET hodd _hdk hhomT hunitT using fun t : {i // ev i ≠ 0} =>
    Osserman.Cited.nik2006_lemma_3_1 R hO ev hev m hpos hsum hpat ⟨jz, hjz⟩ t.1 t.2 (hsmall t)
  have hcard : Fintype.card (Σ t : {i // ev i ≠ 0}, Fin (m t.1)) = 15 - M := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    have hz : m jz = M := by rw [← hpat x0 hx0, hjz, h0 x0 hx0]
    have herase : Finset.univ.erase jz = Finset.univ.filter fun i => ev i ≠ 0 := by
      ext i
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter, true_and]
      exact ⟨fun hi he => hi (hev (he.trans hjz.symm)), fun hi he => hi (he ▸ hjz)⟩
    have hsplit := Finset.add_sum_erase Finset.univ m (Finset.mem_univ jz)
    rw [herase, hsum, hz, Finset.sum_subtype (p := fun i => ev i ≠ 0) _ (fun i => by simp) m] at hsplit
    omega
  obtain σ := (Fintype.equivFinOfCardEq hcard).symm
  have key : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ p p' : Σ t : {i // ev i ≠ 0}, Fin (m t.1),
      evalField (ET p.1 p.2) x ⬝ᵥ evalField (ET p'.1 p'.2) x = if p = p' then 1 else 0 := by
    rintro x hx ⟨t, a⟩ ⟨t', b⟩
    by_cases htt : t = t'
    · subst htt
      rw [(hunitT t x hx).1 a b]
      by_cases hab : a = b
      · subst hab
        simp
      · have hp : (⟨t, a⟩ : Σ t : {i // ev i ≠ 0}, Fin (m t.1)) ≠ ⟨t, b⟩ :=
          fun hp => hab (eq_of_heq (Sigma.mk.inj_iff.mp hp).2)
        rw [ite_eq_right hab, ite_eq_right hp]
    · rw [ite_eq_right fun hp => htt (Sigma.mk.inj_iff.mp hp).1]
      have hne : ev t.1 ≠ ev t'.1 := fun he => htt (Subtype.ext (hev he))
      exact S83.esp_dot_eig hne ((hunitT t x hx).2.1 a) (S8Gen.mem_Esp'.mp ((hunitT t' x hx).2.1 b)).1
  refine ⟨fun n => ev (σ n).1.1, fun n => ET (σ n).1 (σ n).2, fun n => dT (σ n).1, fun n => hodd _,
    fun n a => hhomT (σ n).1 (σ n).2 a, fun n => (σ n).1.2, fun n => ?_, fun x hx n n' => ?_⟩
  · have e := S8Tools.eigenfield_of_unit (hhomT (σ n).1 (σ n).2) (ev (σ n).1.1)
      (fun x hx => (hunitT (σ n).1 x hx).2.1 (σ n).2) 0
    simpa using e
  · refine (key x hx (σ n) (σ n')).trans ?_
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (σ.injective h1) h2
    · exact absurd (congrArg σ h2) h1
    · rfl

/-! ### Normalizing: divide by the largest power of `q`, homogenize to the largest degree -/

/-- A nonzero homogeneous polynomial divisible by `q` has degree at least two. -/
lemma two_le_of_dvd {F : MvPolynomial (Fin 16) ℝ} {n : ℕ} (hF : F.IsHomogeneous n) (h0 : F ≠ 0)
    (hq : sqP 16 ∣ F) : 2 ≤ n := by
  obtain ⟨g, rfl⟩ := hq
  have hg : g ≠ 0 := fun h => h0 (by rw [h, mul_zero])
  rw [← hF.totalDegree h0, totalDegree_mul_of_isDomain sqP_ne_zero hg,
    Poly.sqP_isHomogeneous.totalDegree sqP_ne_zero]
  omega

/-- A homogeneous polynomial of degree `m + 2` divisible by `q` is `q` times a homogeneous one of degree `m`. -/
lemma dvd_homog_eq {F : MvPolynomial (Fin 16) ℝ} {m : ℕ} (hF : F.IsHomogeneous (m + 2)) (hq : sqP 16 ∣ F) :
    ∃ g : MvPolynomial (Fin 16) ℝ, g.IsHomogeneous m ∧ F = sqP 16 * g := by
  obtain ⟨g, rfl⟩ := hq
  refine ⟨homogeneousComponent m g, homogeneousComponent_isHomogeneous m g, ?_⟩
  have comp (k : ℕ) : homogeneousComponent (m + 2) (sqP 16 * homogeneousComponent k g) =
      if m + 2 = 2 + k then sqP 16 * homogeneousComponent k g else 0 :=
    homogeneousComponent_of_mem (Poly.sqP_isHomogeneous.mul (homogeneousComponent_isHomogeneous k g))
  have key : homogeneousComponent (m + 2) (sqP 16 * g) = sqP 16 * homogeneousComponent m g := by
    conv_lhs => rw [← sum_homogeneousComponent g]
    rw [Finset.mul_sum, map_sum, Finset.sum_eq_single m]
    · rw [comp]
      exact ite_eq_left (by omega)
    · intro k _ hk
      rw [comp]
      exact ite_eq_right (by omega)
    · intro h1
      have hlt : g.totalDegree < m := by simpa [Finset.mem_range] using h1
      rw [homogeneousComponent_eq_zero m g hlt, mul_zero, map_zero]
  rw [← key, homogeneousComponent_of_mem hF, ite_eq_left rfl]

/-- Strip the largest power of `q` common to all components of a nonzero homogeneous field. -/
lemma strip (n : ℕ) : ∀ F : Fin 16 → MvPolynomial (Fin 16) ℝ, (∀ a, (F a).IsHomogeneous n) → (∃ a, F a ≠ 0) →
    ∃ (k e : ℕ) (Q : Fin 16 → MvPolynomial (Fin 16) ℝ), n = 2 * k + e ∧ (∀ a, (Q a).IsHomogeneous e) ∧
      (∀ a, F a = sqP 16 ^ k * Q a) ∧ ∃ a, ¬ sqP 16 ∣ Q a := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F hF hne
    by_cases hall : ∀ a, sqP 16 ∣ F a
    · obtain ⟨a0, ha0⟩ := hne
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := two_le_of_dvd (hF a0) ha0 (hall a0); omega⟩
      choose G hG hFG using fun a => dvd_homog_eq (hF a) (hall a)
      have hG0 : G a0 ≠ 0 := fun h0 => ha0 (by rw [hFG a0, h0, mul_zero])
      obtain ⟨k, e, Q, he, hQ, hGQ, hnd⟩ := ih m (by omega) G hG ⟨a0, hG0⟩
      exact ⟨k + 1, e, Q, by omega, hQ, fun a => by rw [hFG a, hGQ a]; ring, hnd⟩
    · rw [not_forall] at hall
      exact ⟨0, n, F, by omega, hF, fun a => by rw [pow_zero, one_mul], hall⟩

/-- Row `s8_6_normalize`. -/
theorem s8_6_normalize_proved (R : CurvTensor 16) (M : ℕ) (h : SmallMultHyp R 0 M) (Λ : Fin (15 - M) → ℝ)
    (P : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ) (dg : Fin (15 - M) → ℕ) (hodd : ∀ j, Odd (dg j))
    (hhom : ∀ j a, (P j a).IsHomogeneous (dg j)) (hΛ : ∀ j, Λ j ≠ 0) (hPe : ∀ j, IsEigenfield R (Λ j) (P j))
    (hPo : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then 1 else 0) :
    ∃ (d : ℕ) (P' : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ), Odd d ∧
      (∀ j a, (P' j a).IsHomogeneous d) ∧ (∀ j, IsEigenfield R (Λ j) (P' j)) ∧
      (∀ (x : Vec 16) j l, evalField (P' j) x ⬝ᵥ evalField (P' l) x = if j = l then (x ⬝ᵥ x) ^ d else 0) ∧
      ∃ j a, ¬ sqP 16 ∣ P' j a := by
  have hx0 : (Pi.single 0 1 : Vec 16) ⬝ᵥ Pi.single 0 1 = 1 := by simp
  have hne : ∀ j, ∃ a, P j a ≠ 0 := fun j => by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hz : evalField (P j) (Pi.single 0 1) = 0 := funext fun a => by simp [evalField, hcon a]
    have e := hPo _ hx0 j j
    rw [hz, zero_dotProduct] at e
    simp at e
  choose k e Q hdeg hQh hPQ hnd using fun j => strip (dg j) (P j) (hhom j) (hne j)
  have hQu : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ j, evalField (Q j) x = evalField (P j) x := fun x hx j => by
    funext a
    simp only [evalField, hPQ j a, map_mul, map_pow, Poly.eval_sqP, hx, one_pow, one_mul]
  have hoe : ∀ j, Odd (e j) := fun j => by
    obtain ⟨r, hr⟩ := hodd j
    exact ⟨r - k j, by have := hdeg j; omega⟩
  have hr : (Finset.univ : Finset (Fin (15 - M))).Nonempty :=
    ⟨⟨0, by rcases h.2.1 with rfl | rfl <;> norm_num⟩, Finset.mem_univ _⟩
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ e hr
  have ht : ∀ j, ∃ t, e j0 = 2 * t + e j := fun j => by
    obtain ⟨r1, h1⟩ := hoe j0
    obtain ⟨r2, h2⟩ := hoe j
    have := hj0 j (Finset.mem_univ _)
    exact ⟨r1 - r2, by omega⟩
  choose t hte using ht
  obtain ⟨P', hP'⟩ : ∃ P' : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ,
      ∀ j, P' j = fun a => sqP 16 ^ t j * Q j a := ⟨_, fun _ => rfl⟩
  have hP'h : ∀ j a, (P' j a).IsHomogeneous (e j0) := fun j a => by
    rw [hP', hte j]
    exact (Poly.sqP_isHomogeneous.pow (t j)).mul (hQh j a)
  have hP'u : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ j, evalField (P' j) x = evalField (P j) x := fun x hx j => by
    rw [← hQu x hx j, hP']
    funext a
    simp only [evalField, map_mul, map_pow, Poly.eval_sqP, hx, one_pow, one_mul]
  refine ⟨e j0, P', hoe j0, hP'h, fun j => ?_, fun x j l => ?_, j0, ?_⟩
  · rw [hP']
    exact S8Tools.eigenfield_of_unit (hQh j) (Λ j) (fun x hx => by
      rw [hQu x hx j]
      simpa [hx] using hPe j x) (t j)
  · obtain ⟨s, u, hu, rfl⟩ := Spectral.exists_unit_scale x
    have hq : (s • u) ⬝ᵥ (s • u) = s * s := by
      rw [smul_dotProduct, dotProduct_smul, hu, smul_eq_mul, smul_eq_mul, mul_one]
    rw [S8Tools.evalField_smul (hP'h j) s u, S8Tools.evalField_smul (hP'h l) s u, smul_dotProduct,
      dotProduct_smul, hP'u u hu j, hP'u u hu l, hPo u hu j l, hq]
    split_ifs
    · simp only [smul_eq_mul, mul_one]
      ring
    · simp
  · obtain ⟨a, ha⟩ := hnd j0
    refine ⟨a, ?_⟩
    have ht0 : t j0 = 0 := by have := hte j0; omega
    rw [hP', ht0, pow_zero]
    show ¬ sqP 16 ∣ 1 * Q j0 a
    rw [one_mul]
    exact ha

/-! ### §8.6, the conclusion -/

/-- Row `s8_6_clifford`. -/
theorem s8_6_clifford_proved (R : CurvTensor 16) (μ0 : ℝ) (M : ℕ) (h : SmallMultHyp R μ0 M) : R.IsClifford := by
  obtain ⟨R0, -, h0, hiff⟩ := s8_6_shift_proved R μ0 M h
  obtain ⟨-, Λ, P, dg, hodd, hhom, hΛ, hPe, hPo⟩ := s8_6_fields_proved R0 M h0
  obtain ⟨d, P', hd, hhom', hPe', hPo', hnd⟩ := s8_6_normalize_proved R0 M h0 Λ P dg hodd hhom hΛ hPe hPo
  obtain rfl := s8_6_d_one_proved R0 M h0 Λ P' d hd hhom' hΛ hPe' hPo' hnd
  have hPo1 : ∀ (x : Vec 16) j l, evalField (P' j) x ⬝ᵥ evalField (P' l) x = if j = l then x ⬝ᵥ x else 0 :=
    fun x j l => by rw [hPo', pow_one]
  obtain ⟨-, -, -, -, -, hC⟩ := s8_6_clifford_form_proved R0 M h0 Λ P' hhom' hΛ hPe' hPo1
  exact hiff.mp hC

end Osserman.Proofs.S86

