/-
Osserman/Proofs/S83Opp2.lean — §8.3 of paper 013, opposite signs and conclusion: the Cayley alternative at an endpoint of
pattern `(8,7)` is excluded, the endpoint is Clifford, the original tensor is restored (rows s8_cayley_excluded,
s8_3_endpoint_opp, s8_3_opposite, s8_3_clifford, s8_3_pattern_clifford; statements copied verbatim from
Osserman/Paper/Statements8.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Opposite signs. `a = √(μ(μ-λ))`, `b = √(-σ(σ-λ))`; `ap₁ = ±bp₂` mod `q` (`s8_3_pm`) gives the skew orthogonal `J`
(`s8_3_combination`), the endpoint `R' = R - C R_J` of pattern `(M+1, N+1)` with constant projection lengths
(`s8_3_endpoint`); `R'` is Clifford (`(8,7)`: Theorem A with the Cayley form excluded below; `(9,6)`: [Nik2006, Prop. 2.1]),
and [Nik2006, Lemma 3.2(1)] (`lem_nik_3_2_1`, `C ≠ 0`) restores `R`. Conclusion: same signs -> linear fields; opposite
signs -> the above, after interchanging `(μ, P₁)` and `(σ, P₂)` if `μ(μ-λ) < 0`.

Cayley exclusion. Suppose `R' = αR_1 + βT^*R_Cay` with `T ∈ O(16)`. Both `μ₁` and `μ₂` occur at a unit `x`, so each is `α + β` or
`α + 4β` (Section 7); as `μ₁ ≠ μ₂`, `β ≠ 0`. The eigenspaces of `α + β` and `α + 4β` in `x^⊥` are then the
`T`-preimages of `N(Tx)` and `E(Tx)`, so the skew orthogonal `K = TJTᵀ` has the constant squared projection length `c` of
`Ky` onto `N(y)`, or onto `E(y)`, at every unit `y`. In the second case the projection onto `N(y)` has squared length
`1 - c` (Pythagoras, as `Ky ⊥ y` and `|Ky| = 1`). Scaling gives `c'|y|²` at every `y ≠ 0`, and Lemma 8.1 gives `K = 0`,
so `J = 0`, against `JᵀJ = 1`.
-/
import Osserman.Proofs.ThmECayley
import Osserman.Proofs.Lem81Rest
import Osserman.Proofs.S83Move
import Osserman.Proofs.S83Endpoint
import Osserman.Proofs.S8TCAlgebra

namespace Osserman.Proofs.S83

open Osserman Matrix

section Cayley

/-- Orthogonal projection commutes with scaling. -/
lemma isOrthProj_smul {W : Submodule ℝ (Vec 16)} {v w : Vec 16} (h : IsOrthProj W v w) (s : ℝ) :
    IsOrthProj W (s • v) (s • w) :=
  ⟨W.smul_mem s h.1, by rw [← smul_sub]; exact (orthSub W).smul_mem s h.2⟩

/-- An orthogonal `T` carries the projection onto the preimage `T⁻¹S` to the projection onto `S`. -/
lemma isOrthProj_comap {T : Matrix (Fin 16) (Fin 16) ℝ} (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ)
    {S : Submodule ℝ (Vec 16)} {v w : Vec 16} (h : IsOrthProj (S.comap (Matrix.toLin' T)) v w) :
    IsOrthProj S (T *ᵥ v) (T *ᵥ w) := by
  have tt : T * Tᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).mp hT
  refine ⟨h.1, fun s hs => ?_⟩
  have back : Tᵀ *ᵥ s ∈ S.comap (Matrix.toLin' T) := by
    change T *ᵥ (Tᵀ *ᵥ s) ∈ S
    rwa [Matrix.mulVec_mulVec, tt, Matrix.one_mulVec]
  rw [← Matrix.mulVec_sub, Lem81.dot_mulVec_T]
  exact h.2 _ back

/-- A constant squared projection length `c` onto `N(y)` at unit `y` is `c|y|²` at every `y ≠ 0`. -/
lemma projN_scaled (K : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ)
    (h : ∀ y : Vec 16, y ⬝ᵥ y = 1 → ∃ w, IsOrthProj (Nstd y) (K *ᵥ y) w ∧ w ⬝ᵥ w = c) :
    ∀ z : Vec 16, z ≠ 0 → ∃ w, IsOrthProj (Nstd z) (K *ᵥ z) w ∧ w ⬝ᵥ w = c * (z ⬝ᵥ z) := by
  intro z hz
  obtain ⟨s, u, hu, rfl⟩ := Spectral.exists_unit_scale z
  have hs : s ≠ 0 := by rintro rfl; exact hz (zero_smul ℝ u)
  obtain ⟨w, hw, hlen⟩ := h u hu
  refine ⟨s • w, ?_, ?_⟩
  · rw [ThmECayley.N_smul s hs, Matrix.mulVec_smul]
    exact isOrthProj_smul hw s
  · simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hlen, hu]
    ring

/-- For a skew orthogonal `K`, a squared projection length `c` of `Ky` onto `E(y)` is `1 - c` onto `N(y)`. -/
lemma projN_of_projE {K : Matrix (Fin 16) (Fin 16) ℝ} (hK : Kᵀ = -K) (hKo : Kᵀ * K = 1) {c : ℝ} {y : Vec 16}
    (hy : y ⬝ᵥ y = 1) (hE : ∃ w, IsOrthProj (Estd y) (K *ᵥ y) w ∧ w ⬝ᵥ w = c) :
    ∃ w, IsOrthProj (Nstd y) (K *ᵥ y) w ∧ w ⬝ᵥ w = 1 - c := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  obtain ⟨wE, hwE, hlen⟩ := hE
  refine ⟨Lem81.projN y (K *ᵥ y), Lem81.projN_isOrthProj hy0 _, ?_⟩
  have pyth := Lem81.lem_8_1_pythagoras_proved y hy0 (K *ᵥ y) (Lem81.skew_dot_self hK y) wE _ hwE
    (Lem81.projN_isOrthProj hy0 _)
  have norm : (K *ᵥ y) ⬝ᵥ (K *ᵥ y) = 1 := by
    rw [Lem81.dot_mulVec_T, Matrix.mulVec_mulVec, hKo, Matrix.one_mulVec, hy]
  linarith

/-- The conjugate `TJTᵀ` of a skew orthogonal `J` by an orthogonal `T` is skew and orthogonal. -/
lemma conj_skew_orth {T J : Matrix (Fin 16) (Fin 16) ℝ} (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ)
    (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1) :
    (T * J * Tᵀ)ᵀ = -(T * J * Tᵀ) ∧ (T * J * Tᵀ)ᵀ * (T * J * Tᵀ) = 1 := by
  have tt : T * Tᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).mp hT
  have t't : Tᵀ * T = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hT
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  constructor
  · rw [hJs]; noncomm_ring
  · calc T * (Jᵀ * Tᵀ) * (T * J * Tᵀ) = T * (Jᵀ * (Tᵀ * T) * J) * Tᵀ := by noncomm_ring
      _ = 1 := by rw [t't, Matrix.mul_one, hJo, Matrix.mul_one, tt]

/-- In the Cayley case both multiplicities occur, so `β ≠ 0` and `μ₁` is `α + β` or `α + 4β`. -/
lemma cayley_values (R' : CurvTensor 16) (μ₁ μ₂ : ℝ) (hne : μ₁ ≠ μ₂)
    (hpat : ∀ x : Vec 16, x ⬝ᵥ x = 1 → R'.redMult x μ₁ = 8 ∧ R'.redMult x μ₂ = 7) (α β : ℝ)
    (T : Matrix (Fin 16) (Fin 16) ℝ) (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ)
    (hR : ∀ u v w, R'.op u v w = α • R1fun u v w + β • pullbackFun T RCayFun u v w) :
    β ≠ 0 ∧ (μ₁ = α + β ∨ μ₁ = α + 4 * β) := by
  let x0 : Vec 16 := Pi.single 0 1
  have unit : x0 ⬝ᵥ x0 = 1 := by simp [x0]
  have pos1 : 0 < R'.redMult x0 μ₁ := by rw [(hpat x0 unit).1]; norm_num
  have pos2 : 0 < R'.redMult x0 μ₂ := by rw [(hpat x0 unit).2]; norm_num
  have c1 := ThmECayley.eigenvalue_of_positive R' α β μ₁ T hT hR x0 unit pos1
  have c2 := ThmECayley.eigenvalue_of_positive R' α β μ₂ T hT hR x0 unit pos2
  refine ⟨fun zero => hne ?_, c1⟩
  have first : μ₁ = α := by rcases c1 with h | h <;> simpa only [zero, add_zero, mul_zero] using h
  have second : μ₂ = α := by rcases c2 with h | h <;> simpa only [zero, add_zero, mul_zero] using h
  exact first.trans second.symm

/-- A constant projection length onto the preimage `T⁻¹S(Tx)` of an eigenspace in `x^⊥` moves to a constant projection
length of `(TJTᵀ)y` onto `S(y)` at every unit `y`. -/
lemma moved_proj {R' : CurvTensor 16} {μ c : ℝ} {T J : Matrix (Fin 16) (Fin 16) ℝ}
    (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ) (S : Vec 16 → Submodule ℝ (Vec 16))
    (hS : ∀ x : Vec 16, x ⬝ᵥ x = 1 →
      Module.End.eigenspace (R'.jacobiMap x) μ ⊓ perp x = (S (T *ᵥ x)).comap (Matrix.toLin' T))
    (hc : ∀ x : Vec 16, x ⬝ᵥ x = 1 →
      ∃ w, IsOrthProj (Module.End.eigenspace (R'.jacobiMap x) μ ⊓ perp x) (J *ᵥ x) w ∧ w ⬝ᵥ w = c) :
    ∀ y : Vec 16, y ⬝ᵥ y = 1 → ∃ w, IsOrthProj (S y) ((T * J * Tᵀ) *ᵥ y) w ∧ w ⬝ᵥ w = c := by
  have tt : T * Tᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).mp hT
  have t't : Tᵀ * T = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hT
  intro y hy
  have hx : (Tᵀ *ᵥ y) ⬝ᵥ (Tᵀ *ᵥ y) = 1 := by
    rw [CayleyIdentify.orthogonal_dot Tᵀ (by simpa using tt), hy]
  have restore : T *ᵥ (Tᵀ *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, tt, Matrix.one_mulVec]
  have image : (T * J * Tᵀ) *ᵥ y = T *ᵥ (J *ᵥ (Tᵀ *ᵥ y)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  obtain ⟨w, hw, hlen⟩ := hc _ hx
  rw [hS _ hx, restore] at hw
  refine ⟨T *ᵥ w, image ▸ isOrthProj_comap hT hw, ?_⟩
  rw [CayleyIdentify.orthogonal_dot T t't, hlen]

/-- A skew orthogonal `J` whose conjugate has constant squared projection length onto `N` cannot exist. -/
lemma no_constant_N {T J : Matrix (Fin 16) (Fin 16) ℝ} (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ)
    (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1) (c : ℝ)
    (h : ∀ y : Vec 16, y ⬝ᵥ y = 1 → ∃ w, IsOrthProj (Nstd y) ((T * J * Tᵀ) *ᵥ y) w ∧ w ⬝ᵥ w = c) : False := by
  have zero := Lem81.lem_8_1_proved _ (conj_skew_orth hT hJs hJo).1 c (projN_scaled _ c h)
  have entry := congrFun (congrFun hJo 0) 0
  simp [ThmECayley.conjugated_zero T J hT zero] at entry

/-- **§8.3** (row `s8_cayley_excluded`): at an endpoint of pattern `(8,7)` with a skew orthogonal `J` of constant
projection length onto the multiplicity-8 eigenspace, the tensor is not of Cayley type. -/
theorem s8_cayley_excluded_proved (R' : CurvTensor 16) (μ₁ μ₂ : ℝ) (hne : μ₁ ≠ μ₂)
    (hpat : ∀ x : Vec 16, x ⬝ᵥ x = 1 → R'.redMult x μ₁ = 8 ∧ R'.redMult x μ₂ = 7)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (hproj : ∃ c : ℝ, ∀ x : Vec 16, x ⬝ᵥ x = 1 →
      ∃ w, IsOrthProj (Module.End.eigenspace (R'.jacobiMap x) μ₁ ⊓ perp x) (J *ᵥ x) w ∧ w ⬝ᵥ w = c) :
    ¬ IsCayleyType R' := by
  rintro ⟨α, β, T, hT, hR⟩
  obtain ⟨c, hc⟩ := hproj
  obtain ⟨hβ, cand⟩ := cayley_values R' μ₁ μ₂ hne hpat α β T hT hR
  have spaces := ThmECayley.thm_E_cayley_eigendistributions_proved R' α β hβ T hT hR
  rcases cand with hN | hE
  · exact no_constant_N hT hJs hJo c
      (moved_proj hT Nstd (fun x hx => by rw [hN]; exact (spaces x hx).1) hc)
  · have onE := moved_proj hT Estd (fun x hx => by rw [hE]; exact (spaces x hx).2) hc
    exact no_constant_N hT hJs hJo (1 - c) fun y hy =>
      projN_of_projE (conj_skew_orth hT hJs hJo).1 (conj_skew_orth hT hJs hJo).2 hy (onE y hy)

end Cayley

/-! ### The opposite-sign endpoint and the restoration -/

/-- Row `s8_3_endpoint_opp`. -/
theorem s8_3_endpoint_opp_proved (M N : ℕ) (hMN : (M = 7 ∧ N = 6) ∨ (M = 8 ∧ N = 5)) (R' : CurvTensor 16)
    (lam : ℝ) (hpat : PatternEv R' ![M + 1, N + 1] ![0, lam]) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J)
    (hJo : Jᵀ * J = 1)
    (hproj : ∀ ℓ ∈ ({0, lam} : Set ℝ), ∃ c : ℝ, ∀ x : Vec 16, x ⬝ᵥ x = 1 →
      ∃ w, IsOrthProj (Module.End.eigenspace (R'.jacobiMap x) ℓ ⊓ perp x) (J *ᵥ x) w ∧ w ⬝ᵥ w = c) :
    R'.IsClifford := by
  rcases hMN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hinj, hm⟩ := hpat
    have hne : (0 : ℝ) ≠ lam := by
      intro h
      have := hinj (a₁ := 0) (a₂ := 1) (by simp [h])
      exact absurd this (by decide)
    have h87 (x : Vec 16) (hx : x ⬝ᵥ x = 1) : R'.redMult x 0 = 8 ∧ R'.redMult x lam = 7 :=
      ⟨by simpa using hm x hx 0, by simpa using hm x hx 1⟩
    obtain ⟨μ, κ, -, -, A, -, hcases⟩ := ThmC.thm_C_of_prop_5_2 Sec5c.prop_5_2_proved R' ⟨0, lam, hne, h87⟩
    rcases hcases with ⟨-, hC⟩ | ⟨-, hC⟩ | ⟨-, T, hT, hop⟩
    · exact hC
    · exact hC
    · exact absurd ⟨μ - κ / 3, κ / 3, T, hT, hop⟩
        (s8_cayley_excluded_proved R' 0 lam hne h87 J hJs hJo (hproj 0 (Set.mem_insert _ _)))
  · exact s8_prop21_uses_proved R' (Or.inl ⟨_, hpat⟩)

/-- A tensor with a pattern of multiplicities summing to `15` is Osserman (`hasPattern_osserman`). -/
lemma pattern_osserman {k : ℕ} {R : CurvTensor 16} {m : Fin k → ℕ} {ev : Fin k → ℝ} (hsum : ∑ i, m i + 1 = 16)
    (h : PatternEv R m ev) : R.IsOsserman :=
  (CorD.hasPattern_osserman_proved R m hsum ⟨ev, h⟩).1

/-- Row `s8_3_opposite`. -/
theorem s8_3_opposite_proved (hQ : QPrimeHyp) (hSpec : SpecIdHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P) (ha : 0 < ev 2 * (ev 2 - ev 1))
    (hb : ev 3 * (ev 3 - ev 1) < 0) : R.IsClifford := by
  have hb' : 0 < -(ev 3 * (ev 3 - ev 1)) := by linarith
  have ha0 := Real.sqrt_pos.mpr ha
  have hb0 := Real.sqrt_pos.mpr hb'
  have ha2 := Real.sq_sqrt ha.le
  have hb2 := Real.sq_sqrt hb'.le
  obtain ⟨ε, hε, hpm⟩ := s8_3_pm_proved hQ hSpec R M N ev P h _ _ ha0 hb0 ha2 hb2
  obtain ⟨J, hJs, hJo, hJ⟩ := s8_3_combination_proved R M N ev P h _ _ ha0 hb0 ha2 hb2 ε hε hpm
  obtain ⟨R', hR', hpat', hproj'⟩ := s8_3_endpoint_proved R M N ev P h _ _ ha0 hb0 ha2 hb2 ε hε J hJs hJo hJ
  have hms : ev 2 ≠ ev 3 := fun e => absurd (h.2.1.1 e) (by decide)
  have hC := (s8_3_C_ne_zero_proved (ev 1) (ev 2) (ev 3) _ _ hms ha0 hb0 ha2 hb2).2
  have hsum : ∑ i, (![M, N, 1, 1] : Fin 4 → ℕ) i + 1 = 16 ∧ ∑ i, (![M + 1, N + 1] : Fin 2 → ℕ) i + 1 = 16 := by
    rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Fin.sum_univ_succ]
  exact Rem72c.lem_nik_3_2_1_proved R R' J hJs hJo _ hC hR' (pattern_osserman hsum.1 h.2.1)
    (pattern_osserman hsum.2 hpat') (s8_3_endpoint_opp_proved M N h.1 R' (ev 1) hpat' J hJs hJo hproj')

/-! ### Conclusion of §8.3 -/

/-- `Sec83Data` with `(μ, P₁)` and `(σ, P₂)` interchanged. -/
lemma sec83_swap {R : CurvTensor 16} {M N : ℕ} {ev : Fin 4 → ℝ} {P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ}
    (h : Sec83Data R M N ev P) : Sec83Data R M N (ev ∘ Equiv.swap 2 3) (P ∘ Equiv.swap 0 1) := by
  obtain ⟨hMN, ⟨hinj, hm⟩, h0, hhom, hcub, he2, he3⟩ := h
  refine ⟨hMN, ⟨hinj.comp (Equiv.injective _), fun x hx i => ?_⟩, h0, fun i j => hhom _ j, fun i => hcub _, ?_, ?_⟩
  · rw [Function.comp_apply, hm x hx]
    fin_cases i <;> simp [Equiv.swap_apply_def]
  · simp only [Function.comp_apply, Equiv.swap_apply_left]
    exact he3
  · simp only [Function.comp_apply, Equiv.swap_apply_right]
    exact he2

/-- Row `s8_3_clifford`. -/
theorem s8_3_clifford_proved (hQ : QPrimeHyp) (hDiv : DivQHyp) (hSpec : SpecIdHyp) (hMove : MoveHyp)
    (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec83Data R M N ev P) : R.IsClifford := by
  have hinj := h.2.1.1
  have h0 := h.2.2.1
  have w2 : ev 2 * (ev 2 - ev 1) ≠ 0 := mul_ne_zero (fun e => absurd (hinj (e.trans h0.symm)) (by decide))
    (sub_ne_zero.mpr fun e => absurd (hinj e) (by decide))
  have w3 : ev 3 * (ev 3 - ev 1) ≠ 0 := mul_ne_zero (fun e => absurd (hinj (e.trans h0.symm)) (by decide))
    (sub_ne_zero.mpr fun e => absurd (hinj e) (by decide))
  have linear (hs : 0 < (ev 2 * (ev 2 - ev 1)) * (ev 3 * (ev 3 - ev 1))) : R.IsClifford :=
    s8_3_linear_case_proved hDiv hMove R M N ev P h (s8_3_same_sign_proved hSpec R M N ev P h hs)
  rcases lt_or_gt_of_ne w2 with n2 | p2 <;> rcases lt_or_gt_of_ne w3 with n3 | p3
  · exact linear (mul_pos_of_neg_of_neg n2 n3)
  · exact s8_3_opposite_proved hQ hSpec R M N _ _ (sec83_swap h) (by simpa [Equiv.swap_apply_def] using p3)
      (by simpa [Equiv.swap_apply_def] using n2)
  · exact s8_3_opposite_proved hQ hSpec R M N ev P h p2 n3
  · exact linear (mul_pos p2 p3)

/-- Row `s8_3_pattern_clifford`. -/
theorem s8_3_pattern_clifford_proved (hQ : QPrimeHyp) (hCub : CubicIdHyp) (hDiv : DivQHyp) (hSpec : SpecIdHyp)
    (hMove : MoveHyp) (R : CurvTensor 16) (h : HasPattern R ![7, 6, 1, 1] ∨ HasPattern R ![8, 5, 1, 1]) :
    R.IsClifford := by
  obtain ⟨M, N, hMN, ev, hR⟩ : ∃ M N : ℕ, ((M = 7 ∧ N = 6) ∨ (M = 8 ∧ N = 5)) ∧ HasPattern R ![M, N, 1, 1] := by
    rcases h with h | h
    · exact ⟨7, 6, Or.inl ⟨rfl, rfl⟩, h⟩
    · exact ⟨8, 5, Or.inr ⟨rfl, rfl⟩, h⟩
  obtain ⟨R0, -, -, hR0, -, -, hiff⟩ := S8TC.s8_shift_to_zero_proved R _ ev hR 0
  obtain ⟨P, hP⟩ := s8_3_fields_proved hCub R0 M N hMN _ hR0 (sub_self _)
  exact hiff.mp (s8_3_clifford_proved hQ hDiv hSpec hMove R0 M N _ P hP)

end Osserman.Proofs.S83
