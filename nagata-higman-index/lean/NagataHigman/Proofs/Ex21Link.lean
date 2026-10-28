/-
Ex21Link.lean — project 011 v1.10 (FINAL), Example λ = (2,1) (v1.10 l. 501-513): the LINK of the six explicit 2×2 matrix
facts (Proofs/Ex21Matrices.lean) to an arbitrary Young system.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Rows: (R1) the two standard tableaux T_{12}, T_{13} of (2,1) and their contents; (R2) (T1): ρ((1 2)) = ρ(J_2) acts as
diag(1,-1) on v_{T12}, v_{T13}; (R3) (T2): the diagonal entries -1/2, 1/2 of ρ((2 3)); (R4) over ℂ, a rescaling b' of the
Young basis (Young's orthogonal form) in which ρ((1 2)) = rho12, ρ((2 3)) = rho23, every Γ of (T3) is ±iΓ0, and for
Γ = iΓ0 the six values of ψ(σ) = tr(ρ(σ)Γ).
Route of R4: in b2 = (v_{T12}, v_{T13}) the matrix R of ρ((2 3)) has diagonal -1/2, 1/2 (R3) and R² = 1, so
R₀₁R₁₀ = 3/4; b' = (v_{T12}, t v_{T13}) with t = √3/(2R₀₁) makes both off-diagonal entries √3/2. Matrices in b' are
multiplicative and keep the trace, so the Γ and ψ parts are ex21_Gamma and ex21_psi.
Lean is 0-indexed: paper (1 2) = swap 0 1, (2 3) = swap 1 2, (1 3) = swap 0 2, (1 2 3) = List.formPerm [0,1,2].
-/
import NagataHigman.Proofs.ExV110
import NagataHigman.Proofs.Ex21Matrices
import NagataHigman.Proofs.TwoCorner.Lemma42

universe u

noncomputable section

namespace NagataHigman.Proofs.Ex21

open NagataHigman NagataHigman.Proofs NagataHigman.Proofs.ExV110 Equiv Matrix Complex

/-! ### The matrix of `A` in a basis `v` of `n → K`: multiplicative, trace-preserving, and under rescaling -/

section BasisMatrix

variable {K : Type*} [Field K] {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
  (v : Module.Basis ι K (n → K))

theorem tm_mul (A B : Matrix n n K) :
    LinearMap.toMatrix v v (Matrix.toLin' (A * B)) =
      LinearMap.toMatrix v v (Matrix.toLin' A) * LinearMap.toMatrix v v (Matrix.toLin' B) := by
  rw [Matrix.toLin'_mul, LinearMap.toMatrix_comp v v v]

theorem tm_one : LinearMap.toMatrix v v (Matrix.toLin' (1 : Matrix n n K)) = 1 := by
  rw [Matrix.toLin'_one, LinearMap.toMatrix_id]

theorem tm_neg (A : Matrix n n K) :
    LinearMap.toMatrix v v (Matrix.toLin' (-A)) = -LinearMap.toMatrix v v (Matrix.toLin' A) := by
  rw [map_neg, map_neg]

theorem trace_tm (A : Matrix n n K) : trace (LinearMap.toMatrix v v (Matrix.toLin' A)) = trace A := by
  rw [← LinearMap.trace_eq_matrix_trace K v, LinearMap.trace_eq_matrix_trace K (Pi.basisFun K n),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem tm_unitsSMul (w : ι → Kˣ) (A : Matrix n n K) (i j : ι) :
    LinearMap.toMatrix (v.unitsSMul w) (v.unitsSMul w) (Matrix.toLin' A) i j =
      ((w i : K))⁻¹ * (w j : K) * LinearMap.toMatrix v v (Matrix.toLin' A) i j := by
  simp only [LinearMap.toMatrix_apply, Module.Basis.repr_unitsSMul, Module.Basis.unitsSMul_apply, Units.smul_def,
    map_smul, Finsupp.smul_apply, smul_eq_mul, Units.val_inv_eq_inv_val]
  ring

end BasisMatrix

/-! ### The two standard tableaux of `(2,1)` -/

theorem sort21 : shape21.parts.sort (· ≥ ·) = [2, 1] := by
  show ({2, 1} : Multiset ℕ).sort (· ≥ ·) = [2, 1]
  rw [Multiset.insert_eq_cons, Multiset.sort_cons, Multiset.sort_singleton]
  intro c hc
  rw [Multiset.mem_singleton] at hc
  omega

theorem cells21 (c : ℕ × ℕ) : c ∈ shape21.diagram.cells ↔ c = (0, 0) ∨ c = (0, 1) ∨ c = (1, 0) := by
  obtain ⟨i, j⟩ := c
  rw [mem_cells_of_sort_eq sort21]
  constructor
  · rintro ⟨hi, hj⟩
    have hi' : i < 2 := by simpa using hi
    interval_cases i
    · have hj' : j < 2 := by simpa using hj
      interval_cases j <;> simp
    · have hj' : j < 1 := by simpa using hj
      interval_cases j
      simp
  · rintro (h | h | h) <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> exact ⟨by simp, by simp⟩

/-- `T_{12}`: first row `1, 2` (0-indexed: `0, 1`). -/
def T12 : SYT shape21 where
  pos := ![(0, 0), (0, 1), (1, 0)]
  pos_injective := by decide
  pos_mem k := (cells21 _).2 (by fin_cases k <;> simp)
  pos_mono := by decide

/-- `T_{13}`: first row `1, 3` (0-indexed: `0, 2`). -/
def T13 : SYT shape21 where
  pos := ![(0, 0), (1, 0), (0, 1)]
  pos_injective := by decide
  pos_mem k := (cells21 _).2 (by fin_cases k <;> simp)
  pos_mono := by decide

def tab : Fin 2 → SYT shape21 := ![T12, T13]

theorem T12_ne_T13 : T12 ≠ T13 := by
  intro h
  have h1 := congrArg (fun T : SYT shape21 => T.pos 1) h
  simp [T12, T13] at h1

theorem syt21_cases (T : SYT shape21) : T = T12 ∨ T = T13 := by
  have hc : ∀ k, T.pos k = (0, 0) ∨ T.pos k = (0, 1) ∨ T.pos k = (1, 0) := fun k => (cells21 _).1 (T.pos_mem k)
  have h0 : T.pos 0 = (0, 0) := by
    obtain ⟨m, hm, hm0⟩ := exists_le_of_le T (k := 0) (c := (0, 0)) (Nat.zero_le _) (Nat.zero_le _)
    rwa [Fin.le_zero_iff.1 hm0] at hm
  have hne : ∀ k l : Fin 3, k ≠ l → T.pos k ≠ T.pos l := fun k l hkl h => hkl (T.pos_injective h)
  have h10 := hne 1 0 (by decide)
  have h20 := hne 2 0 (by decide)
  have h12 := hne 1 2 (by decide)
  rcases hc 1 with h1 | h1 | h1 <;> rcases hc 2 with h2 | h2 | h2 <;>
    first
    | exact absurd (h1.trans h0.symm) h10
    | exact absurd (h2.trans h0.symm) h20
    | exact absurd (h1.trans h2.symm) h12
    | (left; apply syt_ext; funext k; fin_cases k <;> simp [T12, h0, h1, h2]; done)
    | (right; apply syt_ext; funext k; fin_cases k <;> simp [T13, h0, h1, h2])

theorem tab_injective : Function.Injective tab := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [tab, T12_ne_T13, T12_ne_T13.symm]

theorem tab_surjective : Function.Surjective tab := by
  intro T
  rcases syt21_cases T with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

def tabEquiv : Fin 2 ≃ SYT shape21 := Equiv.ofBijective tab ⟨tab_injective, tab_surjective⟩

theorem content_T12_one : T12.content 1 = 1 := by decide
theorem content_T12_two : T12.content 2 = -1 := by decide
theorem content_T13_one : T13.content 1 = -1 := by decide
theorem content_T13_two : T13.content 2 = 1 := by decide

/-! ### (T1), (T2) for an arbitrary Young system -/

section YoungSystem21

variable {F : Type*} [Field F]

theorem jucysMurphy_one : jucysMurphy F (1 : Fin 3) = perm F (swap 0 1) := by
  rw [jucysMurphy, show (Finset.univ.filter fun i : Fin 3 => i < 1) = {0} by decide, Finset.sum_singleton]

theorem rhoAlg_jucysMurphy_one (Y : YoungSystem F 3) :
    Y.rhoAlg shape21 (jucysMurphy F 1) = Y.rho shape21 (swap 0 1) := by
  rw [jucysMurphy_one, rhoAlg_perm Y shape21 (swap 0 1)]

end YoungSystem21

/-! ### The rescaled basis for `F = ℂ` -/

section Complex21

variable (Y : YoungSystem ℂ 3) (b : Module.Basis (SYT shape21) ℂ (Fin (Y.dim shape21) → ℂ))

theorem reindex_tab (i : Fin 2) : b.reindex tabEquiv.symm i = b (tab i) := by
  rw [Module.Basis.reindex_apply, Equiv.symm_symm]
  rfl

theorem repr_reindex_tab (x : Fin (Y.dim shape21) → ℂ) (i : Fin 2) :
    (b.reindex tabEquiv.symm).repr x i = b.repr x (tab i) := by
  rw [Module.Basis.repr_reindex_apply, Equiv.symm_symm]
  rfl

/-- The entries of the matrix of `A` in `b2 = (v_{T12}, v_{T13})`. -/
theorem tm_reindex_apply (A : Matrix (Fin (Y.dim shape21)) (Fin (Y.dim shape21)) ℂ) (i j : Fin 2) :
    LinearMap.toMatrix (b.reindex tabEquiv.symm) (b.reindex tabEquiv.symm) (Matrix.toLin' A) i j =
      b.repr (A *ᵥ b (tab j)) (tab i) := by
  rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, reindex_tab, repr_reindex_tab]

end Complex21

end NagataHigman.Proofs.Ex21

namespace NagataHigman.Proofs.Ex21.Rows

open NagataHigman NagataHigman.Proofs NagataHigman.Proofs.ExV110 NagataHigman.Proofs.Ex21 Equiv Matrix Complex

variable (F : Type u) [Field F] [CharZero F]

/-- **Example λ = (2,1)** (v1.10 l. 501): the standard tableaux of `(2,1)` are `T_{12}` and `T_{13}`, with contents
`c_{T12}(2) = 1, c_{T12}(3) = -1, c_{T13}(2) = -1, c_{T13}(3) = 1` (0-indexed points `1, 2`). -/
theorem ex_lam21_tableaux : (∀ T : SYT shape21, T = T12 ∨ T = T13) ∧ T12 ≠ T13 ∧
    T12.content 1 = 1 ∧ T12.content 2 = -1 ∧ T13.content 1 = -1 ∧ T13.content 2 = 1 :=
  ⟨syt21_cases, T12_ne_T13, content_T12_one, content_T12_two, content_T13_one, content_T13_two⟩

omit [CharZero F] in
/-- **Example λ = (2,1), (T1)** (v1.10 l. 502): `ρ((1 2)) = ρ(J_2) = diag(1, -1)` in the basis `v_{T12}, v_{T13}`. -/
theorem ex_lam21_T1 (Y : YoungSystem F 3) (b : Module.Basis (SYT shape21) F (Fin (Y.dim shape21) → F))
    (hb : ∀ (T : SYT shape21) (k : Fin 3),
      Y.rhoAlg shape21 (jucysMurphy F k) *ᵥ b T = ((T.content k : ℤ) : F) • b T) :
    Y.rhoAlg shape21 (jucysMurphy F 1) = Y.rho shape21 (swap 0 1) ∧
      Y.rho shape21 (swap 0 1) *ᵥ b T12 = b T12 ∧ Y.rho shape21 (swap 0 1) *ᵥ b T13 = -b T13 := by
  have hJ := rhoAlg_jucysMurphy_one Y
  refine ⟨hJ, ?_, ?_⟩
  · rw [← hJ, hb T12 1, content_T12_one, Int.cast_one, one_smul]
  · rw [← hJ, hb T13 1, content_T13_one, Int.cast_neg, Int.cast_one, neg_one_smul]

/-- **Example λ = (2,1), (T2)** (v1.10 l. 502-503): the diagonal entries of `ρ((2 3))` are `1/(-1-1) = -1/2` and
`1/(1+1) = 1/2`. -/
theorem ex_lam21_T2 (Y : YoungSystem F 3) (b : Module.Basis (SYT shape21) F (Fin (Y.dim shape21) → F))
    (hb : ∀ (T : SYT shape21) (k : Fin 3),
      Y.rhoAlg shape21 (jucysMurphy F k) *ᵥ b T = ((T.content k : ℤ) : F) • b T) :
    b.repr (Y.rho shape21 (swap 1 2) *ᵥ b T12) T12 = -1/2 ∧ b.repr (Y.rho shape21 (swap 1 2) *ᵥ b T13) T13 = 1/2 := by
  refine ⟨?_, ?_⟩
  · rw [(R_diag_general Y b hb T12 1 2 rfl).2, content_T12_one, content_T12_two]
    norm_num
  · rw [(R_diag_general Y b hb T13 1 2 rfl).2, content_T13_one, content_T13_two]
    norm_num

/-- **Example λ = (2,1), Young's orthogonal form, (T3) and ψ** (v1.10 l. 503-513), over `ℂ`: a rescaling `b'` of the
Young basis `v_{T12}, v_{T13}` in which `ρ((1 2)) = rho12` and `ρ((2 3)) = rho23`; in it every `Γ` of (T3) is `±iΓ0`,
and for `Γ = iΓ0`, `ψ(σ) = tr(ρ(σ)Γ)` vanishes on the identity and the transpositions, `ψ((1 2 3)) = -i√3 = -ψ((1 3 2))`. -/
theorem ex_lam21_orthogonal (Y : YoungSystem ℂ 3)
    (b : Module.Basis (SYT shape21) ℂ (Fin (Y.dim shape21) → ℂ))
    (hb : ∀ (T : SYT shape21) (k : Fin 3),
      Y.rhoAlg shape21 (jucysMurphy ℂ k) *ᵥ b T = ((T.content k : ℤ) : ℂ) • b T) :
    ∃ b' : Module.Basis (Fin 2) ℂ (Fin (Y.dim shape21) → ℂ),
      (∀ i, ∃ c : ℂ, c ≠ 0 ∧ b' i = c • b (tab i)) ∧
      LinearMap.toMatrix b' b' (Matrix.toLin' (Y.rho shape21 (swap 0 1))) = rho12 ∧
      LinearMap.toMatrix b' b' (Matrix.toLin' (Y.rho shape21 (swap 1 2))) = rho23 ∧
      (∀ Γ : Matrix (Fin (Y.dim shape21)) (Fin (Y.dim shape21)) ℂ,
        (∀ σ : Perm (Fin 3), Γ * Y.rho shape21 σ = ((Perm.sign σ : ℤ) : ℂ) • (Y.rho shape21 σ * Γ)) → Γ * Γ = 1 →
        LinearMap.toMatrix b' b' (Matrix.toLin' Γ) = I • Gamma0 ∨
          LinearMap.toMatrix b' b' (Matrix.toLin' Γ) = -I • Gamma0) ∧
      (∀ Γ : Matrix (Fin (Y.dim shape21)) (Fin (Y.dim shape21)) ℂ,
        LinearMap.toMatrix b' b' (Matrix.toLin' Γ) = I • Gamma0 →
        trace (Y.rho shape21 1 * Γ) = 0 ∧ trace (Y.rho shape21 (swap 0 1) * Γ) = 0 ∧
        trace (Y.rho shape21 (swap 1 2) * Γ) = 0 ∧ trace (Y.rho shape21 (swap 0 2) * Γ) = 0 ∧
        trace (Y.rho shape21 (List.formPerm [0, 1, 2]) * Γ) = -I * (Real.sqrt 3 : ℂ) ∧
        trace (Y.rho shape21 (List.formPerm [0, 2, 1]) * Γ) = I * (Real.sqrt 3 : ℂ)) := by
  -- the matrix `R` of `ρ((2 3))` in `b2 = (v_{T12}, v_{T13})`: diagonal `-1/2, 1/2`, `R² = 1`, so `R₀₁ R₁₀ = 3/4`
  obtain ⟨R, hR⟩ : ∃ R, R = LinearMap.toMatrix (b.reindex tabEquiv.symm) (b.reindex tabEquiv.symm)
      (Matrix.toLin' (Y.rho shape21 (swap 1 2))) := ⟨_, rfl⟩
  have hT2 := ex_lam21_T2 ℂ Y b hb
  have hR00 : R 0 0 = -1/2 := by rw [hR, tm_reindex_apply]; exact hT2.1
  have hR11 : R 1 1 = 1/2 := by rw [hR, tm_reindex_apply]; exact hT2.2
  have hRR : R * R = 1 := by
    rw [hR, ← tm_mul, ← map_mul (Y.rho shape21), Equiv.swap_mul_self, map_one, tm_one]
  have hpq : R 0 1 * R 1 0 = 3/4 := by
    have h := congrFun (congrFun hRR 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hR00, Matrix.one_apply_eq] at h
    linear_combination h
  have hp : R 0 1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hpq
    norm_num at hpq
  -- the rescaled basis `b' = (v_{T12}, t v_{T13})`, `t = √3 / (2 R₀₁)`: both off-diagonal entries become `√3/2`
  obtain ⟨t, ht_def⟩ : ∃ t : ℂ, t = (Real.sqrt 3 : ℂ) / (2 * R 0 1) := ⟨_, rfl⟩
  have ht : t ≠ 0 := by rw [ht_def]; exact div_ne_zero sqrt3_ne (mul_ne_zero two_ne_zero hp)
  have e01 : t * R 0 1 = (Real.sqrt 3 : ℂ) / 2 := by
    rw [ht_def]
    field_simp
  have hut : t⁻¹ * t = 1 := inv_mul_cancel₀ ht
  have e10 : t⁻¹ * R 1 0 = (Real.sqrt 3 : ℂ) / 2 := by
    linear_combination (2/3 * (Real.sqrt 3 : ℂ) * R 0 1 * R 1 0) * hut + (2/3 * (Real.sqrt 3 : ℂ)) * hpq -
      (2/3 * (Real.sqrt 3 : ℂ) * t⁻¹ * R 1 0) * e01 - (1/3 * t⁻¹ * R 1 0) * sqrt3_sq
  obtain ⟨b', hb'⟩ : ∃ b' : Module.Basis (Fin 2) ℂ (Fin (Y.dim shape21) → ℂ),
      b' = (b.reindex tabEquiv.symm).unitsSMul ![1, Units.mk0 t ht] := ⟨_, rfl⟩
  have hT1 := ex_lam21_T1 ℂ Y b hb
  have h01 : LinearMap.toMatrix b' b' (Matrix.toLin' (Y.rho shape21 (swap 0 1))) = rho12 := by
    ext i j
    rw [hb', tm_unitsSMul, tm_reindex_apply]
    fin_cases i <;> fin_cases j <;>
      simp [tab, hT1.2.1, hT1.2.2, T12_ne_T13, T12_ne_T13.symm, rho12, ht]
  have h12 : LinearMap.toMatrix b' b' (Matrix.toLin' (Y.rho shape21 (swap 1 2))) = rho23 := by
    ext i j
    rw [hb', tm_unitsSMul, ← hR]
    fin_cases i <;> fin_cases j
    · simpa [rho23] using hR00
    · simpa [rho23] using e01
    · simpa [rho23] using e10
    · simpa [rho23, ht] using hR11
  refine ⟨b', ?_, h01, h12, ?_, ?_⟩
  · intro i
    refine ⟨((![1, Units.mk0 t ht] : Fin 2 → ℂˣ) i : ℂ), Units.ne_zero _, ?_⟩
    rw [hb', Module.Basis.unitsSMul_apply, Units.smul_def, reindex_tab]
  · intro Γ hΓ hΓ2
    have hsgn : ∀ {x y : Fin 3}, x ≠ y → ((Perm.sign (swap x y) : ℤ) : ℂ) = -1 := fun h => by
      simp [Perm.sign_swap h]
    apply (ex21_Gamma _).1
    refine ⟨?_, ?_, ?_⟩
    · rw [← h01, ← tm_mul, hΓ, hsgn (show (0 : Fin 3) ≠ 1 by decide), neg_one_smul, tm_neg, tm_mul]
    · rw [← h12, ← tm_mul, hΓ, hsgn (show (1 : Fin 3) ≠ 2 by decide), neg_one_smul, tm_neg, tm_mul]
    · rw [← tm_mul, hΓ2, tm_one]
  · intro Γ hG
    have htr : ∀ A : Matrix (Fin (Y.dim shape21)) (Fin (Y.dim shape21)) ℂ,
        trace (A * Γ) = trace (LinearMap.toMatrix b' b' (Matrix.toLin' A) * (I • Gamma0)) := by
      intro A
      rw [← trace_tm b' (A * Γ), tm_mul, hG]
    have hpsi := ex21_psi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [htr, map_one, tm_one, one_mul]
      exact hpsi.1
    · rw [htr, h01]
      exact hpsi.2.1
    · rw [htr, h12]
      exact hpsi.2.2.1
    · rw [show (swap 0 2 : Perm (Fin 3)) = swap 0 1 * swap 1 2 * swap 0 1 by decide, map_mul, map_mul, htr,
        tm_mul, tm_mul, h01, h12]
      exact hpsi.2.2.2.1
    · rw [show (List.formPerm [0, 1, 2] : Perm (Fin 3)) = swap 0 1 * swap 1 2 by decide, map_mul, htr, tm_mul,
        h01, h12]
      exact hpsi.2.2.2.2.1
    · rw [show (List.formPerm [0, 2, 1] : Perm (Fin 3)) = swap 1 2 * swap 0 1 by decide, map_mul, htr, tm_mul,
        h01, h12]
      exact hpsi.2.2.2.2.2

end NagataHigman.Proofs.Ex21.Rows

end
