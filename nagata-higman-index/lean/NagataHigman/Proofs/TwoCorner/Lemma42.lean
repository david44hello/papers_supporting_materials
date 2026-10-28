/-
NagataHigman/Proofs/TwoCorner/Lemma42.lean — Lemma 4.2, the star commutant for ν (tex v1.02 lines 412-439).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route (the paper's steps (a)-(e) in one identity): with `k = N-2`, `top = N-1`, `s = (k top)`, on `ν`
  `ρ(s) = -Y_top Y_k Y_top`.
In the Young basis, `Y_top = ρ(J_top)` is diagonal with entries `y_T = c_T(top) = ±1`, and `Y_k = ρ(J_k) + ρ(s)`
(paper (b)). The diagonal entry of `ρ(s)` is `1/(y - x)` with `x = c_T(k)` (paper (T2)); the identity there is
`x² - xy = 2`, true for the four content pairs of step (d). The off-diagonal entries join `T` to `sT`, where `N` sits in
the other corner, so `y_T y_{sT} = -1`. Conjugating by `ρ(g)` permutes the `Y_j` (paper (e)), so `Z` commuting with
every `Y_j` commutes with `ρ` of every transposition, hence with `ρ(S_N)`, hence is a scalar (Burnside + Schur,
`eq_scalar_of_commute_rho`).
-/
import NagataHigman.Proofs.TwoCorner.Spectral
import NagataHigman.Proofs.TwoCorner.Gamma
import NagataHigman.Proofs.Tableaux
import NagataHigman.Proofs.Shapes

noncomputable section

namespace NagataHigman.Proofs

open Equiv Finset Matrix NagataHigman

variable {F : Type*} [Field F] {N : ℕ}

/-- Paper (b): `X^{(k)} = J_k + (k, top)` when `k + 1 = top` and `top` is the last point. -/
theorem starElem_eq_jucysMurphy_add (k top : Fin N) (hk : (k : ℕ) + 1 = top) (htop : (top : ℕ) + 1 = N) :
    starElem F k = jucysMurphy F k + perm F (swap k top) := by
  unfold starElem jucysMurphy
  have hset : univ.filter (fun i : Fin N => i ≠ k) = insert top (univ.filter (fun i : Fin N => i < k)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, ne_eq, Fin.ext_iff, Fin.lt_def]
    have := i.isLt
    omega
  have hnot : top ∉ univ.filter (fun i : Fin N => i < k) := by
    simp only [mem_filter, mem_univ, true_and, Fin.lt_def, not_lt]
    omega
  rw [hset, Finset.sum_insert hnot, Equiv.swap_comm, add_comm]

section General

variable (Y : YoungSystem F N)

theorem rhoAlg_perm (lam : Shape N) (σ : Perm (Fin N)) : Y.rhoAlg lam (perm F σ) = Y.rho lam σ := by
  simp [YoungSystem.rhoAlg, perm, MonoidAlgebra.lift_single]

/-- Two matrices that agree on a basis are equal. -/
theorem matrix_eq_of_basis {lam : Shape N} (b : Module.Basis (SYT lam) F (Fin (Y.dim lam) → F))
    (A B : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) (h : ∀ T, A *ᵥ b T = B *ᵥ b T) : A = B := by
  apply Matrix.toLin'.injective
  exact b.ext fun T => by simpa [Matrix.toLin'_apply] using h T

/-- Paper (e): `ρ(g) Y_j = Y_{g j} ρ(g)`. -/
theorem rho_mul_star (lam : Shape N) (g : Perm (Fin N)) (j : Fin N) (X : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) :
    Y.rho lam g * (Y.rhoAlg lam (starElem F j) * X) = Y.rhoAlg lam (starElem F (g j)) * (Y.rho lam g * X) := by
  have h : perm F g * starElem F j = starElem F (g j) * perm F g := by
    rw [← perm_conj_starElem F g j, mul_assoc _ (perm F g⁻¹), perm_mul_perm F g⁻¹ g, inv_mul_cancel, perm_one,
      mul_one]
  have h' := congrArg (Y.rhoAlg lam) h
  rw [map_mul, map_mul, rhoAlg_perm] at h'
  rw [← mul_assoc, h', mul_assoc]

section Identity

variable [CharZero F] {lam : Shape N} (b : Module.Basis (SYT lam) F (Fin (Y.dim lam) → F))

/-- The key identity on a two-corner shape: `ρ((k top)) = -Y_top Y_k Y_top`, given the content facts of step (d). -/
theorem rho_swap_eq_neg_star (hb : IsYoungBasis Y b) (k top : Fin N) (hk : (k : ℕ) + 1 = top)
    (htop : (top : ℕ) + 1 = N) (hy : ∀ T : SYT lam, T.content top ^ 2 = 1)
    (hrel : ∀ T : SYT lam, T.content k ^ 2 - T.content k * T.content top = 2) :
    Y.rho lam (swap k top) =
      -(Y.rhoAlg lam (starElem F top) * Y.rhoAlg lam (starElem F k) * Y.rhoAlg lam (starElem F top)) := by
  apply matrix_eq_of_basis Y b
  intro T
  apply b.repr.injective
  ext T'
  have hYtop : Y.rhoAlg lam (starElem F top) = Y.rhoAlg lam (jucysMurphy F top) := by
    rw [starElem_top F top htop]
  have hYk : Y.rhoAlg lam (starElem F k) = Y.rhoAlg lam (jucysMurphy F k) + Y.rho lam (swap k top) := by
    rw [starElem_eq_jucysMurphy_add k top hk htop, map_add, rhoAlg_perm]
  rw [hYtop, hYk, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb T top,
    Matrix.mulVec_smul, Matrix.add_mulVec, hb T k, map_neg, Finsupp.neg_apply, repr_jucysMurphy Y b hb top]
  simp only [map_smul, map_add, Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul,
    Module.Basis.repr_self]
  have hyF : ((T.content top : ℤ) : F) ^ 2 = 1 := by exact_mod_cast hy T
  rcases eq_or_ne T' T with rfl | hne
  · obtain ⟨hne0, hdiag⟩ := R_diag_general Y b hb T' k top hk.symm
    have hwd : b.repr (Y.rho lam (swap k top) *ᵥ b T') T' *
        (((T'.content top : ℤ) : F) - ((T'.content k : ℤ) : F)) = 1 := by
      rw [hdiag, ← Int.cast_sub, one_div, inv_mul_cancel₀ hne0]
    have hrelF : ((T'.content k : ℤ) : F) ^ 2 - ((T'.content k : ℤ) : F) * ((T'.content top : ℤ) : F) = 2 := by
      exact_mod_cast hrel T'
    rw [Finsupp.single_eq_same]
    linear_combination (((T'.content k : ℤ) : F) + b.repr (Y.rho lam (swap k top) *ᵥ b T') T') * hyF -
      ((T'.content k : ℤ) : F) * hwd - b.repr (Y.rho lam (swap k top) *ᵥ b T') T' * hrelF
  · rw [Finsupp.single_eq_of_ne hne]
    by_cases hw0 : b.repr (Y.rho lam (swap k top) *ᵥ b T) T' = 0
    · rw [hw0]; ring
    obtain ⟨hother, hpair⟩ := R_support_contents Y b hb T T' k top hk.symm hw0
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (syt_eq_of_content_eq fun i => by
        by_cases hik : i = k
        · rw [hik, h1]
        by_cases hit : i = top
        · rw [hit, h2]
        exact hother i hik hit) hne
    · have hxy : T.content k * T.content top = -1 := by
        have := hy T'
        rw [h2] at this
        linear_combination this - hrel T
      have hxyF : ((T.content k : ℤ) : F) * ((T.content top : ℤ) : F) = -1 := by exact_mod_cast hxy
      rw [h2]
      linear_combination b.repr (Y.rho lam (swap k top) *ᵥ b T) T' * hxyF

end Identity

section Commutant

variable [CharZero F] {lam : Shape N}

omit [CharZero F] in
/-- Paper (e), the identity conjugated by `g`: `ρ((g k, g top)) = -Y_{g top} Y_{g k} Y_{g top}`. -/
theorem rho_conj_swap_eq (k top : Fin N)
    (hid : Y.rho lam (swap k top) =
      -(Y.rhoAlg lam (starElem F top) * Y.rhoAlg lam (starElem F k) * Y.rhoAlg lam (starElem F top)))
    (g : Perm (Fin N)) :
    Y.rho lam (swap (g k) (g top)) =
      -(Y.rhoAlg lam (starElem F (g top)) * Y.rhoAlg lam (starElem F (g k)) * Y.rhoAlg lam (starElem F (g top))) := by
  have hg : Y.rho lam g * Y.rho lam g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc Y.rho lam (swap (g k) (g top)) = Y.rho lam g * (Y.rho lam (swap k top) * Y.rho lam g⁻¹) := by
        rw [swap_apply_apply, map_mul, map_mul, mul_assoc]
    _ = -(Y.rho lam g * (Y.rhoAlg lam (starElem F top) * (Y.rhoAlg lam (starElem F k) *
          (Y.rhoAlg lam (starElem F top) * Y.rho lam g⁻¹)))) := by
        rw [hid]; simp only [neg_mul, mul_neg, mul_assoc]
    _ = _ := by
        rw [rho_mul_star Y lam g, rho_mul_star Y lam g, rho_mul_star Y lam g, hg, mul_one]
        simp only [mul_assoc]

omit [CharZero F] in
/-- A matrix commuting with `ρ` of every transposition commutes with all of `ρ(S_N)` (transpositions generate). -/
theorem commute_rho_of_commute_swaps (Z : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F)
    (hswap : ∀ σ : Perm (Fin N), σ.IsSwap → Z * Y.rho lam σ = Y.rho lam σ * Z) (σ : Perm (Fin N)) :
    Z * Y.rho lam σ = Y.rho lam σ * Z := by
  have hmem : σ ∈ Subgroup.closure {σ : Perm (Fin N) | σ.IsSwap} := by
    rw [Equiv.Perm.closure_isSwap]; exact Subgroup.mem_top σ
  induction hmem using Subgroup.closure_induction with
  | mem x hx => exact hswap x hx
  | one => rw [map_one, mul_one, one_mul]
  | mul x y _ _ hx hy => rw [map_mul, ← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
  | inv x _ hx =>
    have h1 : Y.rho lam x⁻¹ * Y.rho lam x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : Y.rho lam x * Y.rho lam x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc Z * Y.rho lam x⁻¹ = Y.rho lam x⁻¹ * (Y.rho lam x * Z) * Y.rho lam x⁻¹ := by
          rw [← mul_assoc (Y.rho lam x⁻¹), h1, one_mul]
      _ = Y.rho lam x⁻¹ * Z * (Y.rho lam x * Y.rho lam x⁻¹) := by
          rw [← hx]; simp only [mul_assoc]
      _ = Y.rho lam x⁻¹ * Z := by rw [h2, mul_one]

/-- Lemma 4.2 for any shape with the content facts of step (d) at `k = N-2`, `top = N-1`: a matrix commuting with
every `Y_j` is a scalar. -/
theorem eq_scalar_of_commute_stars (b : Module.Basis (SYT lam) F (Fin (Y.dim lam) → F)) (hb : IsYoungBasis Y b)
    (k top : Fin N) (hk : (k : ℕ) + 1 = top) (htop : (top : ℕ) + 1 = N)
    (hy : ∀ T : SYT lam, T.content top ^ 2 = 1)
    (hrel : ∀ T : SYT lam, T.content k ^ 2 - T.content k * T.content top = 2)
    (Z : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F)
    (hZ : ∀ j : Fin N, Z * Y.rhoAlg lam (starElem F j) = Y.rhoAlg lam (starElem F j) * Z) :
    ∃ c : F, Z = c • 1 := by
  have hid := rho_swap_eq_neg_star Y b hb k top hk htop hy hrel
  have hkt : k ≠ top := by intro h; rw [h] at hk; omega
  refine eq_scalar_of_commute_rho Y lam Z (commute_rho_of_commute_swaps Y Z ?_)
  rintro σ ⟨x, y, hxy, rfl⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hkt hxy)
  rw [← hg, ← swap_apply_apply, rho_conj_swap_eq Y k top hid g]
  have hc : ∀ j, Commute Z (Y.rhoAlg lam (starElem F j)) := hZ
  exact (((hc _).mul_right (hc _)).mul_right (hc _)).neg_right

end Commutant

end General

/-- **Lemma 4.2** (v1.02 tex 412-439), for every Young system: on `ν` (the shape of `n² - 1` in the `n × n` box), `n ≥ 2`,
every matrix commuting with all `Y_j = ρ_ν(X^{(j)})` is a scalar. -/
theorem lem_4_2_general [CharZero F] (n : ℕ) (hn : 2 ≤ n) (Y : YoungSystem F (n ^ 2 - 1)) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.InBox n) (Z : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F)
    (hZ : ∀ j : Fin (n ^ 2 - 1), Z * Y.rhoAlg lam (starElem F j) = Y.rhoAlg lam (starElem F j) * Z) :
    ∃ c : F, Z = c • 1 := by
  have hparts := sec_4_1_nu_proved n hn lam hlam
  obtain ⟨b, hb⟩ := Y.youngBasis lam
  have h4 : 4 ≤ n ^ 2 := by nlinarith
  let top : Fin (n ^ 2 - 1) := ⟨n ^ 2 - 2, by omega⟩
  let k : Fin (n ^ 2 - 1) := ⟨n ^ 2 - 3, by omega⟩
  have htop : (top : ℕ) + 1 = n ^ 2 - 1 := by simp only [top]; omega
  have hk : (k : ℕ) + 1 = top := by simp only [k, top]; omega
  have hk2 : (k : ℕ) + 2 = n ^ 2 - 1 := by simp only [k]; omega
  refine eq_scalar_of_commute_stars Y b hb k top hk htop (fun T => ?_)
    (fun T => nu_content_rel n hn lam hparts T top k htop hk2) Z hZ
  rcases nu_content_top n hn lam hparts T top htop with h | h <;> rw [h] <;> norm_num

end NagataHigman.Proofs
