/-
NagataHigman/Proofs/BlocksOrth.lean — the block layer, part 2: characters, the pairing through Fourier inversion,
R6 (the key lemma of the forward criterion), F3 orthogonality, F7 (sign twist), the two-sided ideal of an element,
`A ∩ A' = B_n`. Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Everything is proved for an ARBITRARY Young system `Y : YoungSystem F N`; Statements instantiates the cited one.
Imports: Mathlib + NagataHigman.Defs + Proofs.Blocks only (not Cited, not Statements).
-/
import NagataHigman.Proofs.Blocks

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman Equiv Finset Matrix

variable {F : Type*} [Field F] {N : ℕ}

namespace YoungSystem

variable (Y : YoungSystem F N)

/-! ### Two matrix facts -/

/-- The trace form is nondegenerate on square matrices. -/
lemma eq_zero_of_trace_mul {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (h : ∀ E, trace (M * E) = 0) : M = 0 := by
  ext i j
  have hij := h (Matrix.single j i 1)
  rw [Matrix.trace_mul_single] at hij
  simpa using hij

/-- If `A G X = 0` for every `G` and `X ≠ 0`, then `A = 0`. -/
lemma eq_zero_of_forall_mul_mul {n : ℕ} (A X : Matrix (Fin n) (Fin n) F) (hX : X ≠ 0)
    (h : ∀ G, A * G * X = 0) : A = 0 := by
  obtain ⟨k, l, hkl⟩ : ∃ k l, X k l ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hX (Matrix.ext fun i j => by simpa using hc i j)
  ext i j
  set E : Matrix (Fin n) (Fin n) F := Matrix.single j k 1 with hE
  have h1 := congrFun (congrFun (h E) i) l
  have h2 : (A * E * X) i l = A i j * X k l := by
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · congr 1
      rw [hE, Matrix.mul_apply, Finset.sum_eq_single j]
      · simp
      · intro m _ hm
        simp [Ne.symm hm]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    · intro m _ hm
      rw [hE, Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
      intro m' _
      simp [Ne.symm hm]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [h2, Matrix.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_right hkl

/-! ### Characters and the matrix `Φ_λ(f) = ∑_σ f(σ) ρ_λ(σ⁻¹)` -/

/-- `χ_λ(σ⁻¹) = χ_λ(σ)`: `σ⁻¹` is conjugate to `σ` in `S_N`. -/
lemma trace_rho_inv (lam : Shape N) (σ : Perm (Fin N)) : trace (Y.rho lam σ⁻¹) = trace (Y.rho lam σ) := by
  have hconj : IsConj σ σ⁻¹ := Perm.isConj_iff_cycleType_eq.2 (Perm.cycleType_inv σ).symm
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  calc trace (Y.rho lam σ⁻¹) = trace (Y.rho lam c * Y.rho lam σ * Y.rho lam c⁻¹) := by
        rw [← hc, map_mul, map_mul]
    _ = trace (Y.rho lam c⁻¹ * Y.rho lam c * Y.rho lam σ) := Matrix.trace_mul_cycle _ _ _
    _ = trace (Y.rho lam σ) := by rw [← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]

/-- `Φ_λ(f) = ∑_σ f(σ) ρ_λ(σ⁻¹)` (it is `ρ_λ(f^∨)`; we never need `f^∨` itself). -/
def phiMat (lam : Shape N) (f : GrpAlg F N) : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F :=
  ∑ σ, f.coeff σ • Y.rho lam σ⁻¹

lemma trace_phiMat_mul (lam : Shape N) (f : GrpAlg F N) (τ : Perm (Fin N)) :
    trace (phiMat Y lam f * Y.rho lam τ) = trace (Y.rhoAlg lam f * Y.rho lam τ⁻¹) := by
  rw [rhoAlg_eq_sum Y, phiMat, Finset.sum_mul, Finset.sum_mul, trace_sum, trace_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [smul_mul_assoc, smul_mul_assoc, trace_smul, trace_smul, ← map_mul, ← map_mul]
  congr 1
  rw [← trace_rho_inv Y lam (σ⁻¹ * τ), _root_.mul_inv_rev, inv_inv, map_mul, map_mul, Matrix.trace_mul_comm]

/-- A matrix that has zero trace against every `ρ_λ(τ)` is zero (`ρ_λ` is onto). -/
lemma eq_zero_of_trace_mul_rho (lam : Shape N) (M : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F)
    (h : ∀ τ, trace (M * Y.rho lam τ) = 0) : M = 0 := by
  apply eq_zero_of_trace_mul
  intro E
  obtain ⟨b, rfl⟩ := rhoAlg_surjective Y lam E
  rw [rhoAlg_eq_sum Y, Finset.mul_sum, trace_sum]
  exact Finset.sum_eq_zero fun τ _ => by rw [mul_smul_comm, trace_smul, h τ, smul_zero]

/-- `Φ_λ(f) = 0 ↔ ρ_λ(f) = 0` (the paper's `e_λ^∨ = e_λ`). -/
lemma phiMat_eq_zero_iff (lam : Shape N) (f : GrpAlg F N) : phiMat Y lam f = 0 ↔ Y.rhoAlg lam f = 0 := by
  constructor
  · intro h
    apply eq_zero_of_trace_mul_rho Y lam
    intro τ
    have h1 := trace_phiMat_mul Y lam f τ⁻¹
    rw [h, Matrix.zero_mul, trace_zero, inv_inv] at h1
    exact h1.symm
  · intro h
    apply eq_zero_of_trace_mul_rho Y lam
    intro τ
    rw [trace_phiMat_mul, h, Matrix.zero_mul, trace_zero]

/-- The pairing through Fourier inversion: `⟨f, b⟩ = ∑_μ (f^μ / N!) tr(Φ_μ(f) ρ_μ(b))`. -/
lemma coeffPairing_eq_sum (f b : GrpAlg F N) :
    coeffPairing F f b =
      ∑ mu, ((Y.dim mu : F) / (N.factorial : F)) * trace (phiMat Y mu f * Y.rhoAlg mu b) := by
  have hb : ∀ σ, b.coeff σ =
      ∑ mu, ((Y.dim mu : F) / (N.factorial : F)) * trace (Y.rho mu σ⁻¹ * Y.rhoAlg mu b) :=
    fun σ => Y.fourier b σ
  simp only [coeffPairing, hb, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun mu _ => ?_
  rw [phiMat, Finset.sum_mul, trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [smul_mul_assoc, trace_smul, smul_eq_mul]
  ring

/-! ### C6 (R6) and C7 (F3) -/

/-- C6 (R6), the key lemma of the forward criterion: if `⟨f, g x h⟩ = 0` for all `g, h`, then `ρ_λ(f) = 0` for
every `λ` with `ρ_λ(x) ≠ 0`. -/
theorem rhoAlg_eq_zero_of_pairing [CharZero F] (x f : GrpAlg F N)
    (h : ∀ g k : GrpAlg F N, coeffPairing F f (g * x * k) = 0) (lam : Shape N) (hx : Y.rhoAlg lam x ≠ 0) :
    Y.rhoAlg lam f = 0 := by
  rw [← phiMat_eq_zero_iff]
  have hdim : (Y.dim lam : F) ≠ 0 := by
    intro hd
    have h0 : Y.dim lam = 0 := by exact_mod_cast hd
    have : IsEmpty (Fin (Y.dim lam)) := by rw [h0]; infer_instance
    exact hx (Matrix.ext fun i => isEmptyElim i)
  have hc : ((Y.dim lam : F) / (N.factorial : F)) ≠ 0 :=
    div_ne_zero hdim (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero N))
  have key : ∀ G H, trace (phiMat Y lam f * G * Y.rhoAlg lam x * H) = 0 := by
    intro G H
    obtain ⟨g, hg, rfl⟩ := exists_mem_block Y lam G
    obtain ⟨k, rfl⟩ := rhoAlg_surjective Y lam H
    have hgk := h g k
    rw [coeffPairing_eq_sum Y, Finset.sum_eq_single lam] at hgk
    · rw [map_mul, map_mul] at hgk
      have h2 := (mul_eq_zero.1 hgk).resolve_left hc
      simpa [Matrix.mul_assoc] using h2
    · intro mu _ hmu
      rw [map_mul, map_mul, (mem_block_iff Y).1 hg mu hmu]
      simp
    · intro hh
      exact absurd (Finset.mem_univ lam) hh
  exact eq_zero_of_forall_mul_mul _ _ hx fun G => eq_zero_of_trace_mul _ fun H => key G H

/-- C7 (F3), orthogonality (paper line 267): distinct blocks are orthogonal for `⟨ , ⟩`. -/
theorem coeffPairing_eq_zero_of_mem_block {lam mu : Shape N} (hne : lam ≠ mu) {a b : GrpAlg F N}
    (ha : a ∈ Y.block lam) (hb : b ∈ Y.block mu) : coeffPairing F a b = 0 := by
  rw [coeffPairing_eq_sum Y]
  refine Finset.sum_eq_zero fun nu _ => ?_
  by_cases hnu : nu = mu
  · subst hnu
    have h0 : phiMat Y nu a = 0 := (phiMat_eq_zero_iff Y nu a).2 ((mem_block_iff Y).1 ha nu (Ne.symm hne))
    rw [h0, Matrix.zero_mul, trace_zero, mul_zero]
  · rw [(mem_block_iff Y).1 hb nu hnu, Matrix.mul_zero, trace_zero, mul_zero]

end YoungSystem

end NagataHigman.Proofs

end
