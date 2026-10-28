/-
  NagataHigman/Proofs/ExV110R1.lean - paper 011 v1.10 FINAL (md5 23b0bd3e), coverage review r1: MUST-3 (normalized Γ,
  Γ² = id over ℂ; the λ = (2,1) example's Γ exists; M = κΓ) and MUST-5 (the square has one removable corner; §4.1's
  missing cell). The rows are in Paper/Statements.lean.
  Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Proofs.Ex21Link

universe u

noncomputable section

open NagataHigman NagataHigman.Cited Equiv Finset Matrix

namespace NagataHigman.Proofs.ExV110R1

/-- (T3) over ℂ: rescaling `Γ₀` (with `Γ₀² = c·1`, `c ≠ 0`) by a square root `d` of `c` gives `Γ² = 1`. -/
theorem gamma_normalized (N : ℕ) (Y : YoungSystem ℂ N) (lam : Shape N) (h : lam.conjugate = lam) :
    ∃ Γ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) ℂ, Γ * Γ = 1 ∧
      ∀ σ : Perm (Fin N), Γ * Y.rho lam σ = ((Perm.sign σ : ℤ) : ℂ) • (Y.rho lam σ * Γ) := by
  obtain ⟨Γ₀, hu, hΓ₀⟩ := NagataHigman.Proofs.gamma_exists Y lam h
  obtain ⟨c, hc0, hc⟩ := NagataHigman.Proofs.gamma_sq_scalar Y lam Γ₀ hu hΓ₀
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_eq_mul_self c
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hc0 (by simpa using hd)
  refine ⟨d⁻¹ • Γ₀, ?_, fun σ => ?_⟩
  · have hdd : d⁻¹ * d⁻¹ * c = 1 := by
      rw [hd]
      field_simp
    rw [smul_mul_smul_comm, hc, smul_smul, hdd, one_smul]
  · rw [smul_mul_assoc, hΓ₀ σ, mul_smul_comm, smul_comm]

open NagataHigman.Proofs.ExV110 in
/-- `(2,1)` is self-conjugate: its diagram `{(0,0), (0,1), (1,0)}` is its own transpose. -/
theorem shape21_self_conjugate : shape21.conjugate = shape21 := by
  have hsort : shape21.parts.sort (· ≥ ·) = [2, 1] := by
    have hparts : shape21.parts = (([2, 1] : List ℕ) : Multiset ℕ) := by first | rfl | simp [shape21]
    rw [hparts, Multiset.coe_sort]
    apply List.mergeSort_eq_self
    decide
  have hcells : ∀ i j : ℕ, (i, j) ∈ shape21.diagram.cells ↔ (i = 0 ∧ j < 2) ∨ (i = 1 ∧ j < 1) := by
    intro i j
    rw [mem_cells_of_sort_eq hsort]
    constructor
    · rintro ⟨hi, hj⟩
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i <;> simp_all
    · rintro (⟨rfl, hj⟩ | ⟨rfl, hj⟩) <;> exact ⟨by simp, by simpa using hj⟩
  have htr : (YoungDiagram.ofPartition shape21).transpose = YoungDiagram.ofPartition shape21 := by
    ext ⟨i, j⟩
    have h1 := hcells j i
    have h2 := hcells i j
    simp only [Shape.diagram, YoungDiagram.mem_cells] at h1 h2
    simp only [YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Prod.swap_prod_mk, h1, h2]
    omega
  have hof : YoungDiagram.ofPartition shape21.conjugate = YoungDiagram.ofPartition shape21 := by
    unfold Nat.Partition.conjugate
    rw [YoungDiagram.ofPartition_toPartition]
    exact htr
  apply Nat.Partition.ext
  have h1 := YoungDiagram.rowLens_ofPartition_eq_sort_parts shape21.conjugate
  have h2 := YoungDiagram.rowLens_ofPartition_eq_sort_parts shape21
  rw [hof, h2] at h1
  have h3 := congrArg (fun l : List ℕ => (l : Multiset ℕ)) h1
  simpa [Multiset.sort_eq] using h3.symm

/-- Lemma 4.3 (v1.10 l. 595), "M = κΓ, as Γ² = id": for square matrices over any field. -/
theorem M_eq_of_sq_one {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] (Γ M : Matrix n n K) (κ : K)
    (hsq : Γ * Γ = 1) (hM : Γ * M = κ • 1) : M = κ • Γ := by
  calc M = (Γ * Γ) * M := by rw [hsq, one_mul]
    _ = Γ * (Γ * M) := by rw [mul_assoc]
    _ = κ • Γ := by rw [hM, mul_smul_comm, mul_one]

open NagataHigman.Proofs.ExV110 NagataHigman.Proofs.Ex21 Complex in
/-- Example λ = (2,1) (v1.10 l. 503-513): `Ex21.Rows.ex_lam21_orthogonal` plus the existence half of l. 511: `±iΓ₀` IS a `Γ`
of (T3) (in the basis `b'`, the normalized `Γ` or `-Γ` has matrix `iΓ₀`). -/
theorem ex_lam21_orthogonal_full (Y : YoungSystem ℂ 3)
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
        trace (Y.rho shape21 (List.formPerm [0, 2, 1]) * Γ) = I * (Real.sqrt 3 : ℂ)) ∧
      ∃ Γ : Matrix (Fin (Y.dim shape21)) (Fin (Y.dim shape21)) ℂ,
        (∀ σ : Perm (Fin 3), Γ * Y.rho shape21 σ = ((Perm.sign σ : ℤ) : ℂ) • (Y.rho shape21 σ * Γ)) ∧ Γ * Γ = 1 ∧
        LinearMap.toMatrix b' b' (Matrix.toLin' Γ) = I • Gamma0 := by
  obtain ⟨b', h1, h2, h3, h4, h5⟩ := NagataHigman.Proofs.Ex21.Rows.ex_lam21_orthogonal Y b hb
  refine ⟨b', h1, h2, h3, h4, h5, ?_⟩
  obtain ⟨Γ, hsq, hanti⟩ := gamma_normalized 3 Y shape21 shape21_self_conjugate
  rcases h4 Γ hanti hsq with hpos | hneg
  · exact ⟨Γ, hanti, hsq, hpos⟩
  · refine ⟨-Γ, fun σ => ?_, by rw [neg_mul_neg, hsq], ?_⟩
    · rw [neg_mul, hanti σ, mul_neg, smul_neg]
    · rw [map_neg, map_neg, hneg, neg_smul, neg_neg]

/-! ## MUST-5: the square has one removable corner; §4.1's missing cell -/

theorem sort_square (n : ℕ) : (Multiset.replicate n n).sort (· ≥ ·) = List.replicate n n := by
  rw [← Multiset.coe_replicate, Multiset.coe_sort]
  apply List.mergeSort_eq_self
  exact List.pairwise_replicate.2 (Or.inr le_rfl)

/-- The cells of the square `(n^n)` are exactly the `(i, j)` with `i, j < n`. -/
theorem square_mem_cells (n : ℕ) (lam : Shape (n ^ 2)) (h : lam.InBox n) {i j : ℕ} :
    (i, j) ∈ lam.diagram.cells ↔ i < n ∧ j < n := by
  have hp := NagataHigman.Proofs.lem_3_1_square_proved n lam h
  rw [mem_cells_of_sort_eq (w := List.replicate n n) (by rw [hp]; exact sort_square n)]
  simp

theorem square_one_corner (n : ℕ) (hn : 1 ≤ n) (lam : Shape (n ^ 2)) (h : lam.InBox n) (c : ℕ × ℕ) :
    (c ∈ lam.diagram.cells ∧ (c.1, c.2 + 1) ∉ lam.diagram.cells ∧ (c.1 + 1, c.2) ∉ lam.diagram.cells) ↔
      c = (n - 1, n - 1) := by
  obtain ⟨a, b⟩ := c
  simp only [square_mem_cells n lam h, Prod.mk.injEq]
  omega

/-- The cells of `ν = (n^{n-1}, n-1)` (the only partition of `n² - 1` in the box) are the box minus `(n-1, n-1)`. -/
theorem nu_mem_cells (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1)) (h : lam.InBox n) {i j : ℕ} :
    (i, j) ∈ lam.diagram.cells ↔ i < n ∧ j < n ∧ ¬ (i = n - 1 ∧ j = n - 1) := by
  have hp := NagataHigman.Proofs.sec_4_1_nu_proved n hn lam h
  rw [mem_cells_of_sort_eq (w := List.replicate (n - 1) n ++ [n - 1]) (by rw [hp]; exact sort_nu n)]
  constructor
  · rintro ⟨hi, hj⟩
    simp only [List.length_append, List.length_replicate, List.length_singleton] at hi
    rw [List.getElem_append] at hj
    split_ifs at hj with h1
    · simp only [List.getElem_replicate] at hj
      simp only [List.length_replicate] at h1
      omega
    · simp only [List.getElem_singleton] at hj
      simp only [List.length_replicate] at h1
      omega
  · rintro ⟨hi, hj, hne⟩
    refine ⟨by simp only [List.length_append, List.length_replicate, List.length_singleton]; omega, ?_⟩
    rw [List.getElem_append]
    split_ifs with h1
    · simp only [List.getElem_replicate]
      omega
    · simp only [List.getElem_singleton]
      simp only [List.length_replicate] at h1
      omega

theorem sec_4_1_one_cell (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1)) (h : lam.InBox n) :
    lam.diagram.cells ⊆ Finset.range n ×ˢ Finset.range n ∧
      (Finset.range n ×ˢ Finset.range n) \ lam.diagram.cells = {(n - 1, n - 1)} := by
  constructor
  · rintro ⟨i, j⟩ hc
    rw [nu_mem_cells n hn lam h] at hc
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  · ext ⟨i, j⟩
    simp only [Finset.mem_sdiff, Finset.mem_product, Finset.mem_range, Finset.mem_singleton, Prod.mk.injEq,
      nu_mem_cells n hn lam h]
    omega

end NagataHigman.Proofs.ExV110R1

end
