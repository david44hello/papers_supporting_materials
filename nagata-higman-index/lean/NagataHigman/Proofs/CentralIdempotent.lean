/-
NagataHigman/Proofs/CentralIdempotent.lean — the Young-system-free central idempotent `e_λ` (Defs/CentralIdempotent.lean)
in every Young system: `ρ_μ(e_λ) = δ_{λμ} · 1`, `e_λ` are orthogonal central idempotents summing to 1, and
`Y.block λ = F[S_N] · e_λ`; so the block is the same for every Young system (paper v1.02 line 186: `I_λ = F[S_N] e_λ`).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route. In a Young basis of `ρ_μ`, `J_k` acts on `v_U` by `c_U(k) ∈ (-N, N)`, so the Lagrange factor at `x` acts by
`[c_U(k) = x]`, and the summand of `T` acts by `[c_U = c_T]`. Equal content vectors force equal cells (induction on the
entry, as in Tableaux.syt_eq_of_content_eq, now across two shapes), hence equal diagrams and equal shapes. So
`ρ_μ(e_λ) v_U = 0` for `μ ≠ λ`, and `= v_U` for `μ = λ` (only `T = U` contributes). The rest is `wedderburn`.
-/
import NagataHigman.Defs.CentralIdempotent
import NagataHigman.Proofs.Blocks
import NagataHigman.Proofs.Tableaux

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman Finset Matrix

variable {F : Type*} [Field F] {N : ℕ}

/-! ### Contents determine shapes -/

section Contents

variable {lam mu : Shape N}

private theorem numRows_le' (lam : Shape N) : lam.numRows ≤ N := by
  have h := Multiset.card_nsmul_le_sum fun x (hx : x ∈ lam.parts) => lam.parts_pos hx
  rw [smul_eq_mul, lam.parts_sum] at h
  unfold Shape.numRows
  omega

private theorem firstRow_le' (lam : Shape N) : lam.firstRow ≤ N :=
  Multiset.sup_le.2 fun _ hp => lam.parts_sum ▸ Multiset.le_sum_of_mem hp

/-- Every content of a standard tableau of a shape of `N` lies in `(-N, N)`. -/
theorem content_mem_contentRange (T : SYT lam) (k : Fin N) : T.content k ∈ contentRange N := by
  rcases hp : T.pos k with ⟨i, j⟩
  have hmem : (i, j) ∈ lam.diagram.cells := hp ▸ T.pos_mem k
  have hrow := lt_numRows_of_mem hmem
  have hcol := lt_firstRow_of_mem (lam.diagram.up_left_mem (Nat.zero_le i) le_rfl hmem)
  have h1 := numRows_le' lam
  have h2 := firstRow_le' lam
  rw [contentRange, Finset.mem_Ioo, SYT.content, hp]
  dsimp only
  omega

/-- Agreement below `k` and a weakly north-west cell at `k` force equal cells at `k` (two shapes). -/
private theorem pos_eq_of_le_of_agree' {T : SYT lam} {U : SYT mu} (k : Fin N) (hlt : ∀ m < k, T.pos m = U.pos m)
    (h1 : (T.pos k).1 ≤ (U.pos k).1) (h2 : (T.pos k).2 ≤ (U.pos k).2) : T.pos k = U.pos k := by
  obtain ⟨m, hm, hmk⟩ := exists_le_of_le U h1 h2
  rcases hmk.lt_or_eq with hmk | rfl
  · exact absurd (T.pos_injective ((hlt m hmk).trans hm)) (ne_of_lt hmk)
  · exact hm.symm

/-- Equal content vectors force equal cells, also for tableaux of two different shapes. -/
theorem pos_eq_of_content_eq (T : SYT lam) (U : SYT mu) (h : ∀ k, T.content k = U.content k) : T.pos = U.pos := by
  funext k
  induction k using WellFoundedLT.induction with
  | _ k ih =>
    have hc := h k
    unfold SYT.content at hc
    rcases le_total (T.pos k).1 (U.pos k).1 with h1 | h1
    · exact pos_eq_of_le_of_agree' k ih h1 (by omega)
    · exact (pos_eq_of_le_of_agree' (T := U) (U := T) k (fun m hm => (ih m hm).symm) h1 (by omega)).symm

/-- Equal content vectors force equal shapes. -/
theorem shape_eq_of_content_eq (T : SYT lam) (U : SYT mu) (h : ∀ k, T.content k = U.content k) : lam = mu := by
  have hpos := pos_eq_of_content_eq T U h
  have hcells : lam.diagram.cells = mu.diagram.cells := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, rfl⟩ := exists_pos_eq T hx
      rw [hpos]
      exact U.pos_mem m
    · intro hx
      obtain ⟨m, rfl⟩ := exists_pos_eq U hx
      rw [← hpos]
      exact T.pos_mem m
  have hrow := congrArg YoungDiagram.rowLens (YoungDiagram.ext hcells)
  unfold Shape.diagram at hrow
  rw [YoungDiagram.rowLens_ofPartition_eq_sort_parts, YoungDiagram.rowLens_ofPartition_eq_sort_parts] at hrow
  apply Nat.Partition.ext
  rw [← Multiset.sort_eq lam.parts (· ≥ ·), hrow, Multiset.sort_eq]

end Contents

/-! ### `e_λ` in a Young system -/

/-- A polynomial in a matrix acts on an eigenvector by its value at the eigenvalue. -/
theorem aeval_mulVec_of_eigen {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (v : ι → F) (c : F)
    (hv : A *ᵥ v = c • v) (p : Polynomial F) : Polynomial.aeval A p *ᵥ v = p.eval c • v := by
  have hpow : ∀ n : ℕ, A ^ n *ᵥ v = c ^ n • v := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
    | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Matrix.add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_mulVec, hpow, smul_smul, Polynomial.eval_monomial]

namespace YoungSystem

variable (Y : YoungSystem F N)

/-- The Lagrange factor at `x ∈ (-N, N)` acts on a Young basis vector `v_U` by `[c_U(k) = x]`. -/
theorem rhoAlg_jmFactor_mulVec [CharZero F] {mu : Shape N} (b : Module.Basis (SYT mu) F (Fin (Y.dim mu) → F))
    (hb : ∀ (U : SYT mu) (k : Fin N), Y.rhoAlg mu (jucysMurphy F k) *ᵥ b U = ((U.content k : ℤ) : F) • b U)
    (k : Fin N) {x : ℤ} (hx : x ∈ contentRange N) (U : SYT mu) :
    Y.rhoAlg mu (jmFactor F k x) *ᵥ b U = (if U.content k = x then (1 : F) else 0) • b U := by
  rw [jmFactor, ← Polynomial.aeval_algHom_apply, aeval_mulVec_of_eigen _ _ _ (hb U k)]
  congr 1
  split_ifs with h
  · rw [h]
    exact Lagrange.eval_basis_self (Int.cast_injective.injOn) hx
  · exact Lagrange.eval_basis_of_ne (Ne.symm h) (content_mem_contentRange U k)

/-- A product (in list order) of elements acting diagonally on `v_U` acts by the product of the scalars. -/
theorem rhoAlg_list_prod_mulVec {mu : Shape N} (b : Module.Basis (SYT mu) F (Fin (Y.dim mu) → F)) (U : SYT mu)
    (f : Fin N → GrpAlg F N) (g : Fin N → F) (hfg : ∀ k, Y.rhoAlg mu (f k) *ᵥ b U = g k • b U) :
    ∀ l : List (Fin N), Y.rhoAlg mu (l.map f).prod *ᵥ b U = (l.map g).prod • b U
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.prod_cons, map_mul, ← Matrix.mulVec_mulVec, rhoAlg_list_prod_mulVec b U f g hfg l,
      Matrix.mulVec_smul, hfg, smul_smul, List.map_cons, List.prod_cons, mul_comm]

theorem list_prod_ite {α : Type*} (p : α → Prop) [DecidablePred p] :
    ∀ l : List α, (l.map fun a => if p a then (1 : F) else 0).prod = if ∀ a ∈ l, p a then 1 else 0
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.prod_cons, list_prod_ite p l]
    by_cases ha : p a <;> by_cases hl : ∀ b ∈ l, p b <;> simp [ha, hl]

/-- `ρ_μ(e_λ) = δ_{λμ} · 1` for EVERY Young system. -/
theorem rhoAlg_youngIdem [CharZero F] (lam mu : Shape N) :
    Y.rhoAlg mu (youngIdem F lam) = if mu = lam then 1 else 0 := by
  let _ := Fintype.ofFinite (SYT lam)
  obtain ⟨b, hb⟩ := Y.youngBasis mu
  apply Matrix.toLin'.injective
  apply b.ext
  intro U
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, youngIdem, map_sum, Matrix.sum_mulVec]
  have hT : ∀ T : SYT lam, Y.rhoAlg mu ((List.finRange N).map fun k => jmFactor F k (T.content k)).prod *ᵥ b U =
      (if ∀ k, U.content k = T.content k then (1 : F) else 0) • b U := by
    intro T
    rw [rhoAlg_list_prod_mulVec Y b U _ _ (fun k => rhoAlg_jmFactor_mulVec Y b hb k
      (content_mem_contentRange T k) U), list_prod_ite]
    simp only [List.mem_finRange, true_implies]
  simp_rw [hT, ← Finset.sum_smul]
  split_ifs with hmu
  · subst hmu
    rw [Matrix.one_mulVec]
    convert one_smul F (b U) using 2
    rw [Finset.sum_eq_single U]
    · simp
    · intro T _ hTU
      rw [ite_eq_right_iff]
      intro h
      exact absurd (syt_eq_of_content_eq h).symm hTU
    · intro h
      exact absurd (Finset.mem_univ U) h
  · rw [Matrix.zero_mulVec]
    convert zero_smul F (b U) using 2
    apply Finset.sum_eq_zero
    intro T _
    rw [ite_eq_right_iff]
    intro h
    exact absurd (shape_eq_of_content_eq U T h) hmu

include Y in
/-- `e_λ` is idempotent. -/
theorem youngIdem_mul_self [CharZero F] (lam : Shape N) : youngIdem F lam * youngIdem F lam = youngIdem F lam := by
  apply ext_of_rhoAlg Y
  intro mu
  rw [map_mul, rhoAlg_youngIdem Y]
  split_ifs <;> simp

include Y in
/-- `e_λ e_μ = 0` for `λ ≠ μ`. -/
theorem youngIdem_mul_of_ne [CharZero F] {lam mu : Shape N} (h : lam ≠ mu) :
    youngIdem F lam * youngIdem F mu = 0 := by
  apply eq_zero_of_forall_rhoAlg Y
  intro nu
  rw [map_mul, rhoAlg_youngIdem Y, rhoAlg_youngIdem Y]
  split_ifs with h1 h2 <;> simp_all

include Y in
/-- `e_λ` is central. -/
theorem youngIdem_comm [CharZero F] (lam : Shape N) (a : GrpAlg F N) : youngIdem F lam * a = a * youngIdem F lam := by
  apply ext_of_rhoAlg Y
  intro mu
  rw [map_mul, map_mul, rhoAlg_youngIdem Y]
  split_ifs <;> simp

include Y in
/-- `Σ_λ e_λ = 1`. -/
theorem sum_youngIdem [CharZero F] : ∑ lam : Shape N, youngIdem F lam = 1 := by
  apply ext_of_rhoAlg Y
  intro mu
  rw [map_sum, map_one]
  simp_rw [rhoAlg_youngIdem Y]
  rw [Finset.sum_ite_eq]
  simp

/-- The block of `λ` is the left ideal `F[S_N] · e_λ` (paper v1.02 line 186), in EVERY Young system. -/
theorem block_eq_range_mulRight [CharZero F] (lam : Shape N) :
    Y.block lam = LinearMap.range (LinearMap.mulRight F (youngIdem F lam)) := by
  ext a
  rw [mem_block_iff Y, LinearMap.mem_range]
  constructor
  · intro ha
    refine ⟨a, ?_⟩
    rw [LinearMap.mulRight_apply]
    apply ext_of_rhoAlg Y
    intro mu
    rw [map_mul, rhoAlg_youngIdem Y]
    split_ifs with hmu
    · rw [mul_one]
    · rw [mul_zero, ha mu hmu]
  · rintro ⟨x, rfl⟩ mu hmu
    rw [LinearMap.mulRight_apply, map_mul, rhoAlg_youngIdem Y]
    simp [hmu]

/-- The block does not depend on the Young system. -/
theorem block_eq_block [CharZero F] (Y' : YoungSystem F N) (lam : Shape N) : Y.block lam = Y'.block lam := by
  rw [block_eq_range_mulRight Y, block_eq_range_mulRight Y']

end YoungSystem

end NagataHigman.Proofs

end
