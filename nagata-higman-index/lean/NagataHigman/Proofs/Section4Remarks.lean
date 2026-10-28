/-
NagataHigman/Proofs/Section4Remarks.lean — leaf L: (T2) support in position form, v1.02 Remark 4.3 (cut in v1.03) (rectangle stars are
scalars), Remark 4.4 element (`(0 1 2) - (0 2 1) ∈ C_3 ∩ B_2^{(3)}`, nonzero).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Everything is proved for an ARBITRARY Young system `Y`; Statements instantiates `youngSystem F N`.
  L1 `R_support_pos`: a nonzero entry `ρ(s)_{T'T}` (`s = (k k+1)`) forces `T' = T` or `T'.pos = T.pos ∘ s`
     (from the content form `R_support_contents`: the contents of `T'` are those of `T` with `k, k+1` exchanged,
     and such a content vector pins the cells, `pos_eq_comp_swap_of_content`).
  L2 `rhoAlg_starElem_rectangle`: on a rectangle every `ρ(X^{(j)})` is the same scalar (one corner: `ρ(J_top)` is the
     scalar `c - r`, and `X^{(j)}` is a conjugate of `X^{(top)} = J_top`).
  L3 `rem_4_5_element_of`: the shapes of 3 outside the 2×2 box are the row and the column; each has ONE standard
     tableau, so `ρ_μ` is 1-dimensional, its matrices commute, and `ρ_μ((0 2 1)) = ρ_μ(s (0 1 2) s) = ρ_μ((0 1 2))`.
-/
import NagataHigman.Proofs.Blocks
import NagataHigman.Proofs.Tableaux
import NagataHigman.Proofs.JucysMurphy
import NagataHigman.Proofs.TwoCorner.Spectral

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman Equiv Finset Matrix

variable {F : Type*} [Field F]

/-! ### L1: the support of `ρ(s)` in position form -/

section Position

variable {N : ℕ} {lam : Shape N}

/-- For an adjacent swap `s = (k k+1)`, `a < b` and `s b < s a` force `a = k`, `b = k+1`. -/
private theorem swap_adj_order {k l a b : Fin N} (hkl : (l : ℕ) = k + 1) (hab : a < b)
    (hba : swap k l b < swap k l a) : a = k ∧ b = l := by
  rw [Fin.lt_def] at hab hba
  simp only [swap_apply_def] at hba
  simp only [Fin.ext_iff]
  split_ifs at hba with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only [Fin.ext_iff] at * <;> omega

/-- If the contents of `T'` are those of `T` with the entries `k, k+1` exchanged, then so are the cells. -/
theorem pos_eq_comp_swap_of_content (T T' : SYT lam) (k l : Fin N) (hkl : (l : ℕ) = k + 1)
    (hc : ∀ i, T'.content i = T.content (swap k l i)) : T'.pos = T.pos ∘ swap k l := by
  funext m
  induction m using WellFoundedLT.induction with
  | _ m ih =>
    have hcm := hc m
    unfold SYT.content at hcm
    simp only [Function.comp_apply] at ih ⊢
    rcases le_total (T.pos (swap k l m)).1 (T'.pos m).1 with h1 | h1
    · obtain ⟨m', hm', hm'm⟩ := exists_le_of_le T' (k := m) (c := T.pos (swap k l m)) h1 (by omega)
      rcases hm'm.lt_or_eq with hlt | rfl
      · rw [ih m' hlt] at hm'
        exact absurd ((swap k l).injective (T.pos_injective hm')) (ne_of_lt hlt)
      · exact hm'
    · obtain ⟨m'', hm'', hle⟩ := exists_le_of_le T (k := swap k l m) (c := T'.pos m) h1 (by omega)
      rcases hle.lt_or_eq with hlt | rfl
      · exfalso
        have hPi : T.pos (swap k l (swap k l m'')) = T'.pos m := by rw [swap_apply_self]; exact hm''
        rcases lt_trichotomy (swap k l m'') m with him | heq | hmi
        · have h := ih _ him
          rw [hPi] at h
          exact absurd (T'.pos_injective h) (ne_of_lt him)
        · rw [← heq, swap_apply_self] at hlt
          exact lt_irrefl _ hlt
        · rw [← swap_apply_self k l m''] at hlt
          obtain ⟨hmk, hi⟩ := swap_adj_order hkl hmi hlt
          have hm''k : m'' = k := by rw [← swap_apply_self k l m'', hi, swap_apply_right]
          rw [hm''k, hmk] at hm''
          have hck := hc m
          rw [hmk, swap_apply_left] at hck
          apply J_consecutive N lam T k l hkl
          rw [← hck]
          unfold SYT.content
          rw [hm'']
      · exact hm''.symm

end Position

namespace YoungSystem

variable {N : ℕ} (Y : YoungSystem F N)

/-- **(T2)**, support (position form, Statements `R_support`): a nonzero entry `ρ(s)_{T'T}`, `s = (k k+1)`, forces
`T' = T` or `T'` = `T` with the entries `k, k+1` exchanged. -/
theorem R_support_pos [CharZero F] {lam : Shape N} (b : Module.Basis (SYT lam) F (Fin (Y.dim lam) → F))
    (hb : IsYoungBasis Y b) (T T' : SYT lam) (k l : Fin N) (hkl : (l : ℕ) = k + 1)
    (hne : b.repr (Y.rho lam (swap k l) *ᵥ b T) T' ≠ 0) :
    T' = T ∨ T'.pos = T.pos ∘ swap k l := by
  obtain ⟨hoff, hkl'⟩ := R_support_contents Y b hb T T' k l hkl hne
  rcases hkl' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    apply syt_eq_of_content_eq
    intro i
    by_cases hik : i = k
    · subst hik
      exact h1
    by_cases hil : i = l
    · subst hil
      exact h2
    exact hoff i hik hil
  · right
    apply pos_eq_comp_swap_of_content T T' k l hkl
    intro i
    by_cases hik : i = k
    · subst hik
      rw [swap_apply_left]
      exact h1
    by_cases hil : i = l
    · subst hil
      rw [swap_apply_right]
      exact h2
    rw [swap_apply_of_ne_of_ne hik hil]
    exact hoff i hik hil

/-! ### L2: v1.02 Remark 4.3 (cut in v1.03), rectangles -/

/-- If every standard tableau of `λ` has `top` in a cell of content `cc`, then `ρ_λ(J_top) = cc • 1`. -/
theorem rhoAlg_jucysMurphy_eq_smul (lam : Shape N) (top : Fin N) (cc : ℤ) (h : ∀ T : SYT lam, T.content top = cc) :
    Y.rhoAlg lam (jucysMurphy F top) = ((cc : ℤ) : F) • 1 := by
  obtain ⟨b, hb⟩ := Y.youngBasis lam
  apply Matrix.toLin'.injective
  apply b.ext
  intro T
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hT := hb T top
  rw [h T] at hT
  exact hT

/-- **v1.02 Remark 4.3 (cut in v1.03)** (paper v1.02 line 446): for a rectangle `λ = (c^r)` every `ρ_λ(X^{(j)})` is the same scalar. -/
theorem rhoAlg_starElem_rectangle (lam : Shape N) (r c : ℕ) (hrect : lam.parts = Multiset.replicate r c) :
    ∃ cc : F, ∀ j : Fin N, Y.rhoAlg lam (starElem F j) = cc • 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨0, fun j => j.elim0⟩
  have hsum : r * c = N := by
    have := lam.parts_sum
    rw [hrect, Multiset.sum_replicate, smul_eq_mul] at this
    exact this
  have hr : 1 ≤ r := Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at hsum; omega
  have hc : 1 ≤ c := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hsum; omega
  let top : Fin N := ⟨N - 1, by omega⟩
  have htop : (top : ℕ) + 1 = N := by
    show N - 1 + 1 = N
    omega
  set cc : ℤ := ((c - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ)
  have hJ : Y.rhoAlg lam (jucysMurphy F top) = ((cc : ℤ) : F) • 1 := by
    apply rhoAlg_jucysMurphy_eq_smul Y lam top cc
    intro T
    simp [SYT.content, rect_pos_top lam r c hr hc hrect T top htop, cc]
  refine ⟨((cc : ℤ) : F), fun j => ?_⟩
  have hconj := perm_conj_starElem F (swap top j) top
  rw [swap_apply_left, starElem_top F top htop] at hconj
  rw [← hconj, map_mul, map_mul, hJ, rhoAlg_perm Y, rhoAlg_perm Y, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, ← map_mul, mul_inv_cancel, map_one]

/-- A Young system's `f^λ` is the number of standard tableaux, so at most one tableau gives `f^λ ≤ 1`. -/
theorem dim_le_one_of_subsingleton (lam : Shape N) [Subsingleton (SYT lam)] : Y.dim lam ≤ 1 := by
  obtain ⟨b, -⟩ := Y.youngBasis lam
  have := FiniteDimensional.fintypeBasisIndex b
  have h := Module.finrank_eq_card_basis b
  rw [Module.finrank_fin_fun] at h
  rw [h]
  exact Fintype.card_le_one_iff_subsingleton.2 inferInstance

end YoungSystem

/-! ### L3: Remark 4.4, the element for `n = 2` -/

section Three

variable {N : ℕ} {lam : Shape N}

/-- Agreement below `k` and a weakly north-west cell at `k` force equal cells at `k`. -/
private theorem pos_eq_of_le_of_agree {T T' : SYT lam} (k : Fin N) (hlt : ∀ m < k, T.pos m = T'.pos m)
    (h1 : (T.pos k).1 ≤ (T'.pos k).1) (h2 : (T.pos k).2 ≤ (T'.pos k).2) : T.pos k = T'.pos k := by
  obtain ⟨m, hm, hmk⟩ := exists_le_of_le T' h1 h2
  rcases hmk.lt_or_eq with hmk | rfl
  · exact absurd (T.pos_injective ((hlt m hmk).trans hm)) (ne_of_lt hmk)
  · exact hm.symm

/-- If every cell of `λ` lies in row 0, `λ` has at most one standard tableau. -/
theorem syt_subsingleton_of_row (h : ∀ x ∈ lam.diagram.cells, x.1 = 0) : Subsingleton (SYT lam) := by
  refine ⟨fun T T' => syt_ext ?_⟩
  funext k
  induction k using WellFoundedLT.induction with
  | _ k ih =>
    have hT := h _ (T.pos_mem k)
    have hT' := h _ (T'.pos_mem k)
    rcases le_total (T.pos k).2 (T'.pos k).2 with h2 | h2
    · exact pos_eq_of_le_of_agree k ih (by omega) h2
    · exact (pos_eq_of_le_of_agree (T := T') (T' := T) k (fun m hm => (ih m hm).symm) (by omega) h2).symm

/-- If every cell of `λ` lies in column 0, `λ` has at most one standard tableau. -/
theorem syt_subsingleton_of_col (h : ∀ x ∈ lam.diagram.cells, x.2 = 0) : Subsingleton (SYT lam) := by
  refine ⟨fun T T' => syt_ext ?_⟩
  funext k
  induction k using WellFoundedLT.induction with
  | _ k ih =>
    have hT := h _ (T.pos_mem k)
    have hT' := h _ (T'.pos_mem k)
    rcases le_total (T.pos k).1 (T'.pos k).1 with h1 | h1
    · exact pos_eq_of_le_of_agree k ih h1 (by omega)
    · exact (pos_eq_of_le_of_agree (T := T') (T' := T) k (fun m hm => (ih m hm).symm) h1 (by omega)).symm

/-- A one-row shape has all its cells in row 0. -/
theorem row_eq_zero_of_numRows_le_one (hr : lam.numRows ≤ 1) : ∀ x ∈ lam.diagram.cells, x.1 = 0 := by
  rintro ⟨i, j⟩ hx
  have := lt_numRows_of_mem hx
  dsimp only
  omega

/-- A one-column shape has all its cells in column 0. -/
theorem col_eq_zero_of_firstRow_le_one (hc : lam.firstRow ≤ 1) : ∀ x ∈ lam.diagram.cells, x.2 = 0 := by
  rintro ⟨i, j⟩ hx
  have := lt_firstRow_of_mem (lam.diagram.up_left_mem (Nat.zero_le i) le_rfl hx)
  dsimp only
  omega

/-- The shapes of 3 outside the 2×2 box are the row `(3)` and the column `(1,1,1)`. -/
theorem shape_three_outside_box (mu : Shape 3) (h : ¬ mu.InBox 2) : mu.numRows ≤ 1 ∨ mu.firstRow ≤ 1 := by
  unfold Shape.InBox at h
  rw [not_and_or, not_le, not_le] at h
  have hsum := mu.parts_sum
  have hbound : ∀ p ∈ mu.parts, p + (Multiset.card mu.parts - 1) ≤ 3 := by
    intro p hp
    have h1 := Multiset.sum_erase hp
    have h2 : Multiset.card (mu.parts.erase p) • 1 ≤ (mu.parts.erase p).sum :=
      Multiset.card_nsmul_le_sum fun x hx => mu.parts_pos (Multiset.mem_of_mem_erase hx)
    rw [Multiset.card_erase_of_mem hp, smul_eq_mul, mul_one, Nat.pred_eq_sub_one] at h2
    omega
  rcases h with h | h
  · right
    unfold Shape.numRows at h
    unfold Shape.firstRow
    refine Multiset.sup_le.2 fun p hp => ?_
    have := hbound p hp
    omega
  · left
    unfold Shape.firstRow at h
    obtain ⟨p, hp, hp3⟩ : ∃ p ∈ mu.parts, 2 < p := by
      by_contra hne
      simp only [not_exists, not_and, not_lt] at hne
      have := Multiset.sup_le.2 hne
      omega
    have := hbound p hp
    unfold Shape.numRows
    omega

end Three

/-- Square matrices over a one-point index commute. -/
theorem matrix_mul_comm_of_subsingleton {ι : Type*} [Fintype ι] [Subsingleton ι] (A B : Matrix ι ι F) :
    A * B = B * A := by
  ext i j
  obtain rfl := Subsingleton.elim i j
  simp only [Matrix.mul_apply, Fintype.sum_subsingleton _ i, mul_comm]

/-- On a shape with one standard tableau, `ρ_μ((0 1 2)) = ρ_μ((0 2 1))`: `ρ_μ` is 1-dimensional, so it is constant
on the conjugacy class. -/
theorem rhoAlg_rot_sub_eq_zero (Y : YoungSystem F 3) (mu : Shape 3) [Subsingleton (SYT mu)] :
    Y.rhoAlg mu (perm F (finRotate 3) - perm F (finRotate 3)⁻¹) = 0 := by
  have : Subsingleton (Fin (Y.dim mu)) :=
    Fin.subsingleton_iff_le_one.2 (YoungSystem.dim_le_one_of_subsingleton Y mu)
  have hconj : (finRotate 3)⁻¹ = swap 0 1 * finRotate 3 * swap 0 1 := by decide
  rw [map_sub, YoungSystem.rhoAlg_perm Y, YoungSystem.rhoAlg_perm Y, hconj, map_mul, map_mul,
    matrix_mul_comm_of_subsingleton (Y.rho mu (swap 0 1)) (Y.rho mu (finRotate 3)), mul_assoc, ← map_mul,
    Equiv.swap_mul_self, map_one, mul_one, sub_self]

/-- **Remark 4.4** (paper v1.02 lines 472-474), for an arbitrary Young system: `f = (0 1 2) - (0 2 1)` is a nonzero element
of `C_3 ∩ B_2^{(3)}`. -/
theorem rem_4_5_element_of (Y : YoungSystem F 3) :
    perm F (finRotate 3) - perm F (finRotate 3)⁻¹ ∈ cycleSpan F 3 ⊓ Y.boxSum 2 ∧
      perm F (finRotate 3) - perm F (finRotate 3)⁻¹ ≠ 0 := by
  have hfull : IsFullCycle (finRotate 3) := ⟨isCycle_finRotate, support_finRotate⟩
  have hfull' : IsFullCycle (finRotate 3)⁻¹ := ⟨hfull.1.inv, by rw [Perm.support_inv]; exact hfull.2⟩
  refine ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, hfull, rfl⟩) (Submodule.subset_span ⟨_, hfull', rfl⟩)
  · unfold NagataHigman.YoungSystem.boxSum
    rw [YoungSystem.mem_blockSum_iff Y]
    intro mu hmu
    rcases shape_three_outside_box mu hmu with h | h
    · have := syt_subsingleton_of_row (row_eq_zero_of_numRows_le_one h)
      exact rhoAlg_rot_sub_eq_zero Y mu
    · have := syt_subsingleton_of_col (col_eq_zero_of_firstRow_le_one h)
      exact rhoAlg_rot_sub_eq_zero Y mu
  · intro h0
    have hne : (finRotate 3)⁻¹ ≠ finRotate 3 := by decide
    have h1 := congrArg (fun a : GrpAlg F 3 => a.coeff (finRotate 3)) h0
    simp [MonoidAlgebra.coeff_sub, coeff_perm, hne] at h1

end NagataHigman.Proofs

end
