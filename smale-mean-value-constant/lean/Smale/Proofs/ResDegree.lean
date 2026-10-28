/-
Smale/Proofs/ResDegree.lean — the degree bound of Theorem 5.1, proof (R) (paper 009, posted v1.90, tex l.404-405):
the resultant `Res_w(P_c, P_c*)` at formal degrees `(n-1, n-1)` is a polynomial `F` in `c` of degree at most
`2(n-1)²` (`578` for `n = 18`): the Sylvester matrix has `2(n-1)` rows, and its entries are coefficients of `P_c` or
`P_c*`, polynomials in `c` of degree at most `n - 1` (`U_l` has degree `l`).
-/
import Smale.Proofs.Sec4More

namespace Smale

open Polynomial Complex Matrix ComplexConjugate

/-- A determinant whose entries have degree at most `k` has degree at most `(size) · k`. -/
theorem natDegree_det_le_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ[X]) (k : ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ k) : A.det.natDegree ≤ Fintype.card ι * k := by
  rw [det_apply]
  refine (natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply, Multiset.mem_map, exists_imp,
    Finset.mem_univ_val]
  intro g
  calc natDegree (Equiv.Perm.sign g • ∏ i : ι, A (g i) i) ≤ natDegree (∏ i : ι, A (g i) i) := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign g) with sg | sg
        · rw [sg, one_smul]
        · rw [sg, Units.neg_smul, one_smul, natDegree_neg]
    _ ≤ ∑ i : ι, natDegree (A (g i) i) := natDegree_prod_le _ _
    _ ≤ Finset.univ.card • k := Finset.sum_le_card_nsmul _ _ k fun i _ => h (g i) i
    _ = Fintype.card ι * k := by rw [smul_eq_mul, Finset.card_univ]

/-- Every coefficient of `∑_{l<n} C(C a_l · U_l) X^{e_l}` is a polynomial of degree at most `n - 1`. -/
theorem natDegree_coeff_chebSum_le (n : ℕ) (a : ℕ → ℂ) (e : ℕ → ℕ) (m : ℕ) :
    ((∑ l ∈ Finset.range n, (C (C (a l) * Chebyshev.U ℂ (l : ℤ)) : (ℂ[X])[X]) * X ^ (e l)).coeff m).natDegree ≤
      n - 1 := by
  rw [finsetSum_coeff]
  refine natDegree_sum_le_of_forall_le _ _ fun l hl => ?_
  rw [coeff_C_mul_X_pow]
  split_ifs
  · refine (natDegree_C_mul_le _ _).trans ?_
    rw [Chebyshev.natDegree_U_natCast]
    have := Finset.mem_range.1 hl
    omega
  · rw [natDegree_zero]; exact Nat.zero_le _

theorem natDegree_coeff_dieudonneGen_le (H : ℂ[X]) (n m : ℕ) : ((dieudonneGen H n).coeff m).natDegree ≤ n - 1 := by
  unfold dieudonneGen
  exact natDegree_coeff_chebSum_le n (fun l => H.coeff (l + 1)) (fun l => l) m

theorem natDegree_coeff_dieudonneStarGen_le (H : ℂ[X]) (n m : ℕ) :
    ((dieudonneStarGen H n).coeff m).natDegree ≤ n - 1 := by
  unfold dieudonneStarGen
  exact natDegree_coeff_chebSum_le n (fun l => conj (H.coeff (l + 1))) (fun l => n - 1 - l) m

/-- Every entry of the Sylvester matrix of `P_c`, `P_c*` (as polynomials in `c`) has degree at most `n - 1`. -/
theorem natDegree_sylvester_le (H : ℂ[X]) (n : ℕ) (i j : Fin (n - 1 + (n - 1))) :
    (sylvester (dieudonneGen H n) (dieudonneStarGen H n) (n - 1) (n - 1) i j).natDegree ≤ n - 1 := by
  rw [sylvester, Matrix.of_apply]
  induction j using Fin.addCases with
  | left j₁ =>
    rw [Fin.addCases_left]
    split_ifs
    · exact natDegree_coeff_dieudonneStarGen_le H n _
    · rw [natDegree_zero]; exact Nat.zero_le _
  | right j₁ =>
    rw [Fin.addCases_right]
    split_ifs
    · exact natDegree_coeff_dieudonneGen_le H n _
    · rw [natDegree_zero]; exact Nat.zero_le _

/-- tex l.307 and l.404-405, exactly the Statements type: `Res_w(P_c, P_c*)` is a polynomial `F` in `c` of degree at
most `2(n-1)²`. -/
theorem sec4_res_poly_deg_proved (H : ℂ[X]) (n : ℕ) :
    ∃ F : ℂ[X], F.natDegree ≤ 2 * (n - 1) ^ 2 ∧
      ∀ c : ℝ, resultant (dieudonne H n c) (dieudonneStar H n c) (n - 1) (n - 1) = F.eval (c : ℂ) := by
  refine ⟨resultant (dieudonneGen H n) (dieudonneStarGen H n) (n - 1) (n - 1), ?_, fun c => by
    rw [← map_dieudonneGen H n c, ← map_dieudonneStarGen H n c, resultant_map_map, coe_evalRingHom]⟩
  have h := natDegree_det_le_of_entries _ (n - 1) (natDegree_sylvester_le H n)
  rw [Fintype.card_fin] at h
  rw [resultant]
  calc _ ≤ (n - 1 + (n - 1)) * (n - 1) := h
    _ = 2 * (n - 1) ^ 2 := by ring

/-- tex l.307, l.404-405: the Sylvester matrix of `P_c`, `P_c*` is `M(c)` for one matrix `M` of polynomials in `c` whose
entries have degree at most `n - 1`; `F = det M` has degree at most `2(n-1)²`, and `Res_w(P_c, P_c*) = F(c)`. -/
theorem sec4_res_poly_matrix_proved (H : ℂ[X]) (n : ℕ) :
    ∃ (M : Matrix (Fin (n - 1 + (n - 1))) (Fin (n - 1 + (n - 1))) ℂ[X]) (F : ℂ[X]),
      (∀ i j, (M i j).natDegree ≤ n - 1) ∧
      (∀ c : ℝ, sylvester (dieudonne H n c) (dieudonneStar H n c) (n - 1) (n - 1) = M.map (eval (c : ℂ))) ∧
      F = M.det ∧ F.natDegree ≤ 2 * (n - 1) ^ 2 ∧
      ∀ c : ℝ, resultant (dieudonne H n c) (dieudonneStar H n c) (n - 1) (n - 1) = F.eval (c : ℂ) := by
  refine ⟨sylvester (dieudonneGen H n) (dieudonneStarGen H n) (n - 1) (n - 1),
    resultant (dieudonneGen H n) (dieudonneStarGen H n) (n - 1) (n - 1), natDegree_sylvester_le H n,
    fun c => ?_, rfl, ?_, fun c => ?_⟩
  · rw [← map_dieudonneGen H n c, ← map_dieudonneStarGen H n c, sylvester_map_map]
    rfl
  · have h := natDegree_det_le_of_entries _ (n - 1) (natDegree_sylvester_le H n)
    rw [Fintype.card_fin] at h
    rw [resultant]
    calc _ ≤ (n - 1 + (n - 1)) * (n - 1) := h
      _ = 2 * (n - 1) ^ 2 := by ring
  · rw [← map_dieudonneGen H n c, ← map_dieudonneStarGen H n c, resultant_map_map, coe_evalRingHom]

/-- tex l.301: "a common zero makes the Sylvester matrix singular, at any formal degrees": for formal degrees
`m ≥ deg f`, `k ≥ deg g`, not both `0`, a common zero of `f` and `g` makes the resultant at `(m, k)` vanish. (For
`m = k = 0` the Sylvester matrix is empty, with determinant `1`.) -/
theorem resultant_eq_zero_of_common_zero (f g : ℂ[X]) (m k : ℕ) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ k)
    (hmk : m ≠ 0 ∨ k ≠ 0) (w : ℂ) (h1 : f.eval w = 0) (h2 : g.eval w = 0) : resultant f g m k = 0 := by
  obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant f g hf hg hmk
  have h := congrArg (eval w) hpq
  simpa [eval_add, eval_mul, h1, h2] using h.symm

end Smale
