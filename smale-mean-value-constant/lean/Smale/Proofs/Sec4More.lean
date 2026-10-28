/-
Smale/Proofs/Sec4More.lean — three more Section 4 facts of paper 009: Dieudonné's criterion for every polynomial `H`
(tex l.237-240: subtracting the constant term changes neither univalence nor any `P_c`; from the cited form
`Cited.dieudonne_criterion`, which assumes `H(0) = 0`); `deg H ≤ n` (tex l.283); and `Res_w(P_c, P_c*)` is a polynomial
in `c` (tex l.306: the Chebyshev values are polynomials in `c`, and the resultant commutes with evaluation at `c`).
-/
import Smale.Proofs.Hpoly
import Smale.Cited.Basic

namespace Smale

open Polynomial Complex Metric ComplexConjugate

/-- Only the coefficients `h_ℓ`, `ℓ ≥ 1`, enter `P_c`: subtracting a constant does not change it. -/
theorem dieudonne_sub_C (H : ℂ[X]) (n : ℕ) (a : ℂ) (c : ℝ) : dieudonne (H - C a) n c = dieudonne H n c := by
  unfold dieudonne
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [coeff_sub, coeff_C, ite_eq_right (by omega : l + 1 ≠ 0), sub_zero]

/-- tex l.237-240, exactly the Statements type: Dieudonné's criterion applies to every polynomial `H`. -/
theorem sec4_dieudonne_any_proved (H : ℂ[X])
    (hP : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w ∈ disk, (dieudonne H H.natDegree c).eval w ≠ 0) :
    IsUnivalentOn (fun z => H.eval z) disk := by
  have hc0 : (H - C (H.coeff 0)).coeff 0 = 0 := by rw [coeff_sub, coeff_C_zero, sub_self]
  have hP' : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w ∈ disk,
      (dieudonne (H - C (H.coeff 0)) (H - C (H.coeff 0)).natDegree c).eval w ≠ 0 := by
    intro c hc w hw
    rw [natDegree_sub_C, dieudonne_sub_C]
    exact hP c hc w hw
  obtain ⟨hd, hi⟩ := Cited.dieudonne_criterion _ hc0 hP'
  have heq : ∀ z, H.eval z = (H - C (H.coeff 0)).eval z + H.coeff 0 := fun z => by
    rw [eval_sub, eval_C, sub_add_cancel]
  refine ⟨(hd.add_const (H.coeff 0)).congr fun z _ => heq z, fun z₁ h₁ z₂ h₂ h => hi h₁ h₂ ?_⟩
  have h' : (H - C (H.coeff 0)).eval z₁ + H.coeff 0 = (H - C (H.coeff 0)).eval z₂ + H.coeff 0 := by
    rw [← heq, ← heq]
    exact h
  exact add_right_cancel h'

theorem natDegree_zerosPoly (as : List ℂ) : (zerosPoly as).natDegree = as.length := by
  induction as with
  | nil => simp [zerosPoly]
  | cons a as ih =>
    show ((X - C a) * zerosPoly as).natDegree = (a :: as).length
    rw [(monic_X_sub_C a).natDegree_mul (zerosPoly_monic as), natDegree_X_sub_C, ih, List.length_cons, add_comm]

theorem natDegree_reflPoly_le (as : List ℂ) : (reflPoly as).natDegree ≤ as.length := by
  induction as with
  | nil => simp [reflPoly]
  | cons a as ih =>
    show ((1 - C (conj a) * X) * reflPoly as).natDegree ≤ (a :: as).length
    have h1 : (1 - C (conj a) * X).natDegree ≤ 1 := by compute_degree
    have h2 := natDegree_mul_le (p := 1 - C (conj a) * X) (q := reflPoly as)
    rw [List.length_cons]
    omega

/-- Lemma 4.3 (D) ⇒ (tex l.283), exactly the Statements type: `deg H ≤ n` (this holds for any `as`). -/
theorem lem_4_3_H_deg_proved (Q : ℂ[X]) (n : ℕ) (hQ : Q.natDegree = n) (b : ℂ) (as : List ℂ)
    (_hnd : (b :: as).Nodup) (_hin : ∀ a ∈ b :: as, a ∈ disk) (_hzero : ∀ a ∈ b :: as, Q.eval a = 0) :
    (Hpoly Q as).natDegree ≤ n := by
  rw [Hpoly, natDegree_divByMonic _ (zerosPoly_monic as), natDegree_zerosPoly]
  have h1 := natDegree_mul_le (p := Q) (q := reflPoly as)
  have h2 := natDegree_reflPoly_le as
  omega

/-- `U_l(c)` in `ℂ` is the real value `U_l(c)`. -/
theorem U_eval_ofReal (l : ℤ) (c : ℝ) :
    (Chebyshev.U ℂ l).eval (c : ℂ) = (((Chebyshev.U ℝ l).eval c : ℝ) : ℂ) := by
  rw [← Chebyshev.map_U Complex.ofRealHom, eval_map]
  exact eval₂_hom Complex.ofRealHom c

/-- `P_c` with the Chebyshev values kept as polynomials in `c`: a polynomial in `w` over `ℂ[X]`. -/
noncomputable def dieudonneGen (H : ℂ[X]) (n : ℕ) : (ℂ[X])[X] :=
  ∑ l ∈ Finset.range n, (C (C (H.coeff (l + 1)) * Chebyshev.U ℂ (l : ℤ)) : (ℂ[X])[X]) * X ^ l

/-- `P_c*` with the Chebyshev values kept as polynomials in `c`. -/
noncomputable def dieudonneStarGen (H : ℂ[X]) (n : ℕ) : (ℂ[X])[X] :=
  ∑ l ∈ Finset.range n, (C (C (conj (H.coeff (l + 1))) * Chebyshev.U ℂ (l : ℤ)) : (ℂ[X])[X]) * X ^ (n - 1 - l)

theorem map_dieudonneGen (H : ℂ[X]) (n : ℕ) (c : ℝ) :
    (dieudonneGen H n).map (evalRingHom (c : ℂ)) = dieudonne H n c := by
  simp only [dieudonneGen, dieudonne, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, coe_evalRingHom, eval_mul, eval_C, U_eval_ofReal]

theorem map_dieudonneStarGen (H : ℂ[X]) (n : ℕ) (c : ℝ) :
    (dieudonneStarGen H n).map (evalRingHom (c : ℂ)) = dieudonneStar H n c := by
  simp only [dieudonneStarGen, dieudonneStar, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, coe_evalRingHom, eval_mul, eval_C, U_eval_ofReal]

/-- tex l.306, exactly the Statements type: `Res_w(P_c, P_c*)` is a polynomial in `c`. -/
theorem sec4_res_poly_proved (H : ℂ[X]) (n : ℕ) :
    ∃ F : ℂ[X], ∀ c : ℝ, resultant (dieudonne H n c) (dieudonneStar H n c) (n - 1) (n - 1) = F.eval (c : ℂ) :=
  ⟨resultant (dieudonneGen H n) (dieudonneStarGen H n) (n - 1) (n - 1), fun c => by
    rw [← map_dieudonneGen H n c, ← map_dieudonneStarGen H n c, resultant_map_map, coe_evalRingHom]⟩

end Smale
