/-
Smale/Proofs/Hpoly.lean — Lemma 3.1, first sentence of the proof (tex l.208): if `a₁, …, a_k` are distinct zeros of `Q`,
then `H = Q ∏(1 - ā_j z)/(z - a_j)` is a polynomial, `H ∏(z - a_j) = Q ∏(1 - ā_j z)`.
-/
import Smale.Defs.Basic

namespace Smale

open Polynomial

theorem zerosPoly_monic (as : List ℂ) : (zerosPoly as).Monic := by
  unfold zerosPoly
  induction as with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, List.prod_cons]
    exact (monic_X_sub_C a).mul ih

theorem zerosPoly_eq_multiset (as : List ℂ) :
    zerosPoly as = ((as : Multiset ℂ).map fun a => X - C a).prod := by
  rw [zerosPoly, Multiset.map_coe, Multiset.prod_coe]

/-- Distinct zeros `a_j` of `Q` give `∏(z - a_j) ∣ Q`. -/
theorem zerosPoly_dvd (Q : ℂ[X]) (as : List ℂ) (hnd : as.Nodup) (hz : ∀ a ∈ as, Q.eval a = 0) :
    zerosPoly as ∣ Q := by
  by_cases hQ : Q = 0
  · rw [hQ]
    exact dvd_zero _
  rw [zerosPoly_eq_multiset, Multiset.prod_X_sub_C_dvd_iff_le_roots hQ,
    Multiset.le_iff_subset (Multiset.coe_nodup.2 hnd)]
  intro a ha
  rw [mem_roots hQ, IsRoot.def]
  exact hz a (Multiset.mem_coe.1 ha)

/-- Lemma 3.1, first sentence of the proof (tex l.208), exactly the Statements type. -/
theorem lem_3_1_H_poly_proved (Q : ℂ[X]) (as : List ℂ) (hnd : as.Nodup) (hz : ∀ a ∈ as, Q.eval a = 0) :
    Hpoly Q as * zerosPoly as = Q * reflPoly as := by
  have hdvd : zerosPoly as ∣ Q * reflPoly as := (zerosPoly_dvd Q as hnd hz).mul_right _
  have hmod := (modByMonic_eq_zero_iff_dvd (zerosPoly_monic as)).2 hdvd
  have h := modByMonic_add_div (Q * reflPoly as) (zerosPoly as)
  rw [hmod, zero_add] at h
  rw [Hpoly, mul_comm, h]

end Smale
