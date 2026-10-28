/-
Smale/Proofs/SchurList.lean — the Schur transform `T` on coefficient lists, and certificates for the Schur–Cohn sequence:
if each normalized step `T g_j = c_j · g_{j+1}` (c_j > 0 rational) is checked by the kernel, then
`schurSeq f n j = s_j · g_j` with `s_j > 0` real, so the sign facts about `δ_j` are read off `g_j`'s constant term.
(Normalizing keeps the numbers small: `T (s f) = s² T f` for real `s`.)
-/
import Smale.Proofs.GQPoly

namespace Smale.Exact

open Polynomial Complex ComplexConjugate

/-- `f*` at formal degree `m`: `[ē_m, ē_{m-1}, …, ē_0]`. -/
def pconjRev (p : GP) (m : ℕ) : GP := (List.range (m + 1)).map fun l => GQ.cnj (p.getD (m - l) GQ.zero)

/-- `T f = ē₀ f - e_m f*` at formal degree `m`. -/
def pschurT (p : GP) (m : ℕ) : GP :=
  padd (psmul (GQ.cnj (p.getD 0 GQ.zero)) p) (pneg (psmul (p.getD m GQ.zero) (pconjRev p m)))

theorem toPoly_map_range (g : ℕ → GQ) (m : ℕ) :
    toPoly ((List.range m).map g) = ∑ l ∈ Finset.range m, C (g l).toC * X ^ l := by
  rw [toPoly_eq_sum, List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l < m := Finset.mem_range.mp hl
  simp [List.getD_eq_getElem?_getD, hl']

theorem conjRev_toPoly (p : GP) (m : ℕ) : conjRev (toPoly p) m = toPoly (pconjRev p m) := by
  rw [conjRev, pconjRev, toPoly_map_range]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [coeff_toPoly, GQ.toC_cnj]

theorem schurT_toPoly (p : GP) (m : ℕ) : schurT (toPoly p) m = toPoly (pschurT p m) := by
  rw [schurT, pschurT, toPoly_padd, toPoly_psmul, toPoly_pneg, toPoly_psmul, ← conjRev_toPoly, coeff_toPoly,
    coeff_toPoly, GQ.toC_cnj]
  ring

theorem schurT_C_ofReal_mul (s : ℝ) (f : ℂ[X]) (m : ℕ) :
    schurT (C (s : ℂ) * f) m = C ((s ^ 2 : ℝ) : ℂ) * schurT f m := by
  have hrev : conjRev (C (s : ℂ) * f) m = C (s : ℂ) * conjRev f m := by
    rw [conjRev, conjRev, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [coeff_C_mul, map_mul, Complex.conj_ofReal, C_mul]; ring
  rw [schurT, schurT, hrev, coeff_C_mul, coeff_C_mul, map_mul, Complex.conj_ofReal]
  simp only [C_mul, Complex.ofReal_pow, map_pow]
  ring

/-- The certificate theorem: checked normalized steps give `schurSeq (g 0) n j = s · g j`, `s > 0`. -/
theorem schurSeq_cert (g : ℕ → GP) (c : ℕ → ℚ) (n : ℕ)
    (hstep : ∀ j < n, peq (pschurT (g j) (n - j)) (psmul (GQ.ofQ (c j)) (g (j + 1))) = true)
    (hpos : ∀ j < n, 0 < c j) :
    ∀ j ≤ n, ∃ s : ℝ, 0 < s ∧ schurSeq (toPoly (g 0)) n j = C (s : ℂ) * toPoly (g j) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨1, one_pos, by simp [schurSeq]⟩
  | succ j ih =>
    intro hj
    have hjn : j < n := hj
    obtain ⟨s, hs, hseq⟩ := ih hjn.le
    refine ⟨s ^ 2 * (c j : ℝ), mul_pos (pow_pos hs 2) (by exact_mod_cast hpos j hjn), ?_⟩
    rw [schurSeq, hseq, schurT_C_ofReal_mul, schurT_toPoly, toPoly_eq_of_peq (hstep j hjn), toPoly_psmul,
      GQ.toC_ofQ]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ratCast, map_mul, map_pow]
    ring

/-- The sign facts about `δ_j` from the certificate and `g_j`'s constant term. -/
theorem schurDelta_of_cert (g : ℕ → GP) (c : ℕ → ℚ) (n : ℕ)
    (hstep : ∀ j < n, peq (pschurT (g j) (n - j)) (psmul (GQ.ofQ (c j)) (g (j + 1))) = true)
    (hpos : ∀ j < n, 0 < c j) (j : ℕ) (hj : j ≤ n)
    (him : ((g j).getD 0 GQ.zero).im = 0) (hre : 0 < ((g j).getD 0 GQ.zero).re) :
    (schurDelta (toPoly (g 0)) n j).im = 0 ∧ 0 < (schurDelta (toPoly (g 0)) n j).re := by
  obtain ⟨s, hs, hseq⟩ := schurSeq_cert g c n hstep hpos j hj
  rw [schurDelta, hseq, coeff_C_mul, coeff_toPoly]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, GQ.toC_re, GQ.toC_im, him]
  constructor
  · simp
  · simpa using mul_pos hs (by exact_mod_cast hre : (0 : ℝ) < (((g j).getD 0 GQ.zero).re : ℝ))

end Smale.Exact
