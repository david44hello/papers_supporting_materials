-- Matsaev/Ops/Dual.lean — Lemma 2.3 (duality): ‖P(S)‖_p = ‖P(S)‖_q, ‖P(Tᵀ)‖_p = ‖P(T)‖_q, ‖Tᵀ‖_p = ‖T‖_q, 1/p + 1/q = 1.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.Defs.Spaces
import Matsaev.Bridge.Basic

/-!
Route. (1) Matrices: with the bilinear pairing `x ⬝ᵥ y = ∑ x_i y_i`, Hölder gives `|x ⬝ᵥ y| ≤ ‖x‖_p ‖y‖_q`, with
equality for the dual vector `w_i = conj z_i · |z_i|^(p-2)` of `z`. Since `w ⬝ᵥ Aᵀ y = A w ⬝ᵥ y`, this gives
`‖Aᵀ‖_p ≤ ‖A‖_q`, and equality by symmetry.
(2) Shift: the first `N` coordinates of `P(S) x` are `L_N (x_0, …, x_(N-1))`, with `L_N` the lower-triangular
Toeplitz matrix of the coefficients of `P`. So `‖P(S)‖_p = sup_N ‖L_N‖_p`. Now `‖L_N‖_p = ‖L_Nᵀ‖_q` by (1), and
`L_Nᵀ` is `L_N` with rows and columns reversed, so `‖L_Nᵀ‖_q = ‖L_N‖_q ≤ ‖P(S)‖_q`.
-/

namespace Matsaev

open scoped ENNReal Matrix
open Polynomial

section Duality

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Hölder duality on `ℓ^p_n` and `‖Aᵀ‖_p = ‖A‖_q` -/

section Matrices

variable {p q : ℝ≥0∞} {n : Type*} [Fintype n]

/-- Hölder's inequality for the bilinear pairing `x ⬝ᵥ y = ∑ x_i y_i` on `𝕜^n`. -/
theorem norm_dotProduct_le (hpq : p.toReal.HolderConjugate q.toReal) (x y : n → 𝕜) :
    ‖x ⬝ᵥ y‖ ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp q y‖ := by
  rw [PiLp.norm_eq_sum hpq.pos, PiLp.norm_eq_sum hpq.symm.pos]
  calc ‖x ⬝ᵥ y‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
        simpa only [dotProduct, norm_mul] using norm_sum_le Finset.univ fun i => x i * y i
    _ ≤ _ := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq (fun i _ => norm_nonneg _)
          (fun i _ => norm_nonneg _)

/-- The dual vector of `z` for the exponent `r`: `w_i = conj z_i · |z_i|^(r-2)` (it is `0` where `z_i = 0`). -/
noncomputable def dualVec (r : ℝ) (z : n → 𝕜) : n → 𝕜 :=
  fun i => (starRingEnd 𝕜) (z i) * ((‖z i‖ ^ (r - 2) : ℝ) : 𝕜)

omit [Fintype n] in
theorem norm_dualVec {r : ℝ} (hr : 1 < r) (z : n → 𝕜) (i : n) : ‖dualVec r z i‖ = ‖z i‖ ^ (r - 1) := by
  rcases eq_or_ne (z i) 0 with h | h
  · simp [dualVec, h, Real.zero_rpow (by linarith : r - 1 ≠ 0)]
  · have hz : 0 < ‖z i‖ := norm_pos_iff.2 h
    rw [dualVec, norm_mul, RCLike.norm_conj, RCLike.norm_ofReal, abs_of_nonneg (by positivity),
      show r - 1 = 1 + (r - 2) by ring, Real.rpow_add hz, Real.rpow_one]

theorem dualVec_dotProduct {r : ℝ} (hr : 0 < r) (z : n → 𝕜) :
    dualVec r z ⬝ᵥ z = ((∑ i, ‖z i‖ ^ r : ℝ) : 𝕜) := by
  rw [dotProduct, RCLike.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne (z i) 0 with h | h
  · simp [h, Real.zero_rpow hr.ne']
  · have hz : 0 < ‖z i‖ := norm_pos_iff.2 h
    have key : ‖z i‖ ^ r = ‖z i‖ ^ 2 * ‖z i‖ ^ (r - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hz]
      norm_num
    rw [dualVec, mul_right_comm, RCLike.conj_mul, key]
    push_cast
    rfl

/-- The duality inequality `‖Aᵀ‖_p ≤ ‖A‖_q` for conjugate exponents. -/
theorem matNorm_transpose_le (hpq : p.toReal.HolderConjugate q.toReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [DecidableEq n] (A : Matrix n n 𝕜) : matNorm p Aᵀ ≤ matNorm q A := by
  refine (matNorm_le_iff p Aᵀ (matNorm_nonneg q A)).2 fun y => ?_
  have hp : 0 < p.toReal := hpq.pos
  set z := Aᵀ *ᵥ y
  set w := dualVec p.toReal z
  set M := matNorm q A
  set S : ℝ := ∑ i, ‖z i‖ ^ p.toReal with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hz : ‖WithLp.toLp p z‖ = S ^ (1 / p.toReal) := by
    rw [PiLp.norm_eq_sum hp]
  have hw : ‖WithLp.toLp q w‖ = S ^ (1 / q.toReal) := by
    rw [PiLp.norm_eq_sum hpq.symm.pos]
    simp only [w, norm_dualVec hpq.lt]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Real.rpow_mul (norm_nonneg _), hpq.sub_one_mul_conj]
  have key : S ≤ M * S ^ (1 / q.toReal) * ‖WithLp.toLp p y‖ := by
    calc S = ‖w ⬝ᵥ z‖ := by rw [dualVec_dotProduct hp, RCLike.norm_ofReal, abs_of_nonneg hS0]
      _ = ‖(A *ᵥ w) ⬝ᵥ y‖ := by rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ ≤ ‖WithLp.toLp q (A *ᵥ w)‖ * ‖WithLp.toLp p y‖ := norm_dotProduct_le hpq.symm _ _
      _ ≤ M * ‖WithLp.toLp q w‖ * ‖WithLp.toLp p y‖ := by
          gcongr
          exact norm_mulVec_le_matNorm q A w
      _ = M * S ^ (1 / q.toReal) * ‖WithLp.toLp p y‖ := by rw [hw]
  rw [hz]
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (one_div_pos.2 hp).ne']
    exact mul_nonneg (matNorm_nonneg q A) (norm_nonneg _)
  · have hsplit : S = S ^ (1 / p.toReal) * S ^ (1 / q.toReal) := by
      rw [← Real.rpow_add hpos, hpq.one_div_add_one_div, div_one, Real.rpow_one]
    have hq : 0 < S ^ (1 / q.toReal) := Real.rpow_pos_of_pos hpos _
    have key' : S ^ (1 / p.toReal) * S ^ (1 / q.toReal) ≤ M * ‖WithLp.toLp p y‖ * S ^ (1 / q.toReal) :=
      calc S ^ (1 / p.toReal) * S ^ (1 / q.toReal) = S := hsplit.symm
        _ ≤ M * S ^ (1 / q.toReal) * ‖WithLp.toLp p y‖ := key
        _ = M * ‖WithLp.toLp p y‖ * S ^ (1 / q.toReal) := by ring
    exact le_of_mul_le_mul_right key' hq

/-- **Matrix duality**: `‖Aᵀ‖_{ℓ^p_n} = ‖A‖_{ℓ^q_n}` for conjugate exponents `1/p + 1/q = 1`. -/
theorem matNorm_transpose (hpq : p.toReal.HolderConjugate q.toReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [DecidableEq n] (A : Matrix n n 𝕜) : matNorm p Aᵀ = matNorm q A :=
  le_antisymm (matNorm_transpose_le hpq A) (by simpa using matNorm_transpose_le hpq.symm Aᵀ)

/-- `P(Tᵀ) = P(T)ᵀ`. -/
theorem aeval_transpose_eq [DecidableEq n] (T : Matrix n n 𝕜) (P : 𝕜[X]) : aeval Tᵀ P = (aeval T P)ᵀ := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, Matrix.transpose_add]
  | monomial k a => simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.transpose_pow]

end Matrices

/-! ## The shift: Toeplitz truncations of `P(S)` -/

section Shift

/-- `(S^k z)_n = z_(n-k)` if `k ≤ n`, and `0` otherwise. -/
theorem shiftOp_pow_apply_ite (r : ℝ≥0∞) [Fact (1 ≤ r)] (k : ℕ) (z : lp (fun _ : ℕ => 𝕜) r) (n : ℕ) :
    (shiftOp r 𝕜 ^ k) z n = if k ≤ n then z (n - k) else 0 := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, shiftOp_apply]
    cases n with
    | zero => simp [shiftSeq]
    | succ n =>
      simp only [shiftSeq]
      rw [ih]
      simp

/-- The convolution formula `(P(S) z)_n = ∑_(k ≤ n) c_k z_(n-k)`, `c_k` the coefficients of `P`. -/
theorem aeval_shiftOp_apply_conv (r : ℝ≥0∞) [Fact (1 ≤ r)] (P : 𝕜[X]) (z : lp (fun _ : ℕ => 𝕜) r) (n : ℕ) :
    aeval (shiftOp r 𝕜) P z n = ∑ k ∈ Finset.range (n + 1), P.coeff k * z (n - k) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, add_apply, lp.coeFn_add, Pi.add_apply, hP, hQ, ← Finset.sum_add_distrib]
    simp only [coeff_add, add_mul]
  | monomial k a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, shiftOp_pow_apply_ite]
    simp only [coeff_monomial, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]
    split_ifs <;> simp

/-- The `N × N` truncation of `P(S)`: the lower-triangular Toeplitz matrix `(c_(i-j))_(j ≤ i)`. -/
noncomputable def toepTrunc (P : 𝕜[X]) (N : ℕ) : Matrix (Fin N) (Fin N) 𝕜 :=
  fun i j => if (j : ℕ) ≤ i then P.coeff (i - j) else 0

/-- The first `N` coordinates of `P(S) z` are `L_N (z_0, …, z_(N-1))`. -/
theorem aeval_shiftOp_apply_eq_toepTrunc (r : ℝ≥0∞) [Fact (1 ≤ r)] (P : 𝕜[X]) {N : ℕ}
    (z : lp (fun _ : ℕ => 𝕜) r) (i : Fin N) :
    aeval (shiftOp r 𝕜) P z i = (toepTrunc P N *ᵥ fun j : Fin N => z j) i := by
  rw [aeval_shiftOp_apply_conv, Matrix.mulVec, dotProduct]
  simp only [toepTrunc, ite_mul, zero_mul]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j ≤ (i : ℕ) then P.coeff (i - j) * z j else 0) N]
  have hfilt : (Finset.range N).filter (fun j => j ≤ (i : ℕ)) = Finset.range (i + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    have := i.isLt
    omega
  rw [← Finset.sum_filter, hfilt, ← Finset.sum_range_reflect (fun k => P.coeff k * z (↑i - k)) (↑i + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [show (i : ℕ) + 1 - 1 - j = i - j by omega, show (i : ℕ) - (i - j) = j by omega]

/-- Reversing rows and columns of `L_N` gives `L_Nᵀ`. -/
theorem toepTrunc_transpose (P : 𝕜[X]) (N : ℕ) :
    (toepTrunc P N)ᵀ = (toepTrunc P N).submatrix Fin.revPerm Fin.revPerm := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, toepTrunc, Fin.revPerm_apply, Fin.val_rev]
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : (i : ℕ) ≤ j
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    congr 1
    omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- A permutation of coordinates is an isometry of `ℓ^r_n`. -/
theorem norm_toLp_comp_equiv {r : ℝ≥0∞} (hr : 0 < r.toReal) {n : Type*} [Fintype n] (e : n ≃ n) (v : n → 𝕜) :
    ‖WithLp.toLp r (v ∘ e)‖ = ‖WithLp.toLp r v‖ := by
  rw [PiLp.norm_eq_sum hr, PiLp.norm_eq_sum hr]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp e (fun i => ‖v i‖ ^ r.toReal)]

/-- Restricting `f ∈ ℓ^r(ℕ)` to its first `N` coordinates does not increase the norm. -/
theorem norm_toLp_restrict_le (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : 0 < r.toReal) (N : ℕ)
    (f : lp (fun _ : ℕ => 𝕜) r) : ‖WithLp.toLp r (fun j : Fin N => f j)‖ ≤ ‖f‖ := by
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hr,
    norm_toLp_rpow r (ENNReal.toReal_pos_iff.mp hr).2.ne,
    Fin.sum_univ_eq_sum_range (fun m => ‖f m‖ ^ r.toReal) N]
  exact lp.sum_rpow_le_norm_rpow hr f _

/-- Extending `y ∈ 𝕜^N` by zeros gives an element of `ℓ^r(ℕ)` of no larger norm. -/
theorem exists_lp_extend (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : 0 < r.toReal) {N : ℕ} (y : Fin N → 𝕜) :
    ∃ e : lp (fun _ : ℕ => 𝕜) r, (∀ j : Fin N, e j = y j) ∧ ‖e‖ ≤ ‖WithLp.toLp r y‖ := by
  let g : ℕ → 𝕜 := fun m => if h : m < N then y ⟨m, h⟩ else 0
  have hg0 : ∀ m, N ≤ m → g m = 0 := fun m hm => dite_eq_right (by omega)
  have hgy : ∀ j : Fin N, g j = y j := fun j => dite_eq_left j.isLt
  have hmem : Memℓp g r := by
    refine (memℓp_zero ((Set.finite_Iio N).subset fun m hm => ?_)).of_exponent_ge zero_le
    by_contra h
    exact hm (hg0 m (not_lt.1 h))
  refine ⟨⟨g, hmem⟩, hgy, lp.norm_le_of_tsum_le hr (norm_nonneg _) ?_⟩
  rw [norm_toLp_rpow r (ENNReal.toReal_pos_iff.mp hr).2.ne]
  change ∑' m, ‖g m‖ ^ r.toReal ≤ _
  rw [tsum_eq_sum (s := Finset.range N) fun m hm => by
      rw [hg0 m (by simpa using hm), norm_zero, Real.zero_rpow hr.ne'],
    ← Fin.sum_univ_eq_sum_range (fun m => ‖g m‖ ^ r.toReal) N]
  exact le_of_eq (Finset.sum_congr rfl fun j _ => by rw [hgy])

/-- `‖L_N‖_r ≤ ‖P(S)‖_r`. -/
theorem matNorm_toepTrunc_le (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : 0 < r.toReal) (P : 𝕜[X]) (N : ℕ) :
    matNorm r (toepTrunc P N) ≤ shiftNorm r 𝕜 P := by
  refine (matNorm_le_iff r _ (norm_nonneg _)).2 fun y => ?_
  obtain ⟨e, he, hen⟩ := exists_lp_extend r hr y
  have hy : y = fun j : Fin N => e j := funext fun j => (he j).symm
  calc ‖WithLp.toLp r (toepTrunc P N *ᵥ y)‖
        = ‖WithLp.toLp r (fun j : Fin N => aeval (shiftOp r 𝕜) P e j)‖ := by
          rw [hy]
          congr 2
          funext j
          exact (aeval_shiftOp_apply_eq_toepTrunc r P e j).symm
    _ ≤ ‖aeval (shiftOp r 𝕜) P e‖ := norm_toLp_restrict_le r hr N _
    _ ≤ shiftNorm r 𝕜 P * ‖e‖ := (aeval (shiftOp r 𝕜) P).le_opNorm e
    _ ≤ shiftNorm r 𝕜 P * ‖WithLp.toLp r y‖ := mul_le_mul_of_nonneg_left hen (norm_nonneg _)

/-- `‖L_Nᵀ‖_r = ‖L_N‖_r ≤ ‖P(S)‖_r` (reversal of coordinates). -/
theorem matNorm_toepTrunc_transpose_le (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : 0 < r.toReal) (P : 𝕜[X]) (N : ℕ) :
    matNorm r (toepTrunc P N)ᵀ ≤ shiftNorm r 𝕜 P := by
  refine (matNorm_le_iff r _ (norm_nonneg _)).2 fun y => ?_
  rw [toepTrunc_transpose, Matrix.submatrix_mulVec_equiv, norm_toLp_comp_equiv hr,
    ← norm_toLp_comp_equiv hr Fin.revPerm.symm y]
  exact (norm_mulVec_le_matNorm r _ _).trans
    (mul_le_mul_of_nonneg_right (matNorm_toepTrunc_le r hr P N) (norm_nonneg _))

/-- **Shift duality**, one direction: `‖P(S)‖_p ≤ ‖P(S)‖_q` for conjugate exponents. -/
theorem shiftNorm_le_of_holderConjugate {p q : ℝ≥0∞} (hpq : p.toReal.HolderConjugate q.toReal) [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] (P : 𝕜[X]) : shiftNorm p 𝕜 P ≤ shiftNorm q 𝕜 P := by
  have hp : 0 < p.toReal := hpq.pos
  have hC : 0 ≤ shiftNorm q 𝕜 P := norm_nonneg _
  have htoep : ∀ N, matNorm p (toepTrunc P N) ≤ shiftNorm q 𝕜 P := fun N =>
    calc matNorm p (toepTrunc P N) = matNorm p (toepTrunc P N)ᵀᵀ := by rw [Matrix.transpose_transpose]
      _ ≤ matNorm q (toepTrunc P N)ᵀ := matNorm_transpose_le hpq _
      _ ≤ shiftNorm q 𝕜 P := matNorm_toepTrunc_transpose_le q hpq.symm.pos P N
  refine (shiftNorm_le_iff p P hC).2 fun x => ?_
  refine lp.norm_le_of_forall_sum_le hp (mul_nonneg hC (norm_nonneg _)) fun s => ?_
  obtain ⟨N, hN⟩ : ∃ N, s ⊆ Finset.range N :=
    ⟨s.sup id + 1, fun m hm => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hm))⟩
  have hbound : ‖WithLp.toLp p (toepTrunc P N *ᵥ fun j : Fin N => x j)‖ ≤ shiftNorm q 𝕜 P * ‖x‖ :=
    (norm_mulVec_le_matNorm p _ _).trans
      (mul_le_mul (htoep N) (norm_toLp_restrict_le p hp N x) (norm_nonneg _) hC)
  calc ∑ m ∈ s, ‖aeval (shiftOp p 𝕜) P x m‖ ^ p.toReal
        ≤ ∑ m ∈ Finset.range N, ‖aeval (shiftOp p 𝕜) P x m‖ ^ p.toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg hN fun _ _ _ => by positivity
    _ = ‖WithLp.toLp p (toepTrunc P N *ᵥ fun j : Fin N => x j)‖ ^ p.toReal := by
          rw [norm_toLp_rpow p (ENNReal.toReal_pos_iff.mp hp).2.ne,
            ← Fin.sum_univ_eq_sum_range (fun m => ‖aeval (shiftOp p 𝕜) P x m‖ ^ p.toReal) N]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [aeval_shiftOp_apply_eq_toepTrunc]
    _ ≤ (shiftNorm q 𝕜 P * ‖x‖) ^ p.toReal :=
          Real.rpow_le_rpow (norm_nonneg _) hbound hp.le

end Shift

end Duality

/-- **Lemma 2.3** (`lem:dual`), duality, `1 < p < ∞`, `1/p + 1/q = 1`: `‖P(S)‖_p = ‖P(S)‖_q`, and for a
`2 × 2` matrix `T`, `‖P(Tᵀ)‖_p = ‖P(T)‖_q` and `‖Tᵀ‖_p = ‖T‖_q`. -/
theorem lemma_2_3_proved {𝕜 : Type} [RCLike 𝕜] (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p.toReal.HolderConjugate q.toReal) (P : 𝕜[X]) :
    shiftNorm p 𝕜 P = shiftNorm q 𝕜 P ∧
      ∀ T : Matrix (Fin 2) (Fin 2) 𝕜, matNorm p (aeval Tᵀ P) = matNorm q (aeval T P) ∧ matNorm p Tᵀ = matNorm q T := by
  refine ⟨le_antisymm (shiftNorm_le_of_holderConjugate hpq P) (shiftNorm_le_of_holderConjugate hpq.symm P),
    fun T => ⟨?_, matNorm_transpose hpq T⟩⟩
  rw [aeval_transpose_eq, matNorm_transpose hpq]

end Matsaev
