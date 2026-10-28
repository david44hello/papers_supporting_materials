/-
Matsaev/TK/Gain.lean — the inequality of Lemma 4.1: for small `a > 0` and small `ε > 0`, `‖P_a(T_ε)‖_p > ‖P_a(J)‖_p`.
Paper: "Matsaev's (1971) conjecture is false for every p != 2", Dave Goel, short v2.00 (md5 a9b3c6be), Lemma 4.1 (`lem:TK`).

Route. `A = P_a(J) = (1+B) I + a J` maps `e(φ)` to `r e(φ - β)` (`β = arctan(a/(1+B))`), so a maximizing vector of
`A` is `e(φw)` with `φw` a maximum point of `Lb q β` (Moving.lean). There `D* - Q(A e(φw)) ≤ η β` (KEY). With
`P_a(T_ε) = X(ε) I + Y(ε) J` (PaTeps.lean), `f(ε) = ‖P_a(T_ε) e(φw)‖^q` has `f'(0) = q Γ`, and the exact identity
`((1+B)² + a²) Γ = N(y) [(Q(y) - D*)(B(1+B) + a²/2) + a(B-1)(1 + D* Q(y))/2]`, `y = A e(φw)`, makes `Γ > 0` for
`B > 1` and small `a`. So `f(ε) > f(0) = ‖A‖^q ‖e(φw)‖^q` for small `ε > 0`.
-/
import Matsaev.TK.Moving
import Matsaev.TK.PaTeps
import Matsaev.Bridge.Basic
import Matsaev.Scalar.B0

namespace Matsaev

namespace TK

open Real Set Filter Topology Polynomial
open scoped ENNReal Matrix

/-! ### Polar coordinates and the rotation `A` -/

lemma exists_polar (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ φ : ℝ, x = ![ρ * cos φ, ρ * sin φ] := by
  set z : ℂ := ⟨x 0, x 1⟩ with hz
  have hz0 : z ≠ 0 := by
    intro h
    apply hx
    ext i
    fin_cases i
    · have := congrArg Complex.re h
      simpa [hz] using this
    · have := congrArg Complex.im h
      simpa [hz] using this
  refine ⟨‖z‖, norm_pos_iff.mpr hz0, Complex.arg z, ?_⟩
  ext i
  fin_cases i
  · simp [Complex.norm_mul_cos_arg, hz]
  · simp [Complex.norm_mul_sin_arg, hz]

/-- `A e(φ) = r e(φ - β)` with `α = a/(1+B)`, `β = arctan α`, `r = (1+B) √(1+α²)`. -/
lemma A_mulVec_e (a B φ : ℝ) (hB : 0 < 1 + B) :
    ((1 + B) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + a • Jmat) *ᵥ ![cos φ, sin φ] =
      ![((1 + B) * √(1 + (a / (1 + B)) ^ 2)) * cos (φ - arctan (a / (1 + B))),
        ((1 + B) * √(1 + (a / (1 + B)) ^ 2)) * sin (φ - arctan (a / (1 + B)))] := by
  rw [smul_one_add_smul_J_mulVec, cos_sub, sin_sub, cos_arctan, sin_arctan]
  have hs : 0 < √(1 + (a / (1 + B)) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  ext i
  fin_cases i <;> simp <;> field_simp

/-- `‖r e(ψ)‖_q^q = r^q nT(ψ)` for `r ≥ 0`. -/
lemma abs_rpow_polar {q r : ℝ} (hr : 0 ≤ r) (ψ : ℝ) :
    |r * cos ψ| ^ q + |r * sin ψ| ^ q = r ^ q * nT q ψ := by
  unfold nT
  rw [abs_mul, abs_mul, abs_of_nonneg hr, mul_rpow hr (abs_nonneg _), mul_rpow hr (abs_nonneg _)]
  ring

/-- A maximizing direction of `A`: it maximizes `Lb q β` and attains `‖A‖`. -/
lemma exists_max_angle (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (hq : 1 < p.toReal) (a B : ℝ)
    (hB : 0 < 1 + B) :
    ∃ φw : ℝ, (∀ φ, Lb p.toReal (arctan (a / (1 + B))) φ ≤ Lb p.toReal (arctan (a / (1 + B))) φw) ∧
      ‖WithLp.toLp p (((1 + B) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + a • Jmat) *ᵥ ![cos φw, sin φw])‖ =
        matNorm p ((1 + B) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + a • Jmat) * ‖WithLp.toLp p ![cos φw, sin φw]‖ := by
  set q := p.toReal with hqdef
  set A : Matrix (Fin 2) (Fin 2) ℝ := (1 + B) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + a • Jmat with hA
  set β := arctan (a / (1 + B)) with hβ
  set r := (1 + B) * √(1 + (a / (1 + B)) ^ 2) with hr
  set C := matNorm p A with hC
  have hrpos : 0 < r := mul_pos hB (Real.sqrt_pos.mpr (by positivity))
  have hq0 : 0 < q := by linarith
  -- norms of `e(φ)` and `A e(φ)` to the power `q`
  have hnorm_e : ∀ φ, ‖WithLp.toLp p ![cos φ, sin φ]‖ ^ q = nT q φ := fun φ => by
    rw [norm_toLp_fin2_rpow p hptop]; rfl
  have hnorm_Ae : ∀ φ, ‖WithLp.toLp p (A *ᵥ ![cos φ, sin φ])‖ ^ q = r ^ q * nT q (φ - β) := fun φ => by
    rw [hA, A_mulVec_e a B φ hB, norm_toLp_fin2_rpow p hptop, abs_rpow_polar hrpos.le]
  -- the maximizer given by `exists_eq_matNorm`, in polar form
  obtain ⟨w, hw1, hwA⟩ := exists_eq_matNorm p A
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw1
  obtain ⟨ρ, hρ, φw, rfl⟩ := exists_polar w hw0
  have hsmul : ![ρ * cos φw, ρ * sin φw] = ρ • ![cos φw, sin φw] := by
    ext i
    fin_cases i <;> simp
  rw [hsmul, Matrix.mulVec_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hρ] at hwA
  rw [hsmul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hρ] at hw1
  have hattain : ‖WithLp.toLp p (A *ᵥ ![cos φw, sin φw])‖ = C * ‖WithLp.toLp p ![cos φw, sin φw]‖ := by
    have : ρ * ‖WithLp.toLp p (A *ᵥ ![cos φw, sin φw])‖ = ρ * (C * ‖WithLp.toLp p ![cos φw, sin φw]‖) := by
      rw [hwA, ← mul_assoc, mul_comm ρ C, mul_assoc, hw1, mul_one]
    exact mul_left_cancel₀ hρ.ne' this
  refine ⟨φw, ?_, hattain⟩
  -- every direction: `r^q nT(φ - β) ≤ C^q nT(φ)`; equality at `φw`
  have hle : ∀ φ, r ^ q * nT q (φ - β) ≤ C ^ q * nT q φ := by
    intro φ
    have h := norm_mulVec_le_matNorm p A ![cos φ, sin φ]
    have h' := rpow_le_rpow (norm_nonneg _) h hq0.le
    rw [mul_rpow (matNorm_nonneg p A) (norm_nonneg _), hnorm_Ae, hnorm_e] at h'
    exact h'
  have heq : r ^ q * nT q (φw - β) = C ^ q * nT q φw := by
    have h := congrArg (· ^ q) hattain
    rw [mul_rpow (matNorm_nonneg p A) (norm_nonneg _), hnorm_Ae, hnorm_e] at h
    exact h
  have hrq : 0 < r ^ q := rpow_pos_of_pos hrpos q
  intro φ
  have hn1 := nT_pos hq0 (φ - β)
  have hn2 := nT_pos hq0 φ
  have hn3 := nT_pos hq0 (φw - β)
  have hn4 := nT_pos hq0 φw
  have hCq : 0 < C ^ q := by
    have : 0 < C ^ q * nT q φw := by rw [← heq]; positivity
    exact pos_of_mul_pos_left this hn4.le
  unfold Lb
  rw [← Real.log_div hn1.ne' hn2.ne', ← Real.log_div hn3.ne' hn4.ne']
  apply Real.log_le_log (div_pos hn1 hn2)
  rw [div_le_div_iff₀ hn2 hn4]
  have h1 := hle φ
  -- `nT(φ-β) nT(φw) ≤ nT(φw-β) nT(φ)`, from `r^q nT(φ-β) ≤ C^q nT(φ)` and `r^q nT(φw-β) = C^q nT(φw)`
  have key : r ^ q * (nT q (φ - β) * nT q φw) ≤ r ^ q * (nT q (φw - β) * nT q φ) := by
    calc r ^ q * (nT q (φ - β) * nT q φw) = (r ^ q * nT q (φ - β)) * nT q φw := by ring
      _ ≤ (C ^ q * nT q φ) * nT q φw := mul_le_mul_of_nonneg_right h1 hn4.le
      _ = (C ^ q * nT q φw) * nT q φ := by ring
      _ = (r ^ q * nT q (φw - β)) * nT q φ := by rw [heq]
      _ = r ^ q * (nT q (φw - β) * nT q φ) := by ring
  exact le_of_mul_le_mul_left key hrq

/-! ### The gain `Γ` -/

/-- The exact identity for `Γ = ⟨φ(y), M v⟩`, `y = A v`, `M = μ I + ν J`, `μ = -(a/2 + B D)`, `ν = B - a D/2`. -/
lemma gamma_identity {q : ℝ} (hq : 0 < q) (a B D v0 v1 y0 y1 : ℝ) (hy0 : y0 = (1 + B) * v0 + a * v1)
    (hy1 : y1 = (1 + B) * v1 - a * v0) (hN : |y0| ^ q + |y1| ^ q ≠ 0) :
    ((1 + B) ^ 2 + a ^ 2) *
        (phi q y0 * (-(a / 2 + B * D) * v0 + (B - a * D / 2) * v1) +
          phi q y1 * (-(a / 2 + B * D) * v1 - (B - a * D / 2) * v0)) =
      (|y0| ^ q + |y1| ^ q) *
        ((Qf q y0 y1 - D) * (B * (1 + B) + a ^ 2 / 2) + a * (B - 1) * (1 + D * Qf q y0 y1) / 2) := by
  have hQ : (|y0| ^ q + |y1| ^ q) * Qf q y0 y1 = phi q y0 * y1 - phi q y1 * y0 := by
    unfold Qf
    field_simp
  have h0 : phi q y0 * y0 = |y0| ^ q := B0.phi_mul_self hq y0
  have h1 : phi q y1 * y1 = |y1| ^ q := B0.phi_mul_self hq y1
  subst hy0 hy1
  linear_combination (-(B * (1 + B) + a ^ 2 / 2 + a * (B - 1) * D / 2)) * hQ
    + (-(D * (B * (1 + B) + a ^ 2 / 2)) + a * (B - 1) / 2) * h0
    + (-(D * (B * (1 + B) + a ^ 2 / 2)) + a * (B - 1) / 2) * h1

/-- The bracket of `gamma_identity` is positive once `D - Q ≤ η a` with `η = (B-1)/(4(B(1+B)+1))`. -/
lemma bracket_pos {a B D Qy : ℝ} (hB : 1 < B) (ha0 : 0 < a) (ha1 : a ≤ 1) (hQ0 : 0 ≤ Qy) (hD : 0 ≤ D)
    (hclose : D - Qy ≤ (B - 1) / (4 * (B * (1 + B) + 1)) * a) :
    0 < (Qy - D) * (B * (1 + B) + a ^ 2 / 2) + a * (B - 1) * (1 + D * Qy) / 2 := by
  have hK0 : 0 < B * (1 + B) + a ^ 2 / 2 := by positivity
  have hK1 : B * (1 + B) + a ^ 2 / 2 ≤ B * (1 + B) + 1 := by nlinarith
  have hL : 0 < 4 * (B * (1 + B) + 1) := by positivity
  set η := (B - 1) / (4 * (B * (1 + B) + 1)) with hη
  have hη0 : 0 ≤ η := div_nonneg (by linarith) hL.le
  have hηL : η * (4 * (B * (1 + B) + 1)) = B - 1 := div_mul_cancel₀ _ hL.ne'
  -- `(D - Q) K ≤ η a K ≤ η a (B(1+B)+1) = a (B-1)/4`
  have h1 : (D - Qy) * (B * (1 + B) + a ^ 2 / 2) ≤ η * a * (B * (1 + B) + 1) := by
    calc (D - Qy) * (B * (1 + B) + a ^ 2 / 2) ≤ η * a * (B * (1 + B) + a ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right hclose hK0.le
      _ ≤ η * a * (B * (1 + B) + 1) := mul_le_mul_of_nonneg_left hK1 (by positivity)
  have h2 : η * a * (B * (1 + B) + 1) = a * (B - 1) / 4 := by linear_combination (a / 4) * hηL
  have h3 : 0 ≤ D * Qy := mul_nonneg hD hQ0
  have h4 : a * (B - 1) * (1 + D * Qy) / 2 ≥ a * (B - 1) / 2 := by
    have : 0 ≤ a * (B - 1) := mul_nonneg ha0.le (by linarith)
    nlinarith
  have h5 : 0 < a * (B - 1) := mul_pos ha0 (by linarith)
  nlinarith

/-- `f(ε) = ‖P_a(T_ε) v‖_q^q` has derivative `q Γ` at `ε = 0`. -/
lemma hasDerivAt_gainfun {q : ℝ} (hq : 1 < q) (D a B v0 v1 : ℝ) :
    HasDerivAt (fun ε => |Xe D a B ε * v0 + Ye D a B ε * v1| ^ q + |Xe D a B ε * v1 - Ye D a B ε * v0| ^ q)
      (q * (phi q ((1 + B) * v0 + a * v1) * (-(a / 2 + B * D) * v0 + (B - a * D / 2) * v1) +
        phi q ((1 + B) * v1 - a * v0) * (-(a / 2 + B * D) * v1 - (B - a * D / 2) * v0))) 0 := by
  have hX := hasDerivAt_Xe D a B
  have hY := hasDerivAt_Ye D a B
  have h0 : HasDerivAt (fun ε => Xe D a B ε * v0 + Ye D a B ε * v1)
      (-(a / 2 + B * D) * v0 + (B - a * D / 2) * v1) 0 := (hX.mul_const v0).add (hY.mul_const v1)
  have h1 : HasDerivAt (fun ε => Xe D a B ε * v1 - Ye D a B ε * v0)
      (-(a / 2 + B * D) * v1 - (B - a * D / 2) * v0) 0 := (hX.mul_const v1).sub (hY.mul_const v0)
  have g0 := (hasDerivAt_abs_rpow (Xe D a B 0 * v0 + Ye D a B 0 * v1) hq).comp 0 h0
  have g1 := (hasDerivAt_abs_rpow (Xe D a B 0 * v1 - Ye D a B 0 * v0) hq).comp 0 h1
  refine (g0.add g1).congr_deriv ?_
  rw [Xe_zero, Ye_zero, phi_eq_abs_rpow, phi_eq_abs_rpow]
  ring

/-- A function with positive derivative at `0` is larger than its value at `0` just to the right of `0`. -/
lemma exists_gt_of_hasDerivAt_pos {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' 0) (hpos : 0 < f') :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → f 0 < f ε := by
  have ht := hasDerivAt_iff_tendsto_slope.mp hf
  have hev : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), 0 < slope f 0 ε := ht.eventually (lt_mem_nhds hpos)
  have hev' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < slope f 0 ε :=
    hev.filter_mono (nhdsWithin_mono _ fun x hx => (show (0 : ℝ) < x from hx).ne')
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev'
  refine ⟨u, hu, fun ε hε hεu => ?_⟩
  have h := hsub ⟨hε, hεu⟩
  simp only [Set.mem_ofPred_eq, slope_def_field, sub_zero] at h
  have := (div_pos_iff_of_pos_right hε).mp h
  linarith

end TK

open scoped ENNReal Matrix
open Real Polynomial

open TK in
/-- **Lemma 4.1** (`lem:TK`), its inequality: for `p > 2` and `B > 1` there is `a₂ > 0` such that for each `0 < a < a₂`,
`‖P_a(T_ε)‖_p > ‖P_a(J)‖_p` for all sufficiently small `ε > 0`. -/
theorem lemma_4_1_b_proved (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 1 < B) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ a : ℝ, 0 < a → a < a₂ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) < matNorm p (aeval (Teps p.toReal ε) (Pa a B)) := by
  set q := p.toReal with hqdef
  have hq : 2 < q := by
    have h := ENNReal.toReal_strict_mono hptop hp
    simpa using h
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  have hB1 : 0 < 1 + B := by linarith
  obtain ⟨t, -, -, -, hdpos, -, hD, -, -⟩ := lemma_3_3_proved q hq
  have hDpos : 0 < Dstar q := hD ▸ hdpos
  set η := (B - 1) / (4 * (B * (1 + B) + 1)) with hη
  have hηpos : 0 < η := div_pos (by linarith) (by positivity)
  obtain ⟨β₁, hβ₁, hkey⟩ := key_localization hq hηpos
  refine ⟨min 1 (min β₁ (Dstar q / η)), lt_min one_pos (lt_min hβ₁ (div_pos hDpos hηpos)), ?_⟩
  intro a ha ha₂
  have ha1 : a < 1 := lt_of_lt_of_le ha₂ (min_le_left _ _)
  have haβ : a < β₁ := lt_of_lt_of_le ha₂ ((min_le_right _ _).trans (min_le_left _ _))
  have haD : a < Dstar q / η := lt_of_lt_of_le ha₂ ((min_le_right _ _).trans (min_le_right _ _))
  -- the maximizing direction of `A = P_a(J)`
  set A : Matrix (Fin 2) (Fin 2) ℝ := (1 + B) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + a • Jmat with hAdef
  have hA : aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) = A := aeval_Jmat_Pa_proved a B
  set β := arctan (a / (1 + B)) with hβ
  set r := (1 + B) * √(1 + (a / (1 + B)) ^ 2) with hr
  have hrpos : 0 < r := mul_pos hB1 (Real.sqrt_pos.mpr (by positivity))
  have hβpos : 0 < β := arctan_pos.mpr (div_pos ha hB1)
  have hβa : β < a := lt_of_le_of_lt (arctan_le_self (div_pos ha hB1).le) (div_lt_self ha (by linarith))
  obtain ⟨φw, hmax, hattain⟩ := exists_max_angle p hptop hq1 a B hB1
  have hclose := hkey β hβpos (by linarith) φw hmax
  -- `v = e(φw)`, `y = A v`
  set v0 := cos φw with hv0
  set v1 := sin φw with hv1
  set y0 := (1 + B) * v0 + a * v1 with hy0
  set y1 := (1 + B) * v1 - a * v0 with hy1
  have hAv : A *ᵥ ![v0, v1] = ![y0, y1] := smul_one_add_smul_J_mulVec _ _ _ _
  have hpolar := A_mulVec_e a B φw hB1
  rw [← hAdef, hAv] at hpolar
  have hy0' : y0 = r * cos (φw - β) := congrFun hpolar 0
  have hy1' : y1 = r * sin (φw - β) := congrFun hpolar 1
  have hQy : Qf q y0 y1 = Th q (φw - β) := by
    rw [hy0', hy1', Qf_homog q hq1 r _ _ hrpos.ne']
    rfl
  have hN : |y0| ^ q + |y1| ^ q = r ^ q * nT q (φw - β) := by
    rw [hy0', hy1', abs_rpow_polar hrpos.le]
  have hNpos : 0 < |y0| ^ q + |y1| ^ q := by
    rw [hN]
    exact mul_pos (rpow_pos_of_pos hrpos q) (nT_pos hq0 _)
  -- `Γ > 0`
  have hQle : Qf q y0 y1 ≤ Dstar q := by rw [hQy]; exact Th_le_Dstar hq _
  have hclose' : Dstar q - Qf q y0 y1 ≤ η * a := by
    rw [hQy]
    exact hclose.trans (mul_le_mul_of_nonneg_left hβa.le hηpos.le)
  have hQ0 : 0 ≤ Qf q y0 y1 := by
    have : η * a < Dstar q := by rwa [lt_div_iff₀ hηpos, mul_comm] at haD
    linarith
  have hbr := bracket_pos hB ha ha1.le hQ0 hDpos.le hclose'
  have hgam := gamma_identity hq0 a B (Dstar q) v0 v1 y0 y1 hy0 hy1 hNpos.ne'
  set Γ := phi q y0 * (-(a / 2 + B * Dstar q) * v0 + (B - a * Dstar q / 2) * v1) +
    phi q y1 * (-(a / 2 + B * Dstar q) * v1 - (B - a * Dstar q / 2) * v0) with hΓ
  have hΓpos : 0 < Γ := by
    have hr2 : 0 < (1 + B) ^ 2 + a ^ 2 := by positivity
    have : 0 < ((1 + B) ^ 2 + a ^ 2) * Γ := by rw [hgam]; exact mul_pos hNpos hbr
    exact pos_of_mul_pos_right this hr2.le
  -- the ε-derivative
  have hder := hasDerivAt_gainfun hq1 (Dstar q) a B v0 v1
  obtain ⟨ε₀, hε₀, hgt⟩ := exists_gt_of_hasDerivAt_pos hder (mul_pos hq0 hΓpos)
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  have hfε := hgt ε hε hεε₀
  simp only [Xe_zero, Ye_zero] at hfε
  -- norms
  set M := aeval (Teps q ε) (Pa a B) with hM
  have hMform : M = Xe (Dstar q) a B ε • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Ye (Dstar q) a B ε • Jmat :=
    aeval_Teps_Pa q a B ε
  have hMv : ‖WithLp.toLp p (M *ᵥ ![v0, v1])‖ ^ q =
      |Xe (Dstar q) a B ε * v0 + Ye (Dstar q) a B ε * v1| ^ q +
        |Xe (Dstar q) a B ε * v1 - Ye (Dstar q) a B ε * v0| ^ q := by
    rw [hMform, smul_one_add_smul_J_mulVec, norm_toLp_fin2_rpow p hptop]
  have hAv' : ‖WithLp.toLp p (A *ᵥ ![v0, v1])‖ ^ q = |y0| ^ q + |y1| ^ q := by
    rw [hAv, norm_toLp_fin2_rpow p hptop]
  have hvpos : 0 < ‖WithLp.toLp p ![v0, v1]‖ := by
    have h := norm_toLp_fin2_rpow p hptop v0 v1
    have hn : 0 < |v0| ^ q + |v1| ^ q := nT_pos hq0 φw
    rw [← h] at hn
    rcases (norm_nonneg (WithLp.toLp p ![v0, v1])).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_rpow hq0.ne'] at hn
      exact absurd hn (lt_irrefl 0)
  -- `C ‖v‖ < ‖M v‖ ≤ ‖M‖ ‖v‖`
  have hlt : matNorm p A * ‖WithLp.toLp p ![v0, v1]‖ < ‖WithLp.toLp p (M *ᵥ ![v0, v1])‖ := by
    rw [← hattain]
    rw [← rpow_lt_rpow_iff (norm_nonneg _) (norm_nonneg _) hq0, hMv, hAv']
    exact hfε
  have hle := norm_mulVec_le_matNorm p M ![v0, v1]
  rw [hA]
  exact lt_of_mul_lt_mul_right (hlt.trans_le hle) hvpos.le

end Matsaev
