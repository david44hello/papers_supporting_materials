/-
Matsaev/Assembly/Gamma.lean — the proof of Lemma 4.1 (`lem:TK`) in the paper's own form: the derivative of
`ε ↦ ‖exp(εK_*)ξ‖_p^p`, the derivatives of `T_ε`, `T_ε²` at `0`, `d/dε ‖P_a(T_ε)ξ‖_p^p |₀ = p Γ(a, ξ)`, the identities
for `K_* J`, `K_* - J K_* J`, `E_*`, `(1+t^p)(1+D_*²)`, `Γ(0) = 0` and `Γ′(0)`; also the notation of Section 2 and `f` of Section 3.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route of `Γ′(0)`. With `ξ_a = (1, σ(a))`, `Γ(a) = φ(y₁)m₁ + φ(y₂)m₂` where `y = P_a(J)ξ_a = ((1+B) + aσ, (1+B)σ - a)` and
`M_a ξ_a = (m₁, m₂)`, `M_a = μ I + ν J`, `μ = -(a/2 + B D_*)`, `ν = B - a D_*/2`. One-variable product and chain rules give
`Γ′(0)`; the `σ′(0)` terms are `(1+B)^(p-1) B H′(t)` with `H(s) = ⟨φ(1, s), (J - D_* I)(1, s)⟩ ≤ 0 = H(t)`, so they vanish
(a maximum, as in the paper). Powers: `x = t^(p-2)`, `t^(p-1) = x t`, `t^p = x t²`, `c = (1+B)^(p-2)`.
-/
import Matsaev.TK.Gain
import Matsaev.TK.Teps
import Matsaev.Scalar.N1
import Matsaev.Angle.Basic

namespace Matsaev.Gamma

open Real Set Filter Topology Polynomial Matsaev Matsaev.TK
open scoped Matrix ENNReal

/-! ### The matrices `K_* J`, `K_* - J K_* J`, `M_a` -/

lemma Jmat_mul_self : (Jmat : Matrix (Fin 2) (Fin 2) ℝ) * Jmat = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jmat, Matrix.mul_apply, Fin.sum_univ_two]

/-- `K_* J = -½ (I + D_* J)`. -/
lemma kstar_mul_J (q : ℝ) :
    Kstar q * Jmat = -(1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) + Dstar q • Jmat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply] <;>
    simp [Kstar, Jmat]

/-- `K_* - J K_* J = J - D_* I`. -/
lemma kstar_sub_JKJ (q : ℝ) :
    Kstar q - Jmat * Kstar q * Jmat = Jmat - Dstar q • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply] <;>
    simp [Kstar, Jmat] <;> ring

/-- `K_* J² + J K_* J = -K_* + J K_* J`. -/
lemma kstar_JJ (q : ℝ) :
    Kstar q * Jmat * Jmat + Jmat * Kstar q * Jmat = -Kstar q + Jmat * Kstar q * Jmat := by
  rw [mul_assoc, Jmat_mul_self, mul_neg, mul_one]

/-- `M_a = a K_* J + B (K_* - J K_* J) = -(a/2 + B D_*) I + (B - a D_*/2) J`. -/
lemma Mmat_eq (q a B : ℝ) :
    a • (Kstar q * Jmat) + B • (Kstar q - Jmat * Kstar q * Jmat) =
      (-(a / 2 + B * Dstar q)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (B - a * Dstar q / 2) • Jmat := by
  rw [kstar_mul_J, kstar_sub_JKJ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jmat] <;> ring

/-- The paper's `Γ(a, ξ) = ⟨φ(y), M_a ξ⟩`, `y = P_a(J) ξ`. -/
noncomputable def gam (q a B : ℝ) (ξ : Fin 2 → ℝ) : ℝ :=
  ∑ i, phi q ((aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ) i) *
    ((a • (Kstar q * Jmat) + B • (Kstar q - Jmat * Kstar q * Jmat)) *ᵥ ξ) i

lemma gam_two (q a B u v : ℝ) :
    gam q a B ![u, v] =
      phi q ((1 + B) * u + a * v) * (-(a / 2 + B * Dstar q) * u + (B - a * Dstar q / 2) * v) +
        phi q ((1 + B) * v - a * u) * (-(a / 2 + B * Dstar q) * v - (B - a * Dstar q / 2) * u) := by
  unfold gam
  rw [Mmat_eq, aeval_Jmat_Pa_proved, smul_one_add_smul_J_mulVec, smul_one_add_smul_J_mulVec, Fin.sum_univ_two]
  simp

/-! ### Derivatives in `ε` -/

/-- `d/dε ‖P_a(T_ε) ξ‖_p^p |₀ = p Γ(a, ξ)` for every real `ξ` (`p > 1`). -/
lemma hasDerivAt_norm_PaTeps (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal) (hptop : p ≠ ⊤) (a B : ℝ)
    (ξ : Fin 2 → ℝ) :
    HasDerivAt (fun ε => ‖WithLp.toLp p (aeval (Teps p.toReal ε) (Pa a B) *ᵥ ξ)‖ ^ p.toReal)
      (p.toReal * gam p.toReal a B ξ) 0 := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : ℝ, ξ = ![u, v] := ⟨ξ 0, ξ 1, by ext i; fin_cases i <;> rfl⟩
  have hfun : (fun ε => ‖WithLp.toLp p (aeval (Teps p.toReal ε) (Pa a B) *ᵥ ![u, v])‖ ^ p.toReal) = fun ε =>
      |Xe (Dstar p.toReal) a B ε * u + Ye (Dstar p.toReal) a B ε * v| ^ p.toReal +
        |Xe (Dstar p.toReal) a B ε * v - Ye (Dstar p.toReal) a B ε * u| ^ p.toReal := by
    funext ε
    rw [aeval_Teps_Pa, smul_one_add_smul_J_mulVec, norm_toLp_fin2_rpow p hptop]
  rw [hfun, gam_two]
  exact hasDerivAt_gainfun hp (Dstar p.toReal) a B u v

/-- Entry `(i, j)` of `P_a(T_ε)` has derivative entry `(i, j)` of `X′(0) I + Y′(0) J` at `0`. -/
lemma hasDerivAt_aeval_Teps_entry (q a B : ℝ) (i j : Fin 2) :
    HasDerivAt (fun ε => aeval (Teps q ε) (Pa a B) i j)
      (((-(a / 2 + B * Dstar q)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (B - a * Dstar q / 2) • Jmat :
        Matrix (Fin 2) (Fin 2) ℝ) i j) 0 := by
  have hfun : (fun ε => aeval (Teps q ε) (Pa a B) i j) =
      fun ε => Xe (Dstar q) a B ε * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j + Ye (Dstar q) a B ε * (Jmat : Matrix _ _ ℝ) i j := by
    funext ε
    rw [aeval_Teps_Pa]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hfun]
  have h := ((hasDerivAt_Xe (Dstar q) a B).mul_const ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)).add
    ((hasDerivAt_Ye (Dstar q) a B).mul_const ((Jmat : Matrix (Fin 2) (Fin 2) ℝ) i j))
  convert h using 1
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

lemma aeval_Pa_one_zero (T : Matrix (Fin 2) (Fin 2) ℝ) : aeval T (Pa (1 : ℝ) 0) = 1 + T := by
  simp [Pa]

lemma aeval_Pa_zero_neg_one (T : Matrix (Fin 2) (Fin 2) ℝ) : aeval T (Pa (0 : ℝ) (-1)) = 1 + T ^ 2 := by
  simp [Pa]

/-- `d/dε T_ε |₀ = K_* J`, entrywise. -/
lemma hasDerivAt_Teps_entry (q : ℝ) (i j : Fin 2) :
    HasDerivAt (fun ε => Teps q ε i j) ((Kstar q * Jmat : Matrix (Fin 2) (Fin 2) ℝ) i j) 0 := by
  have h := (hasDerivAt_aeval_Teps_entry q 1 0 i j).sub_const ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
  have hfun : (fun ε => aeval (Teps q ε) (Pa (1 : ℝ) 0) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) =
      fun ε => Teps q ε i j := by
    funext ε
    rw [aeval_Pa_one_zero, Matrix.add_apply]
    ring
  rw [hfun] at h
  convert h using 1
  rw [kstar_mul_J]
  fin_cases i <;> fin_cases j <;> simp [Jmat] <;> ring

/-- `d/dε T_ε² |₀ = K_* J² + J K_* J`, entrywise. -/
lemma hasDerivAt_Teps_sq_entry (q : ℝ) (i j : Fin 2) :
    HasDerivAt (fun ε => (Teps q ε ^ 2) i j)
      ((Kstar q * Jmat * Jmat + Jmat * Kstar q * Jmat : Matrix (Fin 2) (Fin 2) ℝ) i j) 0 := by
  have h := (hasDerivAt_aeval_Teps_entry q 0 (-1) i j).sub_const ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
  have hfun : (fun ε => aeval (Teps q ε) (Pa (0 : ℝ) (-1)) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) =
      fun ε => (Teps q ε ^ 2) i j := by
    funext ε
    rw [aeval_Pa_zero_neg_one, Matrix.add_apply]
    ring
  rw [hfun] at h
  have hm : Kstar q * Jmat * Jmat + Jmat * Kstar q * Jmat = Dstar q • (1 : Matrix (Fin 2) (Fin 2) ℝ) - Jmat := by
    rw [kstar_JJ, neg_add_eq_sub, ← neg_sub, kstar_sub_JKJ, neg_sub]
  convert h using 1
  rw [hm]
  fin_cases i <;> fin_cases j <;> simp [Jmat]

/-! ### The contraction paragraph: `d/dε ‖exp(εK_*)ξ‖_p^p` -/

/-- `exp(ε K_*) = e^(-ε D_*/2) R_(ε/2)`. -/
lemma exp_eps_Kstar (q ε : ℝ) :
    NormedSpace.exp (ε • Kstar q) = Real.exp (-(ε * Dstar q / 2)) • Rot (ε / 2) := by
  have h := teps_eq_exp_proved q ε
  calc NormedSpace.exp (ε • Kstar q) = NormedSpace.exp (ε • Kstar q) * Jmat * (-Jmat) := by
        rw [mul_assoc, mul_neg, Jmat_mul_self, neg_neg, mul_one]
    _ = Teps q ε * (-Jmat) := by rw [h]
    _ = _ := by unfold Teps; rw [mul_assoc, mul_neg, Jmat_mul_self, neg_neg, mul_one]

/-- First coordinate of `exp(ε K_*) (u, v)`. -/
noncomputable def ex1 (D u v ε : ℝ) : ℝ :=
  Real.exp (-(ε * D / 2)) * (Real.cos (ε / 2) * u + Real.sin (ε / 2) * v)

/-- Second coordinate of `exp(ε K_*) (u, v)`. -/
noncomputable def ex2 (D u v ε : ℝ) : ℝ :=
  Real.exp (-(ε * D / 2)) * (Real.cos (ε / 2) * v - Real.sin (ε / 2) * u)

lemma expK_mulVec (q u v ε : ℝ) :
    NormedSpace.exp (ε • Kstar q) *ᵥ ![u, v] = ![ex1 (Dstar q) u v ε, ex2 (Dstar q) u v ε] := by
  rw [exp_eps_Kstar]
  have hR : Real.exp (-(ε * Dstar q / 2)) • Rot (ε / 2) =
      (Real.exp (-(ε * Dstar q / 2)) * Real.cos (ε / 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (Real.exp (-(ε * Dstar q / 2)) * Real.sin (ε / 2)) • Jmat := by
    rw [Rot, smul_add, smul_smul, smul_smul]
  rw [hR, smul_one_add_smul_J_mulVec]
  ext i
  fin_cases i <;> simp [ex1, ex2] <;> ring

lemma Kstar_mulVec (q u v : ℝ) :
    Kstar q *ᵥ ![u, v] = ![(v - Dstar q * u) / 2, (-u - Dstar q * v) / 2] := by
  ext i
  fin_cases i <;> simp [Kstar, Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

lemma hasDerivAt_ex1 (D u v ε : ℝ) :
    HasDerivAt (ex1 D u v) ((ex2 D u v ε - D * ex1 D u v ε) / 2) ε := by
  have hE := (((hasDerivAt_id' ε).mul_const D).div_const 2).neg.exp
  have hh := (hasDerivAt_id' ε).div_const 2
  have H := hE.mul ((hh.cos.mul_const u).add (hh.sin.mul_const v))
  convert H using 1
  · funext x
    simp only [ex1, Pi.mul_apply, Pi.add_apply, Pi.neg_apply]
  · simp only [ex1, ex2, Pi.add_apply, Pi.neg_apply]
    ring

lemma hasDerivAt_ex2 (D u v ε : ℝ) :
    HasDerivAt (ex2 D u v) ((-ex1 D u v ε - D * ex2 D u v ε) / 2) ε := by
  have hE := (((hasDerivAt_id' ε).mul_const D).div_const 2).neg.exp
  have hh := (hasDerivAt_id' ε).div_const 2
  have H := hE.mul ((hh.cos.mul_const v).sub (hh.sin.mul_const u))
  convert H using 1
  · funext x
    simp only [ex2, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply]
  · simp only [ex1, ex2, Pi.sub_apply, Pi.neg_apply]
    ring

/-- `d/dε ‖ξ(ε)‖_p^p = p ⟨φ(ξ(ε)), K_* ξ(ε)⟩`, `ξ(ε) = exp(ε K_*) ξ` (`p > 1`). -/
lemma hasDerivAt_norm_expK (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal) (hptop : p ≠ ⊤) (ξ : Fin 2 → ℝ) (ε : ℝ) :
    HasDerivAt (fun ε => ‖WithLp.toLp p (NormedSpace.exp (ε • Kstar p.toReal) *ᵥ ξ)‖ ^ p.toReal)
      (p.toReal * ∑ i, phi p.toReal ((NormedSpace.exp (ε • Kstar p.toReal) *ᵥ ξ) i) *
        (Kstar p.toReal *ᵥ (NormedSpace.exp (ε • Kstar p.toReal) *ᵥ ξ)) i) ε := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : ℝ, ξ = ![u, v] := ⟨ξ 0, ξ 1, by ext i; fin_cases i <;> rfl⟩
  set q := p.toReal with hqdef
  set D := Dstar q with hD
  have hfun : (fun ε => ‖WithLp.toLp p (NormedSpace.exp (ε • Kstar q) *ᵥ ![u, v])‖ ^ q) =
      fun ε => |ex1 D u v ε| ^ q + |ex2 D u v ε| ^ q := by
    funext ε
    rw [expK_mulVec, norm_toLp_fin2_rpow p hptop]
  have g1 := (Matsaev.Angle.hasDerivAt_absRpow hp (ex1 D u v ε)).comp ε (hasDerivAt_ex1 D u v ε)
  have g2 := (Matsaev.Angle.hasDerivAt_absRpow hp (ex2 D u v ε)).comp ε (hasDerivAt_ex2 D u v ε)
  rw [hfun, expK_mulVec, Kstar_mulVec, Fin.sum_univ_two]
  convert g1.add g2 using 1
  · funext x
    simp only [Pi.add_apply, Function.comp_apply]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

/-- `⟨φ(w), K_* w⟩ = ½ ‖w‖_p^p (Q(w) - D_*)` for `w ≠ 0`. -/
lemma inner_phi_Kstar {q : ℝ} (hq : 0 < q) (u v : ℝ) (hN : |u| ^ q + |v| ^ q ≠ 0) :
    ∑ i, phi q (![u, v] i) * (Kstar q *ᵥ ![u, v]) i =
      1 / 2 * (|u| ^ q + |v| ^ q) * (Qf q u v - Dstar q) := by
  rw [Kstar_mulVec, Fin.sum_univ_two]
  have hQ : (|u| ^ q + |v| ^ q) * Qf q u v = phi q u * v - phi q v * u := by
    unfold Qf
    field_simp
  have h0 : phi q u * u = |u| ^ q := B0.phi_mul_self hq u
  have h1 : phi q v * v = |v| ^ q := B0.phi_mul_self hq v
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (-1 / 2 : ℝ) * hQ + (-(Dstar q) / 2) * h0 + (-(Dstar q) / 2) * h1

/-! ### `Γ(0) = 0`, `E_*`, and `(1+t^p)(1+D_*²) = (p-1)E_*` -/

/-- Powers of `t > 0` through `x = t^(q-2)`. -/
lemma rpow_facts {q t : ℝ} (ht : 0 < t) :
    t ^ (q - 1) = t ^ (q - 2) * t ∧ t ^ q = t ^ (q - 2) * t ^ 2 ∧
      t ^ (2 * q - 2) = (t ^ (q - 2) * t) ^ 2 := by
  have h1 : t ^ (q - 1) = t ^ (q - 2) * t := by
    rw [← Real.rpow_add_one ht.ne']
    ring_nf
  have h2 : t ^ q = t ^ (q - 2) * t ^ 2 := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht]
    norm_num
  refine ⟨h1, h2, ?_⟩
  rw [← h1, ← Real.rpow_natCast (t ^ (q - 1)) 2, ← Real.rpow_mul ht.le]
  norm_num
  ring_nf

/-- The identity `(t² + t^(p-2))(1 + t^p) - (t - t^(p-1))² = t^(p-2)(1 + t²)²` (every `t ≥ 0`, `p > 2`). -/
lemma E_identity {q : ℝ} (hq : 2 < q) {t : ℝ} (ht : 0 ≤ t) :
    (t ^ 2 + t ^ (q - 2)) * (1 + t ^ q) - (t - t ^ (q - 1)) ^ 2 = t ^ (q - 2) * (1 + t ^ 2) ^ 2 := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
    ring
  · obtain ⟨h1, h2, -⟩ := rpow_facts (q := q) hpos
    rw [h1, h2]
    ring

/-- `Q(1, s) = f(s) = s (1 - |s|^(p-2)) / (1 + |s|^p)` for every real `s` (Section 3). -/
lemma Qf_one_left (q s : ℝ) : Qf q 1 s = s * (1 - |s| ^ (q - 2)) / (1 + |s| ^ q) := by
  unfold Qf
  rw [Matsaev.Angle.phi_eq_mul q s, Matsaev.Angle.phi_eq_mul q 1]
  simp
  ring

/-- `H(s) = ⟨φ(1, s), (J - D_* I)(1, s)⟩ = ‖(1, s)‖_p^p (Q(1, s) - D_*)`. -/
noncomputable def Hfun (q D s : ℝ) : ℝ := (s - D) - phi q s * (1 + D * s)

lemma Hfun_eq {q : ℝ} (hq : 0 < q) (D s : ℝ) : Hfun q D s = (1 + |s| ^ q) * (Qf q 1 s - D) := by
  have hN : (1 : ℝ) + |s| ^ q ≠ 0 := by positivity
  have hQ : (1 + |s| ^ q) * Qf q 1 s = phi q 1 * s - phi q s * 1 := by
    unfold Qf
    rw [abs_one, Real.one_rpow]
    field_simp
  have h1 : phi q 1 = 1 := by simp [phi]
  have hs : phi q s * s = |s| ^ q := B0.phi_mul_self hq s
  unfold Hfun
  rw [h1] at hQ
  linear_combination (-1 : ℝ) * hQ - D * hs

lemma hasDerivAt_Hfun {q : ℝ} (hq : 2 < q) (D s : ℝ) :
    HasDerivAt (Hfun q D) (1 - ((q - 1) * |s| ^ (q - 2) * (1 + D * s) + phi q s * D)) s := by
  have h := ((hasDerivAt_id' s).sub_const D).sub
    ((Matsaev.Angle.hasDerivAt_phi hq s).mul ((hasDerivAt_id' s).const_mul D |>.const_add 1))
  convert h using 1
  · funext x
    simp only [Hfun, Pi.sub_apply, Pi.mul_apply]
  · ring

lemma Hfun_le {q : ℝ} (hq : 0 < q) {D : ℝ} (hQ : ∀ s : ℝ, Qf q 1 s ≤ D) (s : ℝ) : Hfun q D s ≤ 0 := by
  rw [Hfun_eq hq]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [hQ s])

lemma Qf_one_pos {q t : ℝ} (ht : 0 < t) : Qf q 1 t = dfun q t := by
  obtain ⟨h1, h2, -⟩ := rpow_facts (q := q) ht
  rw [Qf_one_left, abs_of_pos ht, dfun, h1, h2]
  ring

/-- The facts about `t_*` (Lemma 3.4) used below. -/
lemma tstar_facts {q : ℝ} (hq : 2 < q) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcrit : deriv (dfun q) t = 0) :
    Dstar q = dfun q t ∧ (∀ u v : ℝ, (u, v) ≠ (0, 0) → Qf q u v ≤ Dstar q) ∧
      1 + t ^ (2 * q - 2) = (q - 1) * t ^ (q - 2) * (1 + t ^ 2) := by
  obtain ⟨t', -, hcrit', -, -, hle, hD, -, hST⟩ := lemma_3_3_proved q hq
  have htt : t = t' := (hcrit' t ht).mp hcrit
  subst htt
  exact ⟨hD, fun u v h => hD ▸ hle u v h, hST⟩

/-- `D_* (1 + t^p) = t - t^(p-1)` at `t = t_*`. -/
lemma Dstar_mul {q : ℝ} (hq : 2 < q) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcrit : deriv (dfun q) t = 0) :
    Dstar q * (1 + t ^ q) = t - t ^ (q - 1) := by
  rw [(tstar_facts hq ht hcrit).1, dfun]
  have : (1 : ℝ) + t ^ q ≠ 0 := by have := Real.rpow_pos_of_pos ht.1 q; positivity
  field_simp

/-- `H′(t_*) = 0`: `H ≤ 0 = H(t_*)`, a maximum. -/
lemma Hfun_deriv_zero {q : ℝ} (hq : 2 < q) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcrit : deriv (dfun q) t = 0) :
    1 - ((q - 1) * |t| ^ (q - 2) * (1 + Dstar q * t) + phi q t * Dstar q) = 0 := by
  obtain ⟨hD, hle, -⟩ := tstar_facts hq ht hcrit
  have hq0 : 0 < q := by linarith
  have hQ : ∀ s : ℝ, Qf q 1 s ≤ Dstar q := fun s => hle 1 s (by simp)
  have ht0 : Hfun q (Dstar q) t = 0 := by
    rw [Hfun_eq hq0, Qf_one_pos ht.1, hD, sub_self, mul_zero]
  have hmax : IsLocalMax (Hfun q (Dstar q)) t := Filter.Eventually.of_forall fun s => by
    rw [ht0]
    exact Hfun_le hq0 hQ s
  exact hmax.hasDerivAt_eq_zero (hasDerivAt_Hfun hq (Dstar q) t)

/-! ### `Γ′(0)` along `ξ_a = (1, σ(a))` -/

/-- One-sided derivative at `0` of `a ↦ Γ(a, (1, σ(a)))`, `σ(0) = t > 0`, given `H′(t) = 0`. -/
lemma hasDerivWithinAt_gam {q : ℝ} (hq : 2 < q) {B t σ' : ℝ} (hB : 0 < 1 + B) (ht : 0 < t) {σ : ℝ → ℝ}
    (hσ0 : σ 0 = t) (hσ : HasDerivWithinAt σ σ' (Ici 0) 0)
    (hH : 1 - ((q - 1) * |t| ^ (q - 2) * (1 + Dstar q * t) + phi q t * Dstar q) = 0) :
    HasDerivWithinAt (fun a => gam q a B ![1, σ a])
      ((1 + B) ^ (q - 2) * ((q - 1) * B * (t * (t - Dstar q) + t ^ (q - 2) * (1 + Dstar q * t)) -
        1 / 2 * (1 + B) * ((1 + Dstar q * t) + t ^ (q - 1) * (t - Dstar q)))) (Ici 0) 0 := by
  have hq1 : 1 < q := by linarith
  have hid : HasDerivWithinAt (fun a : ℝ => a) 1 (Ici 0) 0 := (hasDerivAt_id' (0 : ℝ)).hasDerivWithinAt
  have hy1 : HasDerivWithinAt (fun a => (1 + B) * 1 + a * σ a) t (Ici 0) 0 :=
    ((hid.mul hσ).const_add ((1 + B) * 1)).congr_deriv (by simp [hσ0])
  have hy2 : HasDerivWithinAt (fun a => (1 + B) * σ a - a * 1) ((1 + B) * σ' - 1) (Ici 0) 0 :=
    ((hσ.const_mul (1 + B)).sub (hid.mul_const 1)).congr_deriv (by ring)
  have hm1 : HasDerivWithinAt (fun a => -(a / 2 + B * Dstar q) * 1 + (B - a * Dstar q / 2) * σ a)
      (-(1 / 2) - Dstar q / 2 * t + B * σ') (Ici 0) 0 :=
    ((((hid.div_const 2).add_const (B * Dstar q)).neg.mul_const 1).add
      ((((hid.mul_const (Dstar q)).div_const 2).const_sub B).mul hσ)).congr_deriv (by simp [hσ0]; ring)
  have hm2 : HasDerivWithinAt (fun a => -(a / 2 + B * Dstar q) * σ a - (B - a * Dstar q / 2) * 1)
      (-(1 / 2) * t - B * Dstar q * σ' + Dstar q / 2) (Ici 0) 0 :=
    ((((hid.div_const 2).add_const (B * Dstar q)).neg.mul hσ).sub
      ((((hid.mul_const (Dstar q)).div_const 2).const_sub B).mul_const 1)).congr_deriv (by simp [hσ0]; ring)
  have hc1 : (1 + B) ^ (q - 1) = (1 + B) ^ (q - 2) * (1 + B) := by
    rw [← Real.rpow_add_one hB.ne']
    ring_nf
  obtain ⟨hx1, -, -⟩ := rpow_facts (q := q) ht
  have hp1 : HasDerivAt (phi q) ((q - 1) * (1 + B) ^ (q - 2)) ((fun a => (1 + B) * 1 + a * σ a) 0) := by
    have h := Matsaev.Angle.hasDerivAt_phi hq (1 + B)
    rw [abs_of_pos hB] at h
    simpa using h
  have hp2 : HasDerivAt (phi q) ((q - 1) * ((1 + B) ^ (q - 2) * t ^ (q - 2)))
      ((fun a => (1 + B) * σ a - a * 1) 0) := by
    have h := Matsaev.Angle.hasDerivAt_phi hq ((1 + B) * t)
    rw [abs_of_pos (mul_pos hB ht), Real.mul_rpow hB.le ht.le] at h
    simpa [hσ0] using h
  have hv1 : phi q ((1 + B) * 1 + 0 * σ 0) = (1 + B) ^ (q - 2) * (1 + B) := by
    rw [mul_one, zero_mul, add_zero, B0.phi_of_nonneg hq1 hB.le, hc1]
  have hv2 : phi q ((1 + B) * σ 0 - 0 * 1) = (1 + B) ^ (q - 2) * (1 + B) * (t ^ (q - 2) * t) := by
    rw [hσ0, zero_mul, sub_zero, B0.phi_of_nonneg hq1 (mul_pos hB ht).le, Real.mul_rpow hB.le ht.le, hc1, hx1]
  have H := ((hp1.comp_hasDerivWithinAt (0 : ℝ) hy1).mul hm1).add
    ((hp2.comp_hasDerivWithinAt (0 : ℝ) hy2).mul hm2)
  have hfun : (fun a => gam q a B ![1, σ a]) = fun a =>
      phi q ((1 + B) * 1 + a * σ a) * (-(a / 2 + B * Dstar q) * 1 + (B - a * Dstar q / 2) * σ a) +
        phi q ((1 + B) * σ a - a * 1) * (-(a / 2 + B * Dstar q) * σ a - (B - a * Dstar q / 2) * 1) :=
    funext fun a => gam_two q a B 1 (σ a)
  rw [hfun]
  refine H.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [hv1, hv2, hσ0, hx1]
  rw [abs_of_pos ht, B0.phi_of_nonneg hq1 ht.le, hx1] at hH
  linear_combination (σ' * (1 + B) ^ (q - 2) * (1 + B) * B) * hH

/-! ### The paper's form of `Γ′(0)`, the identities, and `Γ(a) > 0` -/

/-- `E_* = t^(p-2)(1+t²)²/(1+t^p)` at `t = t_*`. -/
lemma E_eq {q : ℝ} (hq : 2 < q) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcrit : deriv (dfun q) t = 0) :
    t ^ 2 + t ^ (q - 2) - Dstar q * (t - t ^ (q - 1)) = t ^ (q - 2) * (1 + t ^ 2) ^ 2 / (1 + t ^ q) := by
  have hN : (0 : ℝ) < 1 + t ^ q := by have := Real.rpow_pos_of_pos ht.1 q; positivity
  rw [eq_div_iff hN.ne']
  have hDm := Dstar_mul hq ht hcrit
  have hE := E_identity hq ht.1.le
  linear_combination hE - (t - t ^ (q - 1)) * hDm

/-- `(1+t^p)²(1+D_*²) = (1+t^p)² + (t-t^(p-1))² = (1+t²)(1+t^(2p-2)) = (p-1)t^(p-2)(1+t²)²` at `t = t_*`. -/
lemma ST_chain {q : ℝ} (hq : 2 < q) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcrit : deriv (dfun q) t = 0) :
    (1 + t ^ q) ^ 2 * (1 + Dstar q ^ 2) = (1 + t ^ q) ^ 2 + (t - t ^ (q - 1)) ^ 2 ∧
      (1 + t ^ q) ^ 2 + (t - t ^ (q - 1)) ^ 2 = (1 + t ^ 2) * (1 + t ^ (2 * q - 2)) ∧
      (1 + t ^ 2) * (1 + t ^ (2 * q - 2)) = (q - 1) * t ^ (q - 2) * (1 + t ^ 2) ^ 2 := by
  obtain ⟨-, -, hST⟩ := tstar_facts hq ht hcrit
  have hDm := Dstar_mul hq ht hcrit
  obtain ⟨hx1, hx2, hx3⟩ := rpow_facts (q := q) ht.1
  refine ⟨by linear_combination (Dstar q * (1 + t ^ q) + (t - t ^ (q - 1))) * hDm, ?_,
    by linear_combination (1 + t ^ 2) * hST⟩
  rw [hx1, hx2, hx3]
  ring

/-- `(1+t^p)(1+D_*²) = (p-1)E_*` at `t = t_*`. -/
lemma NE_identity {q : ℝ} (hq : 2 < q) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcrit : deriv (dfun q) t = 0) :
    (1 + t ^ q) * (1 + Dstar q ^ 2) = (q - 1) * (t ^ 2 + t ^ (q - 2) - Dstar q * (t - t ^ (q - 1))) := by
  obtain ⟨h1, h2, h3⟩ := ST_chain hq ht hcrit
  have hE := E_eq hq ht hcrit
  have hN : (0 : ℝ) < 1 + t ^ q := by have := Real.rpow_pos_of_pos ht.1 q; positivity
  rw [hE]
  field_simp
  linear_combination h1 + h2 + h3

/-- The paper's `Γ′(0)` and its simplified form agree. -/
lemma gamma_deriv_eq {q : ℝ} (hq : 2 < q) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcrit : deriv (dfun q) t = 0) (B : ℝ) :
    (1 + B) ^ (q - 2) * (-(1 / 2) * (1 + B) * (1 + t ^ q) * (1 + Dstar q ^ 2) +
        (q - 1) * B * (t ^ 2 + t ^ (q - 2) - Dstar q * (t - t ^ (q - 1)))) =
      (1 + B) ^ (q - 2) * (q - 1) * (t ^ 2 + t ^ (q - 2) - Dstar q * (t - t ^ (q - 1))) * (B - 1) / 2 := by
  linear_combination (-(1 / 2) * (1 + B) ^ (q - 2) * (1 + B)) * NE_identity hq ht hcrit

/-- `Γ(a) = Γ(a, ξ_a)` along any `ξ_a` with `(ξ_a)₁ = 1`, `ξ_0 = (1, t_*)`, differentiable from the right at `0`:
`Γ′(0)` in the paper's form. -/
lemma gamma_curve {q : ℝ} (hq : 2 < q) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcrit : deriv (dfun q) t = 0) {B : ℝ}
    (hB : 0 < 1 + B) {ξ : ℝ → Fin 2 → ℝ} {ξ' : Fin 2 → ℝ} (hξ1 : ∀ a, ξ a 0 = 1) (hξ0 : ξ 0 = ![1, t])
    (hξ : HasDerivWithinAt ξ ξ' (Ici 0) 0) :
    HasDerivWithinAt (fun a => gam q a B (ξ a))
      ((1 + B) ^ (q - 2) * (-(1 / 2) * (1 + B) * (1 + t ^ q) * (1 + Dstar q ^ 2) +
        (q - 1) * B * (t ^ 2 + t ^ (q - 2) - Dstar q * (t - t ^ (q - 1))))) (Ici 0) 0 := by
  have hξa : ∀ a, ξ a = ![1, ξ a 1] := fun a => by
    ext i
    fin_cases i
    · simp [hξ1]
    · rfl
  have hσ0 : ξ 0 1 = t := by rw [hξ0]; rfl
  have hσ : HasDerivWithinAt (fun a => ξ a 1) (ξ' 1) (Ici 0) 0 := (hasDerivWithinAt_pi.mp hξ) 1
  have h := hasDerivWithinAt_gam hq hB ht.1 hσ0 hσ (Hfun_deriv_zero hq ht hcrit)
  have hfun : (fun a => gam q a B (ξ a)) = fun a => gam q a B ![1, ξ a 1] := funext fun a => by rw [← hξa a]
  rw [hfun]
  refine h.congr_deriv ?_
  have hDm := Dstar_mul hq ht hcrit
  obtain ⟨hx1, hx2, -⟩ := rpow_facts (q := q) ht.1
  rw [hx1, hx2] at hDm
  rw [hx1, hx2]
  linear_combination ((1 + B) ^ (q - 2) * (1 + B) * Dstar q / 2) * hDm

/-- The paper's `Γ(a) = a Γ′(0) + o(a)` from a one-sided derivative with `Γ(0) = 0`. -/
lemma isLittleO_of_hasDerivWithinAt {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivWithinAt f f' (Ici 0) 0) (h0 : f 0 = 0) :
    (fun a => f a - a * f') =o[𝓝[≥] 0] fun a => a := by
  rw [hasDerivWithinAt_iff_isLittleO] at hf
  simpa [h0, mul_comm] using hf

/-- A positive one-sided derivative at `0` and `f 0 = 0` give `f > 0` on some `(0, a₂)`. -/
lemma exists_pos_of_hasDerivWithinAt {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivWithinAt f f' (Ici 0) 0) (h0 : f 0 = 0)
    (hpos : 0 < f') : ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ a : ℝ, 0 < a → a < a₂ → 0 < f a := by
  have ht := hasDerivWithinAt_iff_tendsto_slope.mp hf
  have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext x
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
  rw [hs] at ht
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < slope f 0 a := ht.eventually (lt_mem_nhds hpos)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨u, hu, fun a ha hau => ?_⟩
  have h := hsub ⟨ha, hau⟩
  simp only [Set.mem_ofPred_eq, slope_def_field, sub_zero, h0] at h
  exact (div_pos_iff_of_pos_right ha).mp h

lemma E_pos {q : ℝ} (hq : 2 < q) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcrit : deriv (dfun q) t = 0) :
    0 < t ^ 2 + t ^ (q - 2) - Dstar q * (t - t ^ (q - 1)) := by
  rw [E_eq hq ht hcrit]
  have h1 := Real.rpow_pos_of_pos ht.1 (q - 2)
  have h2 := Real.rpow_pos_of_pos ht.1 q
  positivity

/-! ### `Γ(0) = 0`, `y_0 = (1+B) ξ_0`, `⟨φ(ξ), (J - D_* I)ξ⟩`, and the values at `ξ_0` -/

lemma J_mulVec (u v : ℝ) : (Jmat : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![u, v] = ![v, -u] := by
  have h := smul_one_add_smul_J_mulVec 0 1 u v
  simp only [zero_smul, one_smul, zero_add, zero_mul, one_mul, zero_sub] at h
  exact h

lemma JD_mulVec (q u v : ℝ) :
    (Jmat - Dstar q • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ ![u, v] = ![v - Dstar q * u, -u - Dstar q * v] := by
  have hM : (Jmat - Dstar q • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      (-Dstar q) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 : ℝ) • Jmat := by
    rw [one_smul, neg_smul, sub_eq_neg_add]
  rw [hM, smul_one_add_smul_J_mulVec]
  exact Matrix.vec2_eq (by ring) (by ring)

/-- The paper's `g(ξ) = ⟨φ(ξ), (J - D_* I) ξ⟩`. -/
noncomputable def gfun (q : ℝ) (ξ : Fin 2 → ℝ) : ℝ :=
  ∑ i, phi q (ξ i) * ((Jmat - Dstar q • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ ξ) i

lemma gfun_two (q u v : ℝ) :
    gfun q ![u, v] = phi q u * (v - Dstar q * u) + phi q v * (-u - Dstar q * v) := by
  unfold gfun
  rw [JD_mulVec, Fin.sum_univ_two]
  simp

lemma gfun_eq {q : ℝ} (hq : 0 < q) (u v : ℝ) (hN : |u| ^ q + |v| ^ q ≠ 0) :
    gfun q ![u, v] = (|u| ^ q + |v| ^ q) * (Qf q u v - Dstar q) := by
  rw [gfun_two]
  have hQ : (|u| ^ q + |v| ^ q) * Qf q u v = phi q u * v - phi q v * u := by
    unfold Qf
    field_simp
  have h0 : phi q u * u = |u| ^ q := B0.phi_mul_self hq u
  have h1 : phi q v * v = |v| ^ q := B0.phi_mul_self hq v
  linear_combination (-1 : ℝ) * hQ + (-Dstar q) * h0 + (-Dstar q) * h1

lemma normq_pos {q : ℝ} {u v : ℝ} (h : (u, v) ≠ (0, 0)) : 0 < |u| ^ q + |v| ^ q := by
  rcases eq_or_ne u 0 with hu | hu
  · have hv : v ≠ 0 := fun hv => h (by rw [hu, hv])
    have := Real.rpow_pos_of_pos (abs_pos.mpr hv) q
    positivity
  · have := Real.rpow_pos_of_pos (abs_pos.mpr hu) q
    positivity

lemma gfun_le {q : ℝ} (hq : 2 < q) (ξ : Fin 2 → ℝ) : gfun q ξ ≤ 0 := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : ℝ, ξ = ![u, v] := ⟨ξ 0, ξ 1, by ext i; fin_cases i <;> rfl⟩
  obtain ⟨t, -, -, -, -, hle, hD, -, -⟩ := lemma_3_3_proved q hq
  by_cases h : (u, v) = (0, 0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp [gfun_two, Matsaev.Angle.phi_zero]
  · rw [gfun_eq (by linarith) u v (normq_pos h).ne']
    exact mul_nonpos_of_nonneg_of_nonpos (normq_pos h).le (by linarith [hle u v h, hD])

/-- `g` has derivative `0` at its maximum `ξ_0 = (1, t_*)` in every direction `ψ`. -/
lemma gfun_dir_deriv {q : ℝ} (hq : 2 < q) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcrit : deriv (dfun q) t = 0)
    (ψ : Fin 2 → ℝ) : HasDerivAt (fun h : ℝ => gfun q (![1, t] + h • ψ)) 0 0 := by
  have h0 : gfun q ![1, t] = 0 := by
    rw [gfun_eq (by linarith) 1 t (by positivity), Qf_one_pos ht.1, (tstar_facts hq ht hcrit).1, sub_self,
      mul_zero]
  have e0 : HasDerivAt (fun h : ℝ => 1 + h * ψ 0) (ψ 0) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const (ψ 0)).const_add 1).congr_deriv (one_mul _)
  have e1 : HasDerivAt (fun h : ℝ => t + h * ψ 1) (ψ 1) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const (ψ 1)).const_add t).congr_deriv (one_mul _)
  have P0 := (Matsaev.Angle.hasDerivAt_phi hq (1 + 0 * ψ 0)).comp (0 : ℝ) e0
  have P1 := (Matsaev.Angle.hasDerivAt_phi hq (t + 0 * ψ 1)).comp (0 : ℝ) e1
  have H := (P0.mul (e1.sub (e0.const_mul (Dstar q)))).add (P1.mul (e0.neg.sub (e1.const_mul (Dstar q))))
  have hfun : (fun h : ℝ => gfun q (![1, t] + h • ψ)) = fun h =>
      phi q (1 + h * ψ 0) * ((t + h * ψ 1) - Dstar q * (1 + h * ψ 0)) +
        phi q (t + h * ψ 1) * (-(1 + h * ψ 0) - Dstar q * (t + h * ψ 1)) := by
    funext h
    have hv : (![1, t] + h • ψ : Fin 2 → ℝ) = ![1 + h * ψ 0, t + h * ψ 1] := by
      ext i
      fin_cases i <;> simp
    rw [hv, gfun_two]
  have hmax : IsLocalMax (fun h : ℝ => gfun q (![1, t] + h • ψ)) 0 := Filter.Eventually.of_forall fun h => by
    simp only [zero_smul, add_zero, h0]
    exact gfun_le hq _
  rw [hfun] at hmax ⊢
  have hV := hmax.hasDerivAt_eq_zero H
  exact H.congr_deriv hV

/-- `y_0 = P_0(J) ξ_0 = (1+B) ξ_0` and `Γ(0, ξ_0) = (1+B)^(p-1) B ‖ξ_0‖_p^p (Q(ξ_0) - D_*)`. -/
lemma gam_zero {q : ℝ} (hq : 1 < q) {B : ℝ} (hB : 0 < 1 + B) {t : ℝ} (ht : 0 < t) :
    aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa 0 B) *ᵥ ![1, t] = (1 + B) • ![1, t] ∧
      gam q 0 B ![1, t] = (1 + B) ^ (q - 1) * B * (1 + t ^ q) * (Qf q 1 t - Dstar q) := by
  refine ⟨?_, ?_⟩
  · rw [aeval_Jmat_Pa_proved, smul_one_add_smul_J_mulVec]
    ext i
    fin_cases i <;> simp
  · have hphi : ∀ y : ℝ, phi q ((1 + B) * y) = (1 + B) ^ (q - 1) * phi q y := fun y => by
      rw [phi_mul, sign_pos hB, abs_of_pos hB]
      simp
    have h1 : phi q 1 = 1 := by simp [phi]
    have hH := Hfun_eq (by linarith : 0 < q) (Dstar q) t
    rw [abs_of_pos ht] at hH
    unfold Hfun at hH
    rw [gam_two, show (1 + B) * 1 + 0 * t = (1 + B) * 1 by ring, show (1 + B) * t - 0 * 1 = (1 + B) * t by ring,
      hphi, hphi, h1]
    linear_combination ((1 + B) ^ (q - 1) * B) * hH

/-- `d/da y_a |₀ = (1+B) ξ̇ + J ξ_0`, `y_a = P_a(J) ξ_a`. -/
lemma hasDerivWithinAt_y (B : ℝ) {ξ : ℝ → Fin 2 → ℝ} {ξ' : Fin 2 → ℝ} (hξ : HasDerivWithinAt ξ ξ' (Ici 0) 0) :
    HasDerivWithinAt (fun a => aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ a)
      ((1 + B) • ξ' + (Jmat : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ξ 0) (Ici 0) 0 := by
  have hv : ∀ w : Fin 2 → ℝ, w = ![w 0, w 1] := fun w => by ext i; fin_cases i <;> rfl
  have hfun : (fun a => aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ a) =
      fun a => ![(1 + B) * ξ a 0 + a * ξ a 1, (1 + B) * ξ a 1 - a * ξ a 0] := by
    funext a
    rw [aeval_Jmat_Pa_proved]
    conv_lhs => rw [hv (ξ a)]
    rw [smul_one_add_smul_J_mulVec]
  have hid : HasDerivWithinAt (fun a : ℝ => a) 1 (Ici 0) 0 := (hasDerivAt_id' (0 : ℝ)).hasDerivWithinAt
  have hc0 := (hasDerivWithinAt_pi.mp hξ) 0
  have hc1 := (hasDerivWithinAt_pi.mp hξ) 1
  rw [hfun, hasDerivWithinAt_pi]
  intro i
  fin_cases i
  · exact ((hc0.const_mul (1 + B)).add (hid.mul hc1)).congr_deriv (by
      conv_rhs => rw [hv (ξ 0), J_mulVec]
      simp)
  · exact ((hc1.const_mul (1 + B)).sub (hid.mul hc0)).congr_deriv (by
      conv_rhs => rw [hv (ξ 0), J_mulVec]
      simp
      ring)

/-! ### Section 2, notation -/

/-- `d/dh ‖ξ + h ψ‖_p^p |₀ = p ⟨φ(ξ), ψ⟩` for real `ξ, ψ` and `p > 1`. -/
lemma hasDerivAt_norm_dir (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal) (hptop : p ≠ ⊤) (ξ ψ : Fin 2 → ℝ) :
    HasDerivAt (fun h : ℝ => ‖WithLp.toLp p (ξ + h • ψ)‖ ^ p.toReal) (p.toReal * ∑ i, phi p.toReal (ξ i) * ψ i) 0 := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : ℝ, ξ = ![u, v] := ⟨ξ 0, ξ 1, by ext i; fin_cases i <;> rfl⟩
  obtain ⟨w₀, w₁, rfl⟩ : ∃ u v : ℝ, ψ = ![u, v] := ⟨ψ 0, ψ 1, by ext i; fin_cases i <;> rfl⟩
  have hfun : (fun h : ℝ => ‖WithLp.toLp p (![u, v] + h • ![w₀, w₁])‖ ^ p.toReal) =
      fun h => |u + h * w₀| ^ p.toReal + |v + h * w₁| ^ p.toReal := by
    funext h
    have hv : (![u, v] + h • ![w₀, w₁] : Fin 2 → ℝ) = ![u + h * w₀, v + h * w₁] := by
      ext i
      fin_cases i <;> simp
    rw [hv, norm_toLp_fin2_rpow p hptop]
  have e0 : HasDerivAt (fun h : ℝ => u + h * w₀) w₀ 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const w₀).const_add u).congr_deriv (one_mul _)
  have e1 : HasDerivAt (fun h : ℝ => v + h * w₁) w₁ 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const w₁).const_add v).congr_deriv (one_mul _)
  have g0 := (Matsaev.Angle.hasDerivAt_absRpow hp (u + 0 * w₀)).comp (0 : ℝ) e0
  have g1 := (Matsaev.Angle.hasDerivAt_absRpow hp (v + 0 * w₁)).comp (0 : ℝ) e1
  rw [hfun, Fin.sum_univ_two]
  convert g0.add g1 using 1
  · funext x
    simp only [Pi.add_apply, Function.comp_apply]
  · simp
    ring

/-! ### The last step of the proof: from `Γ(a) > 0` to `‖P_a(T_ε)‖_p > ‖P_a(J)‖_p` -/

lemma teps_zero (q : ℝ) : Teps q 0 = Jmat := by
  simp [Teps, Rot]

/-- A maximiser stays a maximiser when scaled. -/
lemma attain_smul (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin 2) (Fin 2) ℝ) (C c : ℝ) (e : Fin 2 → ℝ)
    (h : ‖WithLp.toLp p (A *ᵥ e)‖ = C * ‖WithLp.toLp p e‖) :
    ‖WithLp.toLp p (A *ᵥ (c • e))‖ = C * ‖WithLp.toLp p (c • e)‖ := by
  rw [Matrix.mulVec_smul, WithLp.toLp_smul, WithLp.toLp_smul, norm_smul, norm_smul, h]
  ring

/-- `a ↦ (1, s(a)₂/s(a)₁)` is differentiable from the right at `0` when `s` is real-analytic on `[0, a₁)`. -/
lemma curve_hasDerivWithinAt {s : ℝ → Fin 2 → ℝ} {a₁ : ℝ} (ha₁ : 0 < a₁) (hs : AnalyticOn ℝ s (Ico 0 a₁))
    (h0 : s 0 0 ≠ 0) :
    ∃ ξ' : Fin 2 → ℝ, HasDerivWithinAt (fun a => (![1, s a 1 / s a 0] : Fin 2 → ℝ)) ξ' (Ici 0) 0 := by
  have hd : DifferentiableWithinAt ℝ s (Ico 0 a₁) 0 :=
    (hs 0 ⟨le_rfl, ha₁⟩).differentiableWithinAt.mono (subset_insert _ _)
  have hr : DifferentiableWithinAt ℝ (fun a => s a 1 / s a 0) (Ico 0 a₁) 0 :=
    ((differentiableWithinAt_pi.mp hd) 1).div ((differentiableWithinAt_pi.mp hd) 0) h0
  have hv : DifferentiableWithinAt ℝ (fun a => (![1, s a 1 / s a 0] : Fin 2 → ℝ)) (Ico 0 a₁) 0 := by
    rw [differentiableWithinAt_pi]
    intro i
    fin_cases i
    exacts [differentiableWithinAt_const (1 : ℝ), hr]
  exact ⟨_, hv.hasDerivWithinAt.mono_of_mem_nhdsWithin (Ico_mem_nhdsGE ha₁)⟩

/-- If `ξ ≠ 0` attains `‖P_a(J)‖_p` and `Γ(a, ξ) > 0`, then `‖P_a(T_ε)‖_p > ‖P_a(J)‖_p` for all small `ε > 0`:
`‖P_a(T_ε)‖_p ≥ ‖P_a(T_ε)ξ‖_p/‖ξ‖_p > ‖P_a(J)ξ‖_p/‖ξ‖_p = ‖P_a(J)‖_p`. -/
lemma gain_of_gam_pos (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal) (hptop : p ≠ ⊤) (a B : ℝ) (ξ : Fin 2 → ℝ)
    (hξ : ξ ≠ 0)
    (hmax : ‖WithLp.toLp p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ)‖ =
      matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) * ‖WithLp.toLp p ξ‖)
    (hΓ : 0 < gam p.toReal a B ξ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) <
        matNorm p (aeval (Teps p.toReal ε) (Pa a B)) := by
  have hq0 : 0 < p.toReal := by linarith
  obtain ⟨ε₀, hε₀, hgt⟩ := exists_gt_of_hasDerivAt_pos (hasDerivAt_norm_PaTeps p hp hptop a B ξ) (mul_pos hq0 hΓ)
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  have hfε : ‖WithLp.toLp p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ)‖ ^ p.toReal <
      ‖WithLp.toLp p (aeval (Teps p.toReal ε) (Pa a B) *ᵥ ξ)‖ ^ p.toReal := by
    have h := hgt ε hε hεε₀
    simpa only [teps_zero] using h
  have hξpos : 0 < ‖WithLp.toLp p ξ‖ :=
    norm_pos_iff.mpr fun h => hξ (by simpa using congrArg WithLp.ofLp h)
  have hlt : matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) * ‖WithLp.toLp p ξ‖ <
      ‖WithLp.toLp p (aeval (Teps p.toReal ε) (Pa a B) *ᵥ ξ)‖ := by
    rw [← hmax]
    exact (Real.rpow_lt_rpow_iff (norm_nonneg _) (norm_nonneg _) hq0).mp hfε
  exact lt_of_mul_lt_mul_right (hlt.trans_le (norm_mulVec_le_matNorm p _ ξ)) hξpos.le

end Matsaev.Gamma
