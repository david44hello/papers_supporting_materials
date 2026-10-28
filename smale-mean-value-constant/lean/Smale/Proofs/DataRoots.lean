/-
Smale/Proofs/DataRoots.lean — the zeros of `G` (tex l.352-353, `sec5_G_zeros`) and the exact parts of Remark 5.2
(`rem_5_2_exact`). A zero of a monic quadratic lies within `2|G(r)|/|G'(r)|` of any point `r`; the kernel checks this
bound at the rational point `rG` (Smale/Proofs/DataRootsData.lean). All other bounds are exact rational checks.
-/
import Smale.Proofs.DataFacts
import Smale.Proofs.DataRootsData

namespace Smale.Exact

open Polynomial Complex ComplexConjugate

/-- A zero of `X² + pX + q` lies within `ε` of `r` when `2|r² + pr + q| ≤ ε|2r + p|`. -/
theorem quad_root_near (p q r : ℂ) (ε : ℝ) (hε : 0 ≤ ε) (h : 2 * ‖r ^ 2 + p * r + q‖ ≤ ε * ‖2 * r + p‖) :
    ∃ z₁ z₂ : ℂ, X ^ 2 + C p * X + C q = (X - C z₁) * (X - C z₂) ∧ z₁ + z₂ = -p ∧ ‖z₁ - r‖ ≤ ε := by
  obtain ⟨s, hs⟩ := IsAlgClosed.isSquare (p ^ 2 - 4 * q)
  have key : ∀ u v : ℂ, u + v = -p → u * v = q → ‖u - r‖ ≤ ‖v - r‖ →
      ∃ z₁ z₂ : ℂ, X ^ 2 + C p * X + C q = (X - C z₁) * (X - C z₂) ∧ z₁ + z₂ = -p ∧ ‖z₁ - r‖ ≤ ε := by
    intro u v hsum hprod hle
    have hp : p = -(u + v) := by rw [hsum]; ring
    refine ⟨u, v, ?_, hsum, ?_⟩
    · rw [hp, ← hprod]; simp only [map_neg, map_add, map_mul]; ring
    · by_contra hA'
      have hA : ε < ‖u - r‖ := not_le.mp hA'
      have hBpos : 0 < ‖v - r‖ := lt_of_le_of_lt hε (lt_of_lt_of_le hA hle)
      have hN : ‖r ^ 2 + p * r + q‖ = ‖u - r‖ * ‖v - r‖ := by
        rw [← norm_mul]; congr 1; rw [hp, ← hprod]; ring
      have hD : ‖2 * r + p‖ ≤ 2 * ‖v - r‖ := by
        have e : 2 * r + p = -((u - r) + (v - r)) := by rw [hp]; ring
        rw [e, norm_neg]
        linarith [norm_add_le (u - r) (v - r)]
      have h1 : ε * ‖v - r‖ < ‖u - r‖ * ‖v - r‖ := mul_lt_mul_of_pos_right hA hBpos
      nlinarith [mul_le_mul_of_nonneg_left hD hε]
  by_cases hcase : ‖(-p + s) / 2 - r‖ ≤ ‖(-p - s) / 2 - r‖
  · exact key _ _ (by ring) (by linear_combination hs / 4) hcase
  · exact key ((-p - s) / 2) ((-p + s) / 2) (by ring) (by linear_combination hs / 4) (le_of_lt (not_le.mp hcase))

theorem norm_le_of_nsq {a : GQ} {c : ℚ} (hc : 0 ≤ c) (h : nsq a ≤ c ^ 2) : ‖a.toC‖ ≤ c := by
  have h2 : ‖a.toC‖ ^ 2 ≤ (c : ℝ) ^ 2 := by rw [sq_norm_toC]; exact_mod_cast h
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  nlinarith [norm_nonneg a.toC]

theorem le_norm_of_nsq {a : GQ} {c : ℚ} (hc : 0 ≤ c) (h : c ^ 2 ≤ nsq a) : (c : ℝ) ≤ ‖a.toC‖ := by
  have h2 : (c : ℝ) ^ 2 ≤ ‖a.toC‖ ^ 2 := by rw [sq_norm_toC]; exact_mod_cast h
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  nlinarith [norm_nonneg a.toC]

theorem norm_lt_iff_nsq (a : GQ) {c : ℚ} (hc : 0 ≤ c) : ‖a.toC‖ < c ↔ nsq a < c ^ 2 := by
  constructor
  · intro h
    by_contra hn
    exact absurd h (not_lt.mpr (le_norm_of_nsq hc (not_lt.mp hn)))
  · intro h
    by_contra hn
    have h2 : (c : ℝ) ^ 2 ≤ ‖a.toC‖ ^ 2 := by
      have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
      nlinarith [not_lt.mp hn]
    rw [sq_norm_toC] at h2
    exact absurd (by exact_mod_cast h2 : c ^ 2 ≤ nsq a) (not_le.mpr h)

theorem re_im_near {z : ℂ} {c : GQ} {ε : ℝ} (h : ‖z - c.toC‖ ≤ ε) :
    (c.re : ℝ) - ε ≤ z.re ∧ z.re ≤ c.re + ε ∧ (c.im : ℝ) - ε ≤ z.im ∧ z.im ≤ c.im + ε := by
  have hre := abs_le.mp ((Complex.abs_re_le_norm _).trans h)
  have him := abs_le.mp ((Complex.abs_im_le_norm _).trans h)
  simp only [Complex.sub_re, Complex.sub_im, GQ.toC_re, GQ.toC_im] at hre him
  exact ⟨by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩

/-- `G(r)` and `G'(r) = 2r + g₁` as Gaussian rationals; the center `-g₁ - r` of the second zero. -/
def gAt (r : GQ) : GQ := GQ.add (GQ.add (GQ.mul r r) (GQ.mul g1GQ r)) g0GQ
def gDerAt (r : GQ) : GQ := GQ.add (GQ.mul (GQ.ofQ 2) r) g1GQ
def rG2 : GQ := GQ.neg (GQ.add g1GQ rG)

def epsG : ℚ := 1 / 10 ^ 30

theorem check_rG : 4 * nsq (gAt rG) ≤ epsG ^ 2 * nsq (gDerAt rG) := by decide +kernel

/-- The zeros of `G`: `z₁` within `10⁻³⁰` of `rG`, and `z₂` within `10⁻³⁰` of `rG2 = -g₁ - rG`. -/
theorem G_roots : ∃ z₁ z₂ : ℂ, Gpoly = (X - C z₁) * (X - C z₂) ∧ ‖z₁ - rG.toC‖ ≤ (epsG : ℝ) ∧
    ‖z₂ - rG2.toC‖ ≤ (epsG : ℝ) := by
  have hε : (0 : ℝ) ≤ (epsG : ℝ) := by norm_num [epsG]
  have hval : rG.toC ^ 2 + g1D * rG.toC + g0D = (gAt rG).toC := by
    rw [gAt, GQ.toC_add, GQ.toC_add, GQ.toC_mul, GQ.toC_mul, g0D_eq, g1D_eq]; ring
  have hder : 2 * rG.toC + g1D = (gDerAt rG).toC := by
    rw [gDerAt, GQ.toC_add, GQ.toC_mul, GQ.toC_ofQ, g1D_eq]; push_cast; ring
  have h : 2 * ‖rG.toC ^ 2 + g1D * rG.toC + g0D‖ ≤ (epsG : ℝ) * ‖2 * rG.toC + g1D‖ := by
    rw [hval, hder]
    have hq : ((4 * nsq (gAt rG) : ℚ) : ℝ) ≤ ((epsG ^ 2 * nsq (gDerAt rG) : ℚ) : ℝ) := by exact_mod_cast check_rG
    push_cast at hq
    have hsq : (2 * ‖(gAt rG).toC‖) ^ 2 ≤ ((epsG : ℝ) * ‖(gDerAt rG).toC‖) ^ 2 := by
      rw [mul_pow, mul_pow, sq_norm_toC, sq_norm_toC]; linarith
    nlinarith [norm_nonneg (gAt rG).toC, mul_nonneg hε (norm_nonneg (gDerAt rG).toC)]
  obtain ⟨z₁, z₂, hG, hsum, hz⟩ := quad_root_near g1D g0D rG.toC epsG hε h
  refine ⟨z₁, z₂, hG, hz, ?_⟩
  have e : z₂ - rG2.toC = -(z₁ - rG.toC) := by
    rw [rG2, GQ.toC_neg, GQ.toC_add, ← g1D_eq]; linear_combination hsum
  rw [e, norm_neg]; exact hz

theorem check_box :
    (1.00000688 : ℚ) ≤ rG.re - epsG ∧ rG.re + epsG < 1.00000689 ∧ -0.00152262 < rG.im - epsG ∧
      rG.im + epsG ≤ -0.00152261 ∧ -0.41009054 < rG2.re - epsG ∧ rG2.re + epsG ≤ -0.41009053 ∧
      1.04265219 ≤ rG2.im - epsG ∧ rG2.im + epsG < 1.0426522 := by
  decide +kernel

/-- `sec5_G_zeros`, proved. -/
theorem sec5_G_zeros_proved :
    ∃ z₁ z₂ : ℂ, Gpoly = (X - C z₁) * (X - C z₂) ∧
      1.00000688 ≤ z₁.re ∧ z₁.re < 1.00000689 ∧ -0.00152262 < z₁.im ∧ z₁.im ≤ -0.00152261 ∧
      -0.41009054 < z₂.re ∧ z₂.re ≤ -0.41009053 ∧ 1.04265219 ≤ z₂.im ∧ z₂.im < 1.0426522 := by
  obtain ⟨z₁, z₂, hG, h1, h2⟩ := G_roots
  obtain ⟨a1, a2, a3, a4⟩ := re_im_near h1
  obtain ⟨b1, b2, b3, b4⟩ := re_im_near h2
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := check_box
  have q1 : ((1.00000688 : ℚ) : ℝ) ≤ ((rG.re - epsG : ℚ) : ℝ) := by exact_mod_cast c1
  have q2 : ((rG.re + epsG : ℚ) : ℝ) < ((1.00000689 : ℚ) : ℝ) := by exact_mod_cast c2
  have q3 : ((-0.00152262 : ℚ) : ℝ) < ((rG.im - epsG : ℚ) : ℝ) := by exact_mod_cast c3
  have q4 : ((rG.im + epsG : ℚ) : ℝ) ≤ ((-0.00152261 : ℚ) : ℝ) := by exact_mod_cast c4
  have q5 : ((-0.41009054 : ℚ) : ℝ) < ((rG2.re - epsG : ℚ) : ℝ) := by exact_mod_cast c5
  have q6 : ((rG2.re + epsG : ℚ) : ℝ) ≤ ((-0.41009053 : ℚ) : ℝ) := by exact_mod_cast c6
  have q7 : ((1.04265219 : ℚ) : ℝ) ≤ ((rG2.im - epsG : ℚ) : ℝ) := by exact_mod_cast c7
  have q8 : ((rG2.im + epsG : ℚ) : ℝ) < ((1.0426522 : ℚ) : ℝ) := by exact_mod_cast c8
  push_cast at q1 q2 q3 q4 q5 q6 q7 q8
  exact ⟨z₁, z₂, hG, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-- The `ρ_j` stay at distance `≥ 8.05·10⁻⁶` from the circle; `|rG2| ≥ 1.1`; `|rG|` bounds. -/
theorem check_moduli :
    (∀ j : Fin 10, (1.00000805 : ℚ) ^ 2 ≤ nsq (rhoGQ.getD j GQ.zero) ∨ nsq (rhoGQ.getD j GQ.zero) ≤ (0.99999195 : ℚ) ^ 2)
      ∧ ((1.1 : ℚ) + epsG) ^ 2 ≤ nsq rG2 ∧ ((1.00000804 : ℚ) + epsG) ^ 2 ≤ nsq rG ∧
      nsq rG ≤ ((1.00000805 : ℚ) - 2 * epsG) ^ 2 := by
  decide +kernel

theorem rho_near_one_card : (Finset.univ.filter fun j : Fin 10 => ‖rho j - 1‖ < 0.0123).card = 4 := by
  have hc : (0 : ℚ) ≤ 0.0123 := by norm_num
  have e : ∀ j : Fin 10, ‖rho j - 1‖ < 0.0123 ↔
      nsq (GQ.add (rhoGQ.getD j GQ.zero) (GQ.neg one)) < (0.0123 : ℚ) ^ 2 := by
    intro j
    rw [← norm_lt_iff_nsq _ hc, GQ.toC_add, GQ.toC_neg, toC_one, ← rho_eq, ← sub_eq_add_neg]
    norm_num
  rw [Finset.filter_congr (fun j _ => e j)]
  decide +kernel

/-- `rem_5_2_exact`, proved. -/
theorem rem_5_2_exact_proved :
    (Finset.univ.filter fun j : Fin 10 => ‖rho j - 1‖ < 0.0123).card = 4 ∧
    ∃ z : ℂ, Gpoly.eval z = 0 ∧ 1.00000804 ≤ ‖z‖ ∧ ‖z‖ < 1.00000805 ∧
      ∀ w : ℂ, Vdata.eval w = 0 → |‖z‖ - 1| ≤ |‖w‖ - 1| := by
  refine ⟨rho_near_one_card, ?_⟩
  obtain ⟨z₁, z₂, hG, h1, h2⟩ := G_roots
  obtain ⟨mrho, m2, mr1, mr2⟩ := check_moduli
  have hε : (0 : ℝ) ≤ (epsG : ℝ) := by norm_num [epsG]
  have hr1 := le_norm_of_nsq (by norm_num [epsG]) mr1
  have hr2 := norm_le_of_nsq (by norm_num [epsG]) mr2
  have hz2 := le_norm_of_nsq (by norm_num [epsG]) m2
  push_cast at hr1 hr2 hz2
  have n1 : ‖z₁‖ ≥ ‖rG.toC‖ - epsG := by
    have := norm_sub_norm_le rG.toC z₁; rw [norm_sub_rev] at this; linarith
  have n2 : ‖z₁‖ ≤ ‖rG.toC‖ + epsG := by
    have := norm_sub_norm_le z₁ rG.toC; linarith
  have n3 : ‖z₂‖ ≥ ‖rG2.toC‖ - epsG := by
    have := norm_sub_norm_le rG2.toC z₂; rw [norm_sub_rev] at this; linarith
  have hz1lo : (1.00000804 : ℝ) ≤ ‖z₁‖ := by linarith
  have hz1hi : ‖z₁‖ < 1.00000805 := by
    have : (0 : ℝ) < epsG := by norm_num [epsG]
    linarith
  have hzabs : |‖z₁‖ - 1| < 0.00000805 := by rw [abs_lt]; constructor <;> linarith
  refine ⟨z₁, ?_, hz1lo, hz1hi, fun w hw => ?_⟩
  · rw [hG]; simp
  · rw [Vdata, eval_mul, eval_mul, eval_prod] at hw
    rcases mul_eq_zero.mp hw with hw | hw
    · rcases mul_eq_zero.mp hw with hw | hw
      · norm_num at hw
      · rw [hG] at hw
        simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hw
        rcases hw with hw | hw
        · rw [hw]
        · rw [hw]
          have : (1.1 : ℝ) - epsG ≤ ‖z₂‖ := by linarith
          have : (0 : ℝ) < epsG ∧ (epsG : ℝ) < 0.01 := by norm_num [epsG]
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ‖z₂‖ - 1)]; linarith [(abs_lt.mp hzabs).2]
    · obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hw
      simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
      rw [hj, rho_eq]
      rcases mrho j with hm | hm
      · have := le_norm_of_nsq (by norm_num) hm
        push_cast at this
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ‖(rhoGQ.getD j GQ.zero).toC‖ - 1)]; linarith [hzabs]
      · have := norm_le_of_nsq (by norm_num) hm
        push_cast at this
        rw [abs_of_nonpos (by linarith : ‖(rhoGQ.getD j GQ.zero).toC‖ - 1 ≤ 0)]
        linarith [(abs_lt.mp hzabs).2]

end Smale.Exact
