/-
HibiLi/Proofs/Fig2B.lean — Figure 2 caption (paper v2.10 l. 665-667), strict reading: `L` is affine on no neighbourhood in
`B` of a point of `B` with `α = β`, and `U` on none of a point with `γ = η`. The row `fig2_not_affine_near_B` is in
Statements.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Proofs.Cov200Claims

noncomputable section

namespace HibiLi.Proofs.Fig2B

open HibiLi HibiLi.Proofs HibiLi.Proofs.Cov200 HibiLi.Example21 HibiLi.Example21.CenterGeometry

/-- A point whose four coordinates are each within `ε` of those of `v` lies in `ball(v, ε)`. -/
theorem dist_lt_of_abs {v w : Coord → ℝ} {ε : ℝ} (hε : 0 < ε) (h : ∀ c, |w c - v c| < ε) : dist w v < ε :=
  (dist_pi_lt_iff hε).2 fun c => by rw [Real.dist_eq]; exact h c

/-- `L` is not affine on `B ∩ ball(v, ε)` if this set holds `p = (x₀, x₁, x₂, x₃)` with `x₁ < x₀` (so `α > β`), its mirror
`q = (x₁, x₀, x₂, x₃)` (`α < β`) and their midpoint `m`: `L(m) = (x₀ + x₁)/2 < x₀ = (L(p) + L(q))/2`. -/
theorem L_split {v : Coord → ℝ} (hab : v CenterSwitch.canonical.pa = v CenterSwitch.canonical.pb) {ε : ℝ}
    (hε : 0 < ε) (x0 x1 x2 x3 : ℝ) (h1 : 0 ≤ x1) (h10 : x1 < x0) (h02 : x0 ≤ x2) (h03 : x0 ≤ x3)
    (h2 : x2 ≤ 1) (h3 : x3 ≤ 1) (hc0 : |x0 - v CenterSwitch.canonical.pa| < ε)
    (hc1 : |x1 - v CenterSwitch.canonical.pa| < ε) (hc2 : |x2 - v CenterSwitch.canonical.pg| < ε)
    (hc3 : |x3 - v CenterSwitch.canonical.ph| < ε) :
    ¬ AffineOn center.L {u | u ∈ center.B ∧ dist u v < ε} := by
  rintro ⟨g, hg⟩
  obtain ⟨hc0l, hc0r⟩ := abs_lt.mp hc0
  obtain ⟨hc1l, hc1r⟩ := abs_lt.mp hc1
  obtain ⟨hc2l, hc2r⟩ := abs_lt.mp hc2
  obtain ⟨hc3l, hc3r⟩ := abs_lt.mp hc3
  obtain ⟨pa, pb, pg, ph⟩ := coords_symm ![x0, x1, x2, x3]
  obtain ⟨qa, qb, qg, qh⟩ := coords_symm ![x1, x0, x2, x3]
  obtain ⟨ma, mb, mg, mh⟩ := coords_symm ![(x0 + x1) / 2, (x0 + x1) / 2, x2, x3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at pa pb pg ph qa qb qg qh ma mb mg mh
  set p := canonicalEquiv.symm ![x0, x1, x2, x3]
  set q := canonicalEquiv.symm ![x1, x0, x2, x3]
  set m := canonicalEquiv.symm ![(x0 + x1) / 2, (x0 + x1) / 2, x2, x3]
  have hpB : p ∈ center.B := by
    rw [mem_B_iff, pa, pb, pg, ph, max_le_iff, le_min_iff, le_min_iff]
    refine ⟨?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hqB : q ∈ center.B := by
    rw [mem_B_iff, qa, qb, qg, qh, max_le_iff, le_min_iff, le_min_iff]
    refine ⟨?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hmB : m ∈ center.B := by
    rw [mem_B_iff, ma, mb, mg, mh, max_self, le_min_iff]
    refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hpd : dist p v < ε := dist_lt_of_abs hε fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl <;> (rw [abs_lt]; constructor <;> linarith)
  have hqd : dist q v < ε := dist_lt_of_abs hε fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl <;> (rw [abs_lt]; constructor <;> linarith)
  have hmd : dist m v < ε := dist_lt_of_abs hε fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl <;> (rw [abs_lt]; constructor <;> linarith)
  have hp := hg p ⟨hpB, hpd⟩
  have hq := hg q ⟨hqB, hqd⟩
  have hm := hg m ⟨hmB, hmd⟩
  rw [L_eq hpB, pa, pb, max_eq_left h10.le] at hp
  rw [L_eq hqB, qa, qb, max_eq_right h10.le] at hq
  rw [L_eq hmB, ma, mb, max_self] at hm
  have hmid := affine_mid g p q m fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl <;> linarith
  linarith

/-- `U` is not affine on `B ∩ ball(v, ε)` if this set holds `p = (x₀, x₁, x₂, x₃)` with `x₃ < x₂` (so `γ > η`), its mirror
`q = (x₀, x₁, x₃, x₂)` (`γ < η`) and their midpoint `m`: `U(m) = (x₂ + x₃)/2 > x₃ = (U(p) + U(q))/2`. -/
theorem U_split {v : Coord → ℝ} (hgh : v CenterSwitch.canonical.pg = v CenterSwitch.canonical.ph) {ε : ℝ}
    (hε : 0 < ε) (x0 x1 x2 x3 : ℝ) (h0 : 0 ≤ x0) (h1 : 0 ≤ x1) (h03 : x0 ≤ x3) (h13 : x1 ≤ x3) (h32 : x3 < x2)
    (h2 : x2 ≤ 1) (hc0 : |x0 - v CenterSwitch.canonical.pa| < ε) (hc1 : |x1 - v CenterSwitch.canonical.pb| < ε)
    (hc2 : |x2 - v CenterSwitch.canonical.pg| < ε) (hc3 : |x3 - v CenterSwitch.canonical.pg| < ε) :
    ¬ AffineOn center.U {u | u ∈ center.B ∧ dist u v < ε} := by
  rintro ⟨g, hg⟩
  obtain ⟨hc0l, hc0r⟩ := abs_lt.mp hc0
  obtain ⟨hc1l, hc1r⟩ := abs_lt.mp hc1
  obtain ⟨hc2l, hc2r⟩ := abs_lt.mp hc2
  obtain ⟨hc3l, hc3r⟩ := abs_lt.mp hc3
  obtain ⟨pa, pb, pg, ph⟩ := coords_symm ![x0, x1, x2, x3]
  obtain ⟨qa, qb, qg, qh⟩ := coords_symm ![x0, x1, x3, x2]
  obtain ⟨ma, mb, mg, mh⟩ := coords_symm ![x0, x1, (x2 + x3) / 2, (x2 + x3) / 2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at pa pb pg ph qa qb qg qh ma mb mg mh
  set p := canonicalEquiv.symm ![x0, x1, x2, x3]
  set q := canonicalEquiv.symm ![x0, x1, x3, x2]
  set m := canonicalEquiv.symm ![x0, x1, (x2 + x3) / 2, (x2 + x3) / 2]
  have hpB : p ∈ center.B := by
    rw [mem_B_iff, pa, pb, pg, ph, max_le_iff, le_min_iff, le_min_iff]
    refine ⟨?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hqB : q ∈ center.B := by
    rw [mem_B_iff, qa, qb, qg, qh, max_le_iff, le_min_iff, le_min_iff]
    refine ⟨?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hmB : m ∈ center.B := by
    rw [mem_B_iff, ma, mb, mg, mh, max_le_iff, le_min_iff, le_min_iff]
    refine ⟨?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hpd : dist p v < ε := dist_lt_of_abs hε fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl <;> (rw [abs_lt]; constructor <;> linarith)
  have hqd : dist q v < ε := dist_lt_of_abs hε fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl <;> (rw [abs_lt]; constructor <;> linarith)
  have hmd : dist m v < ε := dist_lt_of_abs hε fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl <;> (rw [abs_lt]; constructor <;> linarith)
  have hp := hg p ⟨hpB, hpd⟩
  have hq := hg q ⟨hqB, hqd⟩
  have hm := hg m ⟨hmB, hmd⟩
  rw [U_eq hpB, pg, ph, min_eq_right h32.le] at hp
  rw [U_eq hqB, qg, qh, min_eq_left h32.le] at hq
  rw [U_eq hmB, mg, mh, min_self] at hm
  have hmid := affine_mid g p q m fun c => by
    rcases coord_cases c with rfl | rfl | rfl | rfl <;> linarith
  linarith

/-- Figure 2, `L`: at every point `v` of `B` with `α = β`, `L` is affine on no `B ∩ ball(v, ε)`. If `α > 0`, lower `β`:
`p = (α, α - t, γ, η)`. If `α = β = 0`, raise `α`: `p = (t, 0, max γ t, max η t)`. -/
theorem L_not_affine_near_B_proved (v : Coord → ℝ) (hv : v ∈ center.B)
    (hξ : v CenterSwitch.canonical.pa = v CenterSwitch.canonical.pb) {ε : ℝ} (hε : 0 < ε) :
    ¬ AffineOn center.L {u | u ∈ center.B ∧ dist u v < ε} := by
  rw [mem_B_iff, max_le_iff, le_min_iff, le_min_iff] at hv
  obtain ⟨ha0, -, ⟨⟨hag, hah⟩, -, -⟩, hg1, hh1⟩ := hv
  by_cases ha : 0 < v CenterSwitch.canonical.pa
  · obtain ⟨t, ht0, hta, htε⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ v CenterSwitch.canonical.pa ∧ t < ε :=
      ⟨min (v CenterSwitch.canonical.pa) (ε / 2), lt_min ha (by linarith), min_le_left _ _,
        lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
    refine L_split hξ hε (v CenterSwitch.canonical.pa) (v CenterSwitch.canonical.pa - t)
      (v CenterSwitch.canonical.pg) (v CenterSwitch.canonical.ph) (by linarith) (by linarith) hag hah hg1 hh1
      ?_ ?_ ?_ ?_ <;> (rw [abs_lt]; constructor <;> linarith)
  · rw [not_lt] at ha
    obtain ⟨t, ht0, ht1, htε⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t < ε :=
      ⟨min 1 (ε / 2), lt_min one_pos (by linarith), min_le_left _ _,
        lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
    have hg2 : max (v CenterSwitch.canonical.pg) t ≤ v CenterSwitch.canonical.pg + t :=
      max_le (by linarith) (by linarith)
    have hh2 : max (v CenterSwitch.canonical.ph) t ≤ v CenterSwitch.canonical.ph + t :=
      max_le (by linarith) (by linarith)
    have hg3 := le_max_left (v CenterSwitch.canonical.pg) t
    have hh3 := le_max_left (v CenterSwitch.canonical.ph) t
    refine L_split hξ hε t 0 (max (v CenterSwitch.canonical.pg) t) (max (v CenterSwitch.canonical.ph) t) le_rfl
      ht0 (le_max_right _ _) (le_max_right _ _) (max_le hg1 ht1) (max_le hh1 ht1)
      ?_ ?_ ?_ ?_ <;> (rw [abs_lt]; constructor <;> linarith)

/-- Figure 2, `U`: at every point `v` of `B` with `γ = η`, `U` is affine on no `B ∩ ball(v, ε)`. If `η < 1`, raise `γ`:
`p = (α, β, η + t, η)`. If `γ = η = 1`, lower `η`: `p = (min α (1 - t), min β (1 - t), 1, 1 - t)`. -/
theorem U_not_affine_near_B_proved (v : Coord → ℝ) (hv : v ∈ center.B)
    (hω : v CenterSwitch.canonical.pg = v CenterSwitch.canonical.ph) {ε : ℝ} (hε : 0 < ε) :
    ¬ AffineOn center.U {u | u ∈ center.B ∧ dist u v < ε} := by
  rw [mem_B_iff, max_le_iff, le_min_iff, le_min_iff] at hv
  obtain ⟨ha0, hb0, ⟨⟨-, hah⟩, -, hbh⟩, -, hh1⟩ := hv
  by_cases hc : v CenterSwitch.canonical.ph < 1
  · obtain ⟨t, ht0, ht1, htε⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 - v CenterSwitch.canonical.ph ∧ t < ε :=
      ⟨min (1 - v CenterSwitch.canonical.ph) (ε / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
        lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
    refine U_split hω hε (v CenterSwitch.canonical.pa) (v CenterSwitch.canonical.pb)
      (v CenterSwitch.canonical.ph + t) (v CenterSwitch.canonical.ph) ha0 hb0 hah hbh (by linarith) (by linarith)
      ?_ ?_ ?_ ?_ <;> (rw [abs_lt]; constructor <;> linarith)
  · rw [not_lt] at hc
    obtain ⟨t, ht0, ht1, htε⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t < ε :=
      ⟨min 1 (ε / 2), lt_min one_pos (by linarith), min_le_left _ _,
        lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
    have ha2 : v CenterSwitch.canonical.pa - t ≤ min (v CenterSwitch.canonical.pa) (1 - t) :=
      le_min (by linarith) (by linarith)
    have hb2 : v CenterSwitch.canonical.pb - t ≤ min (v CenterSwitch.canonical.pb) (1 - t) :=
      le_min (by linarith) (by linarith)
    have ha3 := min_le_left (v CenterSwitch.canonical.pa) (1 - t)
    have hb3 := min_le_left (v CenterSwitch.canonical.pb) (1 - t)
    refine U_split hω hε (min (v CenterSwitch.canonical.pa) (1 - t)) (min (v CenterSwitch.canonical.pb) (1 - t))
      1 (1 - t) (le_min ha0 (by linarith)) (le_min hb0 (by linarith)) (min_le_right _ _) (min_le_right _ _)
      (by linarith) le_rfl ?_ ?_ ?_ ?_ <;> (rw [abs_lt]; constructor <;> linarith)

end HibiLi.Proofs.Fig2B

end
