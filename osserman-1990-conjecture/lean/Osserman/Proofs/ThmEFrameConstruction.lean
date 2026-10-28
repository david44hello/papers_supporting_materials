/-
ThmEFrameConstruction.lean — the polynomial eigenframe in Theorem E, paper 013, lines 740–751.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.ThmEElementary
import Osserman.Proofs.ThmEFrames
import Osserman.Proofs.ThmESpectral
import Osserman.Cited.Nik2006

namespace Osserman.Proofs.ThmEFrameConstruction

open Osserman Matrix Osserman.Proofs.Curv Osserman.Proofs.Spectral
open Osserman.Proofs.ThmEElementary Osserman.Proofs.ThmEFrames Osserman.Proofs.ThmESpectral

noncomputable def subTensor {n : ℕ} (R B : CurvTensor n) (c : ℝ) : CurvTensor n where
  op := mkTri (fun u v w => R.op u v w - c • B.op u v w)
    (by intros; simp only [map_add, LinearMap.add_apply]; module)
    (by intros; simp only [map_smul, LinearMap.smul_apply]; module)
    (by intros; simp only [map_add, LinearMap.add_apply]; module)
    (by intros; simp only [map_smul, LinearMap.smul_apply]; module)
    (by intros; simp only [map_add, LinearMap.add_apply]; module)
    (by intros; simp only [map_smul, LinearMap.smul_apply]; module)
  antisymm := by
    intro u v w
    change R.op u v w - c • B.op u v w = -(R.op v u w - c • B.op v u w)
    rw [R.antisymm u v w, B.antisymm u v w]
    module
  skew := by
    intro u v w z
    change (R.op u v w - c • B.op u v w) ⬝ᵥ z = -((R.op u v z - c • B.op u v z) ⬝ᵥ w)
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [R.skew u v w z, B.skew u v w z]
    ring
  bianchi := by
    intro u v w
    change (R.op u v w - c • B.op u v w) + (R.op v w u - c • B.op v w u) +
      (R.op w u v - c • B.op w u v) = 0
    calc
      _ = (R.op u v w + R.op v w u + R.op w u v) - c • (B.op u v w + B.op v w u + B.op w u v) := by module
      _ = 0 := by rw [R.bianchi, B.bianchi, smul_zero, sub_self]

lemma subTensor_op {n : ℕ} (R B : CurvTensor n) (c : ℝ) (u v w : Vec n) :
    (subTensor R B c).op u v w = R.op u v w - c • B.op u v w := rfl

theorem thm_E_frame_proved (R : CurvTensor 16) (m : Fin 3 → ℕ) (hm : IsThmEPattern m)
    (ev : Fin 3 → ℝ) (hev : Function.Injective ev)
    (hpat : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i, R.redMult x (ev i) = m i) :
    ∃ J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ, ThmEFrame R m ev J := by
  obtain ⟨round, round_op⟩ := sec1_R1_curv_proved 16
  let R0 := subTensor R round (ev 0)
  have h0 (u v w : Vec 16) : R0.op u v w = R.op u v w - ev 0 • R1fun u v w := by
    rw [subTensor_op, round_op]
  have ROsserman := pattern_osserman R m hm ev hev hpat
  have R0Osserman : R0.IsOsserman := by
    intro x y hx hy μ
    have first := thm_E_shift_proved R R0 (ev 0) h0 x hx (μ + ev 0)
    have second := thm_E_shift_proved R R0 (ev 0) h0 y hy (μ + ev 0)
    simp only [add_sub_cancel_right] at first second
    rw [first, second]
    exact ROsserman x y hx hy _
  let ev0 : Fin 3 → ℝ := fun i => ev i - ev 0
  have injective : Function.Injective ev0 := by
    intro i j equal
    apply hev
    dsimp only [ev0] at equal
    linarith
  have positive (i : Fin 3) : 0 < m i := by
    rcases hm with rfl | rfl | rfl | rfl <;> fin_cases i <;> norm_num
  have total : ∑ i, m i = 15 := by rcases hm with rfl | rfl | rfl | rfl <;> norm_num [Fin.sum_univ_succ]
  have shifted (x : Vec 16) (hx : x ⬝ᵥ x = 1) (i : Fin 3) : R0.redMult x (ev0 i) = m i := by
    change R0.redMult x (ev i - ev 0) = m i
    rw [thm_E_shift_proved R R0 (ev 0) h0 x hx (ev i), hpat x hx i]
  have zero : ∃ j, ev0 j = 0 := ⟨0, sub_self _⟩
  have tau : ev0 2 ≠ 0 := sub_ne_zero.mpr (hev.ne (by decide))
  have smallest := (thm_E_smallest_proved m hm).1
  obtain ⟨d, E, odd, bound, homogeneous, data⟩ :=
    Osserman.Cited.nik2006_lemma_3_1 R0 R0Osserman ev0 injective m positive total shifted zero 2 tau smallest
  have linear_fields (a : Fin (m 2)) : ∃ J : Matrix (Fin 16) (Fin 16) ℝ,
      ∀ x : Vec 16, evalField (E a) x = J *ᵥ x :=
    thm_E_linear_fields_proved (E a) d odd bound (homogeneous a)
  choose J hJ using linear_fields
  have orthogonal (x : Vec 16) (hx : x ⬝ᵥ x = 1) (a b : Fin (m 2)) :
      (J a *ᵥ x) ⬝ᵥ (J b *ᵥ x) = if a = b then 1 else 0 := by
    simpa only [hJ] using (data x hx).1 a b
  have perpendicular (x : Vec 16) (hx : x ⬝ᵥ x = 1) (a : Fin (m 2)) : x ⬝ᵥ (J a *ᵥ x) = 0 := by
    have member := ((data x hx).2.1 a).2
    change x ⬝ᵥ evalField (E a) x = 0 at member
    rwa [hJ] at member
  refine ⟨J, hm, hev, hpat, (thm_E_frame_clifford_proved J orthogonal perpendicular).1, ?_⟩
  intro x hx a
  have member : J a *ᵥ x ∈ Module.End.eigenspace (R0.jacobiMap x) (ev 2 - ev 0) ⊓ perp x := by
    simpa only [hJ, ev0] using (data x hx).2.1 a
  have spaces := thm_E_shift_eigenspaces_proved R R0 (ev 0) h0 x (ev 2)
  rw [hx, mul_one] at spaces
  rw [spaces] at member
  exact member.1

end Osserman.Proofs.ThmEFrameConstruction

