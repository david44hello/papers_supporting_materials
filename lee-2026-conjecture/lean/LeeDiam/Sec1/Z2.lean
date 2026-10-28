/-
LeeDiam/Sec1/Z2.lean — the picture of the band B_k of paper 004 in the plane: a_{i+1} ↦ (i+1, -(i+1)),
b_{i+1} ↦ (i+1, -i), c_{i+1} ↦ (i+2, -i) is an order embedding of B_k into ℤ × ℤ (product order), and the rows lie on
the lines x + y = 0, 1, 2. From the explicit order of B_k (LeeDiam/Sec4/BandOrder.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Band
import LeeDiam.Sec4.BandOrder

namespace LeeDiam

/-- The point of `ℤ²` of an element of `B_k` (column `i` 0-based, row `0, 1, 2` for `a, b, c`). -/
def S1.bandZ2 {k : ℕ} (x : Band k) : ℤ × ℤ :=
  ((x.1.val : ℤ) + 1 + (if x.2.val = 2 then 1 else 0), -(x.1.val : ℤ) - (if x.2.val = 0 then 1 else 0))

/-- The picture is an order embedding: `f x ≤ f y` (both coordinates) iff `x ≤ y` in `B_k`. -/
theorem S1.bandZ2_le_iff {k : ℕ} (x y : Band k) : S1.bandZ2 x ≤ S1.bandZ2 y ↔ x ≤ y := by
  rw [S4.le_iff_bandLe]
  unfold S4.bandLe S1.bandZ2
  rw [S4.band_ext_iff, Prod.mk_le_mk]
  have hx := x.2.isLt
  have hy := y.2.isLt
  split_ifs <;> omega

/-- The band in the plane (Figure / tex of Section 1): an order embedding `B_k ↪o ℤ × ℤ` with the stated points. -/
theorem S1.band_Z2 (k : ℕ) :
    ∃ f : Band k ↪o ℤ × ℤ, ∀ i : Fin k,
      f (Band.a i) = ((i : ℤ) + 1, -((i : ℤ) + 1)) ∧ f (Band.b i) = ((i : ℤ) + 1, -(i : ℤ)) ∧
      f (Band.c i) = ((i : ℤ) + 2, -(i : ℤ)) ∧
      (f (Band.a i)).1 + (f (Band.a i)).2 = 0 ∧ (f (Band.b i)).1 + (f (Band.b i)).2 = 1 ∧
      (f (Band.c i)).1 + (f (Band.c i)).2 = 2 := by
  refine ⟨OrderEmbedding.ofMapLEIff S1.bandZ2 S1.bandZ2_le_iff, fun i => ?_⟩
  simp only [OrderEmbedding.coe_ofMapLEIff, S1.bandZ2, Band.a, Band.b, Band.c, Prod.ext_iff]
  norm_num
  all_goals omega

end LeeDiam
