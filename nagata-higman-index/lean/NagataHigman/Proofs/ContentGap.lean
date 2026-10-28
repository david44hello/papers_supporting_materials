/- NagataHigman/Proofs/ContentGap.lean — content gaps: consecutive entries off a common row/column, removable corners.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib
import NagataHigman.Defs.Young
import NagataHigman.Proofs.Tableaux

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman

/-! ## Removable corners of a Young diagram -/

/-- No other cell lies weakly south-east of a removable corner `p`. -/
theorem eq_of_corner_le (μ : YoungDiagram) {p q : ℕ × ℕ} (h1 : (p.1 + 1, p.2) ∉ μ.cells)
    (h2 : (p.1, p.2 + 1) ∉ μ.cells) (hq : q ∈ μ.cells) (hle1 : p.1 ≤ q.1) (hle2 : p.2 ≤ q.2) : p = q := by
  rcases hle1.lt_or_eq with h | h
  · exact absurd (μ.up_left_mem (i2 := q.1) (j2 := q.2) (Nat.succ_le_of_lt h) hle2 hq) h1
  · rcases hle2.lt_or_eq with h' | h'
    · exact absurd (μ.up_left_mem (i2 := q.1) (j2 := q.2) h.le (Nat.succ_le_of_lt h') hq) h2
    · exact Prod.ext h h'

/-- Two distinct removable corners: one is strictly north-east of the other. -/
theorem corners_strict (μ : YoungDiagram) {p q : ℕ × ℕ} (hp : p ∈ μ.cells) (hq : q ∈ μ.cells)
    (h1 : (p.1 + 1, p.2) ∉ μ.cells) (h2 : (p.1, p.2 + 1) ∉ μ.cells)
    (h1' : (q.1 + 1, q.2) ∉ μ.cells) (h2' : (q.1, q.2 + 1) ∉ μ.cells) (hne : p ≠ q) :
    (p.1 < q.1 ∧ q.2 < p.2) ∨ (q.1 < p.1 ∧ p.2 < q.2) := by
  have hA := eq_of_corner_le μ h1 h2 hq
  have hB := eq_of_corner_le μ h1' h2' hp
  rcases lt_trichotomy p.1 q.1 with h | h | h
  · rcases lt_or_ge q.2 p.2 with h' | h'
    · exact Or.inl ⟨h, h'⟩
    · exact absurd (hA h.le h') hne
  · rcases le_total p.2 q.2 with h' | h'
    · exact absurd (hA h.le h') hne
    · exact absurd (hB h.ge h').symm hne
  · rcases lt_or_ge p.2 q.2 with h' | h'
    · exact Or.inr ⟨h, h'⟩
    · exact absurd (hB h.le h').symm hne

/-- Distinct removable corners have contents (column minus row) differing by at least `2`. -/
theorem corner_content_gap (μ : YoungDiagram) {p q : ℕ × ℕ} (hp : p ∈ μ.cells) (hq : q ∈ μ.cells)
    (h1 : (p.1 + 1, p.2) ∉ μ.cells) (h2 : (p.1, p.2 + 1) ∉ μ.cells)
    (h1' : (q.1 + 1, q.2) ∉ μ.cells) (h2' : (q.1, q.2 + 1) ∉ μ.cells) (hne : p ≠ q) :
    2 ≤ |((q.2 : ℤ) - q.1) - ((p.2 : ℤ) - p.1)| := by
  rw [le_abs]
  rcases corners_strict μ hp hq h1 h2 h1' h2' hne with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · right
    omega
  · left
    omega

variable {N : ℕ} {lam : Shape N}

/-! ## Consecutive entries -/

/-- The entry `k + 1` never sits strictly south-east of the entry `k`. -/
theorem not_southeast_of_succ (T : SYT lam) (k l : Fin N) (hkl : (l : ℕ) = k + 1)
    (h1 : (T.pos k).1 < (T.pos l).1) (h2 : (T.pos k).2 < (T.pos l).2) : False := by
  obtain ⟨m, hm, hml⟩ := exists_le_of_le T (k := l) (c := ((T.pos k).1, (T.pos l).2))
    (by dsimp only; omega) le_rfl
  have hne : m ≠ l := by
    rintro rfl
    rw [Prod.ext_iff] at hm
    dsimp only at hm
    omega
  obtain ⟨m', hm', hkm⟩ := exists_gt_of_ge T (k := k) (c := ((T.pos k).1, (T.pos l).2))
    (hm ▸ T.pos_mem m) le_rfl (by dsimp only; omega) (by rw [Ne, Prod.ext_iff]; dsimp only; omega)
  have hmm : m' = m := T.pos_injective (hm'.trans hm.symm)
  subst hmm
  have := Fin.lt_def.1 hkm
  have := Fin.lt_def.1 (lt_of_le_of_ne hml hne)
  omega

/-- If `k` and `k + 1` share neither a row nor a column, their contents differ by at least `2`. -/
theorem content_gap_two (T : SYT lam) (k l : Fin N) (hkl : (l : ℕ) = k + 1)
    (hrow : (T.pos k).1 ≠ (T.pos l).1) (hcol : (T.pos k).2 ≠ (T.pos l).2) :
    2 ≤ |T.content l - T.content k| := by
  unfold SYT.content
  rw [le_abs]
  rcases hrow.lt_or_gt with hr | hr <;> rcases hcol.lt_or_gt with hc | hc
  · exact (not_southeast_of_succ T k l hkl hr hc).elim
  · right
    omega
  · left
    omega
  · have := Fin.le_def.1 (T.pos_mono l k hr.le hc.le)
    omega

/-- If `k` and `k + 1` share neither a row nor a column, their contents do not differ by `±1`. -/
theorem content_gap_ne_one {N : ℕ} {lam : Shape N} (T : SYT lam) (k l : Fin N) (hkl : (l : ℕ) = k + 1)
    (hrow : (T.pos k).1 ≠ (T.pos l).1) (hcol : (T.pos k).2 ≠ (T.pos l).2) :
    T.content l - T.content k ≠ 1 ∧ T.content l - T.content k ≠ -1 := by
  have := le_abs.1 (content_gap_two T k l hkl hrow hcol)
  constructor <;> omega

/-! ## The largest entry is determined by its content -/

/-- The cell of the largest entry is determined by its content (it sits at a removable corner). -/
theorem pos_eq_of_content_top {N : ℕ} {lam : Shape N} (T T' : SYT lam) (top : Fin N)
    (htop : (top : ℕ) + 1 = N) (h : T.content top = T'.content top) : T.pos top = T'.pos top := by
  obtain ⟨h1, h2⟩ := top_corner T top htop
  obtain ⟨h1', h2'⟩ := top_corner T' top htop
  by_contra hne
  unfold SYT.content at h
  rcases corners_strict lam.diagram (T.pos_mem top) (T'.pos_mem top) h1 h2 h1' h2' hne with
    ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega

end NagataHigman.Proofs

end
