/-
Cereceda/LB/Moves.lean — Lemmas 4.2 (lem:h1), 4.3 (lem:flat), 4.7 (lem:flat4) of the paper (short version,
Section 4) in this project's encoding (Cereceda/Defs/LowerBound.lean), and the height tracking along walks of R_4 used by
Propositions 4.1 and 4.6.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route: the encoding-free cores of Cereceda/LB/PathCore.lean (namespace Cereceda.PathAux) applied to the residues
`pcol c i` of the path colours. In a plain proper colouring a path vertex never has the colour 3 (it is joined to an
apex on 3), so two path colours differ exactly when their residues mod 3 differ.
-/
import Cereceda.Defs.LowerBound
import Cereceda.LB.PathCore

namespace Cereceda.MovesAux

open Finset

variable {n k : ℕ}

/-- The residue mod 3 of the colour of the path vertex at position `i` (`0` off the path). -/
def pcol (c : Fin n ⊕ Fin k → Fin 4) (i : ℕ) : ZMod 3 :=
  if hi : i < n then (((c (.inl ⟨i, hi⟩)).val : ℕ) : ZMod 3) else 0

theorem pcol_of_lt (c : Fin n ⊕ Fin k → Fin 4) {i : ℕ} (hi : i < n) :
    pcol c i = (((c (.inl ⟨i, hi⟩)).val : ℕ) : ZMod 3) := by
  simp [pcol, hi]

/-- A height in this project's sense is a height in the sense of `PathAux.StepHeight`. -/
theorem stepHeight_of (c : Fin n ⊕ Fin k → Fin 4) (h : ℕ → ℤ) (hh : IsPathHeight c h) :
    PathAux.StepHeight n (pcol c) h := by
  intro i hi
  obtain ⟨hs, hm⟩ := hh i hi
  rw [pcol_of_lt c hi, pcol_of_lt c (by omega : i < n)]
  rcases hs with e | e
  · left
    refine ⟨by linarith, ?_⟩
    rw [e] at hm
    push_cast at hm
    linear_combination -hm
  · right
    refine ⟨by linarith, ?_⟩
    rw [e] at hm
    push_cast at hm
    linear_combination -hm

/-- Conversely, a `PathAux.StepHeight` of the residues is a height in this project's sense. -/
theorem isPathHeight_of (c : Fin n ⊕ Fin k → Fin 4) (h : ℕ → ℤ) (hs : PathAux.StepHeight n (pcol c) h) :
    IsPathHeight c h := by
  intro i hi
  rcases hs i hi with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [pcol_of_lt c hi, pcol_of_lt c (by omega : i < n)] at e2
    refine ⟨Or.inl (by linarith), ?_⟩
    rw [show h (i + 1) - h i = 1 by linarith, e2]
    push_cast
    ring
  · rw [pcol_of_lt c hi, pcol_of_lt c (by omega : i < n)] at e2
    refine ⟨Or.inr (by linarith), ?_⟩
    rw [show h (i + 1) - h i = -1 by linarith, e2]
    push_cast
    ring

/-- In a proper plain colouring a path vertex does not have the colour `3` (it is joined to its apex, on `3`). -/
theorem path_ne_three {f : Fin n → Fin k} {c : Fin n ⊕ Fin k → Fin 4} (hc : IsProperFn (pathApex n k f) c)
    (hp : IsPlain c) (i : Fin n) : c (.inl i) ≠ 3 := by
  have := hc (.inl i) (.inr (f i)) rfl
  rwa [hp] at this

/-- Two colours other than `3` differ exactly when their residues mod 3 differ. -/
theorem res_ne : ∀ x y : Fin 4, x ≠ 3 → y ≠ 3 → x ≠ y → ((x.val : ℕ) : ZMod 3) ≠ ((y.val : ℕ) : ZMod 3) := by
  decide

/-- The path neighbour `inl ⟨j, _⟩` of `inl i` (`j = i ± 1`) is adjacent to it. -/
theorem adj_path {f : Fin n → Fin k} (i : Fin n) (j : ℕ) (hj : j < n) (hij : i.val + 1 = j ∨ j + 1 = i.val) :
    (pathApex n k f).Adj (.inl i) (.inl ⟨j, hj⟩) := hij

end Cereceda.MovesAux

namespace Cereceda

open Finset MovesAux

set_option linter.unusedVariables false in
/-- **Lemma 4.2 (lem:h1)** (v3.90 l. 598-600), for every path-with-apices graph: a move of a path vertex between two
plain colourings changes one value of a height function by exactly `2` and keeps the others.
(`hpc'` is part of the statement, as in the paper; the proof does not need it.) -/
theorem lem_4_2_proved (n k : ℕ) (f : Fin n → Fin k) (c c' : Fin n ⊕ Fin k → Fin 4)
    (hc : IsProperFn (pathApex n k f) c) (hpc : IsPlain c) (hpc' : IsPlain c') (i : Fin n)
    (hmove : LegalMove (pathApex n k f) (fun _ => univ) c (.inl i, c' (.inl i)))
    (hrest : ∀ w, w ≠ .inl i → c' w = c w) (h : ℕ → ℤ) (hh : IsPathHeight c h) :
    ∃ ε : ℤ, (ε = 2 ∨ ε = -2) ∧ IsPathHeight c' (Function.update h i.val (h i.val + ε)) := by
  obtain ⟨hne, -, hnb⟩ := hmove
  have h3 : c' (.inl i) ≠ 3 := by
    have := hnb (.inr (f i)) rfl
    rw [hpc] at this
    exact this.symm
  have hsame : ∀ j, j ≠ i.val → pcol c' j = pcol c j := by
    intro j hj
    unfold pcol
    split_ifs with hjn
    · rw [hrest _ (by simpa [Fin.ext_iff] using hj)]
    · rfl
  have hne' : pcol c' i.val ≠ pcol c i.val := by
    rw [pcol_of_lt c' i.isLt, pcol_of_lt c i.isLt]
    exact res_ne _ _ h3 (path_ne_three hc hpc i) hne
  have hl : 0 < i.val → pcol c' i.val ≠ pcol c (i.val - 1) := by
    intro hi0
    rw [pcol_of_lt c' i.isLt, pcol_of_lt c (by omega : i.val - 1 < n)]
    exact res_ne _ _ h3 (path_ne_three hc hpc _)
      (hnb _ (adj_path i (i.val - 1) (by omega) (Or.inr (by omega)))).symm
  have hr : i.val + 1 < n → pcol c' i.val ≠ pcol c (i.val + 1) := by
    intro hin
    rw [pcol_of_lt c' i.isLt, pcol_of_lt c hin]
    exact res_ne _ _ h3 (path_ne_three hc hpc _)
      (hnb _ (adj_path i (i.val + 1) hin (Or.inl rfl))).symm
  obtain ⟨h', hs', hoff, habs⟩ :=
    PathAux.move_height (stepHeight_of c h hh) (pcol c') i.val i.isLt hsame hne' hl hr
  refine ⟨h' i.val - h i.val, ?_, ?_⟩
  · rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 2)).mp habs with e | e
    · exact Or.inl e
    · exact Or.inr e
  · have hupd : Function.update h i.val (h i.val + (h' i.val - h i.val)) = h' := by
      funext j
      by_cases hj : j = i.val
      · subst hj
        simp
      · rw [Function.update_of_ne hj]
        exact (hoff j hj).symm
    rw [hupd]
    exact isPathHeight_of c' h' hs'

/-- **Lemma 4.3 (lem:flat)** (v3.90 l. 610-611): if a plain colouring of `H_n` allows a move of `a` or of `b`, then
`|W| ≤ 4`. (For `a` the proof gives `3`.) -/
theorem lem_4_3_proved (n : ℕ) (c : Fin n ⊕ Fin 2 → Fin 4) (hc : IsProperFn (Hgraph n) c) (hp : IsPlain c)
    (hmove : ∃ j y, LegalMove (Hgraph n) (fun _ => univ) c (.inr j, y)) (h : ℕ → ℤ)
    (hh : IsPathHeight c h) : |h (n - 1) - h 0| ≤ 4 := by
  obtain ⟨j, y, hy, -, hnb⟩ := hmove
  have hy3 : y ≠ 3 := by
    have := hp j
    simp only at hy
    rwa [this] at hy
  have hs := stepHeight_of c h hh
  have hcls : ∀ i, i < n → i % 2 = j.val → pcol c i ≠ ((y.val : ℕ) : ZMod 3) := by
    intro i hi hij
    rw [pcol_of_lt c hi]
    have hadj : (Hgraph n).Adj (.inr j) (.inl ⟨i, hi⟩) := Fin.ext hij
    exact res_ne _ _ (path_ne_three hc hp _) hy3 (hnb _ hadj)
  have hj : j.val = 0 ∨ j.val = 1 := by omega
  rcases hj with hj | hj
  · have := PathAux.flat_even hs _ (fun i hi hpar => hcls i hi (by omega))
    linarith
  · exact PathAux.flat_odd hs _ (fun i hi hpar => hcls i hi (by omega))

/-- **Lemma 4.7 (lem:flat4)** (v3.90 l. 689-690): if a plain colouring of `J_n` allows a move of some `a_j`, then
`|W| ≤ 3(n-1)/4 + 7`. -/
theorem lem_4_7_proved (n : ℕ) (c : Fin n ⊕ Fin 4 → Fin 4) (hc : IsProperFn (Jgraph n) c) (hp : IsPlain c)
    (hmove : ∃ j y, LegalMove (Jgraph n) (fun _ => univ) c (.inr j, y)) (h : ℕ → ℤ)
    (hh : IsPathHeight c h) : (|h (n - 1) - h 0| : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4 + 7 := by
  obtain ⟨j, y, hy, -, hnb⟩ := hmove
  have hy3 : y ≠ 3 := by
    have := hp j
    simp only at hy
    rwa [this] at hy
  have hs := stepHeight_of c h hh
  have hcls : ∀ i, i < n → i % 4 = (j.val + 3) % 4 → pcol c i ≠ ((y.val : ℕ) : ZMod 3) := by
    intro i hi hij
    rw [pcol_of_lt c hi]
    have hadj : (Jgraph n).Adj (.inr j) (.inl ⟨i, hi⟩) :=
      Fin.ext (show (i + 1) % 4 = j.val by have := j.isLt; omega)
    exact res_ne _ _ (path_ne_three hc hp _) hy3 (hnb _ hadj)
  have := PathAux.flat4 hs _ ((j.val + 3) % 4) (by omega) hcls
  push_cast at this
  exact this

end Cereceda
