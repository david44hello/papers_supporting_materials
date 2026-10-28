/-
NagataHigman/Defs/Young.lean — partitions, Young diagrams, standard tableaux, contents, diagonal hooks.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Cells are `(row, column)` pairs, both 0-indexed (paper: 1-indexed); Mathlib's `YoungDiagram` convention.
Tableau entries are `0, …, N-1` (paper: `1, …, N`).
-/
import Mathlib

noncomputable section

namespace NagataHigman

open Finset

/-- A shape `λ ⊢ N`: a partition of `N` (Mathlib's `Nat.Partition`, a multiset of positive parts). -/
abbrev Shape (N : ℕ) : Type := Nat.Partition N

namespace Shape

variable {N : ℕ}

/-- The Young diagram of `λ`: row `i` has the `i`-th largest part as its length. -/
def diagram (lam : Shape N) : YoungDiagram := YoungDiagram.ofPartition lam

/-- `ℓ(λ)`: the number of rows (paper line 249). -/
def numRows (lam : Shape N) : ℕ := Multiset.card lam.parts

/-- `λ_1`: the length of the first row, i.e. the largest part (paper line 272). -/
def firstRow (lam : Shape N) : ℕ := lam.parts.sup

/-- `λ ⊆ (n^n)`: the diagram fits in the `n × n` box (paper line 273). -/
def InBox (n : ℕ) (lam : Shape N) : Prop := lam.numRows ≤ n ∧ lam.firstRow ≤ n

open scoped Classical in
/-- `h(λ)`: the diagonal hook lengths `h_{11}, h_{22}, …` (paper lines 429-430), as a multiset. The diagonal cell
`(i, i)` has arm `rowLen i - i - 1` and leg `colLen i - i - 1`, so hook length `rowLen i + colLen i - 2 i - 1`. -/
def diagonalHooks (lam : Shape N) : Multiset ℕ :=
  ((range N).filter (fun i => (i, i) ∈ lam.diagram.cells)).val.map
    (fun i => lam.diagram.rowLen i + lam.diagram.colLen i - 2 * i - 1)

end Shape

/-- A standard Young tableau of shape `λ ⊢ N`, filled with `0, …, N-1`: `pos k` is the cell that holds `k`.
The cells are filled bijectively (injective into the `N` cells), and entries increase along every row and down
every column (`pos_mono`: a cell weakly north-west of another holds the smaller entry). -/
structure SYT {N : ℕ} (lam : Shape N) where
  pos : Fin N → ℕ × ℕ
  pos_injective : Function.Injective pos
  pos_mem : ∀ k, pos k ∈ lam.diagram.cells
  pos_mono : ∀ k l, (pos k).1 ≤ (pos l).1 → (pos k).2 ≤ (pos l).2 → k ≤ l

/-- The content `c_T(k)` = column minus row of the cell holding `k` (paper line 406). -/
def SYT.content {N : ℕ} {lam : Shape N} (T : SYT lam) (k : Fin N) : ℤ :=
  ((T.pos k).2 : ℤ) - ((T.pos k).1 : ℤ)

end NagataHigman

end
