/-
LeeDiam/Defs/PnSets.lean — the named sets, maps and neighbour types of Section 6 of paper 004 (short v1.50,
sec_reverse.tex l. 31-216): the targets A, B, U; M_A, M_B, Y_A, Y_B, W_A, W_B, W, T, Q, Λ_A, Λ_B; the connectors
u^-, u^+; the involution σ; mixed pairs and Iso(I, J); N[X]; Z_A, Z_B; the types (D), (E), (L), (H) and their primed
versions; "attached".
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

TRUST SURFACE. Indices are 0-based (`Fin n`): the paper's `a_i` is `PnElem.a (i - 1)`. Each definition quotes the
paper's wording in its docstring. `Γ_h` and the component `Γ` of Lemma 6.5 are not functions here: the statements
quantify over components (`IsComponent`, Defs/Walks.lean) and also assert that the component exists.
-/
import LeeDiam.Defs.Pn
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Vertices
import LeeDiam.Defs.Walks

namespace LeeDiam

section General

variable {P : Type} [Fintype P] [PartialOrder P]

/-- `N[X]` (l. 192): the set of antichains that are equal or adjacent to the antichain `X` in the graph of `C(P)`, i.e.
at distance at most one. -/
def nbhdC (X : Set P) : Set (Set P) :=
  {Y | ∃ (hX : IsAntichainSet X) (hY : IsAntichainSet Y), dC X Y hX hY ≤ 1}

end General

namespace PnSets

open PnElem

variable (n : ℕ)

/-- `A = {a_1, …, a_n}` (Definition 6.1). -/
def tgtA : Set (Pn n) := {x | ∃ i, x = a i}

/-- `B = {b_1, …, b_n}` (Definition 6.1). -/
def tgtB : Set (Pn n) := {x | ∃ j, x = b j}

/-- `U = A ∪ B`, the targets (Definition 6.1). -/
def tgts : Set (Pn n) := tgtA n ∪ tgtB n

/-- `M_A = {m_E}` (Definition 6.1). -/
def pairMinA : Set (Pn n) := {x | ∃ E, x = m E}

/-- `M_B = {m'_E}` (Definition 6.1). -/
def pairMinB : Set (Pn n) := {x | ∃ E, x = m' E}

/-- `Y_A = {y_1, …, y_n}` (Definition 6.1). -/
def lowA : Set (Pn n) := {x | ∃ i, x = y i}

/-- `Y_B = {y'_1, …, y'_n}` (Definition 6.1). -/
def lowB : Set (Pn n) := {x | ∃ j, x = y' j}

/-- `W_A = {w_1, …, w_n}` (Definition 6.1). -/
def upA : Set (Pn n) := {x | ∃ i, x = w i}

/-- `W_B = {w'_1, …, w'_n}` (Definition 6.1). -/
def upB : Set (Pn n) := {x | ∃ j, x = w' j}

/-- `W = W_A ∪ W_B` (Definition 6.1). -/
def ups : Set (Pn n) := upA n ∪ upB n

/-- `T = {t_ij}` (Definition 6.1). -/
def tops : Set (Pn n) := {x | ∃ i j, x = t i j}

/-- `Q = M_A ∪ M_B ∪ Y_A ∪ Y_B` (l. 87). -/
def qSet : Set (Pn n) := pairMinA n ∪ pairMinB n ∪ lowA n ∪ lowB n

/-- `Λ_A = M_A ∪ Y_A ∪ A` (l. 87). -/
def lamA : Set (Pn n) := pairMinA n ∪ lowA n ∪ tgtA n

/-- `Λ_B = M_B ∪ Y_B ∪ B` (l. 87). -/
def lamB : Set (Pn n) := pairMinB n ∪ lowB n ∪ tgtB n

/-- The lower connector `u^-` of a target `u` (l. 89): `a_i^- = y_i`, `b_j^- = y'_j` (other elements: unused, `x`). -/
def lo : Pn n → Pn n
  | a i => y i
  | b j => y' j
  | x => x

/-- The upper connector `u^+` of a target `u` (l. 89): `a_i^+ = w_i`, `b_j^+ = w'_j` (other elements: unused, `x`). -/
def up : Pn n → Pn n
  | a i => w i
  | b j => w' j
  | x => x

/-- The involution `σ` (l. 91): exchanges `a_i, b_i`; `m_E, m'_E`; `y_i, y'_i`; `w_i, w'_i`; `t_ij, t_ji`; fixes `h`. -/
def sigma : Pn n → Pn n
  | a i => b i
  | b j => a j
  | m E => m' E
  | m' E => m E
  | y i => y' i
  | y' j => y j
  | h => h
  | w i => w' i
  | w' j => w j
  | t i j => t j i

/-- A mixed pair (l. 126): ideals `I, J` with `h ∈ I` and `h ∉ J`. -/
def IsMixed (I J : Set (Pn n)) : Prop := IsIdeal I ∧ IsIdeal J ∧ (h : Pn n) ∈ I ∧ (h : Pn n) ∉ J

/-- `Iso(I, J)` (l. 126): the targets `u ∈ I \ J` with `u^- ∈ J` and `u^+ ∉ I`. -/
def isoSet (I J : Set (Pn n)) : Set (Pn n) := {u | u ∈ tgts n ∧ u ∈ I ∧ u ∉ J ∧ lo n u ∈ J ∧ up n u ∉ I}

/-- `Z_A` (l. 194): the elements outside `A` that are incomparable to every target of `A`. -/
def zA : Set (Pn n) := {z | z ∉ tgtA n ∧ ∀ u ∈ tgtA n, ¬ Comp z u}

/-- `Z_B` (l. 194): the elements outside `B` that are incomparable to every target of `B`. -/
def zB : Set (Pn n) := {z | z ∉ tgtB n ∧ ∀ u ∈ tgtB n, ¬ Comp z u}

/-- Type (D) (Lemma 6.8): `X = A \ {a_i}` for some `i`. -/
def IsTypeD (X : Set (Pn n)) : Prop := ∃ i, X = tgtA n \ {a i}

/-- Type (E) (Lemma 6.8): `X = A ∪ {z}` for some `z ∈ Z_A`. -/
def IsTypeE (X : Set (Pn n)) : Prop := ∃ z ∈ zA n, X = insert z (tgtA n)

/-- Type (L) (Lemma 6.8): `X = (A \ R) ∪ S` with `∅ ≠ R ⊆ A`, `∅ ≠ S ⊆ M_A ∪ Y_A`, every element of `S` below some
element of `R` and below no element of `A \ R`. -/
def IsTypeL (X : Set (Pn n)) : Prop :=
  ∃ R S : Set (Pn n), R.Nonempty ∧ R ⊆ tgtA n ∧ S.Nonempty ∧ S ⊆ pairMinA n ∪ lowA n ∧
    (∀ s ∈ S, (∃ r ∈ R, s < r) ∧ ∀ r ∈ tgtA n \ R, ¬ s < r) ∧ X = (tgtA n \ R) ∪ S

/-- Type (H) (Lemma 6.8): `X = (A \ {a_i}) ∪ S` with `S = {w_i}` or `∅ ≠ S ⊆ {t_i1, …, t_in}`. -/
def IsTypeH (X : Set (Pn n)) : Prop :=
  ∃ (i : Fin n) (S : Set (Pn n)), (S = {w i} ∨ (S.Nonempty ∧ S ⊆ {x | ∃ j, x = t i j})) ∧ X = (tgtA n \ {a i}) ∪ S

/-- Type (D') (l. 216): `Y = B \ {b_j}`. -/
def IsTypeD' (Y : Set (Pn n)) : Prop := ∃ j, Y = tgtB n \ {b j}

/-- Type (E') (l. 216): `Y = B ∪ {z}` with `z ∈ Z_B`. -/
def IsTypeE' (Y : Set (Pn n)) : Prop := ∃ z ∈ zB n, Y = insert z (tgtB n)

/-- Type (L') (l. 216): `Y = (B \ R) ∪ S` with `∅ ≠ R ⊆ B`, `∅ ≠ S ⊆ M_B ∪ Y_B`, every element of `S` below some
element of `R` and below no element of `B \ R`. -/
def IsTypeL' (Y : Set (Pn n)) : Prop :=
  ∃ R S : Set (Pn n), R.Nonempty ∧ R ⊆ tgtB n ∧ S.Nonempty ∧ S ⊆ pairMinB n ∪ lowB n ∧
    (∀ s ∈ S, (∃ r ∈ R, s < r) ∧ ∀ r ∈ tgtB n \ R, ¬ s < r) ∧ Y = (tgtB n \ R) ∪ S

/-- Type (H') (l. 216): `Y = (B \ {b_j}) ∪ S` with `S = {w'_j}` or `∅ ≠ S ⊆ {t_1j, …, t_nj}`. -/
def IsTypeH' (Y : Set (Pn n)) : Prop :=
  ∃ (j : Fin n) (S : Set (Pn n)), (S = {w' j} ∨ (S.Nonempty ∧ S ⊆ {x | ∃ i, x = t i j})) ∧ Y = (tgtB n \ {b j}) ∪ S

/-- `z` is attached to the target `u` (l. 225): `z = u` or `z` is comparable to `u`. -/
def Attached {n : ℕ} (z u : Pn n) : Prop := z = u ∨ Comp z u

end PnSets

end LeeDiam
