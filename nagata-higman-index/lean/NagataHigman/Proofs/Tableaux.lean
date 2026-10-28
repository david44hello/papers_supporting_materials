/- NagataHigman/Proofs/Tableaux.lean — standard-tableau combinatorics: ext, (T1), corners, column/row tableaux.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib
import NagataHigman.Defs.Young

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman

/-! ## T2: consecutive entries have different contents (stated first, with the exact paper type) -/

/-- The cell `pos k` is a cell; every cell weakly north-west of it holds an entry `≤ k`. -/
theorem exists_pos_eq {N : ℕ} {lam : Shape N} (T : SYT lam) {c : ℕ × ℕ}
    (hc : c ∈ lam.diagram.cells) : ∃ m, T.pos m = c := by
  classical
  have hsub : Finset.univ.image T.pos ⊆ lam.diagram.cells := by
    intro x hx
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hx
    exact T.pos_mem m
  have hcard : lam.diagram.cells.card ≤ (Finset.univ.image T.pos).card := by
    rw [Finset.card_image_of_injective _ T.pos_injective, Finset.card_univ, Fintype.card_fin]
    exact (YoungDiagram.card_ofPartition lam).le
  rw [← Finset.eq_of_subset_of_card_le hsub hcard] at hc
  obtain ⟨m, -, hm⟩ := Finset.mem_image.1 hc
  exact ⟨m, hm⟩

/-- A cell weakly north-west of the cell of `k` holds an entry `≤ k`. -/
theorem exists_le_of_le {N : ℕ} {lam : Shape N} (T : SYT lam) {k : Fin N} {c : ℕ × ℕ}
    (h1 : c.1 ≤ (T.pos k).1) (h2 : c.2 ≤ (T.pos k).2) : ∃ m, T.pos m = c ∧ m ≤ k := by
  obtain ⟨m, hm⟩ := exists_pos_eq T (lam.diagram.up_left_mem h1 h2 (T.pos_mem k))
  exact ⟨m, hm, T.pos_mono m k (hm ▸ h1) (hm ▸ h2)⟩

/-- A cell weakly south-east of (and different from) the cell of `k` holds an entry `> k`. -/
theorem exists_gt_of_ge {N : ℕ} {lam : Shape N} (T : SYT lam) {k : Fin N} {c : ℕ × ℕ}
    (hc : c ∈ lam.diagram.cells) (h1 : (T.pos k).1 ≤ c.1) (h2 : (T.pos k).2 ≤ c.2) (hne : T.pos k ≠ c) :
    ∃ m, T.pos m = c ∧ k < m := by
  obtain ⟨m, hm⟩ := exists_pos_eq T hc
  refine ⟨m, hm, lt_of_le_of_ne (T.pos_mono k m (hm ▸ h1) (hm ▸ h2)) ?_⟩
  rintro rfl
  exact hne hm

/-- **(T1)**: consecutive entries never have equal content. -/
theorem J_consecutive (N : ℕ) (lam : Shape N) (T : SYT lam) (k l : Fin N) (hkl : (l : ℕ) = k + 1) :
    T.content k ≠ T.content l := by
  intro hc
  unfold SYT.content at hc
  rcases le_or_gt (T.pos l).1 (T.pos k).1 with h | h
  · have := Fin.le_def.1 (T.pos_mono l k h (by omega))
    omega
  · obtain ⟨m, hm, hml⟩ := exists_le_of_le T (k := l) (c := ((T.pos k).1 + 1, (T.pos k).2))
      (by dsimp only; omega) (by dsimp only; omega)
    have hne : m ≠ l := by
      rintro rfl
      rw [Prod.ext_iff] at hm
      dsimp only at hm
      omega
    obtain ⟨m', hm', hkm⟩ := exists_gt_of_ge T (k := k) (c := ((T.pos k).1 + 1, (T.pos k).2))
      (hm ▸ T.pos_mem m)
      (by dsimp only; omega) le_rfl (by rw [Ne, Prod.ext_iff]; dsimp only; omega)
    have hmm : m' = m := T.pos_injective (hm'.trans hm.symm)
    subst hmm
    have := Fin.lt_def.1 hkm
    have := Fin.lt_def.1 (lt_of_le_of_ne hml hne)
    omega

variable {N : ℕ} {lam : Shape N}

/-! ## T1: extensionality -/

theorem syt_ext {T T' : SYT lam} (h : T.pos = T'.pos) : T = T' := by
  cases T
  cases T'
  cases h
  rfl

private theorem pos_eq_aux {T T' : SYT lam} (k : Fin N) (hlt : ∀ m < k, T.pos m = T'.pos m)
    (h1 : (T.pos k).1 ≤ (T'.pos k).1) (h2 : (T.pos k).2 ≤ (T'.pos k).2) : T.pos k = T'.pos k := by
  obtain ⟨m, hm, hmk⟩ := exists_le_of_le T' h1 h2
  rcases hmk.lt_or_eq with hmk | rfl
  · exact absurd (T.pos_injective ((hlt m hmk).trans hm)) (ne_of_lt hmk)
  · exact hm.symm

/-- The content vector determines the tableau. -/
theorem syt_eq_of_content_eq {T T' : SYT lam} (h : ∀ k, T.content k = T'.content k) : T = T' := by
  apply syt_ext
  funext k
  induction k using WellFoundedLT.induction with
  | _ k ih =>
    have hc := h k
    unfold SYT.content at hc
    rcases le_total (T.pos k).1 (T'.pos k).1 with h1 | h1
    · exact pos_eq_aux k ih h1 (by omega)
    · exact (pos_eq_aux (T := T') (T' := T) k (fun m hm => (ih m hm).symm) h1 (by omega)).symm

/-! ## Shape facts -/

theorem mem_cells_iff {i j : ℕ} :
    (i, j) ∈ lam.diagram.cells ↔
      ∃ h : i < (lam.parts.sort (· ≥ ·)).length, j < (lam.parts.sort (· ≥ ·))[i] :=
  YoungDiagram.mem_cellsOfRowLens

theorem mem_cells_of_sort_eq {w : List ℕ} (hw : lam.parts.sort (· ≥ ·) = w) {i j : ℕ} :
    (i, j) ∈ lam.diagram.cells ↔ ∃ h : i < w.length, j < w[i] := by
  subst hw
  exact mem_cells_iff

theorem lt_numRows_of_mem {i j : ℕ} (h : (i, j) ∈ lam.diagram.cells) : i < lam.numRows := by
  obtain ⟨hi, -⟩ := mem_cells_iff.1 h
  rwa [Multiset.length_sort] at hi

theorem mem_col0 {j : ℕ} (hj : j < lam.numRows) : (j, 0) ∈ lam.diagram.cells := by
  have hj' : j < (lam.parts.sort (· ≥ ·)).length := by rwa [Multiset.length_sort]
  exact mem_cells_iff.2 ⟨hj', lam.parts_pos ((Multiset.mem_sort (· ≥ ·)).1 (List.getElem_mem hj'))⟩

theorem lt_firstRow_of_mem {j : ℕ} (h : (0, j) ∈ lam.diagram.cells) : j < lam.firstRow := by
  obtain ⟨h0, hj⟩ := mem_cells_iff.1 h
  exact lt_of_lt_of_le hj (Multiset.le_sup ((Multiset.mem_sort (· ≥ ·)).1 (List.getElem_mem h0)))

theorem mem_row0 {j : ℕ} (hj : j < lam.firstRow) : (0, j) ∈ lam.diagram.cells := by
  obtain ⟨p, hp, hjp⟩ : ∃ p ∈ lam.parts, j < p := by
    by_contra hcon
    push Not at hcon
    exact absurd (Multiset.sup_le.2 hcon) (not_le.2 hj)
  obtain ⟨i, hi, hip⟩ := List.getElem_of_mem ((Multiset.mem_sort (r := (· ≥ ·))).2 hp)
  exact lam.diagram.up_left_mem (Nat.zero_le i) le_rfl (mem_cells_iff.2 ⟨hi, hip ▸ hjp⟩)

/-! ## T3: every shape has a standard tableau; T6: column and row tableaux -/

section KeyTableau

variable (lam) (key : ℕ × ℕ ≃ ℕ ×ₗ ℕ)

/-- The cells, mapped by `key` into the lexicographic order. -/
def keyCells : Finset (ℕ ×ₗ ℕ) := lam.diagram.cells.map key.toEmbedding

theorem card_keyCells : (keyCells lam key).card = N := by
  rw [keyCells, Finset.card_map]
  exact YoungDiagram.card_ofPartition lam

/-- The `key`-increasing enumeration of the cells. -/
def keyEnum : Fin N ↪o ℕ ×ₗ ℕ := (keyCells lam key).orderEmbOfFin (card_keyCells lam key)

theorem keyEnum_mem (k : Fin N) : keyEnum lam key k ∈ keyCells lam key :=
  Finset.orderEmbOfFin_mem _ _ k

theorem exists_keyEnum_eq {x : ℕ ×ₗ ℕ} (hx : x ∈ keyCells lam key) : ∃ i, keyEnum lam key i = x := by
  have : x ∈ Set.range (keyEnum lam key) := by
    rw [keyEnum, Finset.range_orderEmbOfFin]
    exact hx
  exact this

/-- The tableau that fills the cells in increasing `key` order. -/
def sytOfKey (hmono : ∀ a b : ℕ × ℕ, a.1 ≤ b.1 → a.2 ≤ b.2 → key a ≤ key b) : SYT lam where
  pos k := key.symm (keyEnum lam key k)
  pos_injective a b h := (keyEnum lam key).injective (key.symm.injective h)
  pos_mem k := by
    obtain ⟨c, hc, he⟩ := Finset.mem_map.1 (keyEnum_mem lam key k)
    rw [← he]
    simpa using hc
  pos_mono k l h1 h2 := by
    have h := hmono _ _ h1 h2
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact (keyEnum lam key).le_iff_le.1 h

theorem card_filter_lt_keyEnum (m : Fin N) :
    ((keyCells lam key).filter (· < keyEnum lam key m)).card = m := by
  have : (keyCells lam key).filter (· < keyEnum lam key m) =
      (Finset.Iio m).map (keyEnum lam key).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨i, rfl⟩ := exists_keyEnum_eq lam key hx
      exact ⟨i, (keyEnum lam key).lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨keyEnum_mem lam key i, (keyEnum lam key).lt_iff_lt.2 hi⟩
  rw [this, Finset.card_map, Fin.card_Iio]

theorem keyEnum_eq_of_card {x : ℕ ×ₗ ℕ} (hx : x ∈ keyCells lam key) (k : Fin N)
    (hk : ((keyCells lam key).filter (· < x)).card = k) : keyEnum lam key k = x := by
  obtain ⟨i, rfl⟩ := exists_keyEnum_eq lam key hx
  rw [card_filter_lt_keyEnum] at hk
  rw [Fin.ext hk]

/-- If `key` sends an initial segment of cells to `(0, 0), …, (0, n)`, the enumeration starts there. -/
theorem keyEnum_initial (n : ℕ) (hseg : ∀ j ≤ n, toLex (0, j) ∈ keyCells lam key) (k : Fin N)
    (hk : (k : ℕ) ≤ n) : keyEnum lam key k = toLex (0, (k : ℕ)) := by
  apply keyEnum_eq_of_card lam key (hseg k hk)
  have : (keyCells lam key).filter (· < toLex (0, (k : ℕ))) =
      (Finset.range k).map ⟨fun j => toLex (0, j), fun a b h => by simpa using h⟩ := by
    ext x
    obtain ⟨⟨a, b⟩, rfl⟩ : ∃ p : ℕ × ℕ, toLex p = x := ⟨ofLex x, toLex_ofLex x⟩
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_range, Prod.Lex.toLex_lt_toLex]
    constructor
    · rintro ⟨-, hlt⟩
      refine ⟨b, by omega, ?_⟩
      have ha : a = 0 := by omega
      subst ha
      rfl
    · rintro ⟨j, hj, he⟩
      have he' : ((0 : ℕ), j) = (a, b) := toLex.injective he
      simp only [Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      exact ⟨hseg _ (by omega), Or.inr ⟨rfl, hj⟩⟩
  rw [this, Finset.card_map, Finset.card_range]

end KeyTableau

/-- Column-major key: `(i, j) ↦ (j, i)` in lex order. -/
def colKey : ℕ × ℕ ≃ ℕ ×ₗ ℕ := (Equiv.prodComm ℕ ℕ).trans toLex

theorem rowKey_mono (a b : ℕ × ℕ) (h1 : a.1 ≤ b.1) (h2 : a.2 ≤ b.2) :
    (toLex a : ℕ ×ₗ ℕ) ≤ toLex b :=
  Prod.Lex.toLex_mono ⟨h1, h2⟩

theorem colKey_mono (a b : ℕ × ℕ) (h1 : a.1 ≤ b.1) (h2 : a.2 ≤ b.2) : colKey a ≤ colKey b :=
  Prod.Lex.toLex_mono (show (a.2, a.1) ≤ (b.2, b.1) from ⟨h2, h1⟩)

/-- **T3**: every shape has a standard Young tableau (fill row by row). -/
theorem syt_nonempty (lam : Shape N) : Nonempty (SYT lam) :=
  ⟨sytOfKey lam toLex rowKey_mono⟩

/-- **T6** (column): if `λ` has at least `n + 1` rows, some tableau has `0, …, n` down the first column. -/
theorem exists_col_tableau (lam : Shape N) (n : ℕ) (hn : n + 1 ≤ lam.numRows) :
    ∃ T : SYT lam, ∀ k : Fin N, (k : ℕ) ≤ n → T.pos k = ((k : ℕ), 0) := by
  refine ⟨sytOfKey lam colKey colKey_mono, fun k hk => ?_⟩
  have hseg : ∀ j ≤ n, toLex (0, j) ∈ keyCells lam colKey :=
    fun j hj => Finset.mem_map.2 ⟨(j, 0), mem_col0 (by omega), rfl⟩
  change colKey.symm (keyEnum lam colKey k) = _
  rw [keyEnum_initial lam colKey n hseg k hk]
  exact (Equiv.symm_apply_eq _).2 rfl

/-- **T6** (row): if `λ_1 ≥ n + 1`, some tableau has `0, …, n` along the first row. -/
theorem exists_row_tableau (lam : Shape N) (n : ℕ) (hn : n + 1 ≤ lam.firstRow) :
    ∃ T : SYT lam, ∀ k : Fin N, (k : ℕ) ≤ n → T.pos k = (0, (k : ℕ)) := by
  refine ⟨sytOfKey lam toLex rowKey_mono, fun k hk => ?_⟩
  have hseg : ∀ j ≤ n, toLex (0, j) ∈ keyCells lam toLex :=
    fun j hj => Finset.mem_map.2 ⟨(0, j), mem_row0 (by omega), rfl⟩
  change toLex.symm (keyEnum lam toLex k) = _
  rw [keyEnum_initial lam toLex n hseg k hk]
  exact (Equiv.symm_apply_eq _).2 rfl

/-! ## T4, T5: the largest entries of rectangles and of `ν` -/

/-- If `c` is a cell weakly south-east of every cell, the largest entry sits at `c`. -/
theorem pos_top_of_max (T : SYT lam) (top : Fin N) (htop : (top : ℕ) + 1 = N) {c : ℕ × ℕ}
    (hc : c ∈ lam.diagram.cells) (hmax : ∀ d ∈ lam.diagram.cells, d.1 ≤ c.1 ∧ d.2 ≤ c.2) :
    T.pos top = c := by
  obtain ⟨m, hm⟩ := exists_pos_eq T hc
  have h1 := hmax _ (T.pos_mem top)
  have htm : top ≤ m := T.pos_mono top m (hm ▸ h1.1) (hm ▸ h1.2)
  have hmt : m ≤ top := Fin.le_def.2 (by have := m.isLt; omega)
  rw [← hm, le_antisymm hmt htm]

/-- The largest entry sits at a corner: no cell below it, no cell to its right. -/
theorem top_corner (T : SYT lam) (top : Fin N) (htop : (top : ℕ) + 1 = N) :
    ((T.pos top).1 + 1, (T.pos top).2) ∉ lam.diagram.cells ∧
      ((T.pos top).1, (T.pos top).2 + 1) ∉ lam.diagram.cells := by
  have hbig : ∀ m : Fin N, ¬ top < m := fun m h => by
    have := Fin.lt_def.1 h
    have := m.isLt
    omega
  constructor
  · intro hc
    obtain ⟨m, -, hm⟩ := exists_gt_of_ge T hc (Nat.le_succ _) le_rfl
      (by rw [Ne, Prod.ext_iff]; dsimp only; omega)
    exact hbig m hm
  · intro hc
    obtain ⟨m, -, hm⟩ := exists_gt_of_ge T hc le_rfl (Nat.le_succ _)
      (by rw [Ne, Prod.ext_iff]; dsimp only; omega)
    exact hbig m hm

/-- The second largest entry sits at a corner of the shape with the largest entry removed. -/
theorem second_corner (T : SYT lam) (top k : Fin N) (htop : (top : ℕ) + 1 = N) (hk : (k : ℕ) + 2 = N) :
    T.pos k ≠ T.pos top ∧
      (((T.pos k).1 + 1, (T.pos k).2) ∈ lam.diagram.cells →
        ((T.pos k).1 + 1, (T.pos k).2) = T.pos top) ∧
      (((T.pos k).1, (T.pos k).2 + 1) ∈ lam.diagram.cells →
        ((T.pos k).1, (T.pos k).2 + 1) = T.pos top) := by
  have hnext : ∀ m : Fin N, k < m → m = top := fun m h => by
    have := Fin.lt_def.1 h
    have := m.isLt
    exact Fin.ext (by omega)
  refine ⟨fun h => ?_, fun hc => ?_, fun hc => ?_⟩
  · have := congrArg Fin.val (T.pos_injective h)
    omega
  · obtain ⟨m, hm, hkm⟩ := exists_gt_of_ge T hc (Nat.le_succ _) le_rfl
      (by rw [Ne, Prod.ext_iff]; dsimp only; omega)
    rw [← hm, hnext m hkm]
  · obtain ⟨m, hm, hkm⟩ := exists_gt_of_ge T hc le_rfl (Nat.le_succ _)
      (by rw [Ne, Prod.ext_iff]; dsimp only; omega)
    rw [← hm, hnext m hkm]

theorem sort_replicate_ge (r c : ℕ) : (Multiset.replicate r c).sort (· ≥ ·) = List.replicate r c := by
  rw [← Multiset.coe_replicate, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (List.pairwise_replicate.2 (Or.inr le_rfl))

theorem rect_mem {r c : ℕ} (hlam : lam.parts = Multiset.replicate r c) (i j : ℕ) :
    (i, j) ∈ lam.diagram.cells ↔ i < r ∧ j < c := by
  rw [mem_cells_of_sort_eq (by rw [hlam, sort_replicate_ge])]
  simp

/-- **T4** (rectangle): in a tableau of shape `(c^r)` the largest entry is at the corner `(r-1, c-1)`. -/
theorem rect_pos_top (lam : Shape N) (r c : ℕ) (hr : 1 ≤ r) (hc : 1 ≤ c)
    (hlam : lam.parts = Multiset.replicate r c) (T : SYT lam) (top : Fin N) (htop : (top : ℕ) + 1 = N) :
    T.pos top = (r - 1, c - 1) := by
  refine pos_top_of_max T top htop ((rect_mem hlam _ _).2 ⟨by omega, by omega⟩) fun d hd => ?_
  have := (rect_mem hlam d.1 d.2).1 hd
  dsimp only
  omega

/-- **T4** (square): in a tableau of shape `(n^n)` the largest entry is at the corner `(n-1, n-1)`. -/
theorem square_pos_top (n : ℕ) (hn : 1 ≤ n) (lam : Shape (n ^ 2)) (hlam : lam.parts = Multiset.replicate n n)
    (T : SYT lam) (top : Fin (n ^ 2)) (htop : (top : ℕ) + 1 = n ^ 2) : T.pos top = (n - 1, n - 1) :=
  rect_pos_top lam n n hn hn hlam T top htop

theorem sort_nu (n : ℕ) :
    (Multiset.replicate (n - 1) n + {n - 1}).sort (· ≥ ·) = List.replicate (n - 1) n ++ [n - 1] := by
  have : Multiset.replicate (n - 1) n + {n - 1} = ((List.replicate (n - 1) n ++ [n - 1] : List ℕ) :
      Multiset ℕ) := by
    rw [← Multiset.coe_add, Multiset.coe_replicate, Multiset.coe_singleton]
  rw [this, Multiset.coe_sort]
  apply List.mergeSort_eq_self
  rw [List.pairwise_append]
  refine ⟨List.pairwise_replicate.2 (Or.inr le_rfl), List.pairwise_singleton _ _, ?_⟩
  intro a ha b hb
  rw [List.mem_replicate] at ha
  rw [List.mem_singleton] at hb
  omega

theorem nu_mem (m : ℕ) (hlam : lam.parts = Multiset.replicate (m + 1) (m + 2) + {m + 1}) (i j : ℕ) :
    (i, j) ∈ lam.diagram.cells ↔ (i < m + 1 ∧ j < m + 2) ∨ (i = m + 1 ∧ j < m + 1) := by
  rw [mem_cells_of_sort_eq (w := List.replicate (m + 1) (m + 2) ++ [m + 1])
    (by rw [hlam]; exact sort_nu (m + 2))]
  simp only [List.length_append, List.length_replicate, List.length_singleton, List.getElem_append,
    List.getElem_replicate, List.getElem_singleton]
  constructor
  · rintro ⟨h, hj⟩
    split_ifs at hj with hi
    · exact Or.inl ⟨hi, hj⟩
    · exact Or.inr ⟨by omega, hj⟩
  · rintro (⟨hi, hj⟩ | ⟨rfl, hj⟩)
    · exact ⟨by omega, by simpa [hi] using hj⟩
    · exact ⟨by omega, by simpa using hj⟩

/-- Core of **T5**, for the explicit cell set of `ν = ((m+2)^{m+1}, m+1)`. -/
theorem nu_pos_top_core (m : ℕ)
    (hmem : ∀ i j, (i, j) ∈ lam.diagram.cells ↔ (i < m + 1 ∧ j < m + 2) ∨ (i = m + 1 ∧ j < m + 1))
    (T : SYT lam) (top : Fin N) (htop : (top : ℕ) + 1 = N) :
    T.pos top = (m, m + 1) ∨ T.pos top = (m + 1, m) := by
  obtain ⟨h1, h2⟩ := top_corner T top htop
  have h0 := T.pos_mem top
  obtain ⟨⟨a, b⟩, hp⟩ : ∃ p, T.pos top = p := ⟨_, rfl⟩
  rw [hp] at h0 h1 h2 ⊢
  dsimp only at h1 h2
  rw [hmem] at h0 h1 h2
  simp only [Prod.mk.injEq]
  omega

/-- The arithmetic behind **T5**: the corner `(a, b)` of the largest entry and the cell `(c, d)` of the
second largest entry of `ν = ((m+2)^{m+1}, m+1)`. -/
private theorem nu_arith (m a b c d : ℕ) (hp : (a = m ∧ b = m + 1) ∨ (a = m + 1 ∧ b = m))
    (hq : (c < m + 1 ∧ d < m + 2) ∨ (c = m + 1 ∧ d < m + 1)) (hne : ¬ (c = a ∧ d = b))
    (hdown : (c + 1 < m + 1 ∧ d < m + 2) ∨ (c + 1 = m + 1 ∧ d < m + 1) → c + 1 = a ∧ d = b)
    (hright : (c < m + 1 ∧ d + 1 < m + 2) ∨ (c = m + 1 ∧ d + 1 < m + 1) → c = a ∧ d + 1 = b) :
    ((d : ℤ) - c = -1 ∧ (b : ℤ) - a = 1) ∨ ((d : ℤ) - c = 2 ∧ (b : ℤ) - a = 1) ∨
      ((d : ℤ) - c = 1 ∧ (b : ℤ) - a = -1) ∨ ((d : ℤ) - c = -2 ∧ (b : ℤ) - a = -1) := by
  rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> subst a b
  · rcases hq with ⟨hc, hd⟩ | ⟨rfl, hd⟩
    · by_cases hd' : d + 1 < m + 2
      · have h1 := hright (Or.inl ⟨hc, hd'⟩)
        have h2 := hdown (Or.inr ⟨by omega, by omega⟩)
        omega
      · have h1 := hdown (Or.inl ⟨by omega, hd⟩)
        omega
    · by_cases hd' : d + 1 < m + 1
      · have h1 := hright (Or.inr ⟨rfl, hd'⟩)
        omega
      · omega
  · rcases hq with ⟨hc, hd⟩ | ⟨rfl, hd⟩
    · by_cases hc' : c + 1 < m + 1
      · have h1 := hdown (Or.inl ⟨hc', hd⟩)
        omega
      · by_cases hd' : d + 1 < m + 2
        · have h1 := hright (Or.inl ⟨hc, hd'⟩)
          omega
        · omega
    · have h1 := hright (Or.inr ⟨rfl, by omega⟩)
      omega

theorem nu_contents_core (m : ℕ)
    (hmem : ∀ i j, (i, j) ∈ lam.diagram.cells ↔ (i < m + 1 ∧ j < m + 2) ∨ (i = m + 1 ∧ j < m + 1))
    (T : SYT lam) (top k : Fin N) (htop : (top : ℕ) + 1 = N) (hk : (k : ℕ) + 2 = N) :
    (T.content k = -1 ∧ T.content top = 1) ∨ (T.content k = 2 ∧ T.content top = 1) ∨
      (T.content k = 1 ∧ T.content top = -1) ∨ (T.content k = -2 ∧ T.content top = -1) := by
  have htp := nu_pos_top_core m hmem T top htop
  obtain ⟨hne, hdown, hright⟩ := second_corner T top k htop hk
  have hq := T.pos_mem k
  unfold SYT.content
  obtain ⟨⟨a, b⟩, hp⟩ : ∃ p, T.pos top = p := ⟨_, rfl⟩
  obtain ⟨⟨c, d⟩, hq'⟩ : ∃ q, T.pos k = q := ⟨_, rfl⟩
  rw [hp] at htp hne hdown hright ⊢
  rw [hq'] at hne hdown hright hq ⊢
  dsimp only at hdown hright ⊢
  rw [hmem] at hq hdown hright
  simp only [Prod.mk.injEq, ne_eq] at htp hne hdown hright
  exact nu_arith m a b c d htp hq hne hdown hright

/-- **T5**: in a tableau of shape `ν = (n^{n-1}, n-1)` the largest entry is at one of the two corners. -/
theorem nu_pos_top (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.parts = Multiset.replicate (n - 1) n + {n - 1}) (T : SYT lam) (top : Fin (n ^ 2 - 1))
    (htop : (top : ℕ) + 1 = n ^ 2 - 1) :
    T.pos top = (n - 2, n - 1) ∨ T.pos top = (n - 1, n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 2 = m := by omega
  have e2 : m + 2 - 1 = m + 1 := by omega
  rw [e2] at hlam
  rw [e1, e2]
  exact nu_pos_top_core m (nu_mem m hlam) T top htop

/-- **T5**: the contents of the two largest entries of a tableau of shape `ν`. -/
theorem nu_contents (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.parts = Multiset.replicate (n - 1) n + {n - 1}) (T : SYT lam) (top k : Fin (n ^ 2 - 1))
    (htop : (top : ℕ) + 1 = n ^ 2 - 1) (hk : (k : ℕ) + 2 = n ^ 2 - 1) :
    (T.content k = -1 ∧ T.content top = 1) ∨ (T.content k = 2 ∧ T.content top = 1) ∨
      (T.content k = 1 ∧ T.content top = -1) ∨ (T.content k = -2 ∧ T.content top = -1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e2 : m + 2 - 1 = m + 1 := by omega
  rw [e2] at hlam
  exact nu_contents_core m (nu_mem m hlam) T top k htop hk

theorem nu_contents_mem (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.parts = Multiset.replicate (n - 1) n + {n - 1}) (T : SYT lam) (top k : Fin (n ^ 2 - 1))
    (htop : (top : ℕ) + 1 = n ^ 2 - 1) (hk : (k : ℕ) + 2 = n ^ 2 - 1) :
    (T.content k, T.content top) ∈ ({(-1, 1), (2, 1), (1, -1), (-2, -1)} : Set (ℤ × ℤ)) := by
  rcases nu_contents n hn lam hlam T top k htop hk with h | h | h | h <;>
    simp [h.1, h.2]

theorem nu_content_top (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.parts = Multiset.replicate (n - 1) n + {n - 1}) (T : SYT lam) (top : Fin (n ^ 2 - 1))
    (htop : (top : ℕ) + 1 = n ^ 2 - 1) : T.content top = 1 ∨ T.content top = -1 := by
  unfold SYT.content
  rcases nu_pos_top n hn lam hlam T top htop with h | h <;> rw [h] <;> dsimp only <;> omega

theorem nu_content_rel (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.parts = Multiset.replicate (n - 1) n + {n - 1}) (T : SYT lam) (top k : Fin (n ^ 2 - 1))
    (htop : (top : ℕ) + 1 = n ^ 2 - 1) (hk : (k : ℕ) + 2 = n ^ 2 - 1) :
    T.content k ^ 2 - T.content k * T.content top = 2 := by
  rcases nu_contents n hn lam hlam T top k htop hk with h | h | h | h <;> rw [h.1, h.2] <;> norm_num

/-! ## T7: content forcing -/

/-- **T7** (column): contents `0, -1, …, -n` at entries `0, …, n` force them down the first column. -/
theorem pos_eq_col_of_content (T : SYT lam) (n : ℕ)
    (h : ∀ k : Fin N, (k : ℕ) ≤ n → T.content k = -(k : ℤ)) :
    ∀ k : Fin N, (k : ℕ) ≤ n → T.pos k = ((k : ℕ), 0) := by
  intro k
  induction k using WellFoundedLT.induction with
  | _ k ih =>
    intro hk
    have hc := h k hk
    unfold SYT.content at hc
    obtain ⟨m, hm, hmk⟩ := exists_le_of_le T (k := k) (c := ((k : ℕ), 0)) (by dsimp only; omega)
      (Nat.zero_le _)
    rcases hmk.lt_or_eq with hlt | rfl
    · have hmn : (m : ℕ) ≤ n := by
        have := Fin.lt_def.1 hlt
        omega
      rw [ih m hlt hmn, Prod.mk.injEq] at hm
      exact absurd (Fin.ext hm.1) (ne_of_lt hlt)
    · exact hm

/-- **T7** (row): contents `0, 1, …, n` at entries `0, …, n` force them along the first row. -/
theorem pos_eq_row_of_content (T : SYT lam) (n : ℕ)
    (h : ∀ k : Fin N, (k : ℕ) ≤ n → T.content k = (k : ℤ)) :
    ∀ k : Fin N, (k : ℕ) ≤ n → T.pos k = (0, (k : ℕ)) := by
  intro k
  induction k using WellFoundedLT.induction with
  | _ k ih =>
    intro hk
    have hc := h k hk
    unfold SYT.content at hc
    obtain ⟨m, hm, hmk⟩ := exists_le_of_le T (k := k) (c := (0, (k : ℕ))) (Nat.zero_le _)
      (by dsimp only; omega)
    rcases hmk.lt_or_eq with hlt | rfl
    · have hmn : (m : ℕ) ≤ n := by
        have := Fin.lt_def.1 hlt
        omega
      rw [ih m hlt hmn, Prod.mk.injEq] at hm
      exact absurd (Fin.ext hm.2) (ne_of_lt hlt)
    · exact hm

/-- **T7**: if `ℓ(λ) ≤ n < N`, no tableau has content `-k` at every entry `k ≤ n`. -/
theorem not_col_content_of_numRows_le (T : SYT lam) (n : ℕ) (hn : n < N) (hrows : lam.numRows ≤ n) :
    ¬ ∀ k : Fin N, (k : ℕ) ≤ n → T.content k = -(k : ℤ) := by
  intro h
  have hpos := pos_eq_col_of_content T n h ⟨n, hn⟩ le_rfl
  have hmem := T.pos_mem ⟨n, hn⟩
  rw [hpos] at hmem
  have := lt_numRows_of_mem hmem
  dsimp only at this
  omega

/-- **T7**: if `λ_1 ≤ n < N`, no tableau has content `k` at every entry `k ≤ n`. -/
theorem not_row_content_of_firstRow_le (T : SYT lam) (n : ℕ) (hn : n < N) (hrow : lam.firstRow ≤ n) :
    ¬ ∀ k : Fin N, (k : ℕ) ≤ n → T.content k = (k : ℤ) := by
  intro h
  have hpos := pos_eq_row_of_content T n h ⟨n, hn⟩ le_rfl
  have hmem := T.pos_mem ⟨n, hn⟩
  rw [hpos] at hmem
  have := lt_firstRow_of_mem hmem
  dsimp only at this
  omega

/-! ## T8: swapping two consecutive entries in the same row or column is never standard -/

/-- **T8**: if `k` and `l = k + 1` share a row or a column of `T`, then `T ∘ (k l)` is not standard. -/
theorem no_swap_of_same_row_or_col (T : SYT lam) (k l : Fin N) (hkl : (l : ℕ) = k + 1)
    (hsame : (T.pos k).1 = (T.pos l).1 ∨ (T.pos k).2 = (T.pos l).2) :
    ¬ ∃ T' : SYT lam, T'.pos = T.pos ∘ Equiv.swap k l := by
  rintro ⟨T', hT'⟩
  have e1 : T'.pos k = T.pos l := by rw [hT']; simp
  have e2 : T'.pos l = T.pos k := by rw [hT']; simp
  have hnot : ¬ l ≤ k := fun h => by
    have := Fin.le_def.1 h
    omega
  rcases hsame with h | h
  · have h2 : (T.pos k).2 ≤ (T.pos l).2 := by
      by_contra hcon
      exact hnot (T.pos_mono l k h.ge (by omega))
    exact hnot (T'.pos_mono l k (by rw [e1, e2]; exact h.le) (by rw [e1, e2]; exact h2))
  · have h1 : (T.pos k).1 ≤ (T.pos l).1 := by
      by_contra hcon
      exact hnot (T.pos_mono l k (by omega) h.ge)
    exact hnot (T'.pos_mono l k (by rw [e1, e2]; exact h1) (by rw [e1, e2]; exact h.le))

end NagataHigman.Proofs

end
