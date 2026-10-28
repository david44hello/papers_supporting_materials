/- NagataHigman/Proofs/SytConnect.lean — standard-tableau connectivity by consecutive swaps below the top entry.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib
import NagataHigman.Defs.Young
import NagataHigman.Proofs.Tableaux

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman

section Connect

variable {N : ℕ} {lam : Shape N}

/-- `B` is `A` with two consecutive entries `k`, `l = k + 1` swapped, where `l < M`. -/
def SwapBelow (M : ℕ) (A B : SYT lam) : Prop :=
  ∃ k l : Fin N, (l : ℕ) = k + 1 ∧ (l : ℕ) < M ∧ B.pos = A.pos ∘ Equiv.swap k l

theorem SwapBelow.mono {M M' : ℕ} (h : M ≤ M') {A B : SYT lam}
    (hr : Relation.ReflTransGen (SwapBelow M) A B) : Relation.ReflTransGen (SwapBelow M') A B := by
  have hle : (SwapBelow M : SYT lam → SYT lam → Prop) ≤ SwapBelow M' := by
    intro X Y hXY
    obtain ⟨k, l, h1, h2, h3⟩ := hXY
    exact ⟨k, l, h1, by omega, h3⟩
  exact Relation.ReflTransGen.mono hle A B hr

/-- The adjacent transposition `(k k+1)` preserves `≤`, except on the pair `(k, k+1)` itself. -/
private theorem swap_le_swap {k l x y : Fin N} (hkl : (l : ℕ) = k + 1) (hxy : x ≤ y)
    (hne : ¬ (x = k ∧ y = l)) : Equiv.swap k l x ≤ Equiv.swap k l y := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  rw [Fin.le_def] at hxy
  simp only [Fin.ext_iff] at hne
  split_ifs <;> simp only [Fin.le_def, Fin.ext_iff] at * <;> omega

/-- Swapping consecutive entries `k`, `k + 1` whose cells are not weakly ordered north-west to
south-east gives a standard tableau. -/
def swapSYT (T : SYT lam) (k l : Fin N) (hkl : (l : ℕ) = k + 1)
    (h : ¬ ((T.pos k).1 ≤ (T.pos l).1 ∧ (T.pos k).2 ≤ (T.pos l).2)) : SYT lam where
  pos := T.pos ∘ Equiv.swap k l
  pos_injective := T.pos_injective.comp (Equiv.injective _)
  pos_mem _ := T.pos_mem _
  pos_mono a b h1 h2 := by
    have hab := T.pos_mono _ _ h1 h2
    have hne : ¬ (Equiv.swap k l a = k ∧ Equiv.swap k l b = l) := by
      rintro ⟨ha, hb⟩
      simp only [Function.comp_apply, ha, hb] at h1 h2
      exact h ⟨h1, h2⟩
    simpa using swap_le_swap hkl hab hne

theorem swapSYT_pos (T : SYT lam) (k l : Fin N) (hkl : (l : ℕ) = k + 1)
    (h : ¬ ((T.pos k).1 ≤ (T.pos l).1 ∧ (T.pos k).2 ≤ (T.pos l).2)) :
    (swapSYT T k l hkl h).pos = T.pos ∘ Equiv.swap k l := rfl

/-- **Bubbling**: if no cell weakly south-east of the cell of `j` holds an entry in `(j, M']`, a chain of
swaps below `M' + 1` brings that cell's entry up to `M'`, fixing every entry above `M'`. -/
theorem bubble (d : ℕ) : ∀ (T : SYT lam) (j M' : Fin N), (M' : ℕ) = j + d →
    (∀ i : Fin N, j < i → i ≤ M' → ¬ ((T.pos j).1 ≤ (T.pos i).1 ∧ (T.pos j).2 ≤ (T.pos i).2)) →
    ∃ T1 : SYT lam, Relation.ReflTransGen (SwapBelow ((M' : ℕ) + 1)) T T1 ∧ T1.pos M' = T.pos j ∧
      ∀ m : Fin N, M' < m → T1.pos m = T.pos m := by
  induction d with
  | zero =>
    intro T j M' hd _
    obtain rfl : M' = j := Fin.ext (by omega)
    exact ⟨T, Relation.ReflTransGen.refl, rfl, fun _ _ => rfl⟩
  | succ d ih =>
    intro T j M' hd hC
    obtain ⟨j1, hj1⟩ : ∃ j1 : Fin N, (j1 : ℕ) = j + 1 := ⟨⟨j + 1, by have := M'.isLt; omega⟩, rfl⟩
    have hjj1 : j < j1 := Fin.lt_def.2 (by omega)
    have hns := hC j1 hjj1 (Fin.le_def.2 (by omega))
    have e1 : (swapSYT T j j1 hj1 hns).pos j1 = T.pos j := by simp [swapSYT_pos]
    have eo : ∀ i, i ≠ j → i ≠ j1 → (swapSYT T j j1 hj1 hns).pos i = T.pos i := fun i h1 h2 => by
      simp [swapSYT_pos, Equiv.swap_apply_of_ne_of_ne h1 h2]
    obtain ⟨T1, hrt, hpos, hagree⟩ := ih (swapSYT T j j1 hj1 hns) j1 M' (by omega) (by
      intro i hi hiM
      rw [e1, eo i (ne_of_gt (lt_trans hjj1 hi)) (ne_of_gt hi)]
      exact hC i (lt_trans hjj1 hi) hiM)
    refine ⟨T1, Relation.ReflTransGen.head ⟨j, j1, hj1, by omega, rfl⟩ hrt, by rw [hpos, e1], ?_⟩
    intro m hm
    have hm' := Fin.lt_def.1 hm
    rw [hagree m hm, eo m (fun h => by rw [h] at hm'; omega) (fun h => by rw [h] at hm'; omega)]

/-- If `T`, `T'` agree on the entries `> M`, every other cell weakly south-east of the cell of `M` in
`T'` holds, in `T`, an entry `> M`. -/
private theorem other_cell_above {T T' : SYT lam} {Mf : Fin N}
    (h : ∀ m : Fin N, Mf < m → T.pos m = T'.pos m) {i : Fin N} (hi : T.pos i ≠ T'.pos Mf)
    (hle : (T'.pos Mf).1 ≤ (T.pos i).1 ∧ (T'.pos Mf).2 ≤ (T.pos i).2) : Mf < i := by
  obtain ⟨i', hi'⟩ := exists_pos_eq T' (T.pos_mem i)
  have hMi' : Mf ≤ i' := T'.pos_mono Mf i' (hi' ▸ hle.1) (hi' ▸ hle.2)
  rcases hMi'.lt_or_eq with hlt | rfl
  · have : i' = i := T.pos_injective ((h i' hlt).trans hi')
    exact this ▸ hlt
  · exact absurd hi'.symm hi

/-- The inductive step: `T`, `T'` agree on the entries `> M` but put `M` in different cells. -/
private theorem connect_step (M : ℕ) (hM : M < N)
    (ih : ∀ T T' : SYT lam, (∀ m : Fin N, M ≤ (m : ℕ) → T.pos m = T'.pos m) →
      Relation.ReflTransGen (SwapBelow M) T T')
    (T T' : SYT lam) (h : ∀ m : Fin N, M + 1 ≤ (m : ℕ) → T.pos m = T'.pos m)
    (heq : T.pos ⟨M, hM⟩ ≠ T'.pos ⟨M, hM⟩) : Relation.ReflTransGen (SwapBelow (M + 1)) T T' := by
  set Mf : Fin N := ⟨M, hM⟩ with hMf
  have h' : ∀ m : Fin N, Mf < m → T.pos m = T'.pos m := fun m hm => h m (Fin.lt_def.1 hm)
  -- the cell of `M` in `T'` holds `j < M` in `T`
  obtain ⟨j, hj⟩ := exists_pos_eq T (T'.pos_mem Mf)
  have hjM : j < Mf := by
    rcases lt_or_ge j Mf with hlt | hge
    · exact hlt
    rcases hge.lt_or_eq with hgt | rfl
    · exact absurd (T'.pos_injective ((h' j hgt).symm.trans hj)) (ne_of_gt hgt)
    · exact absurd hj heq
  have hjM' := Fin.lt_def.1 hjM
  obtain ⟨M1, hM1⟩ : ∃ M1 : Fin N, (M1 : ℕ) + 1 = M := ⟨⟨M - 1, by omega⟩, by simp [Mf] at hjM'; simp; omega⟩
  -- bubble that entry up to `M - 1`
  obtain ⟨T1, hrt1, hpos1, hagree1⟩ := bubble (M1 - j) T j M1 (by simp [Mf] at hjM'; omega)
    (fun i hji hiM hle => by
      have := other_cell_above h' (fun he => (ne_of_gt hji) (T.pos_injective (he.trans hj.symm)))
        (hj ▸ hle)
      have := Fin.lt_def.1 this
      have := Fin.le_def.1 hiM
      simp [Mf] at *
      omega)
  have hT1M : T1.pos Mf = T.pos Mf := hagree1 Mf (Fin.lt_def.2 (by simp [Mf]; omega))
  -- swap `M - 1` and `M`
  have hns : ¬ ((T1.pos M1).1 ≤ (T1.pos Mf).1 ∧ (T1.pos M1).2 ≤ (T1.pos Mf).2) := fun hle => by
    rw [hpos1, hj, hT1M] at hle
    exact lt_irrefl _ (other_cell_above h' heq hle)
  have hkl : ((Mf : Fin N) : ℕ) = M1 + 1 := by simp [Mf]; omega
  have hrest : ∀ m : Fin N, M ≤ (m : ℕ) → (swapSYT T1 M1 Mf hkl hns).pos m = T'.pos m := by
    intro m hm
    rcases hm.lt_or_eq with hlt | heqm
    · have hne1 : m ≠ M1 := fun he => by rw [he] at hlt; omega
      have hne2 : m ≠ Mf := fun he => by rw [he] at hlt; simp [Mf] at hlt
      rw [swapSYT_pos, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne1 hne2,
        hagree1 m (Fin.lt_def.2 (by omega)), h m hlt]
    · obtain rfl : m = Mf := Fin.ext heqm.symm
      rw [swapSYT_pos, Function.comp_apply, Equiv.swap_apply_right, hpos1, hj]
  refine (SwapBelow.mono (by omega) hrt1).trans (Relation.ReflTransGen.head ?_
    (SwapBelow.mono (Nat.le_succ M) (ih _ T' hrest)))
  exact ⟨M1, Mf, hkl, by simp [Mf], rfl⟩

/-- **Connectivity above `M`**: tableaux agreeing on all entries `≥ M` are joined by swaps of
consecutive entries `k, k + 1` with `k + 1 < M`. -/
theorem connected_above (M : ℕ) : ∀ T T' : SYT lam, (∀ m : Fin N, M ≤ (m : ℕ) → T.pos m = T'.pos m) →
    Relation.ReflTransGen (SwapBelow M) T T' := by
  induction M with
  | zero =>
    intro T T' h
    rw [syt_ext (funext fun m => h m (Nat.zero_le _))]
  | succ M ih =>
    intro T T' h
    by_cases hM : M < N
    · by_cases heq : T.pos ⟨M, hM⟩ = T'.pos ⟨M, hM⟩
      · refine SwapBelow.mono (Nat.le_succ M) (ih T T' fun m hm => ?_)
        rcases hm.lt_or_eq with hlt | heqm
        · exact h m hlt
        · obtain rfl : m = ⟨M, hM⟩ := Fin.ext heqm.symm
          exact heq
      · exact connect_step M hM ih T T' h heq
    · exact SwapBelow.mono (Nat.le_succ M) (ih T T' fun m _ => h m (by have := m.isLt; omega))

end Connect

/-- **H1**: two standard tableaux of the same shape with the largest entry in the same cell are joined
by a chain of standard tableaux, each step swapping two consecutive entries `k, k + 1` below `top`. -/
theorem syt_connected {N : ℕ} {lam : Shape N} (top : Fin N) (htop : (top : ℕ) + 1 = N) (T T' : SYT lam)
    (h : T.pos top = T'.pos top) :
    Relation.ReflTransGen
      (fun A B : SYT lam => ∃ k l : Fin N, (l : ℕ) = k + 1 ∧ (l : ℕ) < (top : ℕ) ∧ B.pos = A.pos ∘ Equiv.swap k l)
      T T' :=
  connected_above (top : ℕ) T T' fun m hm => by
    obtain rfl : m = top := Fin.ext (by have := m.isLt; omega)
    exact h

end NagataHigman.Proofs

end
