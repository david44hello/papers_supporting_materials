/-
LeeDiam/Sec4/Comb.lean — Section 4 helper: the comb walks of Lemma 4.5 (sec_chain.tex v1.50 l. 61-67).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

Proof of the length `m + 1` (the paper counts glue elements): every component of `X ∪ C` (with `X` in row `a`)
contains a helper, and the helper columns that are leftmost in their component are exactly the first helper column
and the columns `t` with `a_{t-1} ∉ X` (`leaders`). Each glue `a_{t-1}` lies in exactly one of `A`, `B`, so the two
phases have `(m - γ_A) + (1 + γ_A) = m + 1` moves.
-/
import LeeDiam.Defs.Chain
import LeeDiam.Sec4.Comps
import LeeDiam.Sec4.WalkOps

namespace LeeDiam.S4

open Finset Band

section WalkAppend

variable {P : Type} [PartialOrder P]

/-- A walk from `A` to `C` followed by a walk from `C` to `B` is a walk from `A` to `B`. -/
theorem walk_append {W₁ W₂ : List (Set P)} {A C B : Set P} (h₁ : IsWalkFromTo W₁ A C)
    (h₂ : IsWalkFromTo W₂ C B) : IsWalkFromTo (W₁ ++ W₂.tail) A B := by
  obtain ⟨⟨hne₁, ha₁, hc₁⟩, hh₁, hl₁⟩ := h₁
  obtain ⟨⟨hne₂, ha₂, hc₂⟩, hh₂, hl₂⟩ := h₂
  obtain ⟨T, rfl⟩ : ∃ T, W₂ = C :: T := by
    cases W₂ with
    | nil => exact absurd rfl hne₂
    | cons Y T =>
      simp only [List.head?_cons, Option.some.injEq] at hh₂
      exact ⟨T, by rw [hh₂]⟩
  simp only [List.tail_cons]
  refine ⟨⟨by simp [hne₁], ?_, ?_⟩, ?_, ?_⟩
  · intro X hX
    rcases List.mem_append.1 hX with hX | hX
    · exact ha₁ X hX
    · exact ha₂ X (List.mem_cons_of_mem _ hX)
  · rw [List.isChain_append]
    refine ⟨hc₁, hc₂.tail, ?_⟩
    intro X hX Y hY
    rw [hl₁] at hX
    cases T with
    | nil => simp at hY
    | cons Y₁ T' =>
      simp only [Option.mem_def, Option.some.injEq] at hX
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hY
      subst hX
      subst hY
      exact (List.isChain_cons_cons.1 hc₂).1
  · simp [List.head?_append, hh₁]
  · cases T with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl₂
      subst hl₂
      simpa using hl₁
    | cons Y₁ T' =>
      have hl₂' : (Y₁ :: T').getLast? = some B := by
        rw [List.getLast?_cons_cons] at hl₂
        exact hl₂
      rw [List.getLast?_append_of_ne_nil _ (by simp), hl₂']

/-- In a list of the components of `S` (without repetition), the component at index `i` is among the first `t`
exactly when `i < t`. -/
theorem mem_take_comps {S : Set P} {L : List (Set P)} (hnd : L.Nodup) (hL : ∀ C, C ∈ L ↔ IsComponent C S)
    {x : P} {i : ℕ} (hi : i < L.length) (hx : x ∈ L[i]) (t : ℕ) : (∃ D ∈ L.take t, x ∈ D) ↔ i < t := by
  constructor
  · rintro ⟨D, hD, hxD⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hD
    rw [List.getElem_take] at hxD
    simp only [List.length_take] at hj
    have heq : L[j] = L[i] :=
      comp_eq_of_mem ((hL _).1 (List.getElem_mem _)) ((hL _).1 (List.getElem_mem _)) hxD hx
    have := (hnd.getElem_inj_iff).1 heq
    omega
  · intro hit
    refine ⟨(L.take t)[i]'(by simp only [List.length_take]; omega), List.getElem_mem _, ?_⟩
    rw [List.getElem_take]
    exact hx

end WalkAppend

section Comb

variable {k : ℕ}

/-- The helper columns of Lemma 4.5: `t ∈ [s, e]` with `t - s ≡ par (mod 2)`. -/
def helperCols (par s e : ℕ) : Finset (Fin k) :=
  univ.filter (fun i => s ≤ i.val ∧ i.val ≤ e ∧ (i.val - s) % 2 = par)

theorem mem_helperCols {par s e : ℕ} {i : Fin k} :
    i ∈ helperCols par s e ↔ s ≤ i.val ∧ i.val ≤ e ∧ (i.val - s) % 2 = par := by
  simp [helperCols]

theorem c_mem_helperSet {par s e : ℕ} {i : Fin k} :
    c i ∈ (helperSet par s e : Set (Band k)) ↔ i ∈ helperCols par s e := by
  rw [mem_helperCols, helperSet, Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem helperSet_ncard (par s e : ℕ) :
    (helperSet par s e : Set (Band k)).ncard = (helperCols (k := k) par s e).card := by
  have hset : (helperSet par s e : Set (Band k)) =
      c '' ((helperCols (k := k) par s e : Finset (Fin k)) : Set (Fin k)) := by
    ext x
    constructor
    · rintro ⟨h2, h3, h4, h5⟩
      exact ⟨x.1, mem_helperCols.2 ⟨h3, h4, h5⟩, Prod.ext rfl h2.symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact c_mem_helperSet.2 hi
  rw [hset, Set.ncard_image_of_injective _ c_injective, Set.ncard_coe_finset]

theorem comp_a_c {x : Band k} (hx : x.2 = 0) {i : Fin k} (h1 : x.1.val ≤ i.val + 1) (h2 : i.val ≤ x.1.val + 1) :
    Comp x (c i) := by
  rw [comp_iff_val]
  have hx' : x.2.val = 0 := by rw [hx]; rfl
  have hc : (c i).2.val = 2 := rfl
  have hc1 : (c i).1 = i := rfl
  rw [hc, hc1]
  omega

variable {par s e : ℕ}

theorem exists_helper_near (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (hek : e < k) {u : ℕ} (hsu : s ≤ u)
    (hue : u ≤ e) : ∃ i : Fin k, i ∈ helperCols par s e ∧ i.val ≤ u + 1 ∧ u ≤ i.val + 1 := by
  by_cases h : (u - s) % 2 = par
  · exact ⟨⟨u, by omega⟩, mem_helperCols.2 ⟨hsu, hue, h⟩, by show u ≤ u + 1; omega, by show u ≤ u + 1; omega⟩
  · by_cases hu : u + 1 ≤ e ∧ par = 1
    · exact ⟨⟨u + 1, by omega⟩, mem_helperCols.2 ⟨by show s ≤ u + 1; omega, by show u + 1 ≤ e; omega,
        by show (u + 1 - s) % 2 = par; omega⟩, by show u + 1 ≤ u + 1; omega, by show u ≤ u + 1 + 1; omega⟩
    · exact ⟨⟨u - 1, by omega⟩, mem_helperCols.2 ⟨by show s ≤ u - 1; omega, by show u - 1 ≤ e; omega,
        by show (u - 1 - s) % 2 = par; omega⟩, by show u - 1 ≤ u + 1; omega, by show u ≤ u - 1 + 1; omega⟩

variable {X : Set (Band k)}

/-- Every component of `X ∪ C` contains a helper. -/
theorem comp_has_helper (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (hek : e < k) (hX : X ⊆ rowSeg 0 s e)
    {D : Set (Band k)} (hD : IsComponent D (X ∪ helperSet par s e)) :
    ∃ i : Fin k, i ∈ helperCols par s e ∧ c i ∈ D := by
  obtain ⟨x, hxD⟩ := isConnSet_nonempty hD.1
  rcases hD.2.1 hxD with hxX | hxC
  · obtain ⟨h0, hs, he⟩ := hX hxX
    obtain ⟨i, hi, h1, h2⟩ := exists_helper_near hpar hek hs he
    exact ⟨i, hi, comp_closed hD hxD (Or.inr (c_mem_helperSet.2 hi)) (comp_a_c h0 h2 h1)⟩
  · obtain ⟨h2, h3, h4, h5⟩ := hxC
    refine ⟨x.1, mem_helperCols.2 ⟨h3, h4, h5⟩, ?_⟩
    have : c x.1 = x := Prod.ext rfl h2.symm
    rw [this]
    exact hxD

/-- If `a_{t-1} ∈ X` and `t` is not the first helper column, then `c_{t-2}` is in the component of `c_t`. -/
theorem glue_reach (hX : X ⊆ rowSeg 0 s e) {i : Fin k} (hi : i ∈ helperCols par s e) (hne : i.val ≠ s + par)
    (hg : ∃ x ∈ X, x.1.val + 1 = i.val) :
    ∃ j : Fin k, j ∈ helperCols par s e ∧ j.val + 2 = i.val ∧ c j ∈ reach (X ∪ helperSet par s e) (c i) := by
  obtain ⟨x, hxX, hx1⟩ := hg
  obtain ⟨h0, hs, he⟩ := hX hxX
  rw [mem_helperCols] at hi
  obtain ⟨j, hjv⟩ : ∃ j : Fin k, j.val = i.val - 2 := ⟨⟨i.val - 2, by omega⟩, rfl⟩
  have hj : j ∈ helperCols par s e := mem_helperCols.2 ⟨by omega, by omega, by omega⟩
  refine ⟨j, hj, by omega, ?_⟩
  have hxS : x ∈ X ∪ helperSet par s e := Or.inl hxX
  have hciS : c i ∈ X ∪ helperSet par s e := Or.inr (c_mem_helperSet.2 (mem_helperCols.2 hi))
  have hcjS : c j ∈ X ∪ helperSet par s e := Or.inr (c_mem_helperSet.2 hj)
  exact (Relation.ReflTransGen.single ⟨hciS, hxS, comp_symm (comp_a_c h0 (by omega) (by omega))⟩).tail
    ⟨hxS, hcjS, comp_a_c h0 (by omega) (by omega)⟩

open Classical in
/-- The leader columns: helper columns that are leftmost in their component of `X ∪ C`. -/
noncomputable def leaders (par s e : ℕ) (X : Set (Band k)) : Finset (Fin k) :=
  (helperCols par s e).filter (fun i => i.val = s + par ∨ ¬ ∃ x ∈ X, x.1.val + 1 = i.val)

open Classical in
theorem mem_leaders {i : Fin k} :
    i ∈ leaders par s e X ↔ i ∈ helperCols par s e ∧ (i.val = s + par ∨ ¬ ∃ x ∈ X, x.1.val + 1 = i.val) := by
  unfold leaders
  exact Finset.mem_filter

/-- A leader is leftmost: no helper of a smaller column lies in its component. -/
theorem leader_min {i : Fin k} (hi : i ∈ leaders par s e X) {j : Fin k}
    (hj : j ∈ helperCols par s e) (hji : j.val < i.val) : c j ∉ reach (X ∪ helperSet par s e) (c i) := by
  intro hmem
  obtain ⟨hiH, hlead⟩ := mem_leaders.1 hi
  rw [mem_helperCols] at hiH hj
  rcases hlead with h | h
  · omega
  · have hS : c i ∈ X ∪ helperSet par s e := Or.inr (c_mem_helperSet.2 (mem_helperCols.2 hiH))
    have hD := isComponent_reach hS
    obtain ⟨u, -, v, hv, hQu, hQv, huv⟩ := isConnSet_cross hD.1 (fun y => i.val ≤ y.1.val)
      (mem_reach_self _ _) hmem (le_refl i.val) (by show ¬ i.val ≤ j.val; omega)
    have hcols := comp_cols huv
    rcases hD.2.1 hv with hvX | hvC
    · exact h ⟨v, hvX, by omega⟩
    · obtain ⟨-, h3, -, h5⟩ := hvC
      omega

/-- The components of `X ∪ C`, listed without repetition, are as many as the leaders. -/
theorem comps_length (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (hek : e < k) (hX : X ⊆ rowSeg 0 s e)
    (L : List (Set (Band k))) (hnd : L.Nodup) (hL : ∀ D, D ∈ L ↔ IsComponent D (X ∪ helperSet par s e)) :
    L.length = (leaders par s e X).card := by
  classical
  have hcS : ∀ i ∈ helperCols par s e, c i ∈ X ∪ helperSet par s e := fun i hi => Or.inr (c_mem_helperSet.2 hi)
  have key : ∀ D, IsComponent D (X ∪ helperSet par s e) ↔
      ∃ i ∈ leaders par s e X, reach (X ∪ helperSet par s e) (c i) = D := by
    intro D
    constructor
    · intro hD
      obtain ⟨i₀, hi₀, hci₀⟩ := comp_has_helper hpar hek hX hD
      have hF : ((helperCols par s e).filter (fun j => c j ∈ D)).Nonempty := ⟨i₀, mem_filter.2 ⟨hi₀, hci₀⟩⟩
      have hiF := ((helperCols par s e).filter (fun j => c j ∈ D)).min'_mem hF
      rw [mem_filter] at hiF
      have hreach : reach (X ∪ helperSet par s e) (c (((helperCols par s e).filter (fun j => c j ∈ D)).min' hF)) = D :=
        comp_eq_of_mem (isComponent_reach (hcS _ hiF.1)) hD (mem_reach_self _ _) hiF.2
      refine ⟨_, ?_, hreach⟩
      rw [mem_leaders]
      refine ⟨hiF.1, ?_⟩
      by_contra hcon
      simp only [not_or, not_not] at hcon
      obtain ⟨j, hj, hji, hjr⟩ := glue_reach hX hiF.1 hcon.1 hcon.2
      rw [hreach] at hjr
      have hle := ((helperCols par s e).filter (fun j => c j ∈ D)).min'_le j (mem_filter.2 ⟨hj, hjr⟩)
      have := Fin.le_iff_val_le_val.1 hle
      omega
    · rintro ⟨i, hi, rfl⟩
      exact isComponent_reach (hcS i (mem_leaders.1 hi).1)
  have hinj : Set.InjOn (fun i => reach (X ∪ helperSet par s e) (c i)) (leaders par s e X : Set (Fin k)) := by
    intro i hi j hj hij
    simp only at hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
    · refine leader_min hj (mem_leaders.1 hi).1 hlt ?_
      rw [← hij]
      exact mem_reach_self _ _
    · refine leader_min hi (mem_leaders.1 hj).1 hlt ?_
      rw [hij]
      exact mem_reach_self _ _
  rw [← List.toFinset_card_of_nodup hnd, ← card_image_of_injOn hinj]
  congr 1
  ext D
  rw [List.mem_toFinset, hL, key, mem_image]

theorem first_helper_mem (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (hse : s ≤ e) (hek : e < k) :
    (⟨s + par, by omega⟩ : Fin k) ∈ helperCols par s e :=
  mem_helperCols.2 ⟨by show s ≤ s + par; omega, by show s + par ≤ e; omega,
    by show (s + par - s) % 2 = par; omega⟩

open Classical in
/-- Each glue element lies in exactly one of `A`, `B`: the leaders of the two phases number `m + 1`. -/
theorem leaders_sum (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (hse : s ≤ e) (hek : e < k) (A B : Set (Band k))
    (hAB : IsSplit A B (rowSeg 0 s e)) :
    (leaders par s e A).card + (leaders par s e B).card = (helperCols (k := k) par s e).card + 1 := by
  obtain ⟨hdis, hU, -⟩ := hAB
  have hA : A ⊆ rowSeg 0 s e := hU ▸ Set.subset_union_left
  have hB : B ⊆ rowSeg 0 s e := hU ▸ Set.subset_union_right
  have hi₀ := first_helper_mem hpar hse hek
  rw [leaders, leaders, card_filter, card_filter, ← sum_add_distrib]
  rw [sum_congr rfl (g := fun i => 1 + if i = (⟨s + par, by omega⟩ : Fin k) then 1 else 0) ?_]
  · rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one, sum_ite_eq' _ _ (fun _ => 1), ite_eq_left hi₀]
  · intro i hi
    rw [mem_helperCols] at hi
    by_cases h0 : i.val = s + par
    · have : i = ⟨s + par, by omega⟩ := Fin.ext h0
      simp [this]
    · have hne : i ≠ ⟨s + par, by omega⟩ := fun h => h0 (by rw [h])
      have hi1 : 1 ≤ i.val := by omega
      obtain ⟨u, hu⟩ : ∃ u : Fin k, u.val = i.val - 1 := ⟨⟨i.val - 1, by omega⟩, rfl⟩
      obtain ⟨a', ha'⟩ : ∃ a' : Band k, a'.1 = u ∧ a'.2 = 0 := ⟨(u, 0), rfl, rfl⟩
      have ha'U : a' ∈ rowSeg 0 s e := ⟨ha'.2, by rw [ha'.1]; omega, by rw [ha'.1]; omega⟩
      have hg : ∀ Y ⊆ rowSeg 0 s e, (∃ x ∈ Y, x.1.val + 1 = i.val) ↔ a' ∈ Y := by
        intro Y hY
        constructor
        · rintro ⟨x, hx, hx1⟩
          have : x = a' := Prod.ext (Fin.ext (by rw [ha'.1]; omega)) ((hY hx).1.trans ha'.2.symm)
          exact this ▸ hx
        · intro h
          exact ⟨a', h, by rw [ha'.1]; omega⟩
      simp only [hg A hA, hg B hB]
      rw [← hU] at ha'U
      rcases ha'U with hA' | hB'
      · have : a' ∉ B := fun h => Set.disjoint_left.1 hdis hA' h
        simp [h0, hne, hA', this]
      · have : a' ∉ A := fun h => Set.disjoint_left.1 hdis h hB'
        simp [h0, hne, hB', this]

theorem not_mem_rows {x : Band k} {X Y : Set (Band k)} (hX : ∀ y ∈ X, y.2 = 0) (hY : ∀ y ∈ Y, y.2 = 2)
    (hx : x ∈ X) (hy : x ∈ Y) : False := by
  have h1 := hX x hx
  rw [hY x hy] at h1
  exact absurd h1 (by decide)

/-- Lemma 4.5 (comb walks), in the statement form of Sec4/Chain.lean `lem_4_5`. -/
theorem comb (s e : ℕ) (hse : s ≤ e) (hek : e < k) (par : ℕ) (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e))
    (A B : Set (Band k)) (hAB : IsSplit A B (rowSeg 0 s e))
    (L₁ L₂ : List (Set (Band k))) (hL₁ : L₁.Nodup) (hL₁c : ∀ D, D ∈ L₁ ↔ IsComponent D (A ∪ helperSet par s e))
    (hL₂ : L₂.Nodup) (hL₂c : ∀ D, D ∈ L₂ ↔ IsComponent D (helperSet par s e ∪ B)) :
    (L₁.scanl symmDiff A).getLast? = some (helperSet par s e) ∧
      IsWalkFromTo (L₁.scanl symmDiff A ++ (L₂.scanl symmDiff (helperSet par s e)).tail) A B ∧
      (L₁.scanl symmDiff A ++ (L₂.scanl symmDiff (helperSet par s e)).tail).length - 1 =
        (helperSet par s e : Set (Band k)).ncard + 1 ∧
      (∀ X ∈ L₁.scanl symmDiff A ++ (L₂.scanl symmDiff (helperSet par s e)).tail,
        X ⊆ rowSeg 0 s e ∪ helperSet par s e) ∧
      ∀ h ∈ (helperSet par s e : Set (Band k)), ∀ i₁ < L₁.length, ∀ i₂ < L₂.length,
        h ∈ L₁.getD i₁ ∅ → h ∈ L₂.getD i₂ ∅ → ∀ t < L₁.length + L₂.length + 1,
          (h ∈ (L₁.scanl symmDiff A ++ (L₂.scanl symmDiff (helperSet par s e)).tail).getD t ∅ ↔
            i₁ < t ∧ t ≤ L₁.length + i₂) := by
  have hAB' := hAB
  obtain ⟨hdis, hU, hUanti⟩ := hAB'
  have hA : A ⊆ rowSeg 0 s e := hU ▸ Set.subset_union_left
  have hB : B ⊆ rowSeg 0 s e := hU ▸ Set.subset_union_right
  have hrowA : ∀ y ∈ A, y.2 = 0 := fun y hy => (hA hy).1
  have hrowB : ∀ y ∈ B, y.2 = 0 := fun y hy => (hB hy).1
  have hrowC : ∀ y ∈ (helperSet par s e : Set (Band k)), y.2 = 2 := fun y hy => hy.1
  have hAanti : IsAntichainSet A := hUanti.subset hA
  have hBanti : IsAntichainSet B := hUanti.subset hB
  have hCanti : IsAntichainSet (helperSet par s e : Set (Band k)) := isAntichainSet_row 2 _ hrowC
  have hAC : Disjoint A (helperSet par s e) :=
    Set.disjoint_left.2 fun x hx hy => not_mem_rows hrowA hrowC hx hy
  have hCB : Disjoint (helperSet par s e) B :=
    Set.disjoint_left.2 fun x hx hy => not_mem_rows hrowB hrowC hy hx
  have hL₁' : ∀ D, D ∈ L₁ ↔ IsComponent D (symmDiff A (helperSet par s e)) := by
    intro D
    rw [(symmDiff_eq_sup _ _).2 hAC]
    exact hL₁c D
  have hL₂' : ∀ D, D ∈ L₂ ↔ IsComponent D (symmDiff (helperSet par s e) B) := by
    intro D
    rw [(symmDiff_eq_sup _ _).2 hCB]
    exact hL₂c D
  have hL₂B : ∀ D, D ∈ L₂ ↔ IsComponent D (B ∪ helperSet par s e) := by
    intro D
    rw [hL₂c, Set.union_comm]
  have hW₁ := components_walk A _ hAanti hCanti L₁ hL₁ hL₁'
  have hW₂ := components_walk _ B hCanti hBanti L₂ hL₂ hL₂'
  have hpw₁ := comps_pairwise hL₁ hL₁c
  have hpw₂ := comps_pairwise hL₂ hL₂c
  refine ⟨hW₁.2.2, walk_append hW₁ hW₂, ?_, ?_, ?_⟩
  · have h1 := comps_length hpar hek hA L₁ hL₁ hL₁c
    have h2 := comps_length hpar hek hB L₂ hL₂ hL₂B
    have h3 := leaders_sum hpar hse hek A B hAB
    simp only [List.length_append, List.length_scanl, List.length_tail]
    rw [helperSet_ncard]
    omega
  · intro X hX x hx
    rcases List.mem_append.1 hX with hX | hX
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hX
      rw [mem_scanl_symmDiff A L₁ hpw₁ hi] at hx
      by_cases hxA : x ∈ A
      · exact Or.inl (hA hxA)
      · obtain ⟨D, hD, hxD⟩ := not_not.1 (mt hx.2 hxA)
        rcases ((hL₁c D).1 (List.mem_of_mem_take hD)).2.1 hxD with h | h
        · exact Or.inl (hA h)
        · exact Or.inr h
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_tail hX)
      rw [mem_scanl_symmDiff _ L₂ hpw₂ hi] at hx
      by_cases hxC : x ∈ (helperSet par s e : Set (Band k))
      · exact Or.inr hxC
      · obtain ⟨D, hD, hxD⟩ := not_not.1 (mt hx.2 hxC)
        rcases ((hL₂c D).1 (List.mem_of_mem_take hD)).2.1 hxD with h | h
        · exact Or.inr h
        · exact Or.inl (hB h)
  · intro h hh i₁ hi₁ i₂ hi₂ h1 h2 t ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁, Option.getD_some] at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₂, Option.getD_some] at h2
    have hhA : h ∉ A := fun hA' => not_mem_rows hrowA hrowC hA' hh
    rw [List.getD_eq_getElem?_getD]
    by_cases htl : t < L₁.length + 1
    · have htl' : t < (L₁.scanl symmDiff A).length := by rw [List.length_scanl]; exact htl
      rw [List.getElem?_append_left htl', List.getElem?_eq_getElem htl', Option.getD_some,
        mem_scanl_symmDiff A L₁ hpw₁ htl', mem_take_comps hL₁ hL₁c hi₁ h1 t]
      simp only [hhA, false_iff, not_not]
      exact ⟨fun hlt => ⟨hlt, by omega⟩, fun hh' => hh'.1⟩
    · have htl' : (L₁.scanl symmDiff A).length ≤ t := by rw [List.length_scanl]; omega
      have hj : t - (L₁.scanl symmDiff A).length + 1 < (L₂.scanl symmDiff (helperSet par s e)).length := by
        rw [List.length_scanl, List.length_scanl]
        omega
      rw [List.getElem?_append_right htl', List.getElem?_tail, List.getElem?_eq_getElem hj, Option.getD_some,
        mem_scanl_symmDiff _ L₂ hpw₂ hj, mem_take_comps hL₂ hL₂c hi₂ h2, List.length_scanl]
      simp only [hh, true_iff]
      constructor
      · intro hn
        exact ⟨by omega, by omega⟩
      · intro hc
        omega

end Comb

section CombCor

variable {k : ℕ}

/-- The components of a set in a finite poset can be listed without repetition. -/
theorem exists_comps_list {P : Type} [PartialOrder P] [Finite P] (S : Set P) :
    ∃ L : List (Set P), L.Nodup ∧ ∀ D, D ∈ L ↔ IsComponent D S := by
  have hfin : {D : Set P | IsComponent D S}.Finite := Set.toFinite _
  exact ⟨hfin.toFinset.toList, Finset.nodup_toList _, fun D => by simp⟩

/-- Corollary 4.6, row `a`: a walk of length `⌊j/2⌋ + 1` inside `{a_s, …, a_e}` and the even helper positions. -/
theorem comb_walk_a (s e : ℕ) (hse : s ≤ e) (hek : e < k) (A B : Set (Band k))
    (hAB : IsSplit A B (rowSeg 0 s e)) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 = (e - s + 1) / 2 + 1 ∧
      ∀ X ∈ W, X ⊆ rowSeg 0 s e ∪ helperSet 1 s e := by
  obtain ⟨hdis, hU, hUanti⟩ := hAB
  have hA : A ⊆ rowSeg 0 s e := hU ▸ Set.subset_union_left
  have hB : B ⊆ rowSeg 0 s e := hU ▸ Set.subset_union_right
  rcases Nat.lt_or_ge s e with hlt | hge
  · obtain ⟨L₁, h₁, h₁c⟩ := exists_comps_list (A ∪ helperSet 1 s e : Set (Band k))
    obtain ⟨L₂, h₂, h₂c⟩ := exists_comps_list (helperSet 1 s e ∪ B : Set (Band k))
    obtain ⟨-, hW, hlen, hsub, -⟩ :=
      comb s e hse hek 1 (Or.inr ⟨rfl, hlt⟩) A B ⟨hdis, hU, hUanti⟩ L₁ L₂ h₁ h₁c h₂ h₂c
    refine ⟨_, hW, ?_, hsub⟩
    rw [hlen, helper_count 1 s e le_rfl hse hek]
    omega
  · have hse' : s = e := le_antisymm hse hge
    subst hse'
    have hone : (rowSeg 0 s s : Set (Band k)) = {((⟨s, hek⟩ : Fin k), (0 : Fin 3))} := by
      ext x
      constructor
      · rintro ⟨h0, h1, h2⟩
        exact Prod.ext (Fin.ext (by show x.1.val = s; omega)) h0
      · rintro rfl
        exact ⟨rfl, le_rfl, le_rfl⟩
    refine ⟨[A, B], ⟨⟨by simp, ?_, ?_⟩, rfl, rfl⟩, by simp, ?_⟩
    · intro X hX
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl
      · exact hUanti.subset hA
      · exact hUanti.subset hB
    · rw [List.isChain_cons_cons]
      refine ⟨?_, List.isChain_singleton _⟩
      rw [(symmDiff_eq_sup _ _).2 hdis]
      show IsConnSet (A ∪ B)
      rw [hU, hone]
      exact isConnSet_singleton _
    · intro X hX
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl
      · exact hA.trans Set.subset_union_left
      · exact hB.trans Set.subset_union_left

theorem sigma_image_image (X : Set (Band k)) : sigmaAC '' (sigmaAC '' X) = X := by
  rw [Set.image_image]
  simp [sigma_sigma]

theorem sigma_rowSeg (s e : ℕ) : sigmaAC '' (rowSeg 2 s e : Set (Band k)) = rowSeg 0 s e := by
  ext x
  rw [sigma_mem_image_iff]
  have hv := sigma_snd_val x
  have hx := x.2.isLt
  constructor
  · rintro ⟨h2, h3, h4⟩
    refine ⟨Fin.ext ?_, h3, h4⟩
    rw [h2] at hv
    simp at hv
    show x.2.val = 0
    omega
  · rintro ⟨h0, h3, h4⟩
    refine ⟨Fin.ext ?_, h3, h4⟩
    rw [hv, h0]
    rfl

/-- The property of the states of Corollary 4.6 for row `a`. -/
theorem comb_state_prop {s e : ℕ} {x : Band k} (hx : x ∈ (rowSeg 0 s e ∪ helperSet 1 s e : Set (Band k))) :
    (x.2 ≠ 1 ∧ s ≤ x.1.val ∧ x.1.val ≤ e) ∧ (x.1.val = s → x.2 = 0) := by
  rcases hx with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2, h3⟩
  · exact ⟨⟨by rw [h0]; decide, h1, h2⟩, fun _ => h0⟩
  · refine ⟨⟨by rw [h0]; decide, h1, h2⟩, fun hs => ?_⟩
    rw [hs, Nat.sub_self] at h3
    simp at h3

/-- Corollary 4.6, in the statement form of Sec4/Chain.lean `cor_4_6`. -/
theorem comb_cor (r : Fin 3) (hr : r ≠ 1) (s e : ℕ) (hse : s ≤ e) (hek : e < k)
    (A B : Set (Band k)) (hAB : IsSplit A B (rowSeg r s e)) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 = (e - s + 1) / 2 + 1 ∧
      (∀ X ∈ W, ∀ x ∈ X, x.2 ≠ 1 ∧ s ≤ x.1.val ∧ x.1.val ≤ e) ∧
      (∀ X ∈ W, ∀ x ∈ X, x.1.val = s → x.2 = r) := by
  have hr' : r = 0 ∨ r = 2 := by
    have h := r.isLt
    have h1 : r.val ≠ 1 := fun h' => hr (Fin.ext h')
    rcases (by omega : r.val = 0 ∨ r.val = 2) with h0 | h2
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (Fin.ext h2)
  rcases hr' with rfl | rfl
  · obtain ⟨W, hW, hlen, hsub⟩ := comb_walk_a s e hse hek A B hAB
    exact ⟨W, hW, hlen, fun X hX x hx => (comb_state_prop (hsub X hX hx)).1,
      fun X hX x hx hs => (comb_state_prop (hsub X hX hx)).2 hs⟩
  · obtain ⟨hdis, hU, -⟩ := hAB
    have hAB' : IsSplit (sigmaAC '' A) (sigmaAC '' B) (rowSeg 0 s e) :=
      ⟨(Set.disjoint_image_iff sigma_injective).2 hdis, by rw [← Set.image_union, hU, sigma_rowSeg],
        isAntichainSet_row 0 _ fun x hx => hx.1⟩
    obtain ⟨W, hW, hlen, hsub⟩ := comb_walk_a s e hse hek _ _ hAB'
    refine ⟨W.map (sigmaAC '' ·), ⟨isWalk_map sigmaAC sigma_injective sigma_comp_iff W hW.1, ?_, ?_⟩,
      by rw [List.length_map]; exact hlen, ?_, ?_⟩
    · rw [List.head?_map, hW.2.1, Option.map_some, sigma_image_image]
    · rw [List.getLast?_map, hW.2.2, Option.map_some, sigma_image_image]
    · intro X hX x hx
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨⟨h1, h2, h3⟩, -⟩ := comb_state_prop (hsub Y hY hy)
      refine ⟨fun h => h1 (Fin.ext ?_), h2, h3⟩
      have hv := sigma_snd_val y
      have := y.2.isLt
      rw [h] at hv
      simp at hv
      show y.2.val = 1
      omega
    · intro X hX x hx hs
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      obtain ⟨y, hy, rfl⟩ := hx
      have hy0 := (comb_state_prop (hsub Y hY hy)).2 hs
      refine Fin.ext ?_
      rw [sigma_snd_val, hy0]
      rfl

end CombCor

end LeeDiam.S4

