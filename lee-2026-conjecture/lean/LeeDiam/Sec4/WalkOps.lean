/-
LeeDiam/Sec4/WalkOps.lean — Section 4 helpers: walks one after the other (Lemma 4.3, l. 45), adding an element to a
walk (Lemma 4.4, l. 47-55), tame walks (Definition 4.7, l. 77, and the remarks after it, l. 79), and the number of
helpers (after Lemma 4.5, l. 62) — paper 004, short v0.60, sec_chain.tex.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Sec4.Words

namespace LeeDiam.S4

open Band

/-! ### Small facts on sets and lists -/

section SetFacts

variable {P : Type}

theorem symmDiff_union_right_of_disjoint {X Y C : Set P} (hX : Disjoint X C) (hY : Disjoint Y C) :
    symmDiff (X ∪ C) (Y ∪ C) = symmDiff X Y := by
  ext z
  have h1 : z ∈ X → z ∉ C := fun hz => Set.disjoint_left.1 hX hz
  have h2 : z ∈ Y → z ∉ C := fun hz => Set.disjoint_left.1 hY hz
  simp only [Set.mem_symmDiff, Set.mem_union]
  tauto

theorem symmDiff_union_left_of_disjoint {X Y C : Set P} (hX : Disjoint C X) (hY : Disjoint C Y) :
    symmDiff (C ∪ X) (C ∪ Y) = symmDiff X Y := by
  rw [Set.union_comm C X, Set.union_comm C Y]
  exact symmDiff_union_right_of_disjoint hX.symm hY.symm

theorem symmDiff_insert_insert {X Y : Set P} {y : P} (hX : y ∉ X) (hY : y ∉ Y) :
    symmDiff (insert y X) (insert y Y) = symmDiff X Y := by
  ext z
  simp only [Set.mem_symmDiff, Set.mem_insert_iff]
  by_cases hz : z = y
  · subst hz
    tauto
  · tauto

theorem symmDiff_insert_left {X Y : Set P} {y : P} (hX : y ∉ X) (hY : y ∉ Y) :
    symmDiff (insert y X) Y = insert y (symmDiff X Y) := by
  ext z
  simp only [Set.mem_symmDiff, Set.mem_insert_iff]
  by_cases hz : z = y
  · subst hz
    tauto
  · tauto

theorem symmDiff_insert_right {X Y : Set P} {y : P} (hX : y ∉ X) (hY : y ∉ Y) :
    symmDiff X (insert y Y) = insert y (symmDiff X Y) := by
  rw [symmDiff_comm, symmDiff_insert_left hY hX, symmDiff_comm]

theorem getD_of_lt {α : Type} (L : List α) (d : α) {i : ℕ} (h : i < L.length) : L.getD i d = L[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem three_getElem? {α : Type} {u v w : α} {p q r t : ℕ} (ht : t < p + q + r) :
    (List.replicate p u ++ List.replicate q v ++ List.replicate r w)[t]? =
      some (if t < p then u else if t < p + q then v else w) := by
  simp only [List.getElem?_append, List.getElem?_replicate, List.length_append, List.length_replicate]
  split_ifs <;> first | rfl | omega

variable [PartialOrder P]

theorem isAntichainSet_insert {X : Set P} {y : P} (hX : IsAntichainSet X) (hy : ∀ z ∈ X, ¬ Comp y z) :
    IsAntichainSet (insert y X) := by
  rw [Set.insert_eq]
  refine isAntichainSet_union (isAntichainSet_iff_comp.2 ?_) hX ?_
  · intro u hu v hv
    obtain rfl : u = y := hu
    obtain rfl : v = u := hv
    exact fun h => comp_ne h rfl
  · intro u hu z hz
    obtain rfl : u = y := hu
    exact hy z hz

end SetFacts

/-! ### Lemma 4.3, l. 45: two walks one after the other, on columns at distance at least two -/

section Sequential

variable {k : ℕ}

theorem walk_sequential (W₁ W₂ : List (Set (Band k))) (A₁ B₁ A₂ B₂ : Set (Band k))
    (h₁ : IsWalkFromTo W₁ A₁ B₁) (h₂ : IsWalkFromTo W₂ A₂ B₂)
    (hfar : ∀ X ∈ W₁, ∀ Y ∈ W₂, ∀ x ∈ X, ∀ y ∈ Y, x.1.val + 2 ≤ y.1.val ∨ y.1.val + 2 ≤ x.1.val) :
    IsWalkFromTo (W₁.map (· ∪ A₂) ++ W₂.tail.map (B₁ ∪ ·)) (A₁ ∪ A₂) (B₁ ∪ B₂) ∧
      (W₁.map (· ∪ A₂) ++ W₂.tail.map (B₁ ∪ ·)).length - 1 = (W₁.length - 1) + (W₂.length - 1) := by
  obtain ⟨⟨hne₁, ha₁, hc₁⟩, hh₁, hl₁⟩ := h₁
  obtain ⟨⟨hne₂, ha₂, hc₂⟩, hh₂, hl₂⟩ := h₂
  have hA₂ : A₂ ∈ W₂ := List.mem_of_mem_head? hh₂
  have hB₁ : B₁ ∈ W₁ := List.mem_of_mem_getLast? hl₁
  have hdisj : ∀ X ∈ W₁, ∀ Y ∈ W₂, Disjoint X Y := by
    intro X hX Y hY
    rw [Set.disjoint_left]
    intro z hzX hzY
    have := hfar X hX Y hY z hzX z hzY
    omega
  have hinc : ∀ X ∈ W₁, ∀ Y ∈ W₂, ∀ x ∈ X, ∀ y ∈ Y, ¬ Comp x y :=
    fun X hX Y hY x hx y hy => not_comp_of_far (hfar X hX Y hY x hx y hy)
  have hlen₁ : 1 ≤ W₁.length := List.length_pos_of_ne_nil hne₁
  obtain ⟨T, rfl⟩ : ∃ T, W₂ = A₂ :: T := by
    cases W₂ with
    | nil => exact absurd rfl hne₂
    | cons Y T =>
      simp only [List.head?_cons, Option.some.injEq] at hh₂
      exact ⟨T, by rw [hh₂]⟩
  simp only [List.tail_cons]
  refine ⟨⟨⟨by simp [hne₁], ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · intro Z hZ
    rcases List.mem_append.1 hZ with hZ | hZ
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hZ
      exact isAntichainSet_union (ha₁ X hX) (ha₂ A₂ hA₂) (fun x hx y hy => hinc X hX A₂ hA₂ x hx y hy)
    · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hZ
      have hY' : Y ∈ A₂ :: T := List.mem_cons_of_mem _ hY
      exact isAntichainSet_union (ha₁ B₁ hB₁) (ha₂ Y hY') (fun x hx y hy => hinc B₁ hB₁ Y hY' x hx y hy)
  · rw [List.isChain_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.isChain_iff_getElem] at hc₁ ⊢
      intro i hi
      simp only [List.length_map] at hi
      simp only [List.getElem_map]
      rw [symmDiff_union_right_of_disjoint (hdisj _ (List.getElem_mem _) _ hA₂)
        (hdisj _ (List.getElem_mem _) _ hA₂)]
      exact hc₁ i hi
    · have hcT : T.IsChain (fun X Y => IsConnSet (symmDiff X Y)) := hc₂.tail
      rw [List.isChain_iff_getElem] at hcT ⊢
      intro i hi
      simp only [List.length_map] at hi
      simp only [List.getElem_map]
      rw [symmDiff_union_left_of_disjoint (hdisj _ hB₁ _ (List.mem_cons_of_mem _ (List.getElem_mem _)))
        (hdisj _ hB₁ _ (List.mem_cons_of_mem _ (List.getElem_mem _)))]
      exact hcT i hi
    · intro X hX Y hY
      rw [List.getLast?_map, hl₁] at hX
      cases T with
      | nil => simp at hY
      | cons Y₁ T' =>
        simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hX
        simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hY
        subst hX
        subst hY
        have hY₁ : Y₁ ∈ A₂ :: Y₁ :: T' := by simp
        rw [symmDiff_union_left_of_disjoint (hdisj _ hB₁ _ hA₂) (hdisj _ hB₁ _ hY₁)]
        exact (List.isChain_cons_cons.1 hc₂).1
  · simp [List.head?_append, hh₁]
  · cases T with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl₂
      subst hl₂
      simp [List.getLast?_map, hl₁]
    | cons Y₁ T' =>
      have hl₂' : (Y₁ :: T').getLast? = some B₂ := by
        rw [List.getLast?_cons_cons] at hl₂
        exact hl₂
      rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_map, hl₂']
      rfl
  · simp only [List.length_append, List.length_map, List.length_cons]
    omega

end Sequential

/-! ### Lemma 4.4, l. 47-55: adding an element to the states of a walk -/

section Ride

variable {P : Type} [PartialOrder P]

/-- Inserting `y` into the states with index in `S` keeps a walk a walk, provided `y` is incomparable to those
states and, wherever `S` changes, the difference of the move has an element comparable to `y`. -/
theorem walk_insert (W : List (Set P)) (hW : IsWalk W) (y : P) (hy : ∀ X ∈ W, y ∉ X) (S : ℕ → Prop)
    [DecidablePred S] (hS : ∀ t (ht : t < W.length), S t → ∀ z ∈ W[t], ¬ Comp y z)
    (hbd : ∀ i (hi : i + 1 < W.length), (S i ↔ ¬ S (i + 1)) → ∃ z ∈ symmDiff W[i] W[i + 1], Comp y z) :
    IsWalk (W.mapIdx fun t X => if S t then insert y X else X) := by
  obtain ⟨hne, ha, hc⟩ := hW
  refine ⟨by simpa using hne, ?_, ?_⟩
  · intro Z hZ
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hZ
    have ht' : t < W.length := by simpa using ht
    simp only [List.getElem_mapIdx]
    split_ifs with hSt
    · exact isAntichainSet_insert (ha _ (List.getElem_mem ht')) (hS t ht' hSt)
    · exact ha _ (List.getElem_mem ht')
  · rw [List.isChain_iff_getElem] at hc ⊢
    intro i hi
    have hi' : i + 1 < W.length := by simpa using hi
    simp only [List.getElem_mapIdx]
    have hyi := hy _ (List.getElem_mem (Nat.lt_of_succ_lt hi'))
    have hyj := hy _ (List.getElem_mem hi')
    by_cases h1 : S i <;> by_cases h2 : S (i + 1)
    · rw [ite_eq_left h1, ite_eq_left h2, symmDiff_insert_insert hyi hyj]
      exact hc i hi'
    · rw [ite_eq_left h1, ite_eq_right h2, symmDiff_insert_left hyi hyj]
      obtain ⟨z, hz, hcz⟩ := hbd i hi' (by tauto)
      exact isConnSet_insert (hc i hi') hz hcz
    · rw [ite_eq_right h1, ite_eq_left h2, symmDiff_insert_right hyi hyj]
      obtain ⟨z, hz, hcz⟩ := hbd i hi' (by tauto)
      exact isConnSet_insert (hc i hi') hz hcz
    · rw [ite_eq_right h1, ite_eq_right h2]
      exact hc i hi'

theorem ride_prefix (W : List (Set P)) (hW : IsWalk W) (y : P) (hy : ∀ X ∈ W, y ∉ X) (μ : ℕ)
    (hμy : ∃ z ∈ W.getD μ ∅, Comp y z) (hmin : ∀ t < μ, ∀ z ∈ W.getD t ∅, ¬ Comp y z) :
    IsWalk (W.mapIdx fun t X => if t < μ then insert y X else X) ∧
      (W.mapIdx fun t X => if t < μ then insert y X else X).length = W.length := by
  refine ⟨walk_insert W hW y hy (fun t => t < μ) ?_ ?_, by simp⟩
  · intro t ht hSt z hz
    exact hmin t hSt z (by rwa [getD_of_lt _ _ ht])
  · intro i hi hiff
    have hiμ : i + 1 = μ := by omega
    obtain ⟨z, hz, hcz⟩ := hμy
    have hzμ : z ∈ W[i + 1] := by
      rw [← hiμ, getD_of_lt _ _ hi] at hz
      exact hz
    have hzi : z ∉ W[i] := fun h => hmin i (by omega) z (by rwa [getD_of_lt _ _ (by omega)]) hcz
    exact ⟨z, Or.inr ⟨hzμ, hzi⟩, hcz⟩

theorem ride_suffix (W : List (Set P)) (hW : IsWalk W) (y : P) (hy : ∀ X ∈ W, y ∉ X) (ν : ℕ) (hν1 : 1 ≤ ν)
    (hνy : ∃ z ∈ W.getD (ν - 1) ∅, Comp y z) (hmax : ∀ t, ν ≤ t → ∀ z ∈ W.getD t ∅, ¬ Comp y z) :
    IsWalk (W.mapIdx fun t X => if ν ≤ t then insert y X else X) ∧
      (W.mapIdx fun t X => if ν ≤ t then insert y X else X).length = W.length := by
  refine ⟨walk_insert W hW y hy (fun t => ν ≤ t) ?_ ?_, by simp⟩
  · intro t ht hSt z hz
    exact hmax t hSt z (by rwa [getD_of_lt _ _ ht])
  · intro i hi hiff
    have hiν : i + 1 = ν := by omega
    obtain ⟨z, hz, hcz⟩ := hνy
    have hzi : z ∈ W[i] := by
      rw [show ν - 1 = i by omega, getD_of_lt _ _ (by omega)] at hz
      exact hz
    have hzj : z ∉ W[i + 1] := fun h => hmax (i + 1) (by omega) z (by rwa [getD_of_lt _ _ hi]) hcz
    exact ⟨z, Or.inl ⟨hzi, hzj⟩, hcz⟩

end Ride

/-! ### Tame walks (Definition 4.7, l. 77-79) -/

section Tame

variable {k : ℕ}

theorem c_injective : Function.Injective (c (k := k)) := fun _ _ h => congrArg Prod.fst h

theorem mem_iff_outerAt {X : Set (Band k)} {e : Fin k} {h : Band k} (h1 : h.1 = e) (h2 : h.2 ≠ 1)
    (hX : outerAt X e = none ∨ outerAt X e = some h) : h ∈ X ↔ outerAt X e = some h := by
  have hh : h = a e ∨ h = c e := by
    have hlt := h.2.isLt
    have h2' : h.2.val ≠ 1 := fun hv => h2 (Fin.ext hv)
    rcases (by omega : h.2.val = 0 ∨ h.2.val = 2) with hv | hv
    · exact Or.inl (Prod.ext h1 (Fin.ext hv))
    · exact Or.inr (Prod.ext h1 (Fin.ext hv))
  by_cases ha : a e ∈ X <;> by_cases hc : c e ∈ X
  · rw [outerAt_of_a_mem ha] at hX ⊢
    rcases hh with rfl | rfl
    · simp [ha]
    · simp [a_ne_c] at hX
  · rw [outerAt_of_a_mem ha] at hX ⊢
    rcases hh with rfl | rfl
    · simp [ha]
    · simp [a_ne_c] at hX
  · rw [outerAt_of_c_mem ha hc] at hX ⊢
    rcases hh with rfl | rfl
    · simp [ha, (a_ne_c e e).symm]
    · simp [hc]
  · rw [outerAt_none ha hc] at hX ⊢
    rcases hh with rfl | rfl <;> simp [ha, hc]

theorem tame_trace {W : List (Set (Band k))} {i : Fin k} {h : Band k} (hT : IsTameAt W i h) :
    ∃ p q r, 1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧
      W.map (outerAt · i) = List.replicate p none ++ List.replicate q (some h) ++ List.replicate r none :=
  (destutter_eq_three_iff (u := (none : Option (Band k))) (v := some h) (w := none) (by simp) (by simp) _).1
    hT.2.2.2

theorem tame_arrive_depart (W : List (Set (Band k))) (i : Fin k) (h : Band k) (hT : IsTameAt W i h) :
    ∃ μ ν : ℕ, 1 ≤ μ ∧ μ < ν ∧ ν ≤ W.length - 1 ∧ ∀ t < W.length, (h ∈ W.getD t ∅ ↔ μ ≤ t ∧ t < ν) := by
  obtain ⟨p, q, r, hp, hq, hr, hL⟩ := tame_trace hT
  have hlen : W.length = p + q + r := by
    have := congrArg List.length hL
    simp at this
    omega
  refine ⟨p, p + q, hp, by omega, by omega, fun t ht => ?_⟩
  have hget : (W.map (outerAt · i))[t]? = some (outerAt (W.getD t ∅) i) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem ht, getD_of_lt _ _ ht]
    try rfl
  rw [hL, three_getElem? (by omega)] at hget
  have hval := Option.some_inj.1 hget
  have hX : outerAt (W.getD t ∅) i = none ∨ outerAt (W.getD t ∅) i = some h := by
    rw [← hval]
    split_ifs <;> simp
  rw [mem_iff_outerAt hT.2.1 hT.2.2.1 hX, ← hval]
  split_ifs with h₁ h₂ <;> simp <;> omega

theorem tame_reverse {W : List (Set (Band k))} {i : Fin k} {h : Band k} (hT : IsTameAt W i h) :
    IsTameAt W.reverse i h := by
  obtain ⟨p, q, r, hp, hq, hr, hL⟩ := tame_trace hT
  obtain ⟨hcols, hh1, hh2, -⟩ := hT
  refine ⟨fun X hX x hx => hcols X (List.mem_reverse.1 hX) x hx, hh1, hh2, ?_⟩
  unfold outerTrace
  rw [List.map_reverse, hL]
  refine (destutter_eq_three_iff (by simp) (by simp) _).2 ⟨r, q, p, hr, hq, hp, ?_⟩
  simp [List.reverse_append, List.reverse_replicate]

theorem sigma_a (e : Fin k) : sigmaAC (a e) = c e := Prod.ext rfl rfl

theorem sigma_c (e : Fin k) : sigmaAC (c e) = a e := Prod.ext rfl rfl

theorem outerAt_sigma {X : Set (Band k)} (hX : IsAntichainSet X) (e : Fin k) :
    outerAt (sigmaAC '' X) e = (outerAt X e).map sigmaAC := by
  have hma : a e ∈ sigmaAC '' X ↔ c e ∈ X := by rw [sigma_mem_image_iff, sigma_a]
  have hmc : c e ∈ sigmaAC '' X ↔ a e ∈ X := by rw [sigma_mem_image_iff, sigma_c]
  by_cases ha : a e ∈ X <;> by_cases hc : c e ∈ X
  · exact absurd (antichain_col hX ha hc rfl) (a_ne_c e e)
  · rw [outerAt_of_a_mem ha, outerAt_of_c_mem (by rwa [hma]) (by rwa [hmc])]
    simp [sigma_a]
  · rw [outerAt_of_c_mem ha hc, outerAt_of_a_mem (by rwa [hma])]
    simp [sigma_c]
  · rw [outerAt_none ha hc, outerAt_none (by rwa [hma]) (by rwa [hmc])]
    rfl

theorem tame_sigma {W : List (Set (Band k))} (hW : IsWalk W) {i : Fin k} {h : Band k} (hT : IsTameAt W i h) :
    IsTameAt (W.map (sigmaAC '' ·)) i (sigmaAC h) := by
  obtain ⟨hcols, hh1, hh2, htr⟩ := hT
  refine ⟨?_, hh1, ?_, ?_⟩
  · intro X hX x hx
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    obtain ⟨y, hy, rfl⟩ := hx
    exact hcols Y hY y hy
  · intro h'
    have e1 := sigma_snd_val h
    rw [h', Fin.val_one] at e1
    have hlt := h.2.isLt
    exact hh2 (Fin.ext (by rw [Fin.val_one]; omega))
  · unfold outerTrace at htr ⊢
    have hmap : (W.map (sigmaAC '' ·)).map (outerAt · i) = (W.map (outerAt · i)).map (Option.map sigmaAC) := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro X hX
      exact outerAt_sigma (hW.2.1 X hX) i
    rw [hmap, ← List.map_destutter_ne _ (Option.map_injective sigma_injective), htr]
    rfl

theorem tame_symm (W : List (Set (Band k))) (hW : IsWalk W) (i : Fin k) (h : Band k) (hT : IsTameAt W i h) :
    IsTameAt W.reverse i h ∧ IsTameAt (W.map (sigmaAC '' ·)) i (sigmaAC h) ∧
      ∀ A B : Set (Band k), IsWalkFromTo W A B → (∀ x ∈ A ∪ B, x.2 = 1) →
        IsWalkFromTo (W.map (sigmaAC '' ·)) A B := by
  refine ⟨tame_reverse hT, tame_sigma hW hT, fun A B hAB hmid => ?_⟩
  obtain ⟨hw, hh, hl⟩ := hAB
  refine ⟨isWalk_map _ sigma_injective sigma_comp_iff W hw, ?_, ?_⟩
  · rw [List.head?_map, hh]
    simp [sigma_image_mid (fun x hx => hmid x (Or.inl hx))]
  · rw [List.getLast?_map, hl]
    simp [sigma_image_mid (fun x hx => hmid x (Or.inr hx))]

/-! ### The number of helpers (after Lemma 4.5, l. 62) -/

theorem helper_count (par s e : ℕ) (hpar : par ≤ 1) (hse : s ≤ e) (hek : e < k) :
    (helperSet par s e : Set (Band k)).ncard = (e - s + 2 - par) / 2 := by
  have hS : ∀ t, t ∈ (Finset.range ((e - s + 2 - par) / 2)).image (fun m => s + 2 * m + par) ↔
      s ≤ t ∧ t ≤ e ∧ (t - s) % 2 = par := by
    intro t
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨m, hm, rfl⟩
      omega
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(t - s) / 2, by omega, by omega⟩
  have hset : (helperSet par s e : Set (Band k)) =
      c '' (Fin.val ⁻¹' (((Finset.range ((e - s + 2 - par) / 2)).image (fun m => s + 2 * m + par) :
        Finset ℕ) : Set ℕ)) := by
    ext x
    simp only [helperSet, Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage, Finset.mem_coe, hS]
    constructor
    · rintro ⟨h2, h3, h4, h5⟩
      exact ⟨x.1, ⟨h3, h4, h5⟩, Prod.ext rfl h2.symm⟩
    · rintro ⟨t, ⟨h3, h4, h5⟩, rfl⟩
      exact ⟨rfl, h3, h4, h5⟩
  rw [hset, Set.ncard_image_of_injective _ c_injective,
    Set.ncard_preimage_of_injective_subset_range Fin.val_injective, Set.ncard_coe_finset,
    Finset.card_image_of_injective _ (by intro m m' hm; simp only at hm; omega), Finset.card_range]
  intro t ht
  rw [Finset.mem_coe, hS] at ht
  exact ⟨⟨t, by omega⟩, rfl⟩

end Tame

end LeeDiam.S4
