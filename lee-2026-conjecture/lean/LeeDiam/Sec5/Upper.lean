/-
LeeDiam/Sec5/Upper.lean — Section 5: Lemma 5.1 (Pair lemma) and Theorem 1.5 (sec_reverse.tex l. 6-28).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Vertices
import LeeDiam.Defs.Walks
import LeeDiam.Cited.Lee26
import LeeDiam.Bridge.Graphs
import LeeDiam.Sec2.Walks
import LeeDiam.Sec4.BandOrder

namespace LeeDiam

open Finset

namespace S5

variable {P : Type} [Fintype P] [PartialOrder P]

/-! ### Distances between antichains -/

theorem dC_triangle (A B C : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B) (hC : IsAntichainSet C) :
    dC A C hA hC ≤ dC A B hA hB + dC B C hB hC := by
  rw [dC_eq, dC_eq, dC_eq]
  exact SimpleGraph.edist_triangle

theorem dC_comm (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B) : dC A B hA hB = dC B A hB hA := by
  rw [dC_eq, dC_eq]
  exact SimpleGraph.edist_comm

/-- Equal or adjacent antichains are at distance at most one. -/
theorem dC_le_one (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B)
    (h : A = B ∨ IsConnSet (symmDiff A B)) : dC A B hA hB ≤ 1 := by
  rw [dC_eq]
  rcases h with rfl | h
  · rw [SimpleGraph.edist_self]
    exact zero_le_one
  · exact ((SimpleGraph.edist_eq_one_iff_adj).2 h).le

/-- If `X ∪ Y` is an antichain, exchanging the elements of `X △ Y` one at a time gives `d_C(X, Y) ≤ |X △ Y|`. -/
theorem dC_le_ncard (Y : Set P) (hY : IsAntichainSet Y) :
    ∀ n : ℕ, ∀ X : Set P, ∀ hX : IsAntichainSet X, IsAntichainSet (X ∪ Y) → (symmDiff X Y).ncard ≤ n →
      dC X Y hX hY ≤ n := by
  intro n
  induction n with
  | zero =>
    intro X hX _ hn
    have h0 : symmDiff X Y = ∅ := (Set.ncard_eq_zero).1 (by omega)
    have hXY : X = Y := symmDiff_eq_bot.1 h0
    subst hXY
    rw [dC_eq, SimpleGraph.edist_self]
    rfl
  | succ n ih =>
    intro X hX hXY hn
    by_cases hxy : X = Y
    · subst hxy
      rw [dC_eq, SimpleGraph.edist_self]
      exact zero_le
    obtain ⟨z, hz⟩ : (symmDiff X Y).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hxy (symmDiff_eq_bot.1 h)
    have hzXY : z ∈ X ∪ Y := by
      rw [Set.mem_symmDiff] at hz
      rcases hz with hz | hz
      · exact Or.inl hz.1
      · exact Or.inr hz.1
    have hsub : symmDiff X {z} ⊆ X ∪ Y := by
      intro x hx
      rw [Set.mem_symmDiff, Set.mem_singleton_iff] at hx
      rcases hx with ⟨hx, -⟩ | ⟨rfl, -⟩
      · exact Or.inl hx
      · exact hzXY
    have hX' : IsAntichainSet (symmDiff X {z}) := hXY.subset hsub
    have hX'Y : IsAntichainSet (symmDiff X {z} ∪ Y) :=
      hXY.subset (Set.union_subset hsub Set.subset_union_right)
    have hset : symmDiff (symmDiff X {z}) Y = symmDiff X Y \ {z} := by
      ext x
      rw [Set.mem_symmDiff] at hz
      simp only [Set.mem_symmDiff, Set.mem_sdiff, Set.mem_singleton_iff]
      by_cases hxz : x = z
      · subst hxz
        tauto
      · tauto
    have hcard : (symmDiff (symmDiff X {z}) Y).ncard ≤ n := by
      rw [hset, Set.ncard_sdiff_singleton_of_mem hz]
      omega
    have hstep : dC X (symmDiff X {z}) hX hX' ≤ 1 := by
      refine dC_le_one _ _ _ _ (Or.inr ?_)
      rw [symmDiff_symmDiff_cancel_left]
      exact S4.isConnSet_singleton z
    calc dC X Y hX hY ≤ dC X (symmDiff X {z}) hX hX' + dC (symmDiff X {z}) Y hX' hY := dC_triangle _ _ _ _ _ _
      _ ≤ 1 + n := add_le_add hstep (ih _ hX' hX'Y hcard)
      _ = ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring

/-! ### Lemma 5.1 (Pair lemma) -/

/-- Lemma 5.1, sec_reverse l. 9-16. -/
theorem pair_lemma (h : orderDiam P ≤ 2) (p q r : P) (hpq : p ≠ q) (hpq' : ¬ Comp p q) (hrp : r ≠ p) (hrq : r ≠ q)
    (hr1 : ¬ Comp r p) (hr2 : ¬ Comp r q) : (∃ c, c ≤ p ∧ c ≤ q) ∨ (∃ c, p ≤ c ∧ q ≤ c) := by
  by_contra hno
  push Not at hno
  obtain ⟨hlow, hup⟩ := hno
  have npq : ¬ p ≤ q := fun hle => hpq' (Or.inl (lt_of_le_of_ne hle hpq))
  have nqp : ¬ q ≤ p := fun hle => hpq' (Or.inr (lt_of_le_of_ne hle (Ne.symm hpq)))
  have nrp : ¬ r ≤ p := fun hle => hr1 (Or.inl (lt_of_le_of_ne hle hrp))
  have npr : ¬ p ≤ r := fun hle => hr1 (Or.inr (lt_of_le_of_ne hle (Ne.symm hrp)))
  have nrq : ¬ r ≤ q := fun hle => hr2 (Or.inl (lt_of_le_of_ne hle hrq))
  have nqr : ¬ q ≤ r := fun hle => hr2 (Or.inr (lt_of_le_of_ne hle (Ne.symm hrq)))
  -- the ideals `I = ↓p ∪ ↓q` and `J = P \ (↑p ∪ ↑q)`
  set I : Set P := {x | x ≤ p ∨ x ≤ q} with hIdef
  set J : Set P := {x | ¬ p ≤ x ∧ ¬ q ≤ x} with hJdef
  have hI : IsIdeal I := fun a b hba ha => ha.imp hba.trans hba.trans
  have hJ : IsIdeal J := fun a b hba ha => ⟨fun h' => ha.1 (h'.trans hba), fun h' => ha.2 (h'.trans hba)⟩
  have hpI : p ∈ I := Or.inl le_rfl
  have hqI : q ∈ I := Or.inr le_rfl
  have hpJ : p ∉ J := fun h' => h'.1 le_rfl
  have hqJ : q ∉ J := fun h' => h'.2 le_rfl
  have hrJ : r ∈ J := ⟨npr, nqr⟩
  have hrI : r ∉ I := fun h' => h'.elim nrp nrq
  have hd : dO I J hI hJ ≤ ((2 : ℕ) : ℕ∞) := by
    have := (orderDiam_le_iff 2).1 h I J hI hJ
    exact_mod_cast this
  obtain ⟨L, hhead, hlast, hlen, hchain⟩ := (dO_le_iff I J hI hJ 2).1 hd
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, L⟩⟩⟩⟩
  · simp at hhead
  · simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at hhead hlast
    have hIJ : I = J := congrArg Subtype.val (hhead.symm.trans hlast)
    exact hrI (hIJ ▸ hrJ)
  · simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons, List.getLast?_singleton] at hhead hlast
    subst hhead hlast
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hchain
    rcases hchain with ⟨hIJ, -⟩ | ⟨hJI, -⟩
    · exact hpJ (hIJ hpI)
    · exact hrI (hJI hrJ)
  · simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons, List.getLast?_singleton] at hhead hlast
    subst hhead hlast
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hchain
    obtain ⟨h1, h2⟩ := hchain
    obtain ⟨K, hK⟩ := b
    change (I ⊆ K ∧ IsConnSet (K \ I)) ∨ (K ⊆ I ∧ IsConnSet (I \ K)) at h1
    change (K ⊆ J ∧ IsConnSet (J \ K)) ∨ (J ⊆ K ∧ IsConnSet (K \ J)) at h2
    rcases h1 with ⟨hIK, -⟩ | ⟨hKI, hc1⟩ <;> rcases h2 with ⟨hKJ, -⟩ | ⟨hJK, hc2⟩
    · exact hpJ (hKJ (hIK hpI))
    · -- `K ⊇ I ∪ J`: `K \ J` is connected and contains `p, q`; cut at `↑p`
      obtain ⟨u, hu, v, hv, hpu, hpv, huv⟩ :=
        S4.isConnSet_cross hc2 (fun x => p ≤ x) ⟨hIK hpI, hpJ⟩ ⟨hIK hqI, hqJ⟩ le_rfl npq
      have hqv : q ≤ v := by
        by_contra hqv
        exact hv.2 ⟨hpv, hqv⟩
      rcases huv with huv | huv
      · exact hup v (hpu.trans huv.le) hqv
      · exact hup u hpu (hqv.trans huv.le)
    · -- `K ⊆ I ∩ J`: `I \ K` is connected and contains `p, q`; cut at `↓p`
      obtain ⟨u, hu, v, hv, hup', hvp, huv⟩ :=
        S4.isConnSet_cross hc1 (fun x => x ≤ p) ⟨hpI, fun h' => hpJ (hKJ h')⟩ ⟨hqI, fun h' => hqJ (hKJ h')⟩
          le_rfl nqp
      have hvq : v ≤ q := hv.1.resolve_left hvp
      rcases huv with huv | huv
      · exact hlow u hup' (huv.le.trans hvq)
      · exact hlow v (huv.le.trans hup') hvq
    · exact hrI (hKI (hJK hrJ))
  · simp at hlen
    omega

/-! ### Theorem 1.5 -/

omit [Fintype P] in
/-- `U' = (U \ U_t) ∪ {t}` is an antichain: `t` is maximal and lies above no element of `U \ U_t`. -/
theorem U'_anti (A B : Set P) (t : P) (htmax : ∀ y, t ≤ y → y = t) (hU : IsAntichainSet (A ∪ B)) :
    IsAntichainSet (((A ∪ B) \ {x | x ≤ t}) ∪ {t}) := by
  intro x hx y hy hxy hle
  rcases hx with ⟨hxU, hxt⟩ | rfl <;> rcases hy with ⟨hyU, hyt⟩ | rfl
  · exact hU hxU hyU hxy hle
  · exact hxt hle
  · exact hyt (le_of_eq (htmax y hle))
  · exact hxy rfl

omit [Fintype P] in
/-- `S ⊆ U`: `S` and `S_t = (S \ U_t) ∪ {t}` are equal or adjacent. -/
theorem step_t (A B : Set P) (t : P) (hU : IsAntichainSet (A ∪ B)) (S : Set P) (hS : S ⊆ A ∪ B) :
    S = (S \ {x | x ≤ t}) ∪ {t} ∨ IsConnSet (symmDiff S ((S \ {x | x ≤ t}) ∪ {t})) := by
  by_cases ht : t ∈ S
  · left
    ext x
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_cases hxt : x ≤ t
      · right
        by_contra hne
        exact hU (hS hx) (hS ht) hne hxt
      · exact Or.inl ⟨hx, hxt⟩
    · rintro (⟨hx, -⟩ | rfl)
      · exact hx
      · exact ht
  · right
    have htD : t ∈ symmDiff S ((S \ {x | x ≤ t}) ∪ {t}) := Or.inr ⟨Or.inr rfl, ht⟩
    refine S4.isConnSet_of_rtg htD (fun y hy => ?_)
    have hyt : y = t ∨ y < t := by
      rcases hy with ⟨hyS, hyS'⟩ | ⟨hyS', hyS⟩
      · right
        have hle : y ≤ t := by
          by_contra hle
          exact hyS' (Or.inl ⟨hyS, hle⟩)
        refine lt_of_le_of_ne hle ?_
        rintro rfl
        exact ht hyS
      · left
        rcases hyS' with ⟨hyS', -⟩ | hyt
        · exact absurd hyS' hyS
        · exact hyt
    rcases hyt with rfl | hyt
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨htD, hy, Or.inr hyt⟩

/-- The walk on a split (proof of Theorem 1.5, sec_reverse l. 19-27): `d_C(A, B) ≤ 4`. -/
theorem split_bound (h : orderDiam P ≤ 2) (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B)
    (hAB : IsSplit A B (A ∪ B)) : dC A B hA hB ≤ 4 := by
  have hU : IsAntichainSet (A ∪ B) := hAB.2.2
  by_cases hU0 : A ∪ B = ∅
  · have hAe : A = B := by
      rw [Set.union_empty_iff] at hU0
      rw [hU0.1, hU0.2]
    exact (dC_le_one A B hA hB (Or.inl hAe)).trans (by norm_num)
  obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.2 hU0
  obtain ⟨t, -, htm⟩ := Finite.exists_le_maximal (p := fun _ : P => True) (a := u) trivial
  have htmax : ∀ y, t ≤ y → y = t := fun y hy => le_antisymm (htm.2 trivial hy) hy
  set Ut : Set P := {x | x ≤ t} with hUt
  set U' : Set P := ((A ∪ B) \ Ut) ∪ {t} with hU'
  have hU'a : IsAntichainSet U' := U'_anti A B t htmax hU
  have hAt_sub : (A \ Ut) ∪ {t} ⊆ U' :=
    Set.union_subset_union_left _ (Set.sdiff_subset_sdiff_left Set.subset_union_left)
  have hBt_sub : (B \ Ut) ∪ {t} ⊆ U' :=
    Set.union_subset_union_left _ (Set.sdiff_subset_sdiff_left Set.subset_union_right)
  have hAt : IsAntichainSet ((A \ Ut) ∪ {t}) := hU'a.subset hAt_sub
  have hBt : IsAntichainSet ((B \ Ut) ∪ {t}) := hU'a.subset hBt_sub
  have h1 : dC A ((A \ Ut) ∪ {t}) hA hAt ≤ 1 :=
    dC_le_one _ _ _ _ (step_t A B t hU A Set.subset_union_left)
  have h3 : dC ((B \ Ut) ∪ {t}) B hBt hB ≤ 1 := by
    rw [dC_comm]
    exact dC_le_one _ _ _ _ (step_t A B t hU B Set.subset_union_right)
  have h2 : dC ((A \ Ut) ∪ {t}) ((B \ Ut) ∪ {t}) hAt hBt ≤ 2 := by
    have hdiff : symmDiff ((A \ Ut) ∪ {t}) ((B \ Ut) ∪ {t}) ⊆ (A ∪ B) \ Ut := by
      intro x hx
      rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
      · rcases hx1 with hx1 | hx1
        · exact ⟨Or.inl hx1.1, hx1.2⟩
        · exact absurd (Or.inr hx1) hx2
      · rcases hx1 with hx1 | hx1
        · exact ⟨Or.inr hx1.1, hx1.2⟩
        · exact absurd (Or.inr hx1) hx2
    by_cases hsmall : ((A ∪ B) \ Ut).ncard ≤ 2
    · have hc := dC_le_ncard ((B \ Ut) ∪ {t}) hBt 2 ((A \ Ut) ∪ {t}) hAt
        (hU'a.subset (Set.union_subset hAt_sub hBt_sub))
        ((Set.ncard_le_ncard hdiff).trans hsmall)
      exact_mod_cast hc
    -- `|U \ U_t| ≥ 3`: the walk `A_t → M_t → B_t`
    push Not at hsmall
    set Mt : Set P := {m | m ≤ t ∧ ∀ y, y ≤ m → y = m} with hMt
    have hMa : IsAntichainSet Mt := fun x hx y hy hxy hle => hxy (hy.2 x hle)
    -- every `v ∈ U \ U_t` lies above an element of `M_t`
    have hvM : ∀ v ∈ (A ∪ B) \ Ut, ∃ m ∈ Mt, m < v := by
      intro v hv
      obtain ⟨r, hr, hrv⟩ := Set.exists_ne_of_one_lt_ncard (s := (A ∪ B) \ Ut) (by omega) v
      have hvt : v ≠ t := fun hvt => hv.2 (le_of_eq hvt)
      have hnc : ∀ w ∈ (A ∪ B) \ Ut, ¬ Comp w t := by
        intro w hw hwt
        rcases hwt with hwt | hwt
        · exact hw.2 hwt.le
        · exact hw.2 (le_of_eq (htmax w hwt.le))
      have hrv' : ¬ Comp r v := by
        rintro (hlt | hlt)
        · exact hU hr.1 hv.1 hrv hlt.le
        · exact hU hv.1 hr.1 (Ne.symm hrv) hlt.le
      obtain ⟨c, hcv, hct⟩ | ⟨c, hvc, htc⟩ :=
        pair_lemma h v t r hvt (hnc v hv) hrv (fun hrt => hr.2 (le_of_eq hrt)) hrv' (hnc r hr)
      · obtain ⟨m, hmc, hmin⟩ := (Set.toFinite {x : P | x ≤ c}).exists_le_minimal (le_refl c)
        refine ⟨m, ⟨hmc.trans hct, fun y hy => le_antisymm hy (hmin.2 (hy.trans hmin.1) hy)⟩,
          lt_of_le_of_ne (hmc.trans hcv) ?_⟩
        rintro rfl
        exact hv.2 (hmc.trans hct)
      · have hct : c = t := htmax c htc
        rw [hct] at hvc
        exact absurd hvc hv.2
    obtain ⟨v0, hv0⟩ : ((A ∪ B) \ Ut).Nonempty := by
      rw [← Set.ncard_pos]
      omega
    have htM : t ∉ Mt := by
      intro htM
      obtain ⟨m, hm, hmv⟩ := hvM v0 hv0
      have hmt : m = t := htM.2 m hm.1
      rw [hmt] at hmv
      exact hv0.2 (le_of_eq (htmax v0 hmv.le))
    have hMU : Disjoint Mt U' := by
      rw [Set.disjoint_left]
      intro m hm hmU
      rcases hmU with ⟨-, hmt⟩ | hmt
      · exact hmt hm.1
      · exact htM (hmt ▸ hm)
    -- `S_t △ M_t` is connected through `t`
    have hconn : ∀ S : Set P, S ⊆ (A ∪ B) → IsConnSet (symmDiff ((S \ Ut) ∪ {t}) Mt) := by
      intro S hS
      have hSt : (S \ Ut) ∪ {t} ⊆ U' := Set.union_subset_union_left _ (Set.sdiff_subset_sdiff_left hS)
      have htD : t ∈ symmDiff ((S \ Ut) ∪ {t}) Mt := Or.inl ⟨Or.inr rfl, htM⟩
      have hmD : ∀ m ∈ Mt, m ∈ symmDiff ((S \ Ut) ∪ {t}) Mt :=
        fun m hm => Or.inr ⟨hm, fun h' => Set.disjoint_left.1 hMU hm (hSt h')⟩
      have hmt : ∀ m ∈ Mt, m < t := fun m hm =>
        lt_of_le_of_ne hm.1 (fun hmt => htM (hmt ▸ hm))
      refine S4.isConnSet_of_rtg htD (fun y hy => ?_)
      rcases hy with ⟨hyS, -⟩ | ⟨hyM, -⟩
      · rcases hyS with hyS | rfl
        · obtain ⟨m, hm, hmy⟩ := hvM y ⟨hS hyS.1, hyS.2⟩
          have hyD : y ∈ symmDiff ((S \ Ut) ∪ {t}) Mt :=
            Or.inl ⟨Or.inl hyS, fun h' => Set.disjoint_left.1 hMU h' (hSt (Or.inl hyS))⟩
          exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨htD, hmD m hm, Or.inr (hmt m hm)⟩)
            ⟨hmD m hm, hyD, Or.inl hmy⟩
        · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single ⟨htD, hmD y hyM, Or.inr (hmt y hyM)⟩
    have hAM : dC ((A \ Ut) ∪ {t}) Mt hAt hMa ≤ 1 :=
      dC_le_one _ _ _ _ (Or.inr (hconn A Set.subset_union_left))
    have hMB : dC Mt ((B \ Ut) ∪ {t}) hMa hBt ≤ 1 := by
      rw [dC_comm]
      exact dC_le_one _ _ _ _ (Or.inr (hconn B Set.subset_union_right))
    calc dC ((A \ Ut) ∪ {t}) ((B \ Ut) ∪ {t}) hAt hBt
        ≤ dC ((A \ Ut) ∪ {t}) Mt hAt hMa + dC Mt ((B \ Ut) ∪ {t}) hMa hBt := dC_triangle _ _ _ _ _ _
      _ ≤ 1 + 1 := add_le_add hAM hMB
      _ = 2 := by norm_num
  calc dC A B hA hB ≤ dC A ((A \ Ut) ∪ {t}) hA hAt + dC ((A \ Ut) ∪ {t}) B hAt hB := dC_triangle _ _ _ _ _ _
    _ ≤ dC A ((A \ Ut) ∪ {t}) hA hAt +
          (dC ((A \ Ut) ∪ {t}) ((B \ Ut) ∪ {t}) hAt hBt + dC ((B \ Ut) ∪ {t}) B hBt hB) :=
        add_le_add le_rfl (dC_triangle _ _ _ _ _ _)
    _ ≤ 1 + (2 + 1) := add_le_add h1 (add_le_add h2 h3)
    _ = 4 := by norm_num

end S5

theorem lem_5_1_proved (P : Type) [Fintype P] [PartialOrder P] (h : orderDiam P ≤ 2) (p q r : P) (hpq : p ≠ q)
    (hpq' : ¬ Comp p q) (hrp : r ≠ p) (hrq : r ≠ q) (hr1 : ¬ Comp r p) (hr2 : ¬ Comp r q) :
    (∃ c, c ≤ p ∧ c ≤ q) ∨ (∃ c, p ≤ c ∧ q ≤ c) :=
  S5.pair_lemma h p q r hpq hpq' hrp hrq hr1 hr2

theorem thm_1_5_proved (P : Type) [Fintype P] [PartialOrder P] (h : orderDiam P ≤ 2) : chainDiam P ≤ 4 := by
  rw [chainDiam_le_iff]
  intro X Y hX hY
  obtain ⟨A, B, hA, hB, -, -, hsplit, hle⟩ := (lem_2_4_proved P).1 X Y hX hY
  exact hle.trans (S5.split_bound h A B hA hB hsplit)

end LeeDiam

