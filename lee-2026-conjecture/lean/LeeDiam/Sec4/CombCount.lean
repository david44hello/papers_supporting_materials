/-
LeeDiam/Sec4/CombCount.lean — the counting steps of the paper's proof of Lemma 4.5 (sec_chain.tex v1.50 l. 66) and
the arithmetic steps of Lemma 4.14 (ii) (l. 177).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

The helpers comparable to `a_u` are the `c_t` with `t ∈ T`, `|t - u| ≤ 1` (`nearCols`); one or two of them. The glue
elements are the `a_u` with `s < u < e` and `u` of the other parity, so `u ↦ u + 1` maps them onto the helper columns
other than the first. The components of `X ∪ C` are as many as the leaders (`comps_length`), and the non-leaders are
the `u + 1` for the glue elements `a_u ∈ X`.
-/
import LeeDiam.Sec4.Comb
import LeeDiam.Sec2.ComponentPaths

namespace LeeDiam.S4

open Band Finset

variable {k : ℕ}

section CombCount

variable {par s e : ℕ}

theorem a_inj : Function.Injective (a (k := k)) := fun _ _ h => congrArg Prod.fst h

/-- (P2): `a_u` and `c_t` are comparable iff `|u - t| ≤ 1`. -/
theorem comp_a_c_iff (u t : Fin k) : Comp (a u) (c t) ↔ t.val ≤ u.val + 1 ∧ u.val ≤ t.val + 1 := by
  rw [comp_iff_val]
  have h1 : (a u).2.val = 0 := rfl
  have h2 : (c t).2.val = 2 := rfl
  have h3 : (a u).1 = u := rfl
  have h4 : (c t).1 = t := rfl
  rw [h1, h2, h3, h4]
  omega

/-- The helper columns within distance one of `u`. -/
def nearCols (par s e : ℕ) (u : Fin k) : Finset (Fin k) :=
  (helperCols par s e).filter (fun t => t.val ≤ u.val + 1 ∧ u.val ≤ t.val + 1)

theorem helpers_near (u : Fin k) :
    {y : Band k | y ∈ helperSet par s e ∧ Comp (a u) y} = c '' (nearCols par s e u : Set (Fin k)) := by
  ext y
  constructor
  · rintro ⟨hy, hcomp⟩
    obtain ⟨h2, h3, h4, h5⟩ := hy
    obtain ⟨t, rfl⟩ : ∃ t, y = c t := ⟨y.1, (Prod.ext rfl h2.symm : c y.1 = y).symm⟩
    refine ⟨t, ?_, rfl⟩
    rw [Finset.mem_coe, nearCols, Finset.mem_filter]
    exact ⟨mem_helperCols.2 ⟨h3, h4, h5⟩, (comp_a_c_iff u t).1 hcomp⟩
  · rintro ⟨t, ht, rfl⟩
    rw [Finset.mem_coe, nearCols, Finset.mem_filter] at ht
    exact ⟨c_mem_helperSet.2 ht.1, (comp_a_c_iff u t).2 ht.2⟩

theorem helpers_near_ncard (u : Fin k) :
    {y : Band k | y ∈ helperSet par s e ∧ Comp (a u) y}.ncard = (nearCols par s e u).card := by
  rw [helpers_near, Set.ncard_image_of_injective _ c_injective, Set.ncard_coe_finset]

theorem nearCols_card (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (hek : e < k) (u : Fin k) (hsu : s ≤ u.val)
    (hue : u.val ≤ e) :
    1 ≤ (nearCols par s e u).card ∧ (nearCols par s e u).card ≤ 2 ∧
      ((nearCols par s e u).card = 2 ↔ s < u.val ∧ u.val < e ∧ (u.val - s) % 2 ≠ par) := by
  by_cases hp : (u.val - s) % 2 = par
  · have hset : nearCols par s e u = {u} := by
      ext t
      simp only [nearCols, Finset.mem_filter, mem_helperCols, Finset.mem_singleton, Fin.ext_iff]
      constructor
      · intro h
        omega
      · intro h
        omega
    rw [hset, Finset.card_singleton]
    exact ⟨le_rfl, by norm_num, ⟨fun h => absurd h (by norm_num), fun h => absurd hp h.2.2⟩⟩
  · by_cases hin : s < u.val ∧ u.val < e
    · have hset : nearCols par s e u = {⟨u.val - 1, by omega⟩, ⟨u.val + 1, by omega⟩} := by
        ext t
        simp only [nearCols, Finset.mem_filter, mem_helperCols, Finset.mem_insert, Finset.mem_singleton,
          Fin.ext_iff]
        constructor
        · intro h
          omega
        · intro h
          omega
      rw [hset, Finset.card_pair (by rw [Ne, Fin.mk.injEq]; omega)]
      exact ⟨by norm_num, le_rfl, ⟨fun _ => ⟨hin.1, hin.2, hp⟩, fun _ => rfl⟩⟩
    · have hone : (nearCols par s e u).card = 1 := by
        by_cases hs : u.val = s
        · have hset : nearCols par s e u = {⟨u.val + 1, by omega⟩} := by
            ext t
            simp only [nearCols, Finset.mem_filter, mem_helperCols, Finset.mem_singleton, Fin.ext_iff]
            constructor
            · intro h
              omega
            · intro h
              omega
          rw [hset, Finset.card_singleton]
        · have hset : nearCols par s e u = {⟨u.val - 1, by omega⟩} := by
            ext t
            simp only [nearCols, Finset.mem_filter, mem_helperCols, Finset.mem_singleton, Fin.ext_iff]
            constructor
            · intro h
              omega
            · intro h
              omega
          rw [hset, Finset.card_singleton]
      rw [hone]
      exact ⟨le_rfl, by norm_num, ⟨fun h => absurd h (by norm_num), fun h => absurd ⟨h.1, h.2.1⟩ hin⟩⟩

/-- The two neighbouring helpers of a glue column. -/
theorem glue_iff (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (hek : e < k) (u : Fin k) :
    (∃ t t' : Fin k, c t ∈ helperSet par s e ∧ c t' ∈ helperSet par s e ∧ t'.val = t.val + 2 ∧
      u.val = t.val + 1) ↔ s < u.val ∧ u.val < e ∧ (u.val - s) % 2 ≠ par := by
  constructor
  · rintro ⟨t, t', ht, ht', h1, h2⟩
    rw [c_mem_helperSet, mem_helperCols] at ht ht'
    omega
  · intro h
    refine ⟨⟨u.val - 1, by omega⟩, ⟨u.val + 1, by omega⟩, ?_, ?_, ?_, ?_⟩
    · rw [c_mem_helperSet, mem_helperCols]
      dsimp only
      omega
    · rw [c_mem_helperSet, mem_helperCols]
      dsimp only
      omega
    · dsimp only
      omega
    · dsimp only
      omega

/-- The glue columns: `s < u < e` and `u` of the other parity. -/
def glueCols (par s e : ℕ) : Finset (Fin k) :=
  univ.filter (fun u => s < u.val ∧ u.val < e ∧ (u.val - s) % 2 ≠ par)

theorem glueCols_card (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (hse : s ≤ e) (hek : e < k) :
    (glueCols (k := k) par s e).card = (helperCols (k := k) par s e).card - 1 := by
  have hfirst := first_helper_mem hpar hse hek
  rw [← Finset.card_erase_of_mem hfirst]
  refine Finset.card_bij (fun u hu => ⟨u.val + 1, ?_⟩) ?_ ?_ ?_
  · simp only [glueCols, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    omega
  · intro u hu
    simp only [glueCols, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [Finset.mem_erase, mem_helperCols, Ne, Fin.mk.injEq]
    dsimp only
    omega
  · intro u _ v _ h
    rw [Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  · intro t ht
    rw [Finset.mem_erase, mem_helperCols, Ne, Fin.ext_iff] at ht
    dsimp only at ht
    refine ⟨⟨t.val - 1, by omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
    simp only [glueCols, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

/-- An element of `U = rowSeg 0 s e` is some `a_u`. -/
theorem eq_a_of_row0 {x : Band k} (hx : x ∈ (rowSeg 0 s e : Set (Band k))) :
    x = a x.1 ∧ s ≤ x.1.val ∧ x.1.val ≤ e :=
  ⟨Prod.ext rfl hx.1, hx.2.1, hx.2.2⟩

open Classical in
/-- The glue elements in `X ⊆ U`, as columns. -/
theorem glue_in_eq (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (hek : e < k) {X : Set (Band k)}
    (hX : X ⊆ rowSeg 0 s e) :
    {x : Band k | x ∈ X ∧ {y | y ∈ helperSet par s e ∧ Comp x y}.ncard = 2} =
      a '' ((univ.filter (fun u : Fin k => a u ∈ X ∧ s < u.val ∧ u.val < e ∧ (u.val - s) % 2 ≠ par) :
        Finset (Fin k)) : Set (Fin k)) := by
  ext x
  constructor
  · rintro ⟨hxX, h2⟩
    obtain ⟨hxa, hs, he⟩ := eq_a_of_row0 (hX hxX)
    rw [hxa, helpers_near_ncard] at h2
    refine ⟨x.1, ?_, hxa.symm⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hxa ▸ hxX, (nearCols_card hpar hek x.1 hs he).2.2.1 h2⟩
  · rintro ⟨u, hu, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter] at hu
    obtain ⟨-, huX, hcond⟩ := hu
    obtain ⟨-, hs, he⟩ := eq_a_of_row0 (hX huX)
    refine ⟨huX, ?_⟩
    rw [helpers_near_ncard]
    exact (nearCols_card hpar hek u hs he).2.2.2 hcond

open Classical in
/-- The components of `X ∪ C` (`X ⊆ U`) number `m` minus the number of glue elements in `X`. -/
theorem numComp_comb (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (hek : e < k) {X : Set (Band k)}
    (hX : X ⊆ rowSeg 0 s e) :
    numComp (X ∪ helperSet par s e) = (helperSet par s e : Set (Band k)).ncard -
      {x : Band k | x ∈ X ∧ {y | y ∈ helperSet par s e ∧ Comp x y}.ncard = 2}.ncard := by
  obtain ⟨L, hnd, hL, hlen⟩ := component_enumeration (X ∪ helperSet par s e)
  rw [← hlen, comps_length hpar hek hX L hnd hL, helperSet_ncard, glue_in_eq hpar hek hX,
    Set.ncard_image_of_injective _ a_inj, Set.ncard_coe_finset]
  have hsplit := Finset.card_filter_add_card_filter_not (s := helperCols (k := k) par s e)
    (fun i : Fin k => i.val = s + par ∨ ¬ ∃ x ∈ X, x.1.val + 1 = i.val)
  have hnon : ((helperCols (k := k) par s e).filter
      (fun i : Fin k => ¬ (i.val = s + par ∨ ¬ ∃ x ∈ X, x.1.val + 1 = i.val))).card =
      (univ.filter (fun u : Fin k => a u ∈ X ∧ s < u.val ∧ u.val < e ∧ (u.val - s) % 2 ≠ par)).card := by
    symm
    refine Finset.card_bij (fun u hu => ⟨u.val + 1, ?_⟩) ?_ ?_ ?_
    · rw [Finset.mem_filter] at hu
      omega
    · intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨-, huX, h1, h2, h3⟩ := hu
      rw [Finset.mem_filter, mem_helperCols]
      dsimp only
      refine ⟨by omega, ?_⟩
      push Not
      exact ⟨by omega, ⟨a u, huX, rfl⟩⟩
    · intro u _ v _ h
      rw [Fin.mk.injEq] at h
      exact Fin.ext (by omega)
    · intro t ht
      rw [Finset.mem_filter, mem_helperCols] at ht
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := ht
      push Not at h4
      obtain ⟨h5, x, hxX, hx⟩ := h4
      obtain ⟨hxa, hs, he⟩ := eq_a_of_row0 (hX hxX)
      refine ⟨x.1, ?_, Fin.ext (by dsimp only; omega)⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hxa ▸ hxX, by omega, by omega, by omega⟩
  rw [leaders]
  omega

end CombCount

end LeeDiam.S4

namespace LeeDiam

open Band

theorem lem_4_5_helpers_proved {k : ℕ} (s e : ℕ) (_hse : s ≤ e) (hek : e < k) (par : ℕ)
    (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (u : Fin k) (hsu : s ≤ u.val) (hue : u.val ≤ e) :
    1 ≤ {y : Band k | y ∈ helperSet par s e ∧ Comp (Band.a u) y}.ncard ∧
    {y : Band k | y ∈ helperSet par s e ∧ Comp (Band.a u) y}.ncard ≤ 2 ∧
    ({y : Band k | y ∈ helperSet par s e ∧ Comp (Band.a u) y}.ncard = 2 ↔
      ∃ t t' : Fin k, Band.c t ∈ helperSet par s e ∧ Band.c t' ∈ helperSet par s e ∧ t'.val = t.val + 2 ∧
        u.val = t.val + 1) := by
  rw [S4.helpers_near_ncard, S4.glue_iff hpar hek u]
  exact S4.nearCols_card hpar hek u hsu hue

theorem lem_4_5_glue_proved {k : ℕ} (s e : ℕ) (hse : s ≤ e) (hek : e < k) (par : ℕ)
    (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) :
    {x : Band k | x ∈ rowSeg 0 s e ∧ {y | y ∈ helperSet par s e ∧ Comp x y}.ncard = 2}.ncard =
      (helperSet par s e : Set (Band k)).ncard - 1 := by
  classical
  have hset : {x : Band k | x ∈ rowSeg 0 s e ∧ {y | y ∈ helperSet par s e ∧ Comp x y}.ncard = 2} =
      a '' ((S4.glueCols par s e : Finset (Fin k)) : Set (Fin k)) := by
    rw [S4.glue_in_eq hpar hek subset_rfl]
    congr 1
    ext u
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, S4.glueCols, Set.mem_ofPred_eq]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨rfl, by show s ≤ u.val; omega, by show u.val ≤ e; omega⟩, h⟩
  rw [hset, Set.ncard_image_of_injective _ S4.a_inj, Set.ncard_coe_finset, S4.glueCols_card hpar hse hek,
    S4.helperSet_ncard]

theorem lem_4_5_same_comp_proved {k : ℕ} (s e : ℕ) (_hse : s ≤ e) (_hek : e < k) (par : ℕ)
    (_hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (A B : Set (Band k)) (hAB : IsSplit A B (rowSeg 0 s e))
    (t t' u : Fin k) (ht : Band.c t ∈ helperSet par s e) (ht' : Band.c t' ∈ helperSet par s e)
    (htt' : t'.val = t.val + 2) (hu : u.val = t.val + 1) :
    (∃ D, IsComponent D (A ∪ helperSet par s e) ∧ Band.c t ∈ D ∧ Band.c t' ∈ D) ↔ Band.a u ∈ A := by
  obtain ⟨-, hU, -⟩ := hAB
  have hA : A ⊆ rowSeg 0 s e := hU ▸ Set.subset_union_left
  have hS' : c t' ∈ A ∪ helperSet par s e := Or.inr ht'
  rw [S4.c_mem_helperSet] at ht ht'
  have hne : t'.val ≠ s + par := by
    rw [S4.mem_helperCols] at ht
    omega
  constructor
  · rintro ⟨D, hD, htD, ht'D⟩
    by_contra hua
    have hlead : t' ∈ S4.leaders par s e A := by
      rw [S4.mem_leaders]
      refine ⟨ht', Or.inr ?_⟩
      rintro ⟨x, hxA, hx1⟩
      obtain ⟨hxa, -, -⟩ := S4.eq_a_of_row0 (hA hxA)
      have hxu : x.1 = u := Fin.ext (by omega)
      exact hua (hxu ▸ hxa ▸ hxA)
    have hDr : D = S4.reach (A ∪ helperSet par s e) (c t') :=
      S4.comp_eq_of_mem hD (S4.isComponent_reach hS') ht'D (S4.mem_reach_self _ _)
    exact S4.leader_min hlead ht (by omega) (hDr ▸ htD)
  · intro hua
    obtain ⟨j, -, hjv, hjr⟩ := S4.glue_reach hA ht' hne ⟨a u, hua, by show u.val + 1 = t'.val; omega⟩
    have hjt : j = t := Fin.ext (by omega)
    subst hjt
    exact ⟨_, S4.isComponent_reach hS', hjr, S4.mem_reach_self _ _⟩

theorem lem_4_5_comp_count_proved {k : ℕ} (s e : ℕ) (_hse : s ≤ e) (hek : e < k) (par : ℕ)
    (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (A B : Set (Band k)) (hAB : IsSplit A B (rowSeg 0 s e)) :
    numComp (A ∪ helperSet par s e) = (helperSet par s e : Set (Band k)).ncard -
      {x : Band k | x ∈ A ∧ {y | y ∈ helperSet par s e ∧ Comp x y}.ncard = 2}.ncard ∧
    numComp (helperSet par s e ∪ B) = (helperSet par s e : Set (Band k)).ncard -
      {x : Band k | x ∈ B ∧ {y | y ∈ helperSet par s e ∧ Comp x y}.ncard = 2}.ncard := by
  obtain ⟨-, hU, -⟩ := hAB
  have hA : A ⊆ rowSeg 0 s e := hU ▸ Set.subset_union_left
  have hB : B ⊆ rowSeg 0 s e := hU ▸ Set.subset_union_right
  refine ⟨S4.numComp_comb hpar hek hA, ?_⟩
  rw [Set.union_comm]
  exact S4.numComp_comb hpar hek hB

theorem lem_4_14_steps_proved :
    ((2 + 1) / 2 + 1 = 2 ∧ 3 * (2 + 1) / 4 = 2) ∧ ((3 + 1) / 2 + 1 = 3 ∧ 3 * (3 + 1) / 4 = 3) ∧
    ((4 + 1) / 2 + 1 = 3 ∧ 3 * (4 + 1) / 4 = 3) ∧ ((5 + 1) / 2 + 1 = 4 ∧ 3 * (5 + 1) / 4 = 4) ∧
    ∀ k : ℕ, 6 ≤ k → (3 * k : ℝ) / 4 ≤ ((3 * (k + 1) / 4 : ℕ) : ℝ) ∧ ((k : ℝ) + 3) / 2 ≤ (3 * k : ℝ) / 4 ∧
      (((k + 1) / 2 + 1 : ℕ) : ℝ) ≤ ((k : ℝ) + 3) / 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, fun k hk => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨n, hn⟩ : ∃ n, n = 3 * (k + 1) / 4 := ⟨_, rfl⟩
    rw [← hn]
    have h : 3 * k ≤ 4 * n := by omega
    have h' : (3 : ℝ) * k ≤ 4 * (n : ℝ) := by exact_mod_cast h
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith
  · have hk' : (6 : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 4)]
    linarith
  · obtain ⟨m, hm⟩ : ∃ m, m = (k + 1) / 2 + 1 := ⟨_, rfl⟩
    rw [← hm]
    have h : 2 * m ≤ k + 3 := by omega
    have h' : (2 : ℝ) * m ≤ (k : ℝ) + 3 := by exact_mod_cast h
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith

end LeeDiam
