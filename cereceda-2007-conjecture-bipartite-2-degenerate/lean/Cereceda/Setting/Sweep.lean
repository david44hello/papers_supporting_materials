/-
Cereceda/Setting/Sweep.lean — Lemma 2.5 (the sweep).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Basic
import Cereceda.Defs.Instance
import Cereceda.Setting.Small
import Cereceda.Setting.CaseA
import Cereceda.Setting.CaseAPaperCounts

namespace Cereceda

open Finset

namespace Sweep

/-! ### Sequences in general (R1) -/

section Generic

variable {W : Type} [Fintype W] [DecidableEq W]

omit [Fintype W] in
/-- Two sequences, one after the other, form a sequence. -/
theorem isSeq_append (H : SimpleGraph W) (A : W → Finset (Fin 4)) :
    ∀ (ms₁ ms₂ : List (W × Fin 4)) (c c' c'' : W → Fin 4),
      IsSeq H A c ms₁ c' → IsSeq H A c' ms₂ c'' → IsSeq H A c (ms₁ ++ ms₂) c''
  | [], _, c, c', c'', h₁, h₂ => by
      simp only [IsSeq] at h₁
      subst h₁
      simpa using h₂
  | m :: ms₁, ms₂, c, c', c'', h₁, h₂ => by
      simp only [IsSeq] at h₁
      simp only [List.cons_append, IsSeq]
      exact ⟨h₁.1, isSeq_append H A ms₁ ms₂ _ c' c'' h₁.2 h₂⟩

omit [Fintype W] in
/-- A legal move keeps a colouring proper. -/
theorem isProperFn_update (H : SimpleGraph W) (A : W → Finset (Fin 4)) (c : W → Fin 4) (m : W × Fin 4)
    (hc : IsProperFn H c) (hm : LegalMove H A c m) : IsProperFn H (Function.update c m.1 m.2) := by
  intro u v huv
  by_cases hu : u = m.1
  · have hv : v ≠ m.1 := fun h => H.ne_of_adj huv (hu.trans h.symm)
    rw [hu, Function.update_self, Function.update_of_ne hv]
    exact (hm.2.2 v (hu ▸ huv)).symm
  · by_cases hv : v = m.1
    · rw [hv, Function.update_self, Function.update_of_ne hu]
      exact hm.2.2 u (hv ▸ huv.symm)
    · rw [Function.update_of_ne hu, Function.update_of_ne hv]
      exact hc u v huv

omit [Fintype W] in
/-- A sequence keeps a colouring proper. -/
theorem isProperFn_of_isSeq (H : SimpleGraph W) (A : W → Finset (Fin 4)) :
    ∀ (ms : List (W × Fin 4)) (c c' : W → Fin 4), IsSeq H A c ms c' → IsProperFn H c → IsProperFn H c'
  | [], c, c', h, hc => by
      simp only [IsSeq] at h
      subst h
      exact hc
  | m :: ms, c, c', h, hc => by
      simp only [IsSeq] at h
      exact isProperFn_of_isSeq H A ms _ c' h.2 (isProperFn_update H A c m hc h.1)

/-- If fewer than four colours are used, a least free colour exists. -/
theorem exists_isLeastFree (U : Finset (Fin 4)) (hU : U.card < 4) : ∃ y, IsLeastFree univ U y := by
  have hne : (Uᶜ).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [Finset.compl_eq_empty_iff] at h
    subst h
    simp at hU
  refine ⟨Uᶜ.min' hne, mem_univ _, ?_, ?_⟩
  · exact mem_compl.1 (Uᶜ.min'_mem hne)
  · intro z _ hz
    by_contra hzU
    exact absurd (Uᶜ.min'_le z (mem_compl.2 hzU)) (not_le.2 hz)

end Generic

section GraphLevel

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A sequence on `G` from a proper colouring `C` reaches a proper colouring `C'` with
`edist C C' ≤` the number of moves (each move is one edge of `R_4(G)`). -/
theorem edist_of_isSeq (G : SimpleGraph V) (A : V → Finset (Fin 4)) :
    ∀ (ms : List (V × Fin 4)) (C : G.Coloring (Fin 4)) (c' : V → Fin 4), IsSeq G A C ms c' →
      ∃ C' : G.Coloring (Fin 4), ⇑C' = c' ∧ (recolGraph G 4).edist C C' ≤ ms.length
  | [], C, c', h => by
      simp only [IsSeq] at h
      exact ⟨C, h.symm, by simp⟩
  | m :: ms, C, c', h => by
      simp only [IsSeq] at h
      obtain ⟨hm, hs⟩ := h
      have hp : IsProperFn G (Function.update (⇑C) m.1 m.2) :=
        isProperFn_update G A C m (fun u v huv => C.valid huv) hm
      let C₁ : G.Coloring (Fin 4) := SimpleGraph.Coloring.mk (Function.update (⇑C) m.1 m.2)
        (fun huv => hp _ _ huv)
      obtain ⟨C', hC', hd⟩ := edist_of_isSeq G A ms C₁ c' hs
      refine ⟨C', hC', ?_⟩
      have hadj : (recolGraph G 4).Adj C C₁ := by
        refine ⟨m.1, ?_, fun u hu => ?_⟩
        · show C m.1 ≠ Function.update (⇑C) m.1 m.2 m.1
          rw [Function.update_self]
          exact hm.1.symm
        · show C u = Function.update (⇑C) m.1 m.2 u
          rw [Function.update_of_ne hu]
      have h1 : (recolGraph G 4).edist C C₁ ≤ 1 :=
        SimpleGraph.edist_le_one_iff_adj_or_eq.2 (Or.inl hadj)
      calc (recolGraph G 4).edist C C' ≤ (recolGraph G 4).edist C C₁ + (recolGraph G 4).edist C₁ C' :=
            SimpleGraph.edist_triangle
        _ ≤ 1 + ms.length := add_le_add h1 hd
        _ = ((m :: ms).length : ℕ∞) := by
            simp only [List.length_cons]
            push_cast
            ring

/-- `v` is greedy in the colouring `c` of `G`: `c v` is the least colour no later neighbour of `v` has. -/
def IsGr (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (ρ : V ≃ Fin n) (c : V → Fin 4) (v : V) : Prop :=
  IsLeastFree univ ((laterNbrs G ρ v).image c) (c v)

omit [DecidableEq V] in
theorem mem_laterNbrs {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ} {ρ : V ≃ Fin n} {u v : V} :
    v ∈ laterNbrs G ρ u ↔ G.Adj u v ∧ ρ u < ρ v := by
  simp [laterNbrs]

omit [DecidableEq V] in
/-- Going back along an arc from a cone vertex stays in the cone (if the start is not later than the tip). -/
theorem mem_cone_of_arc {G : SimpleGraph V} {n : ℕ} {ρ : V ≃ Fin n} {w a b : V} (hab : G.Adj a b)
    (hlt : ρ a < ρ b) (hb : b ∈ cone G ρ w) (ha : ρ a ≤ ρ w) : a ∈ cone G ρ w := by
  classical
  simp only [cone, mem_filter, mem_univ, true_and] at hb ⊢
  exact ⟨ha, Relation.ReflTransGen.head ⟨⟨hab, hlt⟩, ha, hb.1⟩ hb.2⟩

omit [DecidableEq V] in
/-- Fact (a): a neighbour outside the cone of a cone vertex is a later neighbour. -/
theorem lt_of_adj_mem_cone {G : SimpleGraph V} {n : ℕ} {ρ : V ≃ Fin n} {w u v : V} (huv : G.Adj u v)
    (hu : u ∈ cone G ρ w) (hv : v ∉ cone G ρ w) : ρ u < ρ v := by
  rcases lt_or_gt_of_ne (show ρ u ≠ ρ v from fun h => G.ne_of_adj huv (ρ.injective h)) with h | h
  · exact h
  · exact absurd (mem_cone_of_arc huv.symm h hu (le_trans h.le (le_of_mem_cone hu))) hv

end GraphLevel

/-! ### The instance on a cone (R2) -/

section ConeInst

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ}
  (ρ : V ≃ Fin n)

/-- The later neighbours of `u` that lie outside the cone of `w`. -/
noncomputable def outNbrs (w u : V) : Finset V :=
  (laterNbrs G ρ u).filter (fun v => v ∉ cone G ρ w)

/-- The lists of the cone instance: `{g, c w}` at the sink, and all colours minus those of the later neighbours
outside the cone elsewhere. -/
noncomputable def coneL (w : V) (c : V → Fin 4) (g : Fin 4) (u : ConeV G ρ w) : Finset (Fin 4) :=
  if u.1 = w then {g, c w} else ((outNbrs G ρ w u.1).image c)ᶜ

variable {G ρ}

theorem mem_out {hρ : IsDegOrder G 2 ρ} {w : V} {u v : ConeV G ρ w} :
    v ∈ (coneSkeleton G ρ hρ w).out u ↔ G.Adj u.1 v.1 ∧ ρ u.1 < ρ v.1 := by
  simp [coneSkeleton]

theorem card_out_add_card_outNbrs (hρ : IsDegOrder G 2 ρ) (w : V) (u : ConeV G ρ w) :
    ((coneSkeleton G ρ hρ w).out u).card + (outNbrs G ρ w u.1).card ≤ 2 := by
  have h1 : ((coneSkeleton G ρ hρ w).out u).card ≤
      ((laterNbrs G ρ u.1).filter (fun v => v ∈ cone G ρ w)).card := by
    refine card_le_card_of_injOn (fun v => v.1) ?_ ?_
    · intro v hv
      have hv' := mem_out.1 (mem_coe.1 hv)
      exact mem_coe.2 (mem_filter.2 ⟨mem_laterNbrs.2 hv', v.2⟩)
    · intro v _ v' _ h
      exact Subtype.ext h
  have h2 := card_filter_add_card_filter_not (s := laterNbrs G ρ u.1) (fun v => v ∈ cone G ρ w)
  have h3 := hρ u.1
  unfold outNbrs
  omega

theorem coneL_card (hρ : IsDegOrder G 2 ρ) (w : V) (c : V → Fin 4) (g : Fin 4) (hgx : g ≠ c w)
    (u : ConeV G ρ w) : ((coneSkeleton G ρ hρ w).out u).card + 2 ≤ (coneL G ρ w c g u).card := by
  unfold coneL
  split_ifs with hu
  · have hs : u = (coneSkeleton G ρ hρ w).sink := Subtype.ext hu
    rw [hs, (coneSkeleton G ρ hρ w).sink_out, card_pair hgx]
    simp
  · rw [card_compl]
    have h1 := card_out_add_card_outNbrs hρ w u
    have h2 : ((outNbrs G ρ w u.1).image c).card ≤ (outNbrs G ρ w u.1).card := card_image_le
    simp only [Fintype.card_fin]
    omega

/-- The instance on the cone of `w` (proof of Lemma 2.5), for the colouring `c` and the target sink colour `g`. -/
noncomputable def coneInst (hρ : IsDegOrder G 2 ρ) (w : V) (c : V → Fin 4) (g : Fin 4) (hgx : g < c w) :
    Instance (ConeV G ρ w) where
  toSkeleton := coneSkeleton G ρ hρ w
  L := coneL G ρ w c g
  L_card := coneL_card hρ w c g hgx.ne
  g := g
  x := c w
  g_lt_x := hgx
  L_sink := by
    show coneL G ρ w c g ⟨w, mem_cone_self G ρ w⟩ = {g, c w}
    unfold coneL
    exact ite_eq_left rfl

/-- Colourings of `G` read in the cone: the later neighbours of a cone vertex split into those in the cone (the
out-neighbours of the instance) and those outside (whose colours are removed from the list). -/
theorem mem_image_laterNbrs (hρ : IsDegOrder G 2 ρ) (w : V) (c d : V → Fin 4)
    (hd : ∀ v, v ∉ cone G ρ w → d v = c v) (a : ConeV G ρ w → Fin 4) (hda : ∀ v : ConeV G ρ w, d v.1 = a v)
    (u : ConeV G ρ w) (z : Fin 4) :
    z ∈ (laterNbrs G ρ u.1).image d ↔
      z ∈ ((coneSkeleton G ρ hρ w).out u).image a ∨ z ∈ (outNbrs G ρ w u.1).image c := by
  constructor
  · intro hz
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hz
    by_cases hvc : v ∈ cone G ρ w
    · left
      exact mem_image.2 ⟨⟨v, hvc⟩, mem_out.2 (mem_laterNbrs.1 hv), (hda ⟨v, hvc⟩).symm⟩
    · right
      exact mem_image.2 ⟨v, mem_filter.2 ⟨hv, hvc⟩, (hd v hvc).symm⟩
  · rintro (hz | hz)
    · obtain ⟨v, hv, rfl⟩ := mem_image.1 hz
      exact mem_image.2 ⟨v.1, mem_laterNbrs.2 (mem_out.1 hv), hda v⟩
    · obtain ⟨v, hv, rfl⟩ := mem_image.1 hz
      obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
      exact mem_image.2 ⟨v, hv1, hd v hv2⟩

/-- Greedy in `G` = greedy in the cone instance, for a cone vertex other than the sink. -/
theorem isGr_iff (hρ : IsDegOrder G 2 ρ) (w : V) (c : V → Fin 4) (g : Fin 4) (hgx : g < c w)
    (d : V → Fin 4) (hd : ∀ v, v ∉ cone G ρ w → d v = c v) (a : ConeV G ρ w → Fin 4)
    (hda : ∀ v : ConeV G ρ w, d v.1 = a v) (u : ConeV G ρ w) (hu : u.1 ≠ w) :
    IsGr G ρ d u.1 ↔
      IsLeastFree ((coneInst hρ w c g hgx).L u) (((coneInst hρ w c g hgx).out u).image a) (a u) := by
  have hmem := mem_image_laterNbrs hρ w c d hd a hda u
  have hL : ∀ z, z ∈ (coneInst hρ w c g hgx).L u ↔ z ∉ (outNbrs G ρ w u.1).image c := by
    intro z
    show z ∈ coneL G ρ w c g u ↔ _
    rw [coneL, ite_eq_right hu, mem_compl]
  have hout : (coneInst hρ w c g hgx).out u = (coneSkeleton G ρ hρ w).out u := rfl
  rw [hout, ← hda u]
  unfold IsGr
  constructor
  · rintro ⟨-, h2, h3⟩
    refine ⟨(hL _).2 fun hb => h2 ((hmem _).2 (Or.inr hb)), fun ha => h2 ((hmem _).2 (Or.inl ha)),
      fun z hz hzy => ((hmem z).1 (h3 z (mem_univ z) hzy)).resolve_right ((hL z).1 hz)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨mem_univ _, fun hy => ?_, fun z _ hzy => ?_⟩
    · rcases (hmem _).1 hy with ha | hb
      · exact h2 ha
      · exact (hL _).1 h1 hb
    · by_cases hb : z ∈ (outNbrs G ρ w u.1).image c
      · exact (hmem z).2 (Or.inr hb)
      · exact (hmem z).2 (Or.inl (h3 z ((hL z).2 hb) hzy))

/-- Fact (c): `c` restricted to the cone is the greedy colouring `α` (sink on `x = c w`). -/
theorem isGreedy_x (hρ : IsDegOrder G 2 ρ) (w : V) (c : V → Fin 4) (g : Fin 4) (hgx : g < c w)
    (hgr : ∀ u, ρ u < ρ w → IsGr G ρ c u) :
    (coneInst hρ w c g hgx).IsGreedy (coneInst hρ w c g hgx).x (fun u => c u.1) := by
  refine ⟨rfl, fun v hv => ?_⟩
  have hvw : v.1 ≠ w := fun h => hv (Subtype.ext h)
  have hlt : ρ v.1 < ρ w := lt_of_le_of_ne (le_of_mem_cone v.2) (fun h => hvw (ρ.injective h))
  exact (isGr_iff hρ w c g hgx c (fun _ _ => rfl) (fun u => c u.1) (fun _ => rfl) v hvw).1 (hgr v.1 hlt)

/-- A colouring of the cone, glued with `c` outside the cone. -/
noncomputable def glue (w : V) (c : V → Fin 4) (a : ConeV G ρ w → Fin 4) (v : V) : Fin 4 :=
  if h : v ∈ cone G ρ w then a ⟨v, h⟩ else c v

omit [DecidableRel G.Adj] in
theorem glue_of_mem {w : V} {c : V → Fin 4} {a : ConeV G ρ w → Fin 4} {v : V} (h : v ∈ cone G ρ w) :
    glue w c a v = a ⟨v, h⟩ := dite_eq_left h

omit [DecidableRel G.Adj] in
theorem glue_of_not_mem {w : V} {c : V → Fin 4} {a : ConeV G ρ w → Fin 4} {v : V} (h : v ∉ cone G ρ w) :
    glue w c a v = c v := dite_eq_right h

omit [DecidableRel G.Adj] in
theorem glue_val (w : V) (c : V → Fin 4) : glue w c (fun u : ConeV G ρ w => c u.1) = c := by
  funext v
  by_cases h : v ∈ cone G ρ w
  · rw [glue_of_mem h]
  · rw [glue_of_not_mem h]

omit [DecidableRel G.Adj] in
theorem glue_update (w : V) (c : V → Fin 4) (a : ConeV G ρ w → Fin 4) (u : ConeV G ρ w) (y : Fin 4) :
    glue w c (Function.update a u y) = Function.update (glue w c a) u.1 y := by
  funext v
  by_cases h : v ∈ cone G ρ w
  · rw [glue_of_mem h]
    by_cases hvu : v = u.1
    · have hu : (⟨v, h⟩ : ConeV G ρ w) = u := Subtype.ext hvu
      rw [hu, Function.update_self, hvu, Function.update_self]
    · have hu : (⟨v, h⟩ : ConeV G ρ w) ≠ u := fun h' => hvu (congrArg Subtype.val h')
      rw [Function.update_of_ne hu, Function.update_of_ne hvu, glue_of_mem h]
  · have hvu : v ≠ u.1 := fun h' => h (h' ▸ u.2)
    rw [glue_of_not_mem h, Function.update_of_ne hvu, glue_of_not_mem h]

/-- Fact (d), one move: a legal move of the cone instance is a legal move in `G` (outside the cone `c` stays). -/
theorem legalMove_lift (hρ : IsDegOrder G 2 ρ) (w : V) (c : V → Fin 4) (g : Fin 4) (hgx : g < c w)
    (hc : IsProperFn G c) (hg : g ∉ (laterNbrs G ρ w).image c) (a : ConeV G ρ w → Fin 4)
    (m : ConeV G ρ w × Fin 4)
    (hm : LegalMove (coneInst hρ w c g hgx).graph (coneInst hρ w c g hgx).L a m) :
    LegalMove G (fun _ => univ) (glue w c a) (m.1.1, m.2) := by
  obtain ⟨h1, h2, h3⟩ := hm
  refine ⟨?_, mem_univ _, fun u hu => ?_⟩
  · show m.2 ≠ glue w c a m.1.1
    rw [glue_of_mem m.1.2]
    exact h1
  · change G.Adj m.1.1 u at hu
    by_cases huc : u ∈ cone G ρ w
    · rw [glue_of_mem huc]
      apply h3 ⟨u, huc⟩
      show (coneSkeleton G ρ hρ w).graph.Adj m.1 ⟨u, huc⟩
      rw [Skeleton.graph, SimpleGraph.fromRel_adj]
      refine ⟨fun h => G.ne_of_adj hu (congrArg Subtype.val h), ?_⟩
      rcases lt_or_gt_of_ne (show ρ m.1.1 ≠ ρ u from fun h => G.ne_of_adj hu (ρ.injective h)) with hlt | hlt
      · exact Or.inl (mem_out.2 ⟨hu, hlt⟩)
      · exact Or.inr (mem_out.2 ⟨hu.symm, hlt⟩)
    · rw [glue_of_not_mem huc]
      have hlt := lt_of_adj_mem_cone hu m.1.2 huc
      intro hcu
      have hL : m.2 ∈ coneL G ρ w c g m.1 := h2
      by_cases hw : m.1.1 = w
      · rw [coneL, ite_eq_left hw] at hL
        rw [hw] at hu hlt
        rcases mem_insert.1 hL with h | h
        · exact hg (mem_image.2 ⟨u, mem_laterNbrs.2 ⟨hu, hlt⟩, hcu.trans h⟩)
        · rw [mem_singleton] at h
          exact hc w u hu (hcu.trans h).symm
      · rw [coneL, ite_eq_right hw, mem_compl] at hL
        exact hL (mem_image.2 ⟨u, mem_filter.2 ⟨mem_laterNbrs.2 ⟨hu, hlt⟩, huc⟩, hcu⟩)

/-- Fact (d): a sequence of the cone instance, glued with `c` outside the cone, is a sequence in `G`. -/
theorem isSeq_lift (hρ : IsDegOrder G 2 ρ) (w : V) (c : V → Fin 4) (g : Fin 4) (hgx : g < c w)
    (hc : IsProperFn G c) (hg : g ∉ (laterNbrs G ρ w).image c) :
    ∀ (ms : List (ConeV G ρ w × Fin 4)) (a b : ConeV G ρ w → Fin 4),
      (coneInst hρ w c g hgx).IsSeq a ms b →
      IsSeq G (fun _ => univ) (glue w c a) (ms.map (fun m => (m.1.1, m.2))) (glue w c b)
  | [], a, b, h => by
      simp only [Instance.IsSeq, IsSeq] at h
      subst h
      simp only [List.map_nil, IsSeq]
  | m :: ms, a, b, h => by
      simp only [Instance.IsSeq, IsSeq] at h
      simp only [List.map_cons, IsSeq]
      refine ⟨legalMove_lift hρ w c g hgx hc hg a m h.1, ?_⟩
      rw [← glue_update]
      exact isSeq_lift hρ w c g hgx hc hg ms _ b h.2

omit [DecidableEq V] in
/-- Fact (e) at the sink: if `w` gets the least free colour `g`, it is greedy. -/
theorem isGr_sink (w : V) (c d : V → Fin 4) (hd : ∀ v, v ∉ cone G ρ w → d v = c v) (g : Fin 4)
    (hg : IsLeastFree univ ((laterNbrs G ρ w).image c) g) (hdw : d w = g) : IsGr G ρ d w := by
  have himg : (laterNbrs G ρ w).image d = (laterNbrs G ρ w).image c := by
    apply image_congr
    intro v hv
    apply hd
    intro hvc
    exact absurd (le_of_mem_cone hvc) (not_le.2 (mem_laterNbrs.1 (mem_coe.1 hv)).2)
  unfold IsGr
  rw [himg, hdw]
  exact hg

omit [DecidableEq V] in
/-- Fact (b)+(e) outside the cone: an earlier vertex outside the cone keeps its later neighbours' colours. -/
theorem isGr_outside (w : V) (c d : V → Fin 4) (hd : ∀ v, v ∉ cone G ρ w → d v = c v) (u : V)
    (hu : u ∉ cone G ρ w) (hρu : ρ u ≤ ρ w) (hgr : IsGr G ρ c u) : IsGr G ρ d u := by
  have himg : (laterNbrs G ρ u).image d = (laterNbrs G ρ u).image c := by
    apply image_congr
    intro v hv
    apply hd
    intro hvc
    have hv' := mem_laterNbrs.1 (mem_coe.1 hv)
    exact hu (mem_cone_of_arc hv'.1 hv'.2 hvc hρu)
  unfold IsGr
  rw [himg, hd u hu]
  exact hgr

/-- Fact (e): after the glued greedy colouring `β` (sink on `g`), every `u` with `ρ u ≤ ρ w` is greedy. -/
theorem isGr_after (hρ : IsDegOrder G 2 ρ) (w : V) (c : V → Fin 4) (g : Fin 4) (hgx : g < c w)
    (hg : IsLeastFree univ ((laterNbrs G ρ w).image c) g) (hgr : ∀ u, ρ u < ρ w → IsGr G ρ c u)
    (β : ConeV G ρ w → Fin 4) (hβ : (coneInst hρ w c g hgx).IsGreedy (coneInst hρ w c g hgx).g β)
    (u : V) (hu : ρ u ≤ ρ w) : IsGr G ρ (glue w c β) u := by
  have hd : ∀ v, v ∉ cone G ρ w → glue w c β v = c v := fun v hv => glue_of_not_mem hv
  by_cases huc : u ∈ cone G ρ w
  · by_cases huw : u = w
    · subst huw
      exact isGr_sink u c _ hd g hg (by rw [glue_of_mem huc]; exact hβ.1)
    · refine (isGr_iff hρ w c g hgx _ hd β (fun v => glue_of_mem v.2) ⟨u, huc⟩ huw).2 ?_
      exact hβ.2 ⟨u, huc⟩ (fun h => huw (congrArg Subtype.val h))
  · have hlt : ρ u < ρ w := lt_of_le_of_ne hu (fun h => huc (by rw [ρ.injective h]; exact mem_cone_self G ρ w))
    exact isGr_outside w c _ hd u huc hu (hgr u hlt)

end ConeInst

/-! ### One step of the sweep, and the sweep (R2, R3) -/

section Sweep

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}
  {ρ : V ≃ Fin n}

/-- The number of moves inside the cone: by `hlin` in the main case `g = 0`, by Lemma 2.3 if `g ≠ 0`. -/
theorem cone_moves (𝒞 : InstanceClass) (lam : ℝ) (hlam : 2 ≤ lam)
    (hlin : ∀ (W : Type) [Fintype W] [DecidableEq W] (I : Instance W), 𝒞 W I.toSkeleton → I.g = 0 →
      ∀ α β : W → Fin 4, I.IsGreedy I.x α → I.IsGreedy I.g β →
        ∃ ms, I.IsSeq α ms β ∧ (ms.length : ℝ) ≤ lam * Fintype.card W)
    (hρ : IsDegOrder G 2 ρ) (hcones : ∀ w, 𝒞 (ConeV G ρ w) (coneSkeleton G ρ hρ w))
    (w : V) (c : V → Fin 4) (g : Fin 4) (hgx : g < c w) (α β : ConeV G ρ w → Fin 4)
    (hα : (coneInst hρ w c g hgx).IsGreedy (coneInst hρ w c g hgx).x α)
    (hβ : (coneInst hρ w c g hgx).IsGreedy (coneInst hρ w c g hgx).g β) :
    ∃ ms, (coneInst hρ w c g hgx).IsSeq α ms β ∧ (ms.length : ℝ) ≤ lam * (cone G ρ w).card := by
  have hcard : Fintype.card (ConeV G ρ w) = (cone G ρ w).card := Fintype.card_coe _
  by_cases hg0 : g = 0
  · obtain ⟨ms, h1, h2⟩ := hlin (ConeV G ρ w) (coneInst hρ w c g hgx) (hcones w) hg0 α β hα hβ
    exact ⟨ms, h1, by rwa [hcard] at h2⟩
  · obtain ⟨ms, h1, h2⟩ := lem_2_3_proved (coneInst hρ w c g hgx) ((Fin.pos_iff_ne_zero' _).2 hg0) α β hα hβ
    refine ⟨ms, h1, ?_⟩
    rw [hcard] at h2
    have h2' : (ms.length : ℝ) ≤ 2 * (cone G ρ w).card := by exact_mod_cast h2
    have h3 : (0 : ℝ) ≤ (cone G ρ w).card := Nat.cast_nonneg _
    nlinarith

/-- One step of the sweep (R2): if every vertex before `w` is greedy in the proper colouring `c`, then within
`lam · |C_w|` moves all vertices up to `w` are greedy. -/
theorem step (𝒞 : InstanceClass) (lam : ℝ) (hlam : 2 ≤ lam)
    (hlin : ∀ (W : Type) [Fintype W] [DecidableEq W] (I : Instance W), 𝒞 W I.toSkeleton → I.g = 0 →
      ∀ α β : W → Fin 4, I.IsGreedy I.x α → I.IsGreedy I.g β →
        ∃ ms, I.IsSeq α ms β ∧ (ms.length : ℝ) ≤ lam * Fintype.card W)
    (hρ : IsDegOrder G 2 ρ) (hcones : ∀ w, 𝒞 (ConeV G ρ w) (coneSkeleton G ρ hρ w))
    (w : V) (c : V → Fin 4) (hc : IsProperFn G c) (hgr : ∀ u, ρ u < ρ w → IsGr G ρ c u) :
    ∃ ms c', IsSeq G (fun _ => univ) c ms c' ∧ (ms.length : ℝ) ≤ lam * (cone G ρ w).card ∧
      ∀ u, ρ u ≤ ρ w → IsGr G ρ c' u := by
  obtain ⟨g, hg⟩ := exists_isLeastFree ((laterNbrs G ρ w).image c)
    (lt_of_le_of_lt (card_image_le.trans (hρ w)) (by norm_num))
  by_cases hxg : c w = g
  · refine ⟨[], c, rfl, by simp only [List.length_nil, Nat.cast_zero]; positivity, fun u hu => ?_⟩
    rcases lt_or_eq_of_le hu with h | h
    · exact hgr u h
    · have huw := ρ.injective h
      subst huw
      unfold IsGr
      rw [hxg]
      exact hg
  · have hfree : c w ∉ (laterNbrs G ρ w).image c := by
      intro h
      obtain ⟨v, hv, hcv⟩ := mem_image.1 h
      exact hc w v (mem_laterNbrs.1 hv).1 hcv.symm
    have hgx : g < c w := by
      rcases lt_trichotomy g (c w) with h | h | h
      · exact h
      · exact absurd h.symm hxg
      · exact absurd (hg.2.2 (c w) (mem_univ _) h) hfree
    obtain ⟨β, hβ, -⟩ := def_2_2_greedy_proved (coneInst hρ w c g hgx) (coneInst hρ w c g hgx).g
    have hα := isGreedy_x hρ w c g hgx hgr
    obtain ⟨ms, hms, hlen⟩ := cone_moves 𝒞 lam hlam hlin hρ hcones w c g hgx _ β hα hβ
    refine ⟨ms.map (fun m => (m.1.1, m.2)), glue w c β, ?_, by simpa using hlen,
      isGr_after hρ w c g hgx hg hgr β hβ⟩
    have h := isSeq_lift hρ w c g hgx hc hg.2.1 ms _ β hms
    rwa [glue_val] at h

/-- `|C_t|` indexed by the position `t` (`0` beyond `n`). -/
noncomputable def coneSize (G : SimpleGraph V) {n : ℕ} (ρ : V ≃ Fin n) (i : ℕ) : ℝ :=
  if h : i < n then ((cone G ρ (ρ.symm ⟨i, h⟩)).card : ℝ) else 0

omit [DecidableEq V] in
theorem sum_coneSize (G : SimpleGraph V) {n : ℕ} (ρ : V ≃ Fin n) :
    ∑ i ∈ range n, coneSize G ρ i = ∑ w, ((cone G ρ w).card : ℝ) := by
  rw [← Fin.sum_univ_eq_sum_range, ← Equiv.sum_comp ρ.symm]
  refine sum_congr rfl fun i _ => ?_
  simp only [coneSize, dite_eq_left i.isLt, Fin.eta]

/-- The sweep (R3): from a proper colouring, within `lam · ∑_{t < k} |C_t|` moves the first `k` vertices are
greedy. -/
theorem sweep_upto (𝒞 : InstanceClass) (lam : ℝ) (hlam : 2 ≤ lam)
    (hlin : ∀ (W : Type) [Fintype W] [DecidableEq W] (I : Instance W), 𝒞 W I.toSkeleton → I.g = 0 →
      ∀ α β : W → Fin 4, I.IsGreedy I.x α → I.IsGreedy I.g β →
        ∃ ms, I.IsSeq α ms β ∧ (ms.length : ℝ) ≤ lam * Fintype.card W)
    (hρ : IsDegOrder G 2 ρ) (hcones : ∀ w, 𝒞 (ConeV G ρ w) (coneSkeleton G ρ hρ w)) :
    ∀ k, k ≤ n → ∀ c : V → Fin 4, IsProperFn G c →
      ∃ ms c', IsSeq G (fun _ => univ) c ms c' ∧ (ms.length : ℝ) ≤ lam * ∑ i ∈ range k, coneSize G ρ i ∧
        ∀ u, (ρ u).val < k → IsGr G ρ c' u
  | 0, _, c, _ => ⟨[], c, rfl, by simp, fun u hu => absurd hu (Nat.not_lt_zero _)⟩
  | k + 1, hk, c, hc => by
      obtain ⟨ms₁, c₁, hs₁, hl₁, hg₁⟩ := sweep_upto 𝒞 lam hlam hlin hρ hcones k (by omega) c hc
      have hc₁ := isProperFn_of_isSeq G _ ms₁ c c₁ hs₁ hc
      have hkn : k < n := by omega
      have hρw : ρ (ρ.symm ⟨k, hkn⟩) = ⟨k, hkn⟩ := ρ.apply_symm_apply _
      obtain ⟨ms₂, c₂, hs₂, hl₂, hg₂⟩ := step 𝒞 lam hlam hlin hρ hcones (ρ.symm ⟨k, hkn⟩) c₁ hc₁
        (fun u hu => hg₁ u (by rw [hρw] at hu; exact hu))
      refine ⟨ms₁ ++ ms₂, c₂, isSeq_append G _ ms₁ ms₂ c c₁ c₂ hs₁ hs₂, ?_, fun u hu => hg₂ u ?_⟩
      · have hsz : coneSize G ρ k = (cone G ρ (ρ.symm ⟨k, hkn⟩)).card := by
          simp only [coneSize, dite_eq_left hkn]
        rw [sum_range_succ, hsz, List.length_append, Nat.cast_add, mul_add]
        linarith
      · rw [hρw, Fin.le_iff_val_le_val]
        simp only
        omega

end Sweep

end Sweep

theorem lem_2_5_proved (𝒞 : InstanceClass) (lam : ℝ) (hlam : 2 ≤ lam)
    (hlin : ∀ (W : Type) [Fintype W] [DecidableEq W] (I : Instance W), 𝒞 W I.toSkeleton → I.g = 0 →
      ∀ α β : W → Fin 4, I.IsGreedy I.x α → I.IsGreedy I.g β →
        ∃ ms, I.IsSeq α ms β ∧ (ms.length : ℝ) ≤ lam * Fintype.card W)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (ρ : V ≃ Fin n)
    (hρ : IsDegOrder G 2 ρ) (hcones : ∀ w, 𝒞 (ConeV G ρ w) (coneSkeleton G ρ hρ w)) :
    (recolGraph G 4).ediam ≠ ⊤ ∧
      ((recolGraph G 4).diam : ℝ) ≤ 2 * lam * ∑ w, ((cone G ρ w).card : ℝ) ∧
      2 * lam * ∑ w, ((cone G ρ w).card : ℝ) ≤ lam * n * (n + 1) := by
  obtain ⟨γ, -, huniq⟩ := sweep_greedy_unique_proved G ρ hρ
  set B := lam * ∑ w, ((cone G ρ w).card : ℝ) with hB
  have hB0 : 0 ≤ B := mul_nonneg (by linarith) (sum_nonneg fun _ _ => Nat.cast_nonneg _)
  -- (R3) from every colouring, `γ` is reached within `B` moves
  have hreach : ∀ C : G.Coloring (Fin 4), ∃ Γ : G.Coloring (Fin 4), ⇑Γ = γ ∧
      ∃ ℓ : ℕ, (ℓ : ℝ) ≤ B ∧ (recolGraph G 4).edist C Γ ≤ ℓ := by
    intro C
    obtain ⟨ms, c', hs, hl, hgr⟩ :=
      Sweep.sweep_upto 𝒞 lam hlam hlin hρ hcones n le_rfl C (fun u v huv => C.valid huv)
    have hc' : c' = γ := huniq c' (fun v => hgr v (ρ v).isLt)
    subst hc'
    obtain ⟨Γ, hΓ, hd⟩ := Sweep.edist_of_isSeq G _ ms C c' hs
    exact ⟨Γ, hΓ, ms.length, by rwa [Sweep.sum_coneSize] at hl, hd⟩
  -- (R4) any two colourings are joined through `γ`
  have hdist : ∀ C₁ C₂ : G.Coloring (Fin 4), (recolGraph G 4).edist C₁ C₂ ≤ (⌊2 * B⌋₊ : ℕ∞) := by
    intro C₁ C₂
    obtain ⟨Γ₁, h₁, ℓ₁, hl₁, hd₁⟩ := hreach C₁
    obtain ⟨Γ₂, h₂, ℓ₂, hl₂, hd₂⟩ := hreach C₂
    have hΓ : Γ₁ = Γ₂ := DFunLike.coe_injective (h₁.trans h₂.symm)
    subst hΓ
    have hle : ℓ₁ + ℓ₂ ≤ ⌊2 * B⌋₊ := Nat.le_floor (by push_cast; linarith)
    calc (recolGraph G 4).edist C₁ C₂
        ≤ (recolGraph G 4).edist C₁ Γ₁ + (recolGraph G 4).edist Γ₁ C₂ := SimpleGraph.edist_triangle
      _ ≤ ℓ₁ + ℓ₂ := add_le_add hd₁ (by rw [SimpleGraph.edist_comm]; exact hd₂)
      _ ≤ (⌊2 * B⌋₊ : ℕ∞) := by exact_mod_cast hle
  have hediam : (recolGraph G 4).ediam ≤ (⌊2 * B⌋₊ : ℕ∞) := SimpleGraph.ediam_le_iff.2 hdist
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hediam, ?_, ?_⟩
  · have h1 : (recolGraph G 4).diam ≤ ⌊2 * B⌋₊ := ENat.toNat_le_of_le_natCast hediam
    calc ((recolGraph G 4).diam : ℝ) ≤ (⌊2 * B⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ 2 * B := Nat.floor_le (by linarith)
      _ = 2 * lam * ∑ w, ((cone G ρ w).card : ℝ) := by rw [hB]; ring
  · have h := (def_2_1_cones_proved G ρ).2.2
    have h' : 2 * ∑ w, ((cone G ρ w).card : ℝ) ≤ (n : ℝ) * (n + 1) := by exact_mod_cast h
    calc 2 * lam * ∑ w, ((cone G ρ w).card : ℝ) = lam * (2 * ∑ w, ((cone G ρ w).card : ℝ)) := by ring
      _ ≤ lam * ((n : ℝ) * (n + 1)) := mul_le_mul_of_nonneg_left h' (by linarith)
      _ = lam * n * (n + 1) := by ring

end Cereceda
