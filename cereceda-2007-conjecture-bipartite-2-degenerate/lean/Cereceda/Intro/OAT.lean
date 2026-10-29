/-
Cereceda/Intro/OAT.lean — bipartite OAT graphs are semi-false (short v3.90 l. 179-192): complete bipartite graphs,
disjoint unions and adding a vertex `u` with `N(u) ⊆ N(v)` keep a graph semi-false, and by induction along the
construction a bipartite OAT graph is semi-false.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.OAT

namespace Cereceda

open SimpleGraph

/-! ### Semi-false along an injective rank `f : V → ℕ` -/

/-- The three cases of `IsSemiFalse` at `u`, for the order given by `f` (a smaller value means added earlier). -/
def SFAt {V : Type} (G : SimpleGraph V) (f : V → ℕ) (u : V) : Prop :=
  (∀ w, G.Adj u w → ¬ f w < f u) ∨
  (∃ w, G.Adj u w ∧ f w < f u ∧ ∀ w', G.Adj u w' → f w' < f u → w' = w) ∨
  (∃ v, f v < f u ∧ ∀ w, G.Adj u w → f w < f u → G.Adj v w)

/-- `G` is semi-false along some injective `f : V → ℕ`; for finite `V` this is `IsSemiFalse G` (`isSemiFalse_iff`). -/
def SFNat {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ f : V → ℕ, Function.Injective f ∧ ∀ u, SFAt G f u

/-- An injective `f : V → ℕ` on a finite `V` is ranked by an order `ρ : V ≃ Fin (card V)` with the same comparisons. -/
theorem exists_equiv_fin_lt_iff {V : Type} [Fintype V] (f : V → ℕ) (hf : Function.Injective f) :
    ∃ ρ : V ≃ Fin (Fintype.card V), ∀ a b, ρ a < ρ b ↔ f a < f b := by
  let : LinearOrder V := LinearOrder.lift' f hf
  exact ⟨(Fintype.orderIsoFinOfCardEq V rfl).symm.toEquiv,
    fun a b => (Fintype.orderIsoFinOfCardEq V rfl).symm.lt_iff_lt⟩

/-- `IsSemiFalse` (for any `Fintype` instance) is semi-falseness along an injective rank into `ℕ`. -/
theorem isSemiFalse_iff {V : Type} [Fintype V] (G : SimpleGraph V) : IsSemiFalse G ↔ SFNat G := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨fun u => (ρ u : ℕ), Fin.val_injective.comp ρ.injective, hρ⟩
  · rintro ⟨f, hf, hG⟩
    obtain ⟨ρ, hρ⟩ := exists_equiv_fin_lt_iff f hf
    refine ⟨ρ, fun u => ?_⟩
    simp only [hρ]
    exact hG u

/-- Transfer of the semi-false cases along a map `φ` that keeps adjacency and the order, when every earlier neighbour of
`φ a` is some `φ b`. -/
theorem sfAt_transfer {V X : Type} {G : SimpleGraph V} {K : SimpleGraph X} (φ : V → X) {fG : V → ℕ} {fK : X → ℕ}
    (hadj : ∀ a b, K.Adj (φ a) (φ b) ↔ G.Adj a b) (hlt : ∀ a b, fK (φ a) < fK (φ b) ↔ fG a < fG b)
    (hold : ∀ a y, K.Adj (φ a) y → fK y < fK (φ a) → ∃ b, φ b = y) {a : V} (h : SFAt G fG a) :
    SFAt K fK (φ a) := by
  rcases h with h | ⟨w, hw, hwa, huniq⟩ | ⟨v, hva, hv⟩
  · left
    intro y hy hya
    obtain ⟨b, rfl⟩ := hold a y hy hya
    exact h b ((hadj a b).1 hy) ((hlt b a).1 hya)
  · right; left
    refine ⟨φ w, (hadj a w).2 hw, (hlt w a).2 hwa, fun y hy hya => ?_⟩
    obtain ⟨b, rfl⟩ := hold a y hy hya
    rw [huniq b ((hadj a b).1 hy) ((hlt b a).1 hya)]
  · right; right
    refine ⟨φ v, (hlt v a).2 hva, fun y hy hya => ?_⟩
    obtain ⟨b, rfl⟩ := hold a y hy hya
    exact (hadj v b).2 (hv b ((hadj a b).1 hy) ((hlt b a).1 hya))

/-- `SFNat` is invariant under graph isomorphism. -/
theorem sfNat_of_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (hG : SFNat G) :
    SFNat H := by
  obtain ⟨f, hf, hfG⟩ := hG
  refine ⟨f ∘ e.symm, hf.comp e.symm.injective, fun u => ?_⟩
  have key := sfAt_transfer (K := H) (fK := f ∘ e.symm) e (fun a b => e.map_adj_iff) (fun a b => by simp)
    (fun a y _ _ => ⟨e.symm y, e.apply_symm_apply y⟩) (hfG (e.symm u))
  rwa [e.apply_symm_apply u] at key

/-- `IsSemiFalse` is invariant under graph isomorphism. -/
theorem isSemiFalse_of_iso {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (hG : IsSemiFalse G) : IsSemiFalse H :=
  (isSemiFalse_iff H).2 (sfNat_of_iso e ((isSemiFalse_iff G).1 hG))

/-- A finite type has a strict upper bound for any `f : V → ℕ`. -/
theorem exists_bound {V : Type} [Finite V] (f : V → ℕ) : ∃ N, ∀ a, f a < N := by
  obtain ⟨N, hN⟩ := (Set.finite_range f).bddAbove
  exact ⟨N + 1, fun a => Nat.lt_succ_of_le (hN ⟨a, rfl⟩)⟩

/-! ### The three operations of v3.90 l. 186-191 -/

/-- A disjoint union of two semi-false graphs is semi-false (the two ranks, interleaved). -/
theorem sfNat_sum {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (hG : SFNat G) (hH : SFNat H) :
    SFNat (G ⊕g H) := by
  obtain ⟨f, hf, hfG⟩ := hG
  obtain ⟨g, hg, hgH⟩ := hH
  refine ⟨Sum.elim (fun a => 2 * f a) (fun b => 2 * g b + 1), ?_, ?_⟩
  · rintro (a | b) (a' | b') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [hf (show f a = f a' by omega)]
    · omega
    · omega
    · rw [hg (show g b = g b' by omega)]
  · rintro (a | b)
    · refine sfAt_transfer Sum.inl (fun _ _ => Iff.rfl) (fun _ _ => by simp only [Sum.elim_inl]; omega) ?_ (hfG a)
      rintro a' (b | b) hy -
      · exact ⟨b, rfl⟩
      · simp at hy
    · refine sfAt_transfer Sum.inr (fun _ _ => Iff.rfl) (fun _ _ => by simp only [Sum.elim_inr]; omega) ?_ (hgH b)
      rintro b' (a | a) hy -
      · simp at hy
      · exact ⟨a, rfl⟩

/-- Adding a vertex `u` with `N(u) = S ⊆ N(v)` keeps a finite graph semi-false (`u` is added last). -/
theorem sfNat_addVertex {V : Type} [Finite V] {G : SimpleGraph V} (v : V) {S : Set V} (hS : S ⊆ G.neighborSet v)
    (hG : SFNat G) : SFNat (addVertex G S) := by
  obtain ⟨f, hf, hfG⟩ := hG
  obtain ⟨N, hN⟩ := exists_bound f
  refine ⟨fun x => x.elim N f, ?_, ?_⟩
  · rintro (_ | a) (_ | b) h
    · rfl
    · have := hN b
      simp only [Option.elim_none, Option.elim_some] at h
      omega
    · have := hN a
      simp only [Option.elim_none, Option.elim_some] at h
      omega
    · simp only [Option.elim_some] at h
      rw [hf h]
  · rintro (_ | a)
    · right; right
      refine ⟨some v, hN v, ?_⟩
      rintro (_ | w) hw -
      · exact hw.elim
      · exact hS hw
    · refine sfAt_transfer some (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) ?_ (hfG a)
      rintro a' (_ | b) - hy
      · exact ((Nat.lt_asymm (hN a')) hy).elim
      · exact ⟨b, rfl⟩

/-- Attaching a clique of size `k ≤ 1` keeps a finite graph semi-false (its vertex, if any, has degree `1`). -/
theorem sfNat_attachClique {V : Type} [Finite V] {G : SimpleGraph V} (v : V) {k : ℕ} (hk : k ≤ 1)
    (hG : SFNat G) : SFNat (attachClique G v k) := by
  obtain ⟨f, hf, hfG⟩ := hG
  obtain ⟨N, hN⟩ := exists_bound f
  refine ⟨Sum.elim f (fun j => N + j), ?_, ?_⟩
  · rintro (a | i) (b | j) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [hf h]
    · have := hN a
      omega
    · have := hN b
      omega
    · have hij : i = j := Fin.ext (by omega)
      rw [hij]
  · rintro (a | i)
    · refine sfAt_transfer Sum.inl (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) ?_ (hfG a)
      rintro a' (b | j) - hy
      · exact ⟨b, rfl⟩
      · have := hN a'
        simp only [Sum.elim_inl, Sum.elim_inr] at hy
        omega
    · right; left
      refine ⟨Sum.inl v, rfl, ?_, ?_⟩
      · have := hN v
        simp only [Sum.elim_inl, Sum.elim_inr]
        omega
      · rintro (b | j) hb -
        · rw [hb]
        · have := i.isLt
          have := j.isLt
          exact absurd (Fin.ext (by omega)) hb

/-- A join of two edgeless finite graphs (a complete bipartite graph) is semi-false: start from a vertex `x` of the
first side, add the other side (each of degree `1`), then the rest of the first side (each with neighbourhood `N(x)`). -/
theorem sfNat_joinGraph_of_edgeless {V W : Type} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : ∀ a b, ¬ G.Adj a b) (hH : ∀ a b, ¬ H.Adj a b) : SFNat (joinGraph G H) := by
  classical
  obtain ⟨nV, ⟨eV⟩⟩ := Finite.exists_equiv_fin V
  obtain ⟨nW, ⟨eW⟩⟩ := Finite.exists_equiv_fin W
  rcases isEmpty_or_nonempty V with hV | hV
  · refine ⟨Sum.elim (fun a => isEmptyElim a) (fun b => (eW b : ℕ)), ?_, ?_⟩
    · rintro (a | b) (a' | b') h
      · exact isEmptyElim a
      · exact isEmptyElim a
      · exact isEmptyElim a'
      · simp only [Sum.elim_inr] at h
        rw [eW.injective (Fin.ext h)]
    · rintro (a | b)
      · exact isEmptyElim a
      · left
        rintro (a | b') hw
        · exact isEmptyElim a
        · exact absurd hw (hH b b')
  · obtain ⟨x⟩ := hV
    refine ⟨Sum.elim (fun a => if a = x then 0 else nW + 1 + eV a) (fun b => eW b + 1), ?_, ?_⟩
    · rintro (a | b) (a' | b') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · split_ifs at h with ha ha'
        · rw [ha, ha']
        · omega
        · omega
        · rw [eV.injective (Fin.ext (show (eV a : ℕ) = eV a' by omega))]
      · have := (eW b').isLt
        split_ifs at h
        omega
      · have := (eW b).isLt
        split_ifs at h
        omega
      · rw [eW.injective (Fin.ext (show (eW b : ℕ) = eW b' by omega))]
    · rintro (a | b)
      · by_cases ha : a = x
        · left
          rintro w - hw
          subst ha
          simp at hw
        · right; right
          refine ⟨Sum.inl x, ?_, ?_⟩
          · simp only [Sum.elim_inl, ite_eq_right ha, ↓reduceIte]
            omega
          · rintro (b | b) hb -
            · exact absurd hb (hG a b)
            · trivial
      · right; left
        refine ⟨Sum.inl x, trivial, ?_, ?_⟩
        · simp only [Sum.elim_inl, Sum.elim_inr, ↓reduceIte]
          omega
        · rintro (a | b') hb hlt
          · by_cases hax : a = x
            · rw [hax]
            · have := (eW b).isLt
              simp only [Sum.elim_inl, Sum.elim_inr, ite_eq_right hax] at hlt
              omega
          · exact absurd hb (hH b b')

/-! ### Bipartite parts -/

/-- A graph with a homomorphism into a bipartite graph is bipartite. -/
theorem isBipartite_of_hom {V X : Type} {G : SimpleGraph V} {K : SimpleGraph X} (φ : G →g K)
    (h : K.IsBipartite) : G.IsBipartite :=
  Colorable.of_hom φ h

/-- A graph with a triangle is not bipartite. -/
theorem not_isBipartite_of_triangle {X : Type} {K : SimpleGraph X} {x y z : X} (hxy : K.Adj x y) (hyz : K.Adj y z)
    (hxz : K.Adj x z) : ¬ K.IsBipartite := by
  rintro ⟨C⟩
  have key : ∀ p q r : Fin 2, p ≠ q → q ≠ r → p ≠ r → False := by decide
  exact key _ _ _ (C.valid hxy) (C.valid hyz) (C.valid hxz)

/-- In a bipartite join with a nonempty second part, the first part is edgeless (else a triangle). -/
theorem joinGraph_left_edgeless {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : (joinGraph G H).IsBipartite) (b : W) (a a' : V) : ¬ G.Adj a a' := fun hG =>
  not_isBipartite_of_triangle (x := Sum.inl a) (y := Sum.inl a') (z := Sum.inr b) hG trivial trivial h

/-- In a bipartite join with a nonempty first part, the second part is edgeless (else a triangle). -/
theorem joinGraph_right_edgeless {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : (joinGraph G H).IsBipartite) (a : V) (b b' : W) : ¬ H.Adj b b' := fun hH =>
  not_isBipartite_of_triangle (x := Sum.inr b) (y := Sum.inr b') (z := Sum.inl a) hH trivial trivial h

/-- A bipartite graph with an attached clique on `Fin k` has `k ≤ 1` (else a triangle). -/
theorem le_one_of_attachClique_bipartite {V : Type} {G : SimpleGraph V} {v : V} {k : ℕ}
    (h : (attachClique G v k).IsBipartite) : k ≤ 1 := by
  by_contra hk
  have hk' : 1 < k := by omega
  have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, hk'⟩ := fun h01 => Nat.zero_ne_one (congrArg Fin.val h01)
  exact not_isBipartite_of_triangle (K := attachClique G v k) (x := Sum.inr ⟨0, by omega⟩) (y := Sum.inr ⟨1, hk'⟩)
    (z := Sum.inl v) h01 rfl rfl h

/-! ### OAT graphs -/

/-- An OAT graph is finite. -/
theorem IsOAT.finite {V : Type} {G : SimpleGraph V} (hG : IsOAT G) : Finite V := by
  induction hG with
  | single => infer_instance
  | union _ _ ihG ihH => infer_instance
  | join _ _ ihG ihH => infer_instance
  | addSub _ _ _ _ ih => infer_instance
  | attach _ _ _ ih => infer_instance
  | iso _ he ih => exact Finite.of_equiv _ he.some.toEquiv

/-- An OAT graph is nonempty. -/
theorem IsOAT.nonempty {V : Type} {G : SimpleGraph V} (hG : IsOAT G) : Nonempty V := by
  induction hG with
  | single => infer_instance
  | union _ _ ihG _ => exact ⟨Sum.inl ihG.some⟩
  | join _ _ ihG _ => exact ⟨Sum.inl ihG.some⟩
  | addSub _ _ _ _ _ => exact ⟨none⟩
  | attach v _ _ _ => exact ⟨Sum.inl v⟩
  | iso _ he ih => exact ⟨he.some ih.some⟩

/-- A bipartite OAT graph is semi-false along an injective rank (induction along the construction, v3.90 l. 182-192). -/
theorem IsOAT.sfNat {V : Type} {G : SimpleGraph V} (hG : IsOAT G) : G.IsBipartite → SFNat G := by
  induction hG with
  | single =>
    intro _
    exact ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b, fun _ => Or.inl fun _ hw => by simp at hw⟩
  | @union V W G H _ _ ihG ihH =>
    intro hb
    exact sfNat_sum (ihG (isBipartite_of_hom ⟨Sum.inl, fun h => h⟩ hb))
      (ihH (isBipartite_of_hom ⟨Sum.inr, fun h => h⟩ hb))
  | @join V W G H hG hH _ _ =>
    intro hb
    have := hG.finite
    have := hH.finite
    obtain ⟨a0⟩ := hG.nonempty
    obtain ⟨b0⟩ := hH.nonempty
    exact sfNat_joinGraph_of_edgeless (joinGraph_left_edgeless hb b0) (joinGraph_right_edgeless hb a0)
  | @addSub V G v S hG hS ih =>
    intro hb
    have := hG.finite
    exact sfNat_addVertex v hS (ih (isBipartite_of_hom ⟨some, fun h => h⟩ hb))
  | @attach V G v k hG ih =>
    intro hb
    have := hG.finite
    exact sfNat_attachClique v (le_one_of_attachClique_bipartite hb)
      (ih (isBipartite_of_hom ⟨Sum.inl, fun h => h⟩ hb))
  | @iso V W G H _ he ih =>
    intro hb
    obtain ⟨e⟩ := he
    exact sfNat_of_iso e (ih (isBipartite_of_hom ⟨e, fun h => e.map_adj_iff.2 h⟩ hb))

/-! ### The four statements -/

/-- The complete bipartite graph is the join of two edgeless graphs. -/
theorem completeBipartite_eq_joinGraph (V W : Type) :
    completeBipartiteGraph V W = joinGraph (⊥ : SimpleGraph V) (⊥ : SimpleGraph W) := by
  ext (a | b) (a' | b') <;> simp

/-- (a) A complete bipartite graph is semi-false (v3.90 l. 186-188). -/
theorem intro_completeBipartite_semiFalse_proved (m n : ℕ) : IsSemiFalse (completeBipartiteGraph (Fin m) (Fin n)) := by
  rw [isSemiFalse_iff, completeBipartite_eq_joinGraph]
  exact sfNat_joinGraph_of_edgeless (fun _ _ => by simp) (fun _ _ => by simp)

/-- (b) A disjoint union of two semi-false graphs is semi-false (v3.90 l. 190-191). -/
theorem intro_union_semiFalse_proved {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) : IsSemiFalse G → IsSemiFalse H → IsSemiFalse (G ⊕g H) := fun hG hH =>
  (isSemiFalse_iff _).2 (sfNat_sum ((isSemiFalse_iff G).1 hG) ((isSemiFalse_iff H).1 hH))

/-- (c) Adding a vertex `u` with `N(u) ⊆ N(v)` keeps a graph semi-false (v3.90 l. 191). -/
theorem intro_addVertex_semiFalse_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V) (S : Set V)
    (hS : S ⊆ G.neighborSet v) : IsSemiFalse G → IsSemiFalse (addVertex G S) := fun hG =>
  (isSemiFalse_iff _).2 (sfNat_addVertex v hS ((isSemiFalse_iff G).1 hG))

/-- (main) A bipartite OAT graph is semi-false (v3.90 l. 179-192). -/
theorem intro_oat_semiFalse_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : IsOAT G)
    (hbip : G.IsBipartite) : IsSemiFalse G :=
  (isSemiFalse_iff G).2 (hG.sfNat hbip)

/-- v3.90 l. 182-184: "Each operation adds edges only at a new vertex or between the two graphs that it combines, so every
graph built along the way is an induced subgraph of the final graph": each of the four operations embeds the graphs it
is given as induced subgraphs (`↪g` preserves and reflects adjacency), and embeddings compose (`Embedding.trans`). -/
theorem intro_oat_induced_proved {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (S : Set V) (v : V) (k : ℕ) :
    Nonempty (G ↪g G ⊕g H) ∧ Nonempty (H ↪g G ⊕g H) ∧ Nonempty (G ↪g joinGraph G H) ∧
      Nonempty (H ↪g joinGraph G H) ∧ Nonempty (G ↪g addVertex G S) ∧ Nonempty (G ↪g attachClique G v k) :=
  ⟨⟨⟨⟨Sum.inl, Sum.inl_injective⟩, Iff.rfl⟩⟩, ⟨⟨⟨Sum.inr, Sum.inr_injective⟩, Iff.rfl⟩⟩,
    ⟨⟨⟨Sum.inl, Sum.inl_injective⟩, Iff.rfl⟩⟩, ⟨⟨⟨Sum.inr, Sum.inr_injective⟩, Iff.rfl⟩⟩,
    ⟨⟨⟨some, Option.some_injective _⟩, Iff.rfl⟩⟩, ⟨⟨⟨Sum.inl, Sum.inl_injective⟩, Iff.rfl⟩⟩⟩

end Cereceda
