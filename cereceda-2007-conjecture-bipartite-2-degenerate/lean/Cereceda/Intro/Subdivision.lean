/-
Cereceda/Intro/Subdivision.lean — once-subdivided graphs: bipartite, 2-degenerate, Grundy <= 3; treewidth of subdivided K_m.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Basic
import Cereceda.Defs.Intro
import Cereceda.Setting.Degeneracy

namespace Cereceda

open Finset

namespace Subdivision

section Helly

variable {ι ι' : Type}

/-- `u` and `v` are joined by a walk of `T` that stays inside `S`. -/
def JoinedIn (T : SimpleGraph ι) (S : Set ι) (u v : ι) : Prop :=
  ∃ p : T.Walk u v, ∀ z ∈ p.support, z ∈ S

/-- Any two points of `S` are joined inside `S` (`S` may be empty). -/
def SetConn (T : SimpleGraph ι) (S : Set ι) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, JoinedIn T S u v

variable {T : SimpleGraph ι} {S S' : Set ι} {u v w : ι}

lemma JoinedIn.refl (hu : u ∈ S) : JoinedIn T S u u :=
  ⟨.nil, by simpa using hu⟩

lemma JoinedIn.symm (h : JoinedIn T S u v) : JoinedIn T S v u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, fun z hz => hp z (by simpa using hz)⟩

lemma JoinedIn.trans (h1 : JoinedIn T S u v) (h2 : JoinedIn T S v w) : JoinedIn T S u w := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨q, hq⟩ := h2
  refine ⟨p.append q, fun z hz => ?_⟩
  rcases (SimpleGraph.Walk.mem_support_append_iff p q).mp hz with h | h
  exacts [hp z h, hq z h]

lemma JoinedIn.mono (h : JoinedIn T S u v) (hS : S ⊆ S') : JoinedIn T S' u v := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun z hz => hS (hp z hz)⟩

lemma setConn_of_connected (h : (T.induce S).Connected) : SetConn T S := by
  intro u hu v hv
  obtain ⟨p⟩ := h.preconnected ⟨u, hu⟩ ⟨v, hv⟩
  have key : ∀ z ∈ (p.map (SimpleGraph.Embedding.induce S).toHom).support, z ∈ S := by
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨z', -, rfl⟩ := hz
    exact z'.2
  exact ⟨_, key⟩

/-- A set with a point `c` adjacent to all its other points is connected. -/
lemma connected_of_center {c : ι} (hc : c ∈ S) (h : ∀ w ∈ S, w = c ∨ T.Adj c w) :
    (T.induce S).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨c, hc⟩, fun ⟨w, hw⟩ => ?_⟩
  rcases h w hw with rfl | hadj
  · rfl
  · exact SimpleGraph.Adj.reachable (by simpa using hadj)

/-- A map that sends every edge to an edge or to a single point sends walks to walks. -/
lemma exists_walk_image {T' : SimpleGraph ι'} (f : ι → ι')
    (hf : ∀ a b, T.Adj a b → f a = f b ∨ T'.Adj (f a) (f b)) {u v : ι} (p : T.Walk u v) :
    ∃ q : T'.Walk (f u) (f v), ∀ z ∈ q.support, ∃ x ∈ p.support, f x = z := by
  induction p with
  | nil => exact ⟨.nil, by simp⟩
  | @cons a b c h p ih =>
    obtain ⟨q, hq⟩ := ih
    rcases hf a b h with heq | hadj
    · refine ⟨q.copy heq.symm rfl, fun z hz => ?_⟩
      rw [SimpleGraph.Walk.support_copy] at hz
      obtain ⟨x, hx, rfl⟩ := hq z hz
      exact ⟨x, by simp [hx], rfl⟩
    · refine ⟨.cons hadj q, fun z hz => ?_⟩
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨a, by simp, rfl⟩
      · obtain ⟨x, hx, rfl⟩ := hq z hz
        exact ⟨x, by simp [hx], rfl⟩

lemma SetConn.image {T' : SimpleGraph ι'} (f : ι → ι')
    (hf : ∀ a b, T.Adj a b → f a = f b ∨ T'.Adj (f a) (f b)) (h : SetConn T S) :
    SetConn T' (f '' S) := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  obtain ⟨p, hp⟩ := h u hu v hv
  obtain ⟨q, hq⟩ := exists_walk_image f hf p
  refine ⟨q, fun z hz => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hq z hz
  exact ⟨x, hp x hx, rfl⟩

/-- If `ℓ` has the unique neighbour `p`, then a connected set containing `ℓ` and another point contains `p`. -/
lemma mem_of_unique_nbr (hS : SetConn T S) {ℓ p y : ι} (hℓ : ℓ ∈ S) (hy : y ∈ S) (hne : y ≠ ℓ)
    (hp : ∀ q, T.Adj ℓ q → q = p) : p ∈ S := by
  obtain ⟨w, hw⟩ := hS ℓ hℓ y hy
  cases w with
  | nil => exact absurd rfl hne
  | cons h q =>
    rw [← hp _ h]
    exact hw _ (by simp)

/-- HELLY for subtrees: pairwise-intersecting connected node sets of a finite tree have a common node. Induction on
the number of nodes: remove a leaf `ℓ` (contract it into its neighbour `p`). -/
theorem helly_aux (n : ℕ) : ∀ {ι : Type} [Finite ι] (T : SimpleGraph ι), Nat.card ι = n → T.IsTree →
    ∀ {κ : Type} (S : κ → Set ι), (∀ k, SetConn T (S k)) → (∀ k l, (S k ∩ S l).Nonempty) →
    ∃ i, ∀ k, i ∈ S k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ T hn hT κ S hconn hint
  classical
  rcases subsingleton_or_nontrivial ι with hsub | hnt
  · obtain ⟨i⟩ := hT.connected.nonempty
    refine ⟨i, fun k => ?_⟩
    obtain ⟨x, hx, -⟩ := hint k k
    rwa [Subsingleton.elim i x]
  have := Fintype.ofFinite ι
  obtain ⟨ℓ, hℓ⟩ := hT.exists_vert_degree_one_of_nontrivial
  obtain ⟨p, hℓp, hp⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hℓ
  have hT' : (T.induce ({ℓ}ᶜ : Set ι)).IsTree :=
    ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hℓ, hT.isAcyclic.induce _⟩
  have hcard : Nat.card ({ℓ}ᶜ : Set ι) < n := hn ▸ Finite.card_subtype_lt (x := ℓ) (by simp)
  have hpℓ : p ∈ ({ℓ}ᶜ : Set ι) := by simpa using hℓp.ne.symm
  let f : ι → ({ℓ}ᶜ : Set ι) := fun x => if h : x = ℓ then ⟨p, hpℓ⟩ else ⟨x, h⟩
  have hfℓ : f ℓ = ⟨p, hpℓ⟩ := by simp [f]
  have hf' : ∀ x (h : x ≠ ℓ), f x = ⟨x, h⟩ := fun x h => by simp [f, h]
  have hf : ∀ a b, T.Adj a b → f a = f b ∨ (T.induce ({ℓ}ᶜ : Set ι)).Adj (f a) (f b) := by
    intro a b hab
    by_cases ha : a = ℓ
    · subst ha
      obtain rfl := hp b hab
      exact Or.inl (by rw [hfℓ, hf' _ hpℓ])
    by_cases hb : b = ℓ
    · subst hb
      obtain rfl := hp a hab.symm
      exact Or.inl (by rw [hfℓ, hf' _ hpℓ])
    right
    rw [hf' a ha, hf' b hb]
    simpa using hab
  obtain ⟨i', hi'⟩ := ih _ hcard _ rfl hT' (fun k => f '' S k) (fun k => (hconn k).image f hf)
    (fun k l => by
      obtain ⟨x, hxk, hxl⟩ := hint k l
      exact ⟨f x, ⟨x, hxk, rfl⟩, ⟨x, hxl, rfl⟩⟩)
  by_cases hsing : ∃ k, S k ⊆ {ℓ}
  · obtain ⟨k, hk⟩ := hsing
    refine ⟨ℓ, fun l => ?_⟩
    obtain ⟨x, hxk, hxl⟩ := hint k l
    rwa [← Set.mem_singleton_iff.mp (hk hxk)]
  refine ⟨i'.1, fun k => ?_⟩
  obtain ⟨x, hx, hfx⟩ := hi' k
  by_cases hxℓ : x = ℓ
  · subst hxℓ
    rw [← hfx, hfℓ]
    obtain ⟨y, hy, hyℓ⟩ := Set.not_subset.mp (fun h => hsing ⟨k, h⟩)
    exact mem_of_unique_nbr (hconn k) hx hy (by simpa using hyℓ) hp
  · rw [← hfx, hf' x hxℓ]
    exact hx

theorem helly {ι : Type} [Finite ι] {T : SimpleGraph ι} (hT : T.IsTree) {κ : Type} (S : κ → Set ι)
    (hconn : ∀ k, SetConn T (S k)) (hint : ∀ k l, (S k ∩ S l).Nonempty) : ∃ i, ∀ k, i ∈ S k :=
  helly_aux _ T rfl hT S hconn hint

end Helly

section Graph

variable {V : Type} {G : SimpleGraph V}

@[simp] lemma not_adj_inl_inl (x y : V) : ¬ (subdivision G).Adj (.inl x) (.inl y) := id
@[simp] lemma not_adj_inr_inr (e f : G.edgeSet) : ¬ (subdivision G).Adj (.inr e) (.inr f) := id
@[simp] lemma adj_inl_inr (x : V) (e : G.edgeSet) :
    (subdivision G).Adj (.inl x) (.inr e) ↔ x ∈ (e : Sym2 V) := Iff.rfl
@[simp] lemma adj_inr_inl (x : V) (e : G.edgeSet) :
    (subdivision G).Adj (.inr e) (.inl x) ↔ x ∈ (e : Sym2 V) := Iff.rfl

variable (G) in
/-- The colouring `inl ↦ 0`, `inr ↦ 1` is proper. -/
lemma isBipartite : (subdivision G).IsBipartite :=
  ⟨SimpleGraph.Coloring.mk (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1)) (by
    rintro (x | e) (y | f) h <;> simp_all)⟩

variable [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A subdivision vertex has at most two neighbours in any set. -/
lemma card_filter_adj_inr (s : Finset (V ⊕ G.edgeSet)) (e : G.edgeSet) :
    (s.filter ((subdivision G).Adj (.inr e))).card ≤ 2 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b =>
    refine (card_le_card (t := {.inl a, .inl b}) ?_).trans card_le_two
    intro u hu
    rcases u with y | f <;> simp_all

variable (G) in
lemma isDegenerate [DecidableRel G.Adj] : IsDegenerate (subdivision G) 2 := by
  intro s hs
  by_cases h : ∃ e, Sum.inr e ∈ s
  · obtain ⟨e, he⟩ := h
    exact ⟨_, he, card_filter_adj_inr s e⟩
  · simp only [not_exists] at h
    obtain ⟨v, hv⟩ := hs
    refine ⟨v, hv, ?_⟩
    rcases v with x | e
    · have : s.filter ((subdivision G).Adj (.inl x)) = ∅ := by
        refine filter_eq_empty_iff.mpr ?_
        rintro (y | f) hy
        · simp
        · exact absurd hy (h f)
      simp [this]
    · exact absurd hv (h e)

section Grundy

variable [DecidableRel G.Adj] {n : ℕ} {ρ : (V ⊕ G.edgeSet) ≃ Fin n} {c : V ⊕ G.edgeSet → ℕ}

/-- In a greedy colouring, the colour of `a` is at most its number of earlier neighbours. -/
lemma le_card_earlier (hc : IsGreedyRel (subdivision G) ρ c) (a : V ⊕ G.edgeSet) :
    c a ≤ (univ.filter (fun u => (subdivision G).Adj a u ∧ ρ u < ρ a)).card := by
  have h1 : range (c a) ⊆ (univ.filter (fun u => (subdivision G).Adj a u ∧ ρ u < ρ a)).image c :=
    fun y hy => (hc a).2 y (mem_range.mp hy)
  calc c a = (range (c a)).card := (card_range _).symm
    _ ≤ _ := card_le_card h1
    _ ≤ _ := card_image_le

/-- A subdivision vertex that comes before one of its neighbours has at most one earlier neighbour. -/
lemma card_earlier_inr_le_one (e : G.edgeSet) (x : V) (hx : x ∈ (e : Sym2 V))
    (hlt : ρ (.inr e) < ρ (.inl x)) :
    (univ.filter (fun u => (subdivision G).Adj (.inr e) u ∧ ρ u < ρ (.inr e))).card ≤ 1 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b =>
    rw [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · refine (card_le_card (t := {.inl b}) ?_).trans (card_singleton _).le
      rintro (y | f) hu
      · simp only [mem_filter, mem_univ, true_and, adj_inr_inl, Sym2.mem_iff] at hu
        rcases hu with ⟨rfl | rfl, h⟩
        · exact absurd (h.trans hlt) (lt_irrefl _)
        · simp
      · simp at hu
    · refine (card_le_card (t := {.inl a}) ?_).trans (card_singleton _).le
      rintro (y | f) hu
      · simp only [mem_filter, mem_univ, true_and, adj_inr_inl, Sym2.mem_iff] at hu
        rcases hu with ⟨rfl | rfl, h⟩
        · simp
        · exact absurd (h.trans hlt) (lt_irrefl _)
      · simp at hu

/-- Every colour of a greedy colouring of a subdivision is at most `2`. -/
lemma color_le_two (hc : IsGreedyRel (subdivision G) ρ c) (a : V ⊕ G.edgeSet) : c a ≤ 2 := by
  rcases a with x | e
  · by_contra hlt
    obtain ⟨u, hu, hcu⟩ := mem_image.mp ((hc (.inl x)).2 2 (by omega))
    rcases u with y | e
    · simp at hu
    · simp only [mem_filter, mem_univ, true_and, adj_inl_inr] at hu
      have := (le_card_earlier hc (.inr e)).trans (card_earlier_inr_le_one e x hu.1 hu.2)
      omega
  · refine (le_card_earlier hc _).trans ((card_le_card fun u hu => ?_).trans (card_filter_adj_inr univ e))
    simp only [mem_filter, mem_univ, true_and] at hu ⊢
    exact hu.1

variable (G) in
lemma grundy_le_three : grundyNumber (subdivision G) ≤ 3 := by
  apply csSup_le'
  rintro k ⟨ρ, c, hc, rfl⟩
  calc (univ.image c).card ≤ (range 3).card := card_le_card (fun y hy => by
          obtain ⟨a, -, rfl⟩ := mem_image.mp hy
          exact mem_range.mpr (Nat.lt_succ_of_le (color_le_two hc a)))
    _ = 3 := card_range 3

end Grundy

section Upper

variable (G)

/-- The bags of the star decomposition: the centre `none` holds all original vertices; the leaf `some e` holds the
two ends of `e` and its subdivision vertex. -/
def starBag : Option G.edgeSet → Finset (V ⊕ G.edgeSet)
  | none => univ.map Function.Embedding.inl
  | some e => insert (.inr e) ((univ.filter (· ∈ (e : Sym2 V))).map Function.Embedding.inl)

@[simp] lemma inl_mem_starBag_none (x : V) : (.inl x : V ⊕ G.edgeSet) ∈ starBag G none := by
  simp [starBag]
@[simp] lemma inr_not_mem_starBag_none (e : G.edgeSet) : (.inr e : V ⊕ G.edgeSet) ∉ starBag G none := by
  simp [starBag]
@[simp] lemma inl_mem_starBag_some (x : V) (e : G.edgeSet) :
    (.inl x : V ⊕ G.edgeSet) ∈ starBag G (some e) ↔ x ∈ (e : Sym2 V) := by
  simp [starBag]
@[simp] lemma inr_mem_starBag_some (f e : G.edgeSet) :
    (.inr f : V ⊕ G.edgeSet) ∈ starBag G (some e) ↔ f = e := by
  simp [starBag]

lemma card_starBag_none : (starBag G none).card = Fintype.card V := by
  simp [starBag]

lemma card_starBag_some_le (e : G.edgeSet) : (starBag G (some e)).card ≤ 3 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b =>
    refine (card_le_card (t := {.inl a, .inl b, .inr ⟨s(a, b), he⟩}) ?_).trans card_le_three
    rintro (x | f) hz <;> simp_all

variable [DecidableRel G.Adj]

/-- The star decomposition of a once-subdivided graph. -/
def starDecomp : TreeDecomposition (subdivision G) (Option G.edgeSet) where
  T := SimpleGraph.starGraph none
  isTree := SimpleGraph.isTree_starGraph none
  bag := starBag G
  cover_vertex := by
    rintro (x | e)
    · exact ⟨none, by simp⟩
    · exact ⟨some e, by simp⟩
  cover_edge := by
    rintro (x | e) (y | f) h
    · simp at h
    · exact ⟨some f, by simpa using h, by simp⟩
    · exact ⟨some e, by simp, by simpa using h⟩
    · simp at h
  subtree := by
    rintro (x | e)
    · refine connected_of_center (c := none) (by simp) ?_
      rintro (_ | f) _
      · exact Or.inl rfl
      · exact Or.inr (by simp [SimpleGraph.starGraph_adj])
    · refine connected_of_center (c := some e) (by simp) ?_
      rintro (_ | f) hf
      · simp at hf
      · simp only [Set.mem_ofPred_eq, inr_mem_starBag_some] at hf
        exact Or.inl (by rw [hf])

lemma starDecomp_width (h3 : 3 ≤ Fintype.card V) : (starDecomp G).width ≤ Fintype.card V - 1 := by
  refine Nat.sub_le_sub_right (Finset.sup_le fun i _ => ?_) 1
  rcases i with _ | e
  · exact (card_starBag_none G).le
  · exact (card_starBag_some_le G e).trans h3

end Upper

section Lower

variable {m : ℕ} {ι : Type} [Fintype ι] (D : TreeDecomposition (subdivision (⊤ : SimpleGraph (Fin m))) ι)

/-- The branch set of `u`: `u` and the subdivision vertices of the edges `uw` with `u < w`. -/
def branch (u : Fin m) : Set (Fin m ⊕ (⊤ : SimpleGraph (Fin m)).edgeSet) :=
  {z | z = .inl u ∨ ∃ e : (⊤ : SimpleGraph (Fin m)).edgeSet,
    z = .inr e ∧ u ∈ (e : Sym2 (Fin m)) ∧ ∀ w ∈ (e : Sym2 (Fin m)), u ≤ w}

/-- The nodes whose bags meet the branch set of `u`. -/
def branchNodes (u : Fin m) : Set ι := {i | ∃ z ∈ branch u, z ∈ D.bag i}

lemma eq_of_mem_branch {u w : Fin m} {z} (hu : z ∈ branch u) (hw : z ∈ branch w) : u = w := by
  rcases hu with rfl | ⟨e, rfl, hue, hule⟩
  · rcases hw with h | ⟨e, h, -⟩
    · exact Sum.inl_injective h
    · cases h
  · rcases hw with h | ⟨f, h, hwf, hwle⟩
    · cases h
    · cases h
      exact le_antisymm (hule w hwf) (hwle u hue)

include D in
/-- Every node of `branchNodes u` is joined inside `branchNodes u` to a node whose bag holds `u`. -/
lemma joined_to_inl {u : Fin m} {i : ι} (hi : i ∈ branchNodes D u) :
    ∃ i₀, Sum.inl u ∈ D.bag i₀ ∧ JoinedIn D.T (branchNodes D u) i i₀ := by
  obtain ⟨z, hz, hzi⟩ := hi
  rcases hz with rfl | ⟨e, rfl, hue, hle⟩
  · exact ⟨i, hzi, JoinedIn.refl ⟨_, Or.inl rfl, hzi⟩⟩
  · obtain ⟨i₀, hu₀, he₀⟩ := D.cover_edge (.inr e) (.inl u) (by simpa using hue)
    refine ⟨i₀, he₀, ?_⟩
    refine (setConn_of_connected (D.subtree (.inr e)) i hzi i₀ hu₀).mono ?_
    intro j hj
    exact ⟨_, Or.inr ⟨e, rfl, hue, hle⟩, hj⟩

lemma setConn_branchNodes (u : Fin m) : SetConn D.T (branchNodes D u) := by
  intro i hi j hj
  obtain ⟨i₀, hi₀, hii₀⟩ := joined_to_inl D hi
  obtain ⟨j₀, hj₀, hjj₀⟩ := joined_to_inl D hj
  have h₀ : JoinedIn D.T (branchNodes D u) i₀ j₀ :=
    (setConn_of_connected (D.subtree (.inl u)) i₀ hi₀ j₀ hj₀).mono fun k hk => ⟨_, Or.inl rfl, hk⟩
  exact hii₀.trans (h₀.trans hjj₀.symm)

lemma branchNodes_inter_of_lt {u w : Fin m} (h : u < w) : (branchNodes D u ∩ branchNodes D w).Nonempty := by
  let e : (⊤ : SimpleGraph (Fin m)).edgeSet := ⟨s(u, w), by simpa using h.ne⟩
  obtain ⟨i, hei, hwi⟩ := D.cover_edge (.inr e) (.inl w) (by simp [e])
  refine ⟨i, ⟨_, Or.inr ⟨e, rfl, by simp [e], ?_⟩, hei⟩, ⟨_, Or.inl rfl, hwi⟩⟩
  intro x hx
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  exacts [le_rfl, h.le]

lemma branchNodes_inter (u w : Fin m) : (branchNodes D u ∩ branchNodes D w).Nonempty := by
  rcases lt_trichotomy u w with h | rfl | h
  · exact branchNodes_inter_of_lt D h
  · obtain ⟨i, hi⟩ := D.cover_vertex (.inl u)
    exact ⟨i, ⟨_, Or.inl rfl, hi⟩, ⟨_, Or.inl rfl, hi⟩⟩
  · rw [Set.inter_comm]
    exact branchNodes_inter_of_lt D h

/-- Some bag meets all `m` (disjoint) branch sets, so it has at least `m` vertices. -/
lemma exists_large_bag : ∃ i, m ≤ (D.bag i).card := by
  obtain ⟨i, hi⟩ := helly D.isTree (branchNodes D) (setConn_branchNodes D) (branchNodes_inter D)
  choose z hzb hzi using hi
  refine ⟨i, ?_⟩
  have := card_le_card_of_injOn (s := univ) z (fun u _ => hzi u)
    (fun u _ w _ h => eq_of_mem_branch (hzb u) (h ▸ hzb w))
  simpa using this

lemma le_width : m - 1 ≤ D.width := by
  obtain ⟨i, hi⟩ := exists_large_bag D
  exact Nat.sub_le_sub_right (hi.trans (le_sup (f := fun i => (D.bag i).card) (mem_univ i))) 1

end Lower

theorem treewidth_eq (m : ℕ) (hm : 3 ≤ m) : treewidth (subdivision (⊤ : SimpleGraph (Fin m))) = m - 1 := by
  have hmem : (starDecomp (⊤ : SimpleGraph (Fin m))).width ∈ {w | ∃ (ι : Type) (_ : Fintype ι)
      (D : TreeDecomposition (subdivision (⊤ : SimpleGraph (Fin m))) ι), D.width = w} := ⟨_, _, _, rfl⟩
  unfold treewidth
  apply le_antisymm
  · exact (Nat.sInf_le hmem).trans (by simpa using starDecomp_width (⊤ : SimpleGraph (Fin m)) (by simpa using hm))
  · refine le_csInf ⟨_, hmem⟩ ?_
    rintro w ⟨ι, _, D, rfl⟩
    exact le_width D

end Graph

end Subdivision

open Subdivision

theorem intro_subdivision_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (subdivision G).IsBipartite ∧ IsDegenerate (subdivision G) 2 ∧ grundyNumber (subdivision G) ≤ 3 :=
  ⟨isBipartite G, isDegenerate G, grundy_le_three G⟩

theorem intro_treewidth_proved (m : ℕ) (hm : 3 ≤ m) :
    (subdivision (⊤ : SimpleGraph (Fin m))).IsBipartite ∧ IsDegenerate (subdivision (⊤ : SimpleGraph (Fin m))) 2 ∧
      treewidth (subdivision (⊤ : SimpleGraph (Fin m))) = m - 1 :=
  ⟨isBipartite _, isDegenerate _, treewidth_eq m hm⟩

end Cereceda
