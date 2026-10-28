/-
LeeDiam/Paper/Statements.lean — one theorem per claim of paper 004, "The Lee (2026) conjecture on the diameters of order
and chain polytopes fails in both directions" (Dave Goel), short version v1.50 (statements final): P4_short_v1.50.tex
(main; md5 39536615), sec_chain.tex (Section 4; md5 75ec56e2), sec_reverse.tex (Sections 5-6; md5 57aaae09).
Line numbers "l." refer to the main file unless a docstring names sec_chain or sec_reverse.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

Every body is `exact X_proved ...` with `X_proved` in a proof module; compiling the link checks the types.
Proof-internal steps are covered by the row of the result they prove. Displayed walks and sets that later text reuses
are rows of their own (Table 2, the walks `V` of Lemma 4.9, the column walks of Lemma 4.12, `↑y_i`, `↓w_i`, `↓t_ij`).
Indices are 0-based: `Band.a i` is the paper's `a_{i+1}`, `PnElem.a i` is the paper's `a_{i+1}` of `P_n`.
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Vertices
import LeeDiam.Defs.Walks
import LeeDiam.Defs.Band
import LeeDiam.Defs.Pn
import LeeDiam.Defs.PnSets
import LeeDiam.Defs.Chain
import LeeDiam.Defs.Questions
import LeeDiam.Defs.MergeSchedule
import LeeDiam.Cited.Lee26
import LeeDiam.Sec1.Vertices
import LeeDiam.Sec1.Additive
import LeeDiam.Sec1.Main
import LeeDiam.Sec1.Figure1
import LeeDiam.Sec2.Walks
import LeeDiam.Sec2.IdealComponents
import LeeDiam.Sec3.Band
import LeeDiam.Sec4.Chain
import LeeDiam.Sec4.Caption
import LeeDiam.Sec4.CombCount
import LeeDiam.Sec4.Lem411Step
import LeeDiam.Sec5.Upper
import LeeDiam.Sec6.Structure
import LeeDiam.Sec6.SigmaGraph
import LeeDiam.Sec6.SigmaMixed
import LeeDiam.Sec6.Figure2
import LeeDiam.Sec6.Order
import LeeDiam.Sec6.Chain
import LeeDiam.Sec6.RankLt
import LeeDiam.Sec7.Questions

namespace LeeDiam

/-! ## Section 1 — Introduction -/

/-- Section 1, l. 50 (and [Sta86]): the vertices of `O(P)` are exactly the indicator vectors of the ideals. -/
theorem sec1_order_vertices (P : Type) [Fintype P] [PartialOrder P] (v : P → ℝ) :
    HibiLi.IsFace (orderPolytope P) {v} ↔ ∃ I : Set P, IsIdeal I ∧ v = HibiLi.setVector I := by
  exact sec1_order_vertices_proved P v

/-- Section 1, l. 50 (and [Sta86]): the vertices of `C(P)` are exactly the indicator vectors of the antichains. -/
theorem sec1_chain_vertices (P : Type) [Fintype P] [PartialOrder P] (v : P → ℝ) :
    HibiLi.IsFace (chainPolytope P) {v} ↔ ∃ A : Set P, IsAntichainSet A ∧ v = HibiLi.setVector A := by
  exact sec1_chain_vertices_proved P v

/-- Section 1, footnote of l. 50: `x ↦ 1 - x` carries Stanley's order polytope onto the one used here, so the two graphs
are isomorphic. -/
theorem sec1_footnote_stanley (P : Type) [Fintype P] [PartialOrder P] :
    orderPolytope P = (fun x => 1 - x) '' HibiLi.orderPolytope P ∧
      Nonempty (polyGraph (HibiLi.orderPolytope P) ≃g polyGraph (orderPolytope P)) := by
  exact sec1_footnote_stanley_proved P

/-- Section 1, l. 50 (and the abstract, l. 45): the two polytopes have the same number of vertices. -/
theorem sec1_same_vertices (P : Type) [Fintype P] [PartialOrder P] :
    Nat.card {v : P → ℝ // HibiLi.IsFace (orderPolytope P) {v}} =
      Nat.card {v : P → ℝ // HibiLi.IsFace (chainPolytope P) {v}} := by
  exact sec1_same_vertices_proved P

/-- Section 1, l. 50 (with `sec1_same_vertices`): both polytopes have finitely many vertices, so the two counts above are
genuine numbers of vertices (`Nat.card` is `0` on an infinite type). -/
theorem sec1_vertices_finite (P : Type) [Fintype P] [PartialOrder P] :
    Finite {v : P → ℝ // HibiLi.IsFace (orderPolytope P) {v}} ∧
      Finite {v : P → ℝ // HibiLi.IsFace (chainPolytope P) {v}} := by
  exact sec1_vertices_finite_proved P

/-- Section 1, l. 50: both diameters are additive over disjoint unions (`P ⊕ Q`, no relation between the two parts),
since `O(P ⊔ Q) = O(P) × O(Q)`, `C(P ⊔ Q) = C(P) × C(Q)`. (The paper cites [Lee26, Example 5] for "the graph of a
product of polytopes is the Cartesian product of their graphs"; Lean proves the additivity of the diameters.) -/
theorem sec1_additive (P Q : Type) [Fintype P] [PartialOrder P] [Fintype Q] [PartialOrder Q] :
    (∀ x : P ⊕ Q → ℝ, x ∈ orderPolytope (P ⊕ Q) ↔
      (x ∘ Sum.inl ∈ orderPolytope P ∧ x ∘ Sum.inr ∈ orderPolytope Q)) ∧
    (∀ x : P ⊕ Q → ℝ, x ∈ chainPolytope (P ⊕ Q) ↔
      (x ∘ Sum.inl ∈ chainPolytope P ∧ x ∘ Sum.inr ∈ chainPolytope Q)) ∧
    orderDiam (P ⊕ Q) = orderDiam P + orderDiam Q ∧ chainDiam (P ⊕ Q) = chainDiam P + chainDiam Q := by
  exact sec1_additive_proved P Q

/-- Section 1, l. 50: on posets with many components the diameters can differ by any amount, in either direction.
(Both diameters are stated as finite numbers `dO`, `dC`.) -/
theorem sec1_many_components (M : ℕ) :
    (∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (dO dC : ℕ),
      orderDiam P = dO ∧ chainDiam P = dC ∧ dC + M ≤ dO) ∧
    (∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (dO dC : ℕ),
      orderDiam P = dO ∧ chainDiam P = dC ∧ dO + M ≤ dC) := by
  exact sec1_many_components_proved M

/-- Section 1, l. 61: for a connected poset that is not a chain, both diameters lie between `2` and the width `w(P)`
(the upper bound is Proposition 2.3; the paper cites [Lee26, Cor. 25]), hence they differ by at most `w(P) - 2`. -/
theorem sec1_between_two_and_width (P : Type) [Fintype P] [PartialOrder P] (hP : IsConnPoset P)
    (hnc : ¬ IsChain (· ≤ ·) (Set.univ : Set P)) :
    2 ≤ orderDiam P ∧ orderDiam P ≤ width P ∧ 2 ≤ chainDiam P ∧ chainDiam P ≤ width P ∧
      orderDiam P ≤ chainDiam P + (width P - 2 : ℕ) ∧ chainDiam P ≤ orderDiam P + (width P - 2 : ℕ) := by
  exact sec1_between_two_and_width_proved P hP hnc

/-- Section 1, l. 61 and l. 66-68 (with Conjecture 1.1, l. 52-57, and Theorems 1.3-1.4): the Lee (2026) conjecture
fails in both directions on connected posets: the two diameters `dO`, `dC` (finite numbers) differ by at least `2`. -/
theorem lee_conjecture_fails :
    ¬ LeeConjecture ∧
    (∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (dO dC : ℕ),
      IsConnPoset P ∧ orderDiam P = dO ∧ chainDiam P = dC ∧ dC + 1 < dO) ∧
    (∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (dO dC : ℕ),
      IsConnPoset P ∧ orderDiam P = dO ∧ chainDiam P = dC ∧ dO + 1 < dC) := by
  exact lee_conjecture_fails_proved

/-- Section 1, l. 92: the `3k` points `a_i = (i, -i)`, `b_i = (i, 1 - i)`, `c_i = (i + 1, 1 - i)` of `ℤ²` (product order;
`1 ≤ i ≤ k`) induce a subposet isomorphic to `B_k`; "these points lie on three neighboring antidiagonals"
(coordinate sums `0`, `1`, `2`); "Figure 1 shows this picture ..., rotated by 45°": `(x, y) ↦ (x - y, x + y)` sends
`a_i`, `b_i`, `c_i` to the drawn points `(2i, 0)`, `(2i - 1, 1)`, `(2i, 2)` (Figure 1, l. 98-100). -/
theorem band_Z2_picture (k : ℕ) :
    ∃ f : Band k ↪o ℤ × ℤ, ∀ i : Fin k,
      f (Band.a i) = ((i : ℤ) + 1, -((i : ℤ) + 1)) ∧ f (Band.b i) = ((i : ℤ) + 1, -(i : ℤ)) ∧
      f (Band.c i) = ((i : ℤ) + 2, -(i : ℤ)) ∧
      (f (Band.a i)).1 + (f (Band.a i)).2 = 0 ∧ (f (Band.b i)).1 + (f (Band.b i)).2 = 1 ∧
      (f (Band.c i)).1 + (f (Band.c i)).2 = 2 ∧
      ((f (Band.a i)).1 - (f (Band.a i)).2, (f (Band.a i)).1 + (f (Band.a i)).2) = (2 * ((i : ℤ) + 1), 0) ∧
      ((f (Band.b i)).1 - (f (Band.b i)).2, (f (Band.b i)).1 + (f (Band.b i)).2) = (2 * ((i : ℤ) + 1) - 1, 1) ∧
      ((f (Band.c i)).1 - (f (Band.c i)).2, (f (Band.c i)).1 + (f (Band.c i)).2) = (2 * ((i : ℤ) + 1), 2) := by
  exact band_Z2_picture_proved k

/-- Figure 1 (fig:band, l. 94-106): "The Hasse diagram of the band `B_5`". For every `k`, the cover pairs of `B_k` are
exactly the generating relations of Definition 1.2 (the drawn edges `a_i b_i`, `b_i c_i`, `a_i b_{i+1}`,
`b_{i+1} c_i`). -/
theorem fig_1_hasse (k : ℕ) (x y : Band k) : x ⋖ y ↔ bandRel k x y := by
  exact fig_1_hasse_proved k x y

/-- Theorem 1.3 (thm:main), l. 108-113: for every `k ≥ 1` the band `B_k` is a connected poset with `3k` elements,
(i) `diam O(B_k) = k`, (ii) `diam C(B_k) ≤ ⌊3(k+1)/4⌋`. -/
theorem thm_1_3 (k : ℕ) (hk : 1 ≤ k) :
    IsConnPoset (Band k) ∧ Fintype.card (Band k) = 3 * k ∧ orderDiam (Band k) = k ∧
      chainDiam (Band k) ≤ ((3 * (k + 1) / 4 : ℕ) : ℕ∞) := by
  exact thm_1_3_proved k hk

/-- Theorem 1.3, l. 114 (and l. 61, "no constant can replace 1"): consequently `diam O(B_k) - diam C(B_k) ≥ ⌈(k-3)/4⌉`,
which tends to infinity (on connected posets, with finite diameters); in particular `B_8`, with `24` elements, is a
connected counterexample to the Lee (2026) conjecture (difference at least `2`; the abstract, l. 45: "and by at least
`2` already for `k = 8`"). -/
theorem thm_1_3_consequence :
    (∀ k : ℕ, 1 ≤ k → ∃ dO dC : ℕ, orderDiam (Band k) = dO ∧ chainDiam (Band k) = dC ∧
      ⌈((k : ℝ) - 3) / 4⌉ ≤ (dO : ℤ) - dC) ∧
    (∀ M : ℕ, ∃ k, 1 ≤ k ∧ IsConnPoset (Band k) ∧
      ∃ dO dC : ℕ, orderDiam (Band k) = dO ∧ chainDiam (Band k) = dC ∧ dC + M ≤ dO) ∧
    (Fintype.card (Band 8) = 24 ∧ IsConnPoset (Band 8) ∧
      ∃ dO dC : ℕ, orderDiam (Band 8) = dO ∧ chainDiam (Band 8) = dC ∧ dC + 2 ≤ dO) := by
  exact thm_1_3_consequence_proved

/-- Section 1, l. 61: "no constant can replace 1 in the first one" (the inequality `diam O(P) ≤ diam C(P) + 1` of
Conjecture 1.1): for every `C` there is a connected finite poset whose diameters `dO`, `dC` (finite) satisfy
`dC + C < dO`. -/
theorem sec1_no_constant :
    ∀ C : ℕ, ∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (dO dC : ℕ),
      IsConnPoset P ∧ orderDiam P = dO ∧ chainDiam P = dC ∧ dC + C < dO := by
  exact sec1_no_constant_proved

/-- Section 1, l. 61: "Our first family shows that the difference can grow linearly with the width": `w(B_k) = k`
(Lemma 3.1) and `diam O(B_k) - diam C(B_k) ≥ ⌈(k-3)/4⌉`. -/
theorem sec1_linear_width :
    ∀ k : ℕ, 1 ≤ k → width (Band k) = k ∧ ∃ dO dC : ℕ, orderDiam (Band k) = dO ∧ chainDiam (Band k) = dC ∧
      ⌈((k : ℝ) - 3) / 4⌉ ≤ (dO : ℤ) - dC := by
  exact sec1_linear_width_proved

/-- Theorem 1.4 (rv-thm:main), l. 123-129: for every `n ≥ 4`, `P_n` is connected, has `2n² + 5n + 1` elements,
`diam O(P_n) = 2` and `diam C(P_n) = 4`; in particular `P_4` has `53` elements and difference `2`. -/
theorem thm_1_4 :
    (∀ n : ℕ, 4 ≤ n → IsConnPoset (Pn n) ∧ Fintype.card (Pn n) = 2 * n ^ 2 + 5 * n + 1 ∧
      orderDiam (Pn n) = 2 ∧ chainDiam (Pn n) = 4) ∧
    Fintype.card (Pn 4) = 53 ∧ chainDiam (Pn 4) = orderDiam (Pn 4) + 2 := by
  exact thm_1_4_proved

/-- Theorem 1.5 (rv-thm:upper), l. 133-135: if `diam O(P) ≤ 2` then `diam C(P) ≤ 4`, for every finite poset `P`. -/
theorem thm_1_5 (P : Type) [Fintype P] [PartialOrder P] (h : orderDiam P ≤ 2) : chainDiam P ≤ 4 := by
  exact thm_1_5_proved P h

/-- Section 1, l. 134 (and the abstract, l. 45): the largest value of `diam C(P) - diam O(P)` over posets with
`diam O(P) = 2` is exactly `2` (attained by a connected poset). -/
theorem sec1_largest_difference :
    (∀ (P : Type) [Fintype P] [PartialOrder P], orderDiam P = 2 → chainDiam P ≤ orderDiam P + 2) ∧
    ∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P), IsConnPoset P ∧ orderDiam P = 2 ∧ chainDiam P = orderDiam P + 2 := by
  exact sec1_largest_difference_proved

/-! ## Section 2 — Preliminaries -/

/-- Section 2, l. 147: consecutive states of a walk are adjacent in the graph of `C(P)` (Theorem 2.1), so
`d_C(X_0, X_n) ≤ ℓ(W)`. -/
theorem sec2_walk_dist {P : Type} [Fintype P] [PartialOrder P] (W : List (Set P)) (X Y : Set P)
    (hX : IsAntichainSet X) (hY : IsAntichainSet Y) (hW : IsWalkFromTo W X Y) :
    dC X Y hX hY ≤ ((W.length - 1 : ℕ) : ℕ∞) := by
  exact sec2_walk_dist_proved W X Y hX hY hW

/-- Section 2, l. 147: the reversal of a walk is a walk. -/
theorem sec2_walk_reverse {P : Type} [PartialOrder P] (W : List (Set P)) (hW : IsWalk W) : IsWalk W.reverse := by
  exact sec2_walk_reverse_proved W hW

/-- Faithfulness of `IsCompUnion` (Lemma 2.2, l. 150, "a union of components"): a subset of `D` closed under
comparability inside `D` is exactly a union of components of `D` (every element lies in a component of `D` contained
in it). -/
theorem isCompUnion_iff {P : Type} [Fintype P] [PartialOrder P] (C D : Set P) :
    IsCompUnion C D ↔ C ⊆ D ∧ ∀ x ∈ C, ∃ K, IsComponent K D ∧ x ∈ K ∧ K ⊆ C := by
  exact isCompUnion_iff_proved C D

/-- Lemma 2.2 (Components), l. 149-151: for ideals `J ⊆ I` and a union `C` of components of `I \ J`, the sets `J ∪ C`
and `I \ C` are ideals. -/
theorem lem_2_2 {P : Type} [PartialOrder P] (I J C : Set P) (hI : IsIdeal I) (hJ : IsIdeal J) (hJI : J ⊆ I)
    (hC : IsCompUnion C (I \ J)) : IsIdeal (J ∪ C) ∧ IsIdeal (I \ C) := by
  exact lem_2_2_proved I J C hI hJ hJI hC

/-- Proposition 2.3 (Components), l. 156-158 ([Lee26, Prop. 24], proved here): `d_O(I, J)` is at most the number of
components of `I △ J`; exchanging the components of `A △ B` one at a time, in any order, gives a walk from `A` to `B`;
hence `d_C(A, B)` is at most the number of components of `A △ B`; both diameters are at most `w(P)`. -/
theorem prop_2_3 (P : Type) [Fintype P] [PartialOrder P] :
    (∀ (I J : Set P) (hI : IsIdeal I) (hJ : IsIdeal J), dO I J hI hJ ≤ numComp (symmDiff I J)) ∧
    (∀ (A B : Set P), IsAntichainSet A → IsAntichainSet B → ∀ L : List (Set P), L.Nodup →
      (∀ C, C ∈ L ↔ IsComponent C (symmDiff A B)) → IsWalkFromTo (L.scanl symmDiff A) A B) ∧
    (∀ (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B), dC A B hA hB ≤ numComp (symmDiff A B)) ∧
    orderDiam P ≤ width P ∧ chainDiam P ≤ width P := by
  exact prop_2_3_proved P

/-- Proof of Proposition 2.3, l. 160: "No element of `I \ J` is comparable to an element of `J \ I`, since `I` and `J`
are ideals; so the components of `I △ J` are those of `I \ J` and those of `J \ I`." (The Lean proof of Proposition 2.3
exchanges the components in any order; this step of the paper's route is its own row.) -/
theorem prop_2_3_components (P : Type) [Fintype P] [PartialOrder P] (I J : Set P) (hI : IsIdeal I)
    (hJ : IsIdeal J) :
    (∀ x ∈ I \ J, ∀ y ∈ J \ I, ¬ Comp x y) ∧
    ∀ C : Set P, IsComponent C (symmDiff I J) ↔ IsComponent C (I \ J) ∨ IsComponent C (J \ I) := by
  exact prop_2_3_components_proved P I J hI hJ

/-- Proof of Lemma 2.4, l. 169-173: for antichains `R, S`, `π_R(S)` is an antichain, and if `S, S'` are adjacent
(`S △ S'` connected), then `π_R(S)` and `π_R(S')` are equal or adjacent. -/
theorem lem_2_4_proj {P : Type} [PartialOrder P] (R S S' : Set P) (hR : IsAntichainSet R) (hS : IsAntichainSet S)
    (hS' : IsAntichainSet S') (hSS' : IsConnSet (symmDiff S S')) :
    IsAntichainSet (proj R S) ∧ (proj R S = proj R S' ∨ IsConnSet (symmDiff (proj R S) (proj R S'))) := by
  exact lem_2_4_proj_proved R S S' hR hS hS' hSS'

/-- Proof of Lemma 2.4, l. 173: "consequently `d(π_R(S), π_R(S')) ≤ d(S, S')` for all antichains `S, S'`". -/
theorem lem_2_4_proj_dist {P : Type} [Fintype P] [PartialOrder P] (R S S' : Set P) (hR : IsAntichainSet R)
    (hS : IsAntichainSet S) (hS' : IsAntichainSet S') (hp : IsAntichainSet (proj R S))
    (hp' : IsAntichainSet (proj R S')) : dC (proj R S) (proj R S') hp hp' ≤ dC S S' hS hS' := by
  exact lem_2_4_proj_dist_proved R S S' hR hS hS' hp hp'

/-- Lemma 2.4 (Splits), l. 165-167: for antichains `X, Y` there are disjoint antichains `A ⊆ X`, `B ⊆ Y` with `A ∪ B` an
antichain and `d_C(X, Y) ≤ d_C(A, B)`; consequently `diam C(P)` is the largest `d_C(A, B)` over all splits. -/
theorem lem_2_4 (P : Type) [Fintype P] [PartialOrder P] :
    (∀ (X Y : Set P) (hX : IsAntichainSet X) (hY : IsAntichainSet Y), ∃ (A B : Set P) (hA : IsAntichainSet A)
      (hB : IsAntichainSet B), A ⊆ X ∧ B ⊆ Y ∧ IsSplit A B (A ∪ B) ∧ dC X Y hX hY ≤ dC A B hA hB) ∧
    chainDiam P = sSup {d | ∃ (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B),
      IsSplit A B (A ∪ B) ∧ d = dC A B hA hB} := by
  exact lem_2_4_proved P

/-! ## Section 3 — The band and its order polytope -/

/-- Lemma 3.1, l. 179-185: in `B_k` the comparable pairs are exactly `a_i < b_i, b_{i+1}`; `b_i < c_{i-1}, c_i`;
`a_i < c_{i-1}, c_i, c_{i+1}` (indices in range). -/
theorem lem_3_1_pairs (k : ℕ) (x y : Band k) :
    x < y ↔
      (x.2 = 0 ∧ y.2 = 1 ∧ (y.1 = x.1 ∨ y.1.val = x.1.val + 1)) ∨
      (x.2 = 1 ∧ y.2 = 2 ∧ (y.1 = x.1 ∨ y.1.val + 1 = x.1.val)) ∨
      (x.2 = 0 ∧ y.2 = 2 ∧ (y.1.val + 1 = x.1.val ∨ y.1 = x.1 ∨ y.1.val = x.1.val + 1)) := by
  exact lem_3_1_pairs_proved k x y

/-- Lemma 3.1, l. 184, "in particular" (and l. 92): elements whose indices differ by two or more are incomparable; the
rows `{a_i}`, `{b_i}`, `{c_i}` are antichains; `B_k` is connected (`k ≥ 1`); and `w(B_k) = k`. -/
theorem lem_3_1_consequences (k : ℕ) :
    (∀ x y : Band k, x.1.val + 2 ≤ y.1.val → ¬ x ≤ y ∧ ¬ y ≤ x) ∧
    (∀ r : Fin 3, IsAntichainSet {x : Band k | x.2 = r}) ∧
    (1 ≤ k → IsConnPoset (Band k)) ∧ width (Band k) = k := by
  exact lem_3_1_consequences_proved k

/-- Section 3, eq. (cross), l. 189-192: between two different columns `s < t` comparable pairs exist only for `t = s + 1`,
and they are exactly `a_s < b_{s+1}`, `a_s < c_{s+1}`, `a_{s+1} < c_s`, `b_{s+1} < c_s`. -/
theorem band_cross (k : ℕ) (x y : Band k) (hxy : x.1 ≠ y.1) :
    (x < y ∨ y < x) ↔
      (y.1.val = x.1.val + 1 ∨ x.1.val = y.1.val + 1) ∧
      ((x.2 = 0 ∧ y.2 = 1 ∧ y.1.val = x.1.val + 1) ∨ (x.2 = 0 ∧ y.2 = 2 ∧ y.1.val = x.1.val + 1) ∨
       (x.2 = 0 ∧ y.2 = 2 ∧ x.1.val = y.1.val + 1) ∨ (x.2 = 1 ∧ y.2 = 2 ∧ x.1.val = y.1.val + 1) ∨
       (y.2 = 0 ∧ x.2 = 1 ∧ x.1.val = y.1.val + 1) ∨ (y.2 = 0 ∧ x.2 = 2 ∧ x.1.val = y.1.val + 1) ∨
       (y.2 = 0 ∧ x.2 = 2 ∧ y.1.val = x.1.val + 1) ∨ (y.2 = 1 ∧ x.2 = 2 ∧ y.1.val = x.1.val + 1)) := by
  exact band_cross_proved k x y hxy

/-- Lemma 3.2 (Interval lemma), l. 194-196: for a connected convex subset `D` of `B_k`, `{i : b_i ∈ D}` is empty or an
interval of integers. -/
theorem lem_3_2 (k : ℕ) (D : Set (Band k)) (hD : IsConnSet D) (hconv : IsConvexSet D) :
    ∀ i j l : Fin k, Band.b i ∈ D → Band.b j ∈ D → i ≤ l → l ≤ j → Band.b l ∈ D := by
  exact lem_3_2_proved k D hD hconv

open Classical in
/-- Proof of Theorem 3.3, l. 209: for adjacent ideals `I ⊂ J`, `D = J \ I` is convex, and
`Φ(I) = Σ_i (-1)^i [b_i ∈ I]` changes by at most one: `|Φ(J) - Φ(I)| ≤ 1`. (0-based: the paper's sign `(-1)^{i}` for
`b_i` is `(-1)^{i+1}` for `Band.b i`.) -/
theorem thm_3_3_step (k : ℕ) (I J : Set (Band k)) (hI : IsIdeal I) (hJ : IsIdeal J) (hIJ : I ⊆ J)
    (hconn : IsConnSet (J \ I)) :
    IsConvexSet (J \ I) ∧
      |(∑ i : Fin k, if Band.b i ∈ J then (-1 : ℤ) ^ (i.val + 1) else 0) -
        (∑ i : Fin k, if Band.b i ∈ I then (-1 : ℤ) ^ (i.val + 1) else 0)| ≤ 1 := by
  exact thm_3_3_step_proved k I J hI hJ hIJ hconn

open Classical in
/-- Proof of Theorem 3.3, l. 209: "Hence `d_O(I, J) ≥ |Φ(I) - Φ(J)|` for all ideals `I, J`." -/
theorem thm_3_3_lipschitz (k : ℕ) (I J : Set (Band k)) (hI : IsIdeal I) (hJ : IsIdeal J) :
    ((|(∑ i : Fin k, if Band.b i ∈ I then (-1 : ℤ) ^ (i.val + 1) else 0) -
        (∑ i : Fin k, if Band.b i ∈ J then (-1 : ℤ) ^ (i.val + 1) else 0)|).toNat : ℕ∞) ≤ dO I J hI hJ := by
  exact thm_3_3_lipschitz_proved k I J hI hJ

open Classical in
/-- Proof of Theorem 3.3, l. 209: `I_0` (all `a_i` and the `b_i` with `i` even) and `I_1` (all `a_i` and the `b_i`
with `i` odd) are ideals with `Φ(I_0) - Φ(I_1) = ⌊k/2⌋ + ⌈k/2⌉ = k` and `d_O(I_0, I_1) ≥ Φ(I_0) - Φ(I_1) = k`. -/
theorem thm_3_3_far_pair (k : ℕ) :
    ∃ (I0 I1 : Set (Band k)) (h0 : IsIdeal I0) (h1 : IsIdeal I1),
      I0 = {x | x.2 = 0 ∨ (x.2 = 1 ∧ Even (x.1.val + 1))} ∧ I1 = {x | x.2 = 0 ∨ (x.2 = 1 ∧ Odd (x.1.val + 1))} ∧
      (∑ i : Fin k, if Band.b i ∈ I0 then (-1 : ℤ) ^ (i.val + 1) else 0) -
        (∑ i : Fin k, if Band.b i ∈ I1 then (-1 : ℤ) ^ (i.val + 1) else 0) = k ∧
      (k : ℕ∞) ≤ dO I0 I1 h0 h1 := by
  exact thm_3_3_far_pair_proved k

/-- Theorem 3.3 (thm:order), l. 205-207: for every `k ≥ 1`, `diam O(B_k) = k`. -/
theorem thm_3_3 (k : ℕ) (hk : 1 ≤ k) : orderDiam (Band k) = k := by
  exact thm_3_3_proved k hk

/-! ## Section 4 — The chain polytope of the band (sec_chain.tex v1.50) -/

section Sec4

open Band

/-! ### Section 4.1 (sec_chain l. 13-58): words, rows, σ, translations, outer traces, merging -/

/-- sec_chain l. 14: an antichain contains at most one element of each column. -/

theorem sec4_antichain_col {k : ℕ} (X : Set (Band k)) (hX : IsAntichainSet X) (x y : Band k) (hx : x ∈ X) (hy : y ∈ X)
    (hxy : x.1 = y.1) : x = y := by
  exact sec4_antichain_col_proved X hX x y hx hy hxy

/-- sec_chain l. 14: every antichain is described by its word. -/

theorem sec4_word_exists {k : ℕ} (X : Set (Band k)) (hX : IsAntichainSet X) : ∃ w, X = ofWord w := by
  exact sec4_word_exists_proved X hX

/-- sec_chain l. 14, by (cross): a word describes an antichain iff no two neighboring letters are `ab`, `ac`, `ca` or
`cb`. -/

theorem sec4_word_antichain_iff {k : ℕ} (w : Fin k → Option (Fin 3)) :
    IsAntichainSet (ofWord w) ↔ ∀ i j : Fin k, j.val = i.val + 1 → ¬ BadPair (w i) (w j) := by
  exact sec4_word_antichain_iff_proved w

/-- sec_chain l. 14: inside a run (columns `s, …, e` all nonempty) `a` is followed only by `a` and `c` only by `c`;
hence the word of the run is `b^i x^j` with `x ∈ {a, c}`. (This is also the word form that Proposition 4.13 of v1.50
asserts for an antichain without empty columns, `s = 0`, `e = L - 1`.) -/

theorem sec4_run_form {k : ℕ} (U : Set (Band k)) (hU : IsAntichainSet U) (s e : ℕ)
    (hrun : ∀ l : Fin k, s ≤ l.val → l.val ≤ e → ∃ x ∈ U, x.1 = l) :
    ∃ (i : ℕ) (r : Fin 3), r ≠ 1 ∧ ∀ x ∈ U, s ≤ x.1.val → x.1.val ≤ e →
      (x.2 = 1 ↔ x.1.val < s + i) ∧ (x.2 ≠ 1 → x.2 = r) := by
  exact sec4_run_form_proved U hU s e hrun

/-- sec_chain l. 16-20, (P1) and (P2): two elements are comparable iff one is `b_j` and the other is one of
`a_{j-1}, a_j, c_{j-1}, c_j`, or they are `a_s` and `c_t` with `|s - t| ≤ 1`. -/

theorem sec4_P1_P2 {k : ℕ} (x y : Band k) :
    Comp x y ↔
      (x.2 = 1 ∧ y.2 ≠ 1 ∧ (y.1 = x.1 ∨ y.1.val + 1 = x.1.val)) ∨
      (y.2 = 1 ∧ x.2 ≠ 1 ∧ (x.1 = y.1 ∨ x.1.val + 1 = y.1.val)) ∨
      (((x.2 = 0 ∧ y.2 = 2) ∨ (x.2 = 2 ∧ y.2 = 0)) ∧ x.1.val ≤ y.1.val + 1 ∧ y.1.val ≤ x.1.val + 1) := by
  exact sec4_P1_P2_proved x y

/-- sec_chain l. 21: two elements of one row are incomparable, two distinct elements of one column are comparable. -/

theorem sec4_rows_cols {k : ℕ} (x y : Band k) : (x.2 = y.2 → ¬ Comp x y) ∧ (x.1 = y.1 → x ≠ y → Comp x y) := by
  exact sec4_rows_cols_proved x y

/-- sec_chain l. 21: comparability depends only on the rows and the difference of the column indices, so a translation
of the columns maps antichains to antichains, connected sets to connected sets, and walks to walks. -/

theorem sec4_translation {k : ℕ} {k' : ℕ} (d : ℕ) (hd : k + d ≤ k') :
    (∀ x y : Band k, x ≤ y ↔ colShift d hd x ≤ colShift d hd y) ∧
    (∀ X : Set (Band k), IsAntichainSet X ↔ IsAntichainSet (colShift d hd '' X)) ∧
    (∀ D : Set (Band k), IsConnSet D ↔ IsConnSet (colShift d hd '' D)) ∧
    (∀ W : List (Set (Band k)), IsWalk W → IsWalk (W.map (colShift d hd '' ·))) := by
  exact sec4_translation_proved d hd

/-- Lemma 4.2 (sec_chain l. 23-25): a nonempty `F ⊆ B_k` is connected iff its columns form an interval and, for any
two neighboring columns of it, some element of `F` in one is comparable to some element of `F` in the other. -/

theorem lem_4_2 {k : ℕ} (F : Set (Band k)) (hF : F.Nonempty) :
    IsConnSet F ↔
      (∀ x ∈ F, ∀ y ∈ F, ∀ l : Fin k, x.1 ≤ l → l ≤ y.1 → ∃ z ∈ F, z.1 = l) ∧
      ∀ x ∈ F, ∀ y ∈ F, y.1.val = x.1.val + 1 →
        ∃ x' ∈ F, ∃ y' ∈ F, x'.1 = x.1 ∧ y'.1 = y.1 ∧ Comp x' y' := by
  exact lem_4_2_proved F hF

/-- sec_chain l. 30: `σ` reverses the order (so it preserves comparability), maps walks to walks, exchanges the letters
`a` and `c` of words, and fixes every set of middle elements. -/

theorem sec4_sigma {k : ℕ} :
    (∀ x y : Band k, x ≤ y ↔ sigmaAC y ≤ sigmaAC x) ∧ (∀ x y : Band k, Comp x y ↔ Comp (sigmaAC x) (sigmaAC y)) ∧
    (∀ W : List (Set (Band k)), IsWalk W → IsWalk (W.map (sigmaAC '' ·))) ∧
    (∀ w : Fin k → Option (Fin 3), sigmaAC '' ofWord w = ofWord (fun i => (w i).map Fin.rev)) ∧
    (∀ X : Set (Band k), (∀ x ∈ X, x.2 = 1) → sigmaAC '' X = X) := by
  exact sec4_sigma_proved

/-- sec_chain l. 32, the example: if column `e` holds `b_e`, then `c_e`, then `a_e`, then nothing, the outer trace at
`e` is `(-, c_e, a_e, -)`. -/

theorem sec4_trace_example {k : ℕ} (e : Fin k) :
    outerTrace [{b e}, {c e}, {a e}, ∅] e = [none, some (c e), some (a e), none] := by
  exact sec4_trace_example_proved e

/-- sec_chain l. 34: the reversal of a walk for the split `(A, B)` is a walk for `(B, A)`. -/

theorem sec4_reverse_split {P : Type} [PartialOrder P] (W : List (Set P)) (A B : Set P)
    (hW : IsWalkFromTo W A B) : IsWalkFromTo W.reverse B A := by
  exact sec4_reverse_split_proved W A B hW

/-- Lemma 4.3 (Merging walks, sec_chain l. 36-43; v1.50 names the walks `W_q`). Walks `W_t` with states in pairwise
disjoint sets `D_t`; their moves are partitioned into nonempty steps (`step t m` = the step of move `m` of `W_t`; at most
one move of each walk per step and the moves of each walk in increasing steps = `StrictMono (step t)`). If every `Z_α`
is an antichain and every step's move graph is connected, then `(Z_0, …, Z_M)` is a walk from `⋃ X^t_0` to
`⋃ X^t_{n_t}` of length `M = Σ n_t - Σ (|S_α| - 1)`, and it has the outer trace of `W_t` at every column whose occurring
elements lie in `D_t`. -/

theorem lem_4_3 {k : ℕ} {r M : ℕ} (D : Fin r → Set (Band k)) (hD : Pairwise fun t t' => Disjoint (D t) (D t'))
    (W : Fin r → List (Set (Band k))) (hW : ∀ t, IsWalk (W t)) (hWD : ∀ t, ∀ X ∈ W t, X ⊆ D t)
    (step : (t : Fin r) → Fin ((W t).length - 1) → Fin M) (hmono : ∀ t, StrictMono (step t))
    (hne : ∀ β : Fin M, ∃ t m, step t m = β)
    (hanti : ∀ α ≤ M, IsAntichainSet (mergedState W step α))
    (hconn : ∀ β : Fin M, (moveGraph W step β).Connected) :
    IsWalkFromTo ((List.range (M + 1)).map (mergedState W step)) (⋃ t, (W t).headD ∅) (⋃ t, (W t).getLastD ∅) ∧
      M + ∑ β : Fin M,
          ((Finset.univ.filter (fun p : (t : Fin r) × Fin ((W t).length - 1) => step p.1 p.2 = β)).card - 1) =
        ∑ t, ((W t).length - 1) ∧
      ∀ (t : Fin r) (e : Fin k), (∀ t', ∀ X ∈ W t', ∀ x ∈ X, x.1 = e → x ∈ D t) →
        outerTrace ((List.range (M + 1)).map (mergedState W step)) e = outerTrace (W t) e := by
  exact lem_4_3_proved D hD W hW hWD step hmono hne hanti hconn

/-- sec_chain l. 47: walks performed one after the other (all steps of one move) merge into a walk when their elements
lie in columns at distance at least two; the length is the sum of the lengths. -/

theorem lem_4_3_sequential {k : ℕ} (W₁ W₂ : List (Set (Band k))) (A₁ B₁ A₂ B₂ : Set (Band k))
    (h₁ : IsWalkFromTo W₁ A₁ B₁) (h₂ : IsWalkFromTo W₂ A₂ B₂)
    (hfar : ∀ X ∈ W₁, ∀ Y ∈ W₂, ∀ x ∈ X, ∀ y ∈ Y, x.1.val + 2 ≤ y.1.val ∨ y.1.val + 2 ≤ x.1.val) :
    IsWalkFromTo (W₁.map (· ∪ A₂) ++ W₂.tail.map (B₁ ∪ ·)) (A₁ ∪ A₂) (B₁ ∪ B₂) ∧
      (W₁.map (· ∪ A₂) ++ W₂.tail.map (B₁ ∪ ·)).length - 1 = (W₁.length - 1) + (W₂.length - 1) := by
  exact lem_4_3_sequential_proved W₁ W₂ A₁ B₁ A₂ B₂ h₁ h₂ hfar

/-- Lemma 4.4 (i) (Adding an element, sec_chain l. 49-55): if `y` lies in no state, `X_0` has no element comparable to
`y`, and `μ` is the least index such that `X_μ` has one, then `(X_0 ∪ {y}, …, X_{μ-1} ∪ {y}, X_μ, …, X_n)` is a walk of
length `n`. -/

theorem lem_4_4_i {k : ℕ} (W : List (Set (Band k))) (hW : IsWalk W) (y : Band k) (hy : ∀ X ∈ W, y ∉ X)
    (h0 : ∀ z ∈ W.headD ∅, ¬ Comp y z) (μ : ℕ) (hμ : μ < W.length) (hμy : ∃ z ∈ W.getD μ ∅, Comp y z)
    (hmin : ∀ t < μ, ∀ z ∈ W.getD t ∅, ¬ Comp y z) :
    IsWalk (W.mapIdx fun t X => if t < μ then insert y X else X) ∧
      (W.mapIdx fun t X => if t < μ then insert y X else X).length = W.length := by
  exact lem_4_4_i_proved W hW y hy h0 μ hμ hμy hmin

/-- Lemma 4.4 (ii) (sec_chain l. 49-55): if `y` lies in no state, `X_n` has no element comparable to `y`, and `ν` is the
largest index such that `X_{ν-1}` has one, then `(X_0, …, X_{ν-1}, X_ν ∪ {y}, …, X_n ∪ {y})` is a walk of length
`n`. -/

theorem lem_4_4_ii {k : ℕ} (W : List (Set (Band k))) (hW : IsWalk W) (y : Band k) (hy : ∀ X ∈ W, y ∉ X)
    (hn : ∀ z ∈ W.getLastD ∅, ¬ Comp y z) (ν : ℕ) (hν1 : 1 ≤ ν) (hνn : ν < W.length)
    (hνy : ∃ z ∈ W.getD (ν - 1) ∅, Comp y z) (hmax : ∀ t, ν ≤ t → ∀ z ∈ W.getD t ∅, ¬ Comp y z) :
    IsWalk (W.mapIdx fun t X => if ν ≤ t then insert y X else X) ∧
      (W.mapIdx fun t X => if ν ≤ t then insert y X else X).length = W.length := by
  exact lem_4_4_ii_proved W hW y hy hn ν hν1 hνn hνy hmax

/-! ### Section 4.2 (sec_chain l. 60-73): splits of one outer row -/

/-- Lemma 4.5 (sec_chain l. 61-63): for every split `(A, B)` of `U = {a_s, …, a_e}` and helpers `C` (even positions
need `j ≥ 2`), exchanging the components of `A ∪ C` one at a time in ANY order (`L₁`) ends at `C`, and then exchanging
the components of `C ∪ B` one at a time in ANY order (`L₂`) ends at `B`: a walk from `A` to `B` of length `m + 1`,
`m = |C|`, with states in `U ∪ C`; and a helper is present exactly after the move of `L₁` that exchanges its
component and up to the move of `L₂` that exchanges its component. -/

theorem lem_4_5 {k : ℕ} (s e : ℕ) (hse : s ≤ e) (hek : e < k) (par : ℕ) (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e))
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
  exact lem_4_5_proved s e hse hek par hpar A B hAB L₁ L₂ hL₁ hL₁c hL₂ hL₂c

/-- sec_chain l. 64: there are `⌊j/2⌋` even and `⌈j/2⌉` odd helper positions, `j = e - s + 1`. -/

theorem lem_4_5_count {k : ℕ} (s e : ℕ) (hse : s ≤ e) (hek : e < k) :
    (helperSet 1 s e : Set (Band k)).ncard = (e - s + 1) / 2 ∧
      (helperSet 0 s e : Set (Band k)).ncard = (e - s + 2) / 2 := by
  exact lem_4_5_count_proved s e hse hek

/-- Proof of Lemma 4.5, sec_chain l. 66: "every element `a_u` of `U` is comparable to one or two helpers, and to two if
and only if `u = t+1` with `t, t+2 ∈ T`" (helpers: `helperSet par s e`, the `c_t` with `t ∈ T`). (The Lean proof of
Lemma 4.5 counts the components by their leftmost helpers; the counting steps of the paper are rows of their own.) -/
theorem lem_4_5_helpers {k : ℕ} (s e : ℕ) (hse : s ≤ e) (hek : e < k) (par : ℕ)
    (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (u : Fin k) (hsu : s ≤ u.val) (hue : u.val ≤ e) :
    1 ≤ {y : Band k | y ∈ helperSet par s e ∧ Comp (Band.a u) y}.ncard ∧
    {y : Band k | y ∈ helperSet par s e ∧ Comp (Band.a u) y}.ncard ≤ 2 ∧
    ({y : Band k | y ∈ helperSet par s e ∧ Comp (Band.a u) y}.ncard = 2 ↔
      ∃ t t' : Fin k, Band.c t ∈ helperSet par s e ∧ Band.c t' ∈ helperSet par s e ∧ t'.val = t.val + 2 ∧
        u.val = t.val + 1) := by
  exact lem_4_5_helpers_proved s e hse hek par hpar u hsu hue

/-- Proof of Lemma 4.5, sec_chain l. 66: "There are `m - 1` such glue elements" (the elements of `U` comparable to two
helpers; `m` = the number of helpers). -/
theorem lem_4_5_glue {k : ℕ} (s e : ℕ) (hse : s ≤ e) (hek : e < k) (par : ℕ)
    (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) :
    {x : Band k | x ∈ rowSeg 0 s e ∧ {y | y ∈ helperSet par s e ∧ Comp x y}.ncard = 2}.ncard =
      (helperSet par s e : Set (Band k)).ncard - 1 := by
  exact lem_4_5_glue_proved s e hse hek par hpar

/-- Proof of Lemma 4.5, sec_chain l. 66: for a split `(A, B)` of `U`, "two consecutive helpers `c_t`, `c_{t+2}` lie in
the same component [of `A ∪ C`] if and only if `a_{t+1} ∈ A`". -/
theorem lem_4_5_same_comp {k : ℕ} (s e : ℕ) (hse : s ≤ e) (hek : e < k) (par : ℕ)
    (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (A B : Set (Band k)) (hAB : IsSplit A B (rowSeg 0 s e))
    (t t' u : Fin k) (ht : Band.c t ∈ helperSet par s e) (ht' : Band.c t' ∈ helperSet par s e)
    (htt' : t'.val = t.val + 2) (hu : u.val = t.val + 1) :
    (∃ D, IsComponent D (A ∪ helperSet par s e) ∧ Band.c t ∈ D ∧ Band.c t' ∈ D) ↔ Band.a u ∈ A := by
  exact lem_4_5_same_comp_proved s e hse hek par hpar A B hAB t t' u ht ht' htt' hu

/-- Proof of Lemma 4.5, sec_chain l. 66: "`A ∪ C` has `m - γ_A` components, where `γ_A` is the number of glue elements
in `A`, and `C ∪ B` has `m - γ_B` components." -/
theorem lem_4_5_comp_count {k : ℕ} (s e : ℕ) (hse : s ≤ e) (hek : e < k) (par : ℕ)
    (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e)) (A B : Set (Band k)) (hAB : IsSplit A B (rowSeg 0 s e)) :
    numComp (A ∪ helperSet par s e) = (helperSet par s e : Set (Band k)).ncard -
      {x : Band k | x ∈ A ∧ {y | y ∈ helperSet par s e ∧ Comp x y}.ncard = 2}.ncard ∧
    numComp (helperSet par s e ∪ B) = (helperSet par s e : Set (Band k)).ncard -
      {x : Band k | x ∈ B ∧ {y | y ∈ helperSet par s e ∧ Comp x y}.ncard = 2}.ncard := by
  exact lem_4_5_comp_count_proved s e hse hek par hpar A B hAB

/-- Corollary 4.6 (sec_chain l. 68-73): every split of `{a_s, …, a_e}` (row `r = 0`), or of `{c_s, …, c_e}` (`r = 2`),
has a walk of length `⌊j/2⌋ + 1` whose states contain no middle element and lie in the columns `s, …, e`, and in which
the only element of column `s` that occurs is the one of row `r`. -/

theorem cor_4_6 {k : ℕ} (r : Fin 3) (hr : r ≠ 1) (s e : ℕ) (hse : s ≤ e) (hek : e < k)
    (A B : Set (Band k)) (hAB : IsSplit A B (rowSeg r s e)) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 = (e - s + 1) / 2 + 1 ∧
      (∀ X ∈ W, ∀ x ∈ X, x.2 ≠ 1 ∧ s ≤ x.1.val ∧ x.1.val ≤ e) ∧
      (∀ X ∈ W, ∀ x ∈ X, x.1.val = s → x.2 = r) := by
  exact cor_4_6_proved r hr s e hse hek A B hAB

/-! ### Section 4.3 (sec_chain l. 75-124): tame walks -/

/-- Definition 4.7 (sec_chain l. 77-79): the outer element `h` of a tame walk lies exactly in the states
`X_μ, …, X_{ν-1}` for some `1 ≤ μ < ν ≤ n` (it arrives with move `μ` and departs with move `ν`). -/

theorem def_4_7_arrive_depart {k : ℕ} (W : List (Set (Band k))) (i : Fin k) (h : Band k) (hT : IsTameAt W i h) :
    ∃ μ ν : ℕ, 1 ≤ μ ∧ μ < ν ∧ ν ≤ W.length - 1 ∧ ∀ t < W.length, (h ∈ W.getD t ∅ ↔ μ ≤ t ∧ t < ν) := by
  exact def_4_7_arrive_depart_proved W i h hT

/-- sec_chain l. 80: the reversal of a tame walk is tame; the image of a tame walk under `σ` is tame with outer element
`σ(h)`; and if the initial and final sets consist of middle elements, `σ(W)` has the same initial and final sets. -/

theorem sec4_tame_symm {k : ℕ} (W : List (Set (Band k))) (hW : IsWalk W) (i : Fin k) (h : Band k) (hT : IsTameAt W i h) :
    IsTameAt W.reverse i h ∧ IsTameAt (W.map (sigmaAC '' ·)) i (sigmaAC h) ∧
      ∀ A B : Set (Band k), IsWalkFromTo W A B → (∀ x ∈ A ∪ B, x.2 = 1) →
        IsWalkFromTo (W.map (sigmaAC '' ·)) A B := by
  exact sec4_tame_symm_proved W hW i h hT

/-- Table 2 (Tame bases, sec_chain l. 82-94), line 1: `b → c → -` on column 1 (Lean: column `0`) is a walk with outer
trace `(-, c_1, -)` at column 1. -/
theorem table_2_line1 {k : ℕ} (hk : 1 ≤ k) :
    IsWalk [{Band.b ⟨0, hk⟩}, {Band.c ⟨0, hk⟩}, (∅ : Set (Band k))] ∧
    outerTrace [{Band.b ⟨0, hk⟩}, {Band.c ⟨0, hk⟩}, (∅ : Set (Band k))] ⟨0, hk⟩ =
      [none, some (Band.c ⟨0, hk⟩), none] := by
  exact table_2_line1_proved hk

/-- Table 2, lines 2-3 (sec_chain l. 90-91, caption l. 84): `-- → a- → cc → bb` and `b- → a- → cc → -b` on the
columns 1, 2 (Lean: `0`, `1`) are walks with outer trace `(-, c_2, -)` at column 2; the listed pairs `a_1 < c_2` and
`b_2 < c_1` are comparable. -/
theorem table_2_lines23 {k : ℕ} (hk : 2 ≤ k) :
    IsWalk [∅, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨0, by omega⟩, Band.b ⟨1, hk⟩} : Set (Band k))] ∧
    outerTrace [∅, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨0, by omega⟩, Band.b ⟨1, hk⟩} : Set (Band k))] ⟨1, hk⟩ = [none, some (Band.c ⟨1, hk⟩), none] ∧
    IsWalk [{Band.b ⟨0, by omega⟩}, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨1, hk⟩} : Set (Band k))] ∧
    outerTrace [{Band.b ⟨0, by omega⟩}, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨1, hk⟩} : Set (Band k))] ⟨1, hk⟩ = [none, some (Band.c ⟨1, hk⟩), none] ∧
    Band.a ⟨0, by omega⟩ < (Band.c ⟨1, hk⟩ : Band k) ∧ Band.b ⟨1, hk⟩ < (Band.c ⟨0, by omega⟩ : Band k) := by
  exact table_2_lines23_proved hk

/-- Table 2, caption (sec_chain l. 84), line 1: "every move of line 1 ... has its difference in one column" — the
differences of the two moves are `{b_1, c_1}` and `{c_1}` (column 1; Lean: column `0`). -/
theorem table_2_caption_line1 {k : ℕ} (hk : 1 ≤ k) :
    moveDiff [{Band.b ⟨0, hk⟩}, {Band.c ⟨0, hk⟩}, (∅ : Set (Band k))] 0 = {Band.b ⟨0, hk⟩, Band.c ⟨0, hk⟩} ∧
    moveDiff [{Band.b ⟨0, hk⟩}, {Band.c ⟨0, hk⟩}, (∅ : Set (Band k))] 1 = {Band.c ⟨0, hk⟩} := by
  exact table_2_caption_line1_proved hk

/-- Table 2, caption (sec_chain l. 84), lines 2-3: "every first move has its difference in one column. For moves 2 and
3 of lines 2 and 3, the difference meets both columns, and the table lists a comparable pair of its elements, one in
each column" — the explicit differences (columns 1, 2; Lean: `0`, `1`); the listed pairs `a_1 < c_2` (move 2) and
`b_2 < c_1` (move 3) lie in them. -/
theorem table_2_caption_lines23 {k : ℕ} (hk : 2 ≤ k) :
    moveDiff [∅, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨0, by omega⟩, Band.b ⟨1, hk⟩} : Set (Band k))] 0 = {Band.a ⟨0, by omega⟩} ∧
    moveDiff [∅, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨0, by omega⟩, Band.b ⟨1, hk⟩} : Set (Band k))] 1 =
      {Band.a ⟨0, by omega⟩, Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩} ∧
    moveDiff [∅, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨0, by omega⟩, Band.b ⟨1, hk⟩} : Set (Band k))] 2 =
      {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩, Band.b ⟨0, by omega⟩, Band.b ⟨1, hk⟩} ∧
    moveDiff [{Band.b ⟨0, by omega⟩}, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨1, hk⟩} : Set (Band k))] 0 = {Band.b ⟨0, by omega⟩, Band.a ⟨0, by omega⟩} ∧
    moveDiff [{Band.b ⟨0, by omega⟩}, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨1, hk⟩} : Set (Band k))] 1 = {Band.a ⟨0, by omega⟩, Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩} ∧
    moveDiff [{Band.b ⟨0, by omega⟩}, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨1, hk⟩} : Set (Band k))] 2 = {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩, Band.b ⟨1, hk⟩} := by
  exact table_2_caption_lines23_proved hk

/-- Lemma 4.8 (Tame bases, sec_chain l. 96-98, Table 2 l. 82-94), first part: every split of `{b_1}` has a walk of
length `2`, tame at column `1`, with states in column `1` (Lean: column `0`). -/

theorem lem_4_8_one {k : ℕ} (hk : 1 ≤ k) (A B : Set (Band k)) (hAB : IsSplit A B {b ⟨0, hk⟩}) :
    ∃ W h, IsWalkFromTo W A B ∧ W.length - 1 = 2 ∧ IsTameAt W ⟨0, hk⟩ h ∧ ∀ X ∈ W, ∀ x ∈ X, x.1.val = 0 := by
  exact lem_4_8_one_proved hk A B hAB

/-- Lemma 4.8, second part (sec_chain l. 96-98): every split of `{b_1, b_2}` has a walk of length `3`, tame at column
`2`, with states in the columns `1, 2` (Lean: columns `0, 1`). -/

theorem lem_4_8_two {k : ℕ} (hk : 2 ≤ k) (A B : Set (Band k)) (hAB : IsSplit A B {b ⟨0, by omega⟩, b ⟨1, hk⟩}) :
    ∃ W h, IsWalkFromTo W A B ∧ W.length - 1 = 3 ∧ IsTameAt W ⟨1, hk⟩ h ∧ ∀ X ∈ W, ∀ x ∈ X, x.1.val ≤ 1 := by
  exact lem_4_8_two_proved hk A B hAB

/-- Lemma 4.9 (Tame extension, sec_chain l. 103-117): a walk from `A'` to `B'` tame at column `i` (Lean: `i`, 0-based),
with `A' ∪ B'` middle elements, extends for every split `(A'', B'')` of `{b_{i+1}, b_{i+2}}` to a walk from `A' ∪ A''`
to `B' ∪ B''` of length `ℓ(W) + 1`, tame at column `i + 2`. -/

theorem lem_4_9 {k : ℕ} (i : ℕ) (hi : i + 2 < k) (W : List (Set (Band k))) (A' B' : Set (Band k)) (h : Band k)
    (hW : IsWalkFromTo W A' B') (hT : IsTameAt W ⟨i, by omega⟩ h) (hmid : ∀ x ∈ A' ∪ B', x.2 = 1)
    (A'' B'' : Set (Band k)) (hAB : IsSplit A'' B'' {b ⟨i + 1, by omega⟩, b ⟨i + 2, hi⟩}) :
    ∃ W' h', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + 1 ∧
      IsTameAt W' ⟨i + 2, hi⟩ h' := by
  exact lem_4_9_proved i hi W A' B' h hW hT hmid A'' B'' hAB

/-- Proof of Lemma 4.9, sec_chain l. 108-112: on two neighbouring columns `q`, `r = q + 1` (the paper's `i+1`, `i+2`)
the sequences `V`: `-- → a- → cc → bb` and `-b → aa → c- → b-` are walks; the comparable pairs listed there:
`a_q < c_q, c_r`; `b_q, b_r < c_q`; `b_r < c_r`; `a_q, a_r < b_r`; `a_r < c_q`. -/
theorem lem_4_9_V {k : ℕ} (q r : Fin k) (hqr : r.val = q.val + 1) :
    IsWalk [∅, {Band.a q}, {Band.c q, Band.c r}, ({Band.b q, Band.b r} : Set (Band k))] ∧
    IsWalk [{Band.b r}, {Band.a q, Band.a r}, {Band.c q}, ({Band.b q} : Set (Band k))] ∧
    Band.a q < Band.c q ∧ Band.a q < Band.c r ∧ Band.b q < Band.c q ∧ Band.b r < Band.c q ∧
    Band.b r < Band.c r ∧ Band.a q < Band.b r ∧ Band.a r < Band.b r ∧ Band.a r < Band.c q := by
  exact lem_4_9_V_proved q r hqr

/-- Corollary 4.10 (sec_chain l. 119-124; v1.50 puts "i ≥ 1" first): for `i ≥ 1` and every split of `{b_1, …, b_i}`
there is a walk of length `τ(i) = ⌊i/2⌋ + 2`, tame at column `i` (Lean `i - 1`), with states in the columns `1, …, i`,
whose outer element of column `i` lies in a prescribed outer row `r`. -/

theorem cor_4_10 {k : ℕ} (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) (r : Fin 3) (hr : r ≠ 1)
    (A B : Set (Band k)) (hAB : IsSplit A B {x | x.2 = 1 ∧ x.1.val < i}) :
    ∃ W h, IsWalkFromTo W A B ∧ W.length - 1 = i / 2 + 2 ∧ IsTameAt W ⟨i - 1, by omega⟩ h ∧ h.2 = r ∧
      ∀ X ∈ W, ∀ x ∈ X, x.1.val < i := by
  exact cor_4_10_proved i hi hik r hr A B hAB

/-! ### Section 4.4 (sec_chain l. 126-149): junctions. Row `r = 0` is the paper's statement; `r = 2` is "by σ". -/

/-- Lemma 4.11 (Junction, sec_chain l. 129-131): `i, j ≥ 1`, `L = i + j`; `W` a walk from `A'` to `B'` (middle
elements) with states in the columns `≤ i` and some state containing `c_i` (for `r = 2`: `a_i`). Then every split of
`{a_{i+1}, …, a_L}` (row `r`) has, with `W`, a walk from `A' ∪ A''` to `B' ∪ B''` of length `ℓ(W) + ⌊j/2⌋` in the
columns `≤ L`. (Lean columns: `W` in `< i`, `c_i` = `(i - 1, 2)`, the row segment = columns `i, …, i + j - 1`.) -/

theorem lem_4_11 {k : ℕ} (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hL : i + j ≤ k) (r : Fin 3) (hr : r ≠ 1)
    (W : List (Set (Band k))) (A' B' : Set (Band k)) (hW : IsWalkFromTo W A' B') (hmid : ∀ x ∈ A' ∪ B', x.2 = 1)
    (hcols : ∀ X ∈ W, ∀ x ∈ X, x.1.val < i)
    (hc : ∃ X ∈ W, ((⟨i - 1, by omega⟩ : Fin k), Fin.rev r) ∈ X)
    (A'' B'' : Set (Band k)) (hAB : IsSplit A'' B'' (rowSeg r i (i + j - 1))) :
    ∃ W', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + j / 2 ∧
      ∀ X ∈ W', ∀ x ∈ X, x.1.val < i + j := by
  exact lem_4_11_proved i j hi hj hL r hr W A' B' hW hmid hcols hc A'' B'' hAB

/-- Proof of Lemma 4.11, sec_chain l. 133-135, `j ≥ 2` (the case `a_{i+1} ∈ A''`; the paper reduces to it "by
reversal"). The paper's walk `Q`: the walk of Lemma 4.5 with even helper positions `i+2, i+4, …` (`C`), first phase
`A'' → C` (one component of `A'' ∪ C` per move, listed by `L₁`), second phase `C → B''` (`L₂`), "the move `K` of its
first phase that exchanges the component of `a_{i+1}`" last; it is a walk of Corollary 4.6 (length `⌊j/2⌋ + 1`, no
middle element, columns `i+1, …, L`, `a_{i+1}` the only element of column `i+1`). "The element `a_{i+1}` is present
exactly before `K`": it lies in state `t` of `Q` iff `t < |L₁|`. "And `c_i` is absent then": in the merged walk of the
paper (state `α` = `W_{mergeIndexW κ ℓ(W) α} ∪ Q_{mergeIndexQ κ μ ℓ(W) α}`, `K` = move `κ = |L₁| - 1` of `Q`,
performed with `W`'s move into state `μ`, Defs/MergeSchedule.lean), no state contains both `a_{i+1}` and `c_i`.
(Lean columns: `a_{i+1}` = `a i`, `c_i` = `c (i - 1)`, `W` in the columns `< i`.) -/

theorem lem_4_11_step {k : ℕ} (i j : ℕ) (hi : 1 ≤ i) (hj : 2 ≤ j) (hL : i + j ≤ k)
    (A'' B'' : Set (Band k)) (hAB : IsSplit A'' B'' (rowSeg 0 i (i + j - 1)))
    (ha : a ⟨i, by omega⟩ ∈ A'') :
    ∃ L₁ L₂ : List (Set (Band k)),
      L₁.Nodup ∧ (∀ D, D ∈ L₁ ↔ IsComponent D (A'' ∪ helperSet 1 i (i + j - 1))) ∧
      L₂.Nodup ∧ (∀ D, D ∈ L₂ ↔ IsComponent D (helperSet 1 i (i + j - 1) ∪ B'')) ∧
      a ⟨i, by omega⟩ ∈ L₁.getLastD ∅ ∧
      IsWalkFromTo (L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff (helperSet 1 i (i + j - 1))).tail) A'' B'' ∧
      (L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff (helperSet 1 i (i + j - 1))).tail).length - 1 = j / 2 + 1 ∧
      (∀ X ∈ L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff (helperSet 1 i (i + j - 1))).tail, ∀ x ∈ X,
        x.2 ≠ 1 ∧ i ≤ x.1.val ∧ x.1.val ≤ i + j - 1 ∧ (x.1.val = i → x.2 = 0)) ∧
      (∀ t, (a ⟨i, by omega⟩ ∈
          (L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff (helperSet 1 i (i + j - 1))).tail).getD t ∅ ↔
        t < L₁.length)) ∧
      ∀ (W : List (Set (Band k))) (A' B' : Set (Band k)), IsWalkFromTo W A' B' → (∀ x ∈ A' ∪ B', x.2 = 1) →
        (∀ X ∈ W, ∀ x ∈ X, x.1.val < i) → ∀ μ : ℕ, (∀ t < μ, c ⟨i - 1, by omega⟩ ∉ W.getD t ∅) →
        ∀ α : ℕ, a ⟨i, by omega⟩ ∈ W.getD (mergeIndexW (L₁.length - 1) (W.length - 1) α) ∅ ∪
            (L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff (helperSet 1 i (i + j - 1))).tail).getD
              (mergeIndexQ (L₁.length - 1) μ (W.length - 1) α) ∅ →
          c ⟨i - 1, by omega⟩ ∉ W.getD (mergeIndexW (L₁.length - 1) (W.length - 1) α) ∅ ∪
            (L₁.scanl symmDiff A'' ++ (L₂.scanl symmDiff (helperSet 1 i (i + j - 1))).tail).getD
              (mergeIndexQ (L₁.length - 1) μ (W.length - 1) α) ∅ := by
  exact lem_4_11_step_proved i j hi hj hL A'' B'' hAB ha

/-- Proof of Lemma 4.11, sec_chain l. 133-135, `j = 1`: "If `j = 1`, let `K` be the only move of `Q`; then the first
phase consists of `K`, and the second phase has no moves": `Q = (A'', B'')` is a walk of Corollary 4.6 (length
`⌊1/2⌋ + 1`, no middle element, column `i+1` only); `a_{i+1}` is present exactly before `K` (in state `t` iff `t < 1`);
and `c_i` is absent then, in the merged walk with `κ = 0`. -/

theorem lem_4_11_step_one {k : ℕ} (i : ℕ) (hi : 1 ≤ i) (hL : i + 1 ≤ k)
    (A'' B'' : Set (Band k)) (hAB : IsSplit A'' B'' (rowSeg 0 i i)) (ha : a ⟨i, by omega⟩ ∈ A'') :
    IsWalkFromTo [A'', B''] A'' B'' ∧ ([A'', B''] : List (Set (Band k))).length - 1 = 1 / 2 + 1 ∧
      (∀ X ∈ ([A'', B''] : List (Set (Band k))), ∀ x ∈ X,
        x.2 ≠ 1 ∧ i ≤ x.1.val ∧ x.1.val ≤ i ∧ (x.1.val = i → x.2 = 0)) ∧
      (∀ t, (a ⟨i, by omega⟩ ∈ ([A'', B''] : List (Set (Band k))).getD t ∅ ↔ t < 1)) ∧
      ∀ (W : List (Set (Band k))) (A' B' : Set (Band k)), IsWalkFromTo W A' B' → (∀ x ∈ A' ∪ B', x.2 = 1) →
        (∀ X ∈ W, ∀ x ∈ X, x.1.val < i) → ∀ μ : ℕ, (∀ t < μ, c ⟨i - 1, by omega⟩ ∉ W.getD t ∅) →
        ∀ α : ℕ, a ⟨i, by omega⟩ ∈ W.getD (mergeIndexW 0 (W.length - 1) α) ∅ ∪
            ([A'', B''] : List (Set (Band k))).getD (mergeIndexQ 0 μ (W.length - 1) α) ∅ →
          c ⟨i - 1, by omega⟩ ∉ W.getD (mergeIndexW 0 (W.length - 1) α) ∅ ∪
            ([A'', B''] : List (Set (Band k))).getD (mergeIndexQ 0 μ (W.length - 1) α) ∅ := by
  exact lem_4_11_step_one_proved i hi hL A'' B'' hAB ha

/-- Lemma 4.12 (Half junction, sec_chain l. 138-149): `i ≥ 2`, `j ≥ 1`, `L = i + j`; `W` a walk from `A'` to `B'`
(middle elements) tame at column `i - 1`. Then every split of `{b_i, a_{i+1}, …, a_L}` (row `r` for the `a`'s) has a
walk from `A' ∪ A''` to `B' ∪ B''` of length `ℓ(W) + ⌈j/2⌉` in the columns `≤ L`. (Lean: tame at `i - 2`, `b_i` =
`b (i - 1)`.) -/

theorem lem_4_12 {k : ℕ} (i j : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hL : i + j ≤ k) (r : Fin 3) (hr : r ≠ 1)
    (W : List (Set (Band k))) (A' B' : Set (Band k)) (h : Band k) (hW : IsWalkFromTo W A' B')
    (hT : IsTameAt W ⟨i - 2, by omega⟩ h) (hmid : ∀ x ∈ A' ∪ B', x.2 = 1)
    (A'' B'' : Set (Band k)) (hAB : IsSplit A'' B'' (insert (b ⟨i - 1, by omega⟩) (rowSeg r i (i + j - 1)))) :
    ∃ W', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + (j + 1) / 2 ∧
      ∀ X ∈ W', ∀ x ∈ X, x.1.val < i + j := by
  exact lem_4_12_proved i j hi hj hL r hr W A' B' h hW hT hmid A'' B'' hAB

/-- Proof of Lemma 4.12, Part 1, sec_chain l. 144: on one column `e` the sequences `b → c → a → -` and `- → c → a → b`
are walks. -/
theorem lem_4_12_columns {k : ℕ} (e : Fin k) :
    IsWalk [{Band.b e}, {Band.c e}, {Band.a e}, (∅ : Set (Band k))] ∧
    IsWalk [∅, {Band.c e}, {Band.a e}, ({Band.b e} : Set (Band k))] := by
  exact lem_4_12_columns_proved e

/-! ### Section 4.5 (sec_chain l. 151-163): antichains without empty columns -/

/-- Proposition 4.13 (sec_chain l. 152-154): `L ≥ 2`, `U` an antichain of `B_L` without empty columns; v1.50 asserts
that its word is `b^i x^j` with `x ∈ {a, c}`, `i, j ≥ 0`, `i + j = L` — that part is `sec4_run_form` (with `s = 0`,
`e = L - 1`) together with `sec4_word_exists`. Lean assumes here only that the middle elements are exactly those in the
first `i` columns (no bound on `i`), so the statement is at least as strong. Every split of `U` has a walk of length at
most `⌈L/2⌉ + 1` if `i ≥ 1`, and at most `⌊L/2⌋ + 1` if `i = 0`. -/

theorem prop_4_13 (L : ℕ) (hL : 2 ≤ L) (U : Set (Band L)) (hU : IsAntichainSet U)
    (hfull : ∀ l : Fin L, ∃ x ∈ U, x.1 = l) (i : ℕ) (hi : ∀ x ∈ U, x.2 = 1 ↔ x.1.val < i)
    (A B : Set (Band L)) (hAB : IsSplit A B U) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 ≤ (if 1 ≤ i then (L + 1) / 2 + 1 else L / 2 + 1) := by
  exact prop_4_13_proved L hL U hU hfull i hi A B hAB

/-! ### Section 4.6 (sec_chain l. 165-185): the arithmetic and Theorem 4.1 -/

/-- Lemma 4.14 (sec_chain l. 166-177), `g(k) = ⌊3(k+1)/4⌋`: (i) `g(p) + g(q) ≤ g(p + q + 1)`; (ii) `⌈k/2⌉ + 1 ≤ g(k)`
for `k ≥ 2`. (Also `g(0) = 0`, `g(1) = 1`, l. 166.) -/

theorem lem_4_14 :
    (∀ p q : ℕ, 3 * (p + 1) / 4 + 3 * (q + 1) / 4 ≤ 3 * (p + q + 1 + 1) / 4) ∧
      (∀ k : ℕ, 2 ≤ k → (k + 1) / 2 + 1 ≤ 3 * (k + 1) / 4) ∧ 3 * (0 + 1) / 4 = 0 ∧ 3 * (1 + 1) / 4 = 1 := by
  exact lem_4_14_proved

/-- Proof of Lemma 4.14 (ii), sec_chain l. 177: "For `k = 2, 3, 4, 5` both sides equal `2, 3, 3, 4`. For `k ≥ 6`,
`g(k) ≥ 3k/4 ≥ (k+3)/2 ≥ ⌈k/2⌉ + 1`" (`⌈k/2⌉ = (k+1)/2`, `g(k) = 3(k+1)/4` in `ℕ`). (The Lean proof of Lemma 4.14 is
`omega`; these steps are their own row.) -/
theorem lem_4_14_steps :
    ((2 + 1) / 2 + 1 = 2 ∧ 3 * (2 + 1) / 4 = 2) ∧ ((3 + 1) / 2 + 1 = 3 ∧ 3 * (3 + 1) / 4 = 3) ∧
    ((4 + 1) / 2 + 1 = 3 ∧ 3 * (4 + 1) / 4 = 3) ∧ ((5 + 1) / 2 + 1 = 4 ∧ 3 * (5 + 1) / 4 = 4) ∧
    ∀ k : ℕ, 6 ≤ k → (3 * k : ℝ) / 4 ≤ ((3 * (k + 1) / 4 : ℕ) : ℝ) ∧ ((k : ℝ) + 3) / 2 ≤ (3 * k : ℝ) / 4 ∧
      (((k + 1) / 2 + 1 : ℕ) : ℝ) ≤ ((k : ℝ) + 3) / 2 := by
  exact lem_4_14_steps_proved

/-- Proof of Theorem 4.1 (sec_chain l. 179-185), the induction: for every `k ≥ 0` (`B_0` empty), every split `(A, B)`
of every antichain of `B_k` has a walk of length at most `g(k)`. -/

theorem thm_4_1_walks (k : ℕ) (A B U : Set (Band k)) (hAB : IsSplit A B U) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 ≤ 3 * (k + 1) / 4 := by
  exact thm_4_1_walks_proved k A B U hAB

/-- Theorem 4.1 (sec_chain l. 8-10): for every `k ≥ 1`, `diam C(B_k) ≤ ⌊3(k+1)/4⌋`. -/

theorem thm_4_1 (k : ℕ) (hk : 1 ≤ k) : chainDiam (Band k) ≤ ((3 * (k + 1) / 4 : ℕ) : ℕ∞) := by
  exact thm_4_1_proved k hk

/-- sec_chain l. 11 (the overview) and the proof of Theorem 4.1 (sec_chain l. 182): if `k ≥ 2` and every column of `B_k` contains an element of an antichain
`U`, then every split `(A, B)` of `U` has a walk from `A` to `B` of length at most `⌈k/2⌉ + 1`. -/
theorem sec4_overview_fullword {k : ℕ} (hk : 2 ≤ k) (U : Set (Band k)) (hU : IsAntichainSet U)
    (hfull : ∀ l : Fin k, ∃ x ∈ U, x.1 = l) (A B : Set (Band k)) (hAB : IsSplit A B U) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 ≤ (k + 1) / 2 + 1 := by
  exact sec4_overview_fullword_proved hk U hU hfull A B hAB

end Sec4

/-! ## Section 5 — Order diameter at most two implies chain diameter at most four (sec_reverse.tex) -/

/-- Lemma 5.1 (Pair lemma), sec_reverse l. 9-11: if `diam O(P) ≤ 2`, `p, q` are incomparable and a third element `r`
is incomparable to both, then `p` and `q` have a common lower bound or a common upper bound. (Theorem 1.5 is proved in
sec_reverse l. 18-28; its row is `thm_1_5` above.) -/
theorem lem_5_1 (P : Type) [Fintype P] [PartialOrder P] (h : orderDiam P ≤ 2) (p q r : P) (hpq : p ≠ q)
    (hpq' : ¬ Comp p q) (hrp : r ≠ p) (hrq : r ≠ q) (hr1 : ¬ Comp r p) (hr2 : ¬ Comp r q) :
    (∃ c, c ≤ p ∧ c ≤ q) ∨ (∃ c, p ≤ c ∧ q ≤ c) := by
  exact lem_5_1_proved P h p q r hpq hpq' hrp hrq hr1 hr2

/-! ## Section 6 — Connected posets with order diameter two and chain diameter four (sec_reverse.tex) -/

section Sec6

open PnSets

/-! ### Section 6.1 (sec_reverse l. 33-106): the construction -/

/-- Definition 6.1 and sec_reverse l. 85: `P_n` has `2n + n(n-1) + 2n + 1 + 2n + n² = 2n² + 5n + 1` elements (stated
for every `n`; the paper takes `n ≥ 2`). -/
theorem def_6_1_count (n : ℕ) : Fintype.card (Pn n) = 2 * n ^ 2 + 5 * n + 1 := by
  exact def_6_1_count_proved n

/-- sec_reverse l. 85: the rank function (0 on pair minima, 1 on lower connectors, 2 on targets and `h`, 3 on upper
connectors, 4 on tops) increases by one along each listed relation (so the relation generated is a partial order: the
`PartialOrder` instance of `Pn n`). -/
theorem def_6_1_rank (n : ℕ) :
    ∀ x z : Pn n, PnElem.Rel x z → PnElem.level z = PnElem.level x + 1 := by
  exact def_6_1_rank_proved n

/-- sec_reverse l. 85 (new in v1.30): "hence the reflexive and transitive closure of these relations is antisymmetric,
`P_n` is a poset, and `p < q` implies `ρ(p) < ρ(q)`" (`ρ` = `PnElem.level`, the rank; the poset is the
`PartialOrder` instance of `Pn n`, whose `≤` is that closure). Used at l. 105: "elements of equal rank are
incomparable". -/
theorem def_6_1_rank_lt (n : ℕ) : ∀ p q : Pn n, p < q → PnElem.level p < PnElem.level q := by
  exact def_6_1_rank_lt_proved n

/-- Figure 2 (fig:Pn, sec_reverse l. 54-83): "The Hasse diagram of `P_2`". For every `n`, the cover pairs of `P_n` are
exactly the listed relations of Definition 6.1; along each of them the level (the drawn height) rises by one
(`def_6_1_rank`). -/
theorem fig_2_hasse (n : ℕ) (x z : Pn n) : x ⋖ z ↔ PnElem.Rel x z := by
  exact fig_2_hasse_proved n x z

/-- sec_reverse l. 87-89: `P_n` is the disjoint union of `Λ_A`, `Λ_B`, `{h}`, `W` and `T`. -/
theorem def_6_1_partition (n : ℕ) :
    lamA n ∪ lamB n ∪ {PnElem.h} ∪ ups n ∪ tops n = Set.univ ∧ Disjoint (lamA n) (lamB n) ∧
      Disjoint (lamA n ∪ lamB n) {PnElem.h} ∧ Disjoint (lamA n ∪ lamB n ∪ {PnElem.h}) (ups n) ∧
      Disjoint (lamA n ∪ lamB n ∪ {PnElem.h} ∪ ups n) (tops n) := by
  exact def_6_1_partition_proved n

/-- sec_reverse l. 91: `σ` is an involution that maps the listed relations onto the listed relations, so it is an
automorphism of `P_n`; it exchanges `A` and `B`, fixes `h`, maps ideals to ideals and antichains to antichains, and
induces automorphisms of the graphs of `O(P_n)` and `C(P_n)` (`I ↦ σ(I)`, `X ↦ σ(X)`). -/
theorem sec6_sigma (n : ℕ) :
    (∀ x : Pn n, sigma n (sigma n x) = x) ∧
    (∀ x z : Pn n, PnElem.Rel x z ↔ PnElem.Rel (sigma n x) (sigma n z)) ∧
    (∀ x z : Pn n, x ≤ z ↔ sigma n x ≤ sigma n z) ∧
    sigma n '' tgtA n = tgtB n ∧ sigma n '' tgtB n = tgtA n ∧ sigma n PnElem.h = PnElem.h ∧
    (∀ I : Set (Pn n), IsIdeal I → IsIdeal (sigma n '' I)) ∧
    (∀ X : Set (Pn n), IsAntichainSet X → IsAntichainSet (sigma n '' X)) ∧
    (∃ e : polyGraph (orderPolytope (Pn n)) ≃g polyGraph (orderPolytope (Pn n)),
      ∀ (I : Set (Pn n)) (hI : IsIdeal I) (hI' : IsIdeal (sigma n '' I)), e (oVtx I hI) = oVtx (sigma n '' I) hI') ∧
    (∃ e : polyGraph (chainPolytope (Pn n)) ≃g polyGraph (chainPolytope (Pn n)),
      ∀ (X : Set (Pn n)) (hX : IsAntichainSet X) (hX' : IsAntichainSet (sigma n '' X)),
        e (cVtx X hX) = cVtx (sigma n '' X) hX') := by
  exact sec6_sigma_proved n

/-- Definition 6.1 and sec_reverse l. 31, l. 272 ("The states are antichains"): `A`, `B`, `U`, `M_A` and `M_B` are
antichains. -/
theorem sec6_antichains (n : ℕ) :
    IsAntichainSet (tgtA n) ∧ IsAntichainSet (tgtB n) ∧ IsAntichainSet (tgts n) ∧ IsAntichainSet (pairMinA n) ∧
      IsAntichainSet (pairMinB n) := by
  exact sec6_antichains_proved n

/-- sec_reverse l. 85: "`y_i` lies above the `n - 1` pair minima `m_{ik}` (`k ≠ i`)", and nothing else lies below it.
(The rest of l. 85: "each `m_ik` lies below `a_i` and `a_k`" and "`t_ij` lies above `a_i` and `b_j`" are in `lem_6_2_i`
(conjuncts 1, 3 and 7); the count is `def_6_1_count`; the levels are `def_6_1_rank`.) -/
theorem sec6_l85 (n : ℕ) (i : Fin n) :
    {x : Pn n | x < PnElem.y i} = {x | ∃ E : Pair n, i ∈ E.1 ∧ x = PnElem.m E} ∧
    {x : Pn n | x < PnElem.y i}.ncard = n - 1 := by
  exact sec6_l85_proved n i

/-- Proof of Lemma 6.2, sec_reverse l. 105 (reused at l. 254): `↑y_i = {y_i, a_i} ∪ ↑h`, `↓w_i = {w_i, a_i, h} ∪ Q`,
`↓t_{ij} = {t_{ij}, w_i, w'_j, a_i, b_j, h} ∪ Q`. -/
theorem sec6_updown (n : ℕ) (i j : Fin n) :
    {x : Pn n | PnElem.y i ≤ x} = {PnElem.y i, PnElem.a i} ∪ {x | PnElem.h ≤ x} ∧
    {x : Pn n | x ≤ PnElem.w i} = {PnElem.w i, PnElem.a i, PnElem.h} ∪ qSet n ∧
    {x : Pn n | x ≤ PnElem.t i j} =
      {PnElem.t i j, PnElem.w i, PnElem.w' j, PnElem.a i, PnElem.b j, PnElem.h} ∪ qSet n := by
  exact sec6_updown_proved n i j

/-- Lemma 6.2 (i), sec_reverse l. 97: the elements below `a_i` are `y_i` and the `m_{ik}`, all in `↓y_i`; the elements
above `a_i` are `w_i` and the `t_{ij}`, all in `↑w_i`; and by `σ` the same for `b_j` with `y'_j`, `m'_{jl}`, `w'_j`,
`t_{ij}` (stated for every `n`). -/
theorem lem_6_2_i (n : ℕ) (i : Fin n) :
    (∀ x : Pn n, x < PnElem.a i ↔ x = PnElem.y i ∨ ∃ E : Pair n, i ∈ E.1 ∧ x = PnElem.m E) ∧
    (∀ x : Pn n, x < PnElem.a i → x ≤ PnElem.y i) ∧
    (∀ x : Pn n, PnElem.a i < x ↔ x = PnElem.w i ∨ ∃ j, x = PnElem.t i j) ∧
    (∀ x : Pn n, PnElem.a i < x → PnElem.w i ≤ x) ∧
    (∀ x : Pn n, x < PnElem.b i ↔ x = PnElem.y' i ∨ ∃ E : Pair n, i ∈ E.1 ∧ x = PnElem.m' E) ∧
    (∀ x : Pn n, x < PnElem.b i → x ≤ PnElem.y' i) ∧
    (∀ x : Pn n, PnElem.b i < x ↔ x = PnElem.w' i ∨ ∃ j, x = PnElem.t j i) ∧
    (∀ x : Pn n, PnElem.b i < x → PnElem.w' i ≤ x) := by
  exact lem_6_2_i_proved n i

/-- Lemma 6.2 (ii), sec_reverse l. 98: `↓h = Q ∪ {h}` and `↑h = {h} ∪ W ∪ T`; so `h` is comparable to every element
outside `U ∪ {h}` and to no target, and every element of `Q` lies below every element of `W ∪ T`. -/
theorem lem_6_2_ii (n : ℕ) :
    {x : Pn n | x ≤ PnElem.h} = qSet n ∪ {PnElem.h} ∧ {x : Pn n | PnElem.h ≤ x} = {PnElem.h} ∪ ups n ∪ tops n ∧
    (∀ x : Pn n, x ∉ tgts n ∪ {PnElem.h} → Comp x PnElem.h) ∧ (∀ u ∈ tgts n, ¬ Comp u (PnElem.h : Pn n)) ∧
    (∀ q ∈ qSet n, ∀ z ∈ ups n ∪ tops n, q < z) := by
  exact lem_6_2_ii_proved n

/-- Lemma 6.2 (iii), sec_reverse l. 99: no element of `Λ_A` is comparable to an element of `Λ_B`. -/
theorem lem_6_2_iii (n : ℕ) : ∀ x ∈ lamA n, ∀ z ∈ lamB n, ¬ Comp x z := by
  exact lem_6_2_iii_proved n

/-- Lemma 6.2 (iv), sec_reverse l. 100: every element of `W_A ∪ T` lies above exactly one target of `A` (`w_i` and
`t_{ij}` above `a_i`), no element of `W_A` lies above a target of `B`; the same for `W_B ∪ T` and `B` (`t_{ij}` above
`b_j`); `W` and `T` are antichains. -/
theorem lem_6_2_iv (n : ℕ) :
    (∀ z ∈ upA n ∪ tops n, ∃! i : Fin n, PnElem.a i < z) ∧ (∀ i, (PnElem.a i : Pn n) < PnElem.w i) ∧
    (∀ i j, (PnElem.a i : Pn n) < PnElem.t i j) ∧ (∀ z ∈ upA n, ∀ j : Fin n, ¬ (PnElem.b j : Pn n) < z) ∧
    (∀ z ∈ upB n ∪ tops n, ∃! j : Fin n, PnElem.b j < z) ∧ (∀ j, (PnElem.b j : Pn n) < PnElem.w' j) ∧
    (∀ i j, (PnElem.b j : Pn n) < PnElem.t i j) ∧ (∀ z ∈ upB n, ∀ i : Fin n, ¬ (PnElem.a i : Pn n) < z) ∧
    IsAntichainSet (ups n) ∧ IsAntichainSet (tops n) := by
  exact lem_6_2_iv_proved n

/-- Lemma 6.2 (v), sec_reverse l. 101: the comparability graph of `P_n` is connected (stated for every `n`). -/
theorem lem_6_2_v (n : ℕ) : IsConnPoset (Pn n) := by
  exact lem_6_2_v_proved n

/-- sec_reverse l. 194-197: `↓A = Λ_A`, `↑A = A ∪ W_A ∪ T`, hence `Z_A = Λ_B ∪ {h} ∪ W_B` and `Z_B = Λ_A ∪ {h} ∪ W_A`. -/
theorem sec6_ZA (n : ℕ) :
    {x : Pn n | ∃ u ∈ tgtA n, x ≤ u} = lamA n ∧ {x : Pn n | ∃ u ∈ tgtA n, u ≤ x} = tgtA n ∪ upA n ∪ tops n ∧
    zA n = lamB n ∪ {PnElem.h} ∪ upB n ∧ zB n = lamA n ∪ {PnElem.h} ∪ upA n := by
  exact sec6_ZA_proved n

/-! ### Section 6.2 (sec_reverse l. 110-189): the order diameter of `P_n` -/

/-- Lemma 6.3, sec_reverse l. 114-120: (i) every ideal `I` with `h ∈ I` is connected; (ii) for every ideal `J` with
`h ∉ J`, `P \ J` is connected and contains `↑h`. -/
theorem lem_6_3 (n : ℕ) (hn : 2 ≤ n) :
    (∀ I : Set (Pn n), IsIdeal I → (PnElem.h : Pn n) ∈ I → IsConnSet I) ∧
    (∀ J : Set (Pn n), IsIdeal J → (PnElem.h : Pn n) ∉ J → IsConnSet Jᶜ ∧ {x : Pn n | PnElem.h ≤ x} ⊆ Jᶜ) := by
  exact lem_6_3_proved n hn

/-- Lemma 6.4 (i) (Mixed pairs), sec_reverse l. 131: for a mixed pair `(I, J)`, `Q ⊆ I`, `J ⊆ Q ∪ U` and
`J \ I ⊆ U`. -/
theorem lem_6_4_i (n : ℕ) (hn : 2 ≤ n) (I J : Set (Pn n)) (hm : IsMixed n I J) :
    qSet n ⊆ I ∧ J ⊆ qSet n ∪ tgts n ∧ J \ I ⊆ tgts n := by
  exact lem_6_4_i_proved n hn I J hm

/-- Lemma 6.4 (ii), sec_reverse l. 132: if `J ∩ (A ∪ Y_A)` is nonempty, its elements lie in one component of `J`, and
this component is contained in `Λ_A`; the same for `J ∩ (B ∪ Y_B)` and `Λ_B`. -/
theorem lem_6_4_ii (n : ℕ) (hn : 2 ≤ n) (I J : Set (Pn n)) (hm : IsMixed n I J) :
    ((J ∩ (tgtA n ∪ lowA n)).Nonempty →
      ∃ K, IsComponent K J ∧ J ∩ (tgtA n ∪ lowA n) ⊆ K ∧ K ⊆ lamA n) ∧
    ((J ∩ (tgtB n ∪ lowB n)).Nonempty →
      ∃ K, IsComponent K J ∧ J ∩ (tgtB n ∪ lowB n) ⊆ K ∧ K ⊆ lamB n) := by
  exact lem_6_4_ii_proved n hn I J hm

/-- Lemma 6.4 (iii), sec_reverse l. 126 and l. 133: the component `Γ_h` of `I \ J` that contains `h` exists, and
`I \ J = Γ_h ∪ Iso(I, J)`, every `u ∈ Iso(I, J)` forming a component `{u}` of `I \ J`. -/
theorem lem_6_4_iii (n : ℕ) (hn : 2 ≤ n) (I J : Set (Pn n)) (hm : IsMixed n I J) :
    (∃ Γ, IsComponent Γ (I \ J) ∧ (PnElem.h : Pn n) ∈ Γ) ∧
    ∀ Γ, IsComponent Γ (I \ J) → (PnElem.h : Pn n) ∈ Γ →
      I \ J = Γ ∪ isoSet n I J ∧ ∀ u ∈ isoSet n I J, IsComponent {u} (I \ J) := by
  exact lem_6_4_iii_proved n hn I J hm

/-- Lemma 6.5 (A common neighbor of `I` and `J`), sec_reverse l. 144-153: for a mixed pair with `w_i ∉ I`, `w'_j ∉ I`,
the component `Γ` of `P \ I` containing `w_i` exists, and for it: (i) `Γ` contains `W \ I` and `U \ I`; (ii)
`K = I ∪ Γ` is an ideal adjacent to `I` and `J ⊂ K`; (iii) `K \ J` is connected, `K` is adjacent to `J`, and
`d_O(I, J) ≤ 2`. -/
theorem lem_6_5 (n : ℕ) (hn : 2 ≤ n) (I J : Set (Pn n)) (hm : IsMixed n I J) (i j : Fin n)
    (hwi : (PnElem.w i : Pn n) ∉ I) (hwj : (PnElem.w' j : Pn n) ∉ I) :
    (∃ Γ, IsComponent Γ Iᶜ ∧ (PnElem.w i : Pn n) ∈ Γ) ∧
    ∀ Γ, IsComponent Γ Iᶜ → (PnElem.w i : Pn n) ∈ Γ →
      (ups n \ I ⊆ Γ ∧ tgts n \ I ⊆ Γ) ∧
      (IsIdeal (I ∪ Γ) ∧ IsConnSet ((I ∪ Γ) \ I) ∧ J ⊂ I ∪ Γ) ∧
      IsConnSet ((I ∪ Γ) \ J) ∧
      (∃ hK : IsIdeal (I ∪ Γ), dO I (I ∪ Γ) hm.1 hK = 1 ∧ dO (I ∪ Γ) J hK hm.2.1 = 1) ∧
      dO I J hm.1 hm.2.1 ≤ 2 := by
  exact lem_6_5_proved n hn I J hm i j hwi hwj

/-- Proposition 6.6, sec_reverse l. 162-164: for every mixed pair `(I, J)`, `d_O(I, J) ≤ 2`. -/
theorem prop_6_6 (n : ℕ) (hn : 2 ≤ n) (I J : Set (Pn n)) (hm : IsMixed n I J) : dO I J hm.1 hm.2.1 ≤ 2 := by
  exact prop_6_6_proved n hn I J hm

/-- Proof of Proposition 6.6, sec_reverse l. 166: "The automorphism `σ` fixes `h`, so it maps mixed pairs to mixed pairs;
it exchanges `A` and `B`, and `σ(u^-) = σ(u)^-` and `σ(u^+) = σ(u)^+` for every target `u`. Hence
`Iso(σI, σJ) = σ(Iso(I, J))` and `σJ \ σI = σ(J \ I)` ... As `σ` preserves distances, ...". (The Lean proof of
Proposition 6.6 treats the case `Θ ⊆ B` directly; this step of the paper's route is its own row. `σ` exchanging `A`
and `B` is in `sec6_sigma`.) -/
theorem prop_6_6_sigma (n : ℕ) :
    (∀ I J : Set (Pn n), IsMixed n I J → IsMixed n (sigma n '' I) (sigma n '' J)) ∧
    (∀ u ∈ tgts n, sigma n (lo n u) = lo n (sigma n u) ∧ sigma n (up n u) = up n (sigma n u)) ∧
    (∀ I J : Set (Pn n), isoSet n (sigma n '' I) (sigma n '' J) = sigma n '' isoSet n I J ∧
      sigma n '' J \ sigma n '' I = sigma n '' (J \ I)) ∧
    (∀ (I J : Set (Pn n)) (hI : IsIdeal I) (hJ : IsIdeal J) (hI' : IsIdeal (sigma n '' I))
      (hJ' : IsIdeal (sigma n '' J)), dO (sigma n '' I) (sigma n '' J) hI' hJ' = dO I J hI hJ) := by
  exact prop_6_6_sigma_proved n

/-- Theorem 6.7, sec_reverse l. 184-186: for every `n ≥ 2`, `diam O(P_n) = 2`. -/
theorem thm_6_7 (n : ℕ) (hn : 2 ≤ n) : orderDiam (Pn n) = 2 := by
  exact thm_6_7_proved n hn

/-! ### Section 6.3 (sec_reverse l. 191-277): the chain diameter of `P_n` -/

/-- Lemma 6.8 (Neighbors of `A`), sec_reverse l. 201-209: every `X ∈ N[A]` with `X ≠ A` has type (D), (E), (L) or
(H). -/
theorem lem_6_8 (n : ℕ) (hn : 2 ≤ n) (X : Set (Pn n)) (hX : X ∈ nbhdC (tgtA n)) (hne : X ≠ tgtA n) :
    IsTypeD n X ∨ IsTypeE n X ∨ IsTypeL n X ∨ IsTypeH n X := by
  exact lem_6_8_proved n hn X hX hne

/-- sec_reverse l. 216 (Lemma 6.8 by `σ`): every `Y ∈ N[B]` with `Y ≠ B` has type (D'), (E'), (L') or (H'). -/
theorem lem_6_8_B (n : ℕ) (hn : 2 ≤ n) (Y : Set (Pn n)) (hY : Y ∈ nbhdC (tgtB n)) (hne : Y ≠ tgtB n) :
    IsTypeD' n Y ∨ IsTypeE' n Y ∨ IsTypeL' n Y ∨ IsTypeH' n Y := by
  exact lem_6_8_B_proved n hn Y hY hne

/-- Lemma 6.9 (Isolated elements), sec_reverse l. 218-220: for antichains `X, Y` and `G = X △ Y`, if `x ∈ X \ Y` is
comparable to no element of `Y`, then no element of `G` is comparable to `x`; so if moreover `|G| ≥ 2`, `G` is not
connected. (The version with `X` and `Y` exchanged is the same statement for `Y, X`.) -/
theorem lem_6_9 {P : Type} [PartialOrder P] (X Y : Set P) (hX : IsAntichainSet X) (hY : IsAntichainSet Y)
    (x : P) (hx : x ∈ X \ Y) (hxY : ∀ z ∈ Y, ¬ Comp x z) :
    (∀ g ∈ symmDiff X Y, ¬ Comp g x) ∧ (2 ≤ (symmDiff X Y).encard → ¬ IsConnSet (symmDiff X Y)) := by
  exact lem_6_9_proved X Y hX hY x hx hxY

/-- Lemma 6.10, sec_reverse l. 227-235 (for `Y ∈ N[B]`; Lean drops that hypothesis, as each part fixes the form of
`Y`): (i) if `Y = B` or `Y` has type (D') or (L'), then `Y ⊆ Λ_B` and no element of `Y` is attached to a target of `A`;
(ii) if `Y = B ∪ {z}` has type (E'), then `z` is the only element of `Y` that can be attached to a target of `A`, and to
at most two of them; (iii) if `Y = (B \ {b_j}) ∪ S` has type (H'), then `Y ∩ A = ∅`, the only elements of `Y`
comparable to targets of `A` are the tops `t_{pj} ∈ S`, and `t_{pj}` is comparable to `a_p` only. -/
theorem lem_6_10 (n : ℕ) (hn : 2 ≤ n) :
    (∀ Y : Set (Pn n), (Y = tgtB n ∨ IsTypeD' n Y ∨ IsTypeL' n Y) →
      Y ⊆ lamB n ∧ ∀ z ∈ Y, ∀ u ∈ tgtA n, ¬ Attached z u) ∧
    (∀ z ∈ zB n, (∀ z' ∈ insert z (tgtB n), z' ≠ z → ∀ u ∈ tgtA n, ¬ Attached z' u) ∧
      {u | u ∈ tgtA n ∧ Attached z u}.encard ≤ 2) ∧
    (∀ (j : Fin n) (S : Set (Pn n)), (S = {PnElem.w' j} ∨ (S.Nonempty ∧ S ⊆ {x | ∃ i, x = PnElem.t i j})) →
      ((tgtB n \ {PnElem.b j}) ∪ S) ∩ tgtA n = ∅ ∧
      (∀ z ∈ (tgtB n \ {PnElem.b j}) ∪ S, ∀ u ∈ tgtA n, Comp z u → ∃ p, z = PnElem.t p j ∧ z ∈ S) ∧
      ∀ p : Fin n, ∀ u ∈ tgtA n, Comp (PnElem.t p j : Pn n) u → u = PnElem.a p) := by
  exact lem_6_10_proved n hn

/-- Lemma 6.10, sec_reverse l. 234: "The same statements hold with `A` and `B` exchanged, for `X ∈ N[A]`". -/
theorem lem_6_10_swap (n : ℕ) (hn : 2 ≤ n) :
    (∀ X : Set (Pn n), (X = tgtA n ∨ IsTypeD n X ∨ IsTypeL n X) →
      X ⊆ lamA n ∧ ∀ z ∈ X, ∀ u ∈ tgtB n, ¬ Attached z u) ∧
    (∀ z ∈ zA n, (∀ z' ∈ insert z (tgtA n), z' ≠ z → ∀ u ∈ tgtB n, ¬ Attached z' u) ∧
      {u | u ∈ tgtB n ∧ Attached z u}.encard ≤ 2) ∧
    (∀ (i : Fin n) (S : Set (Pn n)), (S = {PnElem.w i} ∨ (S.Nonempty ∧ S ⊆ {x | ∃ j, x = PnElem.t i j})) →
      ((tgtA n \ {PnElem.a i}) ∪ S) ∩ tgtB n = ∅ ∧
      (∀ z ∈ (tgtA n \ {PnElem.a i}) ∪ S, ∀ u ∈ tgtB n, Comp z u → ∃ q, z = PnElem.t i q ∧ z ∈ S) ∧
      ∀ q : Fin n, ∀ u ∈ tgtB n, Comp (PnElem.t i q : Pn n) u → u = PnElem.b q) := by
  exact lem_6_10_swap_proved n hn

/-- Proposition 6.11, sec_reverse l. 240-242: for `n ≥ 4`, `X ∈ N[A]` and `Y ∈ N[B]`, the set `X △ Y` is nonempty and
disconnected; in particular `X ≠ Y` and `X`, `Y` are not adjacent (`d_C(X, Y) ≥ 2`). -/
theorem prop_6_11 (n : ℕ) (hn : 4 ≤ n) (X Y : Set (Pn n)) (hX : X ∈ nbhdC (tgtA n))
    (hY : Y ∈ nbhdC (tgtB n)) :
    (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) ∧ X ≠ Y ∧
      ∀ (hX' : IsAntichainSet X) (hY' : IsAntichainSet Y), 2 ≤ dC X Y hX' hY' := by
  exact prop_6_11_proved n hn X Y hX hY

/-- Proof of Proposition 6.11 and the first sentence of Remark 6.12 (sec_reverse l. 261, "Cases 1, 2, 3 and 5 of the
proof of Proposition 6.11 use only `n ≥ 3`; Case 4 is the only place where `n ≥ 4` is needed"): for `n ≥ 3`, every pair
`X ∈ N[A]`, `Y ∈ N[B]` other than the pairs of types (E), (H') and (H), (E') has `X △ Y` nonempty and disconnected.
(`rem_6_12` shows that at `n = 3` a pair of types (H), (E') can be adjacent.) -/
theorem prop_6_11_n3 (n : ℕ) (hn : 3 ≤ n) (X Y : Set (Pn n)) (hX : X ∈ nbhdC (tgtA n))
    (hY : Y ∈ nbhdC (tgtB n)) (hEH : ¬ (IsTypeE n X ∧ IsTypeH' n Y)) (hHE : ¬ (IsTypeH n X ∧ IsTypeE' n Y)) :
    (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) := by
  exact prop_6_11_n3_proved n hn X Y hX hY hEH hHE

/-- Remark 6.12, sec_reverse l. 260-262: for `n ∈ {2, 3}`, the sequence `A → (A \ {a_1}) ∪ {t_11, …, t_1n} →
B ∪ {m_E} → B` (`E = {2, 3}` if `n = 3`, `E = {1, 2}` if `n = 2`; Lean, 0-based: `E = {n - 2, n - 1}`) is a walk of
length 3 (four states) whose middle states have types (H) and (E') (and lie in `N[A]`, `N[B]`). The remark's first
sentence ("Cases 1, 2, 3 and 5 of the proof of Proposition 6.11 use only `n ≥ 3`; Case 4 is the only place where
`n ≥ 4` is needed") is the row `prop_6_11_n3`. Only the last sentence,
"We do not determine `diam C(P_n)` for `n ≤ 3`", is not a claim. -/
theorem rem_6_12 (n : ℕ) (hn : n = 2 ∨ n = 3) :
    (∃ E : Pair n, E.1 = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩}) ∧
    ∀ E : Pair n, E.1 = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} →
      IsWalkFromTo [tgtA n, (tgtA n \ {PnElem.a ⟨0, by omega⟩}) ∪ {x | ∃ j, x = PnElem.t ⟨0, by omega⟩ j},
          insert (PnElem.m E) (tgtB n), tgtB n] (tgtA n) (tgtB n) ∧
        IsTypeH n ((tgtA n \ {PnElem.a ⟨0, by omega⟩}) ∪ {x | ∃ j, x = PnElem.t ⟨0, by omega⟩ j}) ∧
        (tgtA n \ {PnElem.a ⟨0, by omega⟩}) ∪ {x | ∃ j, x = PnElem.t ⟨0, by omega⟩ j} ∈ nbhdC (tgtA n) ∧
        IsTypeE' n (insert (PnElem.m E) (tgtB n)) ∧ insert (PnElem.m E) (tgtB n) ∈ nbhdC (tgtB n) := by
  exact rem_6_12_proved n hn

/-- Proof of Theorem 6.13 (upper bound), sec_reverse l. 268-272: `A → M_A → {h} → M_B → B` is a walk (stated for
`n ≥ 2`). -/
theorem thm_6_13_walk (n : ℕ) (hn : 2 ≤ n) :
    IsWalkFromTo [tgtA n, pairMinA n, {PnElem.h}, pairMinB n, tgtB n] (tgtA n) (tgtB n) := by
  exact thm_6_13_walk_proved n hn

/-- Theorem 6.13, sec_reverse l. 264-266: for every `n ≥ 4`, `d_C(A, B) = 4`, hence `diam C(P_n) = 4`. -/
theorem thm_6_13 (n : ℕ) (hn : 4 ≤ n) :
    (∀ (hA : IsAntichainSet (tgtA n)) (hB : IsAntichainSet (tgtB n)), dC (tgtA n) (tgtB n) hA hB = 4) ∧
      chainDiam (Pn n) = 4 := by
  exact thm_6_13_proved n hn

end Sec6

/-! ## Section 7 — Questions

Questions 7.1 and 7.2 (l. 221-223, l. 226-227) are open questions, not claims; their exact formal readings are the
propositions `question_7_1` and `question_7_2` (`LeeDiam/Defs/Questions.lean`). -/

/-- Section 7, l. 225: a connected poset with `diam C(P) - diam O(P) ≥ 3` has `diam O(P) ≥ 3` (Lean allows the empty
poset: connectivity here is `Preconnected`; v1.50's "connected" includes nonempty, so this is at least as strong); in
the proof, a nonempty poset with `diam O(P) ≤ 1` is a chain with `diam C(P) = 1` (the empty-poset part is a Lean
helper: both diameters are `0`). -/
theorem sec7_q1_remark :
    (∀ (P : Type) [Fintype P] [PartialOrder P], (compGraph P).Preconnected →
      orderDiam P + 3 ≤ chainDiam P → 3 ≤ orderDiam P) ∧
    (∀ (P : Type) [Fintype P] [PartialOrder P], IsEmpty P → orderDiam P = 0 ∧ chainDiam P = 0) ∧
    (∀ (P : Type) [Fintype P] [PartialOrder P], Nonempty P → orderDiam P ≤ 1 →
      IsChain (· ≤ ·) (Set.univ : Set P) ∧ chainDiam P = 1) := by
  exact sec7_q1_remark_proved

/-- Section 7, l. 227: the supremum of `diam O(P) / diam C(P)` over connected finite posets is at least `4/3`
(Theorem 1.3). -/
theorem sec7_ratio (r : ℝ) (hr : r < 4 / 3) :
    ∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (dO dC : ℕ), IsConnPoset P ∧ orderDiam P = dO ∧
      chainDiam P = dC ∧ 0 < dC ∧ r < (dO : ℝ) / dC := by
  exact sec7_ratio_proved r hr

end LeeDiam
