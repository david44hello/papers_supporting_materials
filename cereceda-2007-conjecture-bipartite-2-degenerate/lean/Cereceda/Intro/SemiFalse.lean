/-
Cereceda/Intro/SemiFalse.lean — embeddings with no edge leaving the image (`Closed`, `closed_sumInl`, `closed_sumInr`),
and two results of an earlier proof route of Section 1 that short v3.90 does not use: no
graph with the subdivided `K_5` as a component is semi-false, and `K_{2,7} ⊔ (subdivided K_5) ⊔ T` (and its disjoint
union with any bipartite 2-degenerate graph) is not semi-false. Earlier drafts used the subdivided `K_4` and the
3-colour-dense graphs instead (a paragraph that short v3.90 no longer has).
Imported by Intro/ColourDense.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Classes
import Cereceda.Intro.UnionNoClass
import Cereceda.Intro.Subdivision
import Cereceda.Intro.Examples

namespace Cereceda

namespace SemiFalse

/-! ### The subdivided `K_5` -/

/-- The subdivided `K_5`: branch vertices `Sum.inl x`, subdivision vertices `Sum.inr e`. -/
abbrev K5s : SimpleGraph (Fin 5 ⊕ (⊤ : SimpleGraph (Fin 5)).edgeSet) := subdivision (⊤ : SimpleGraph (Fin 5))

theorem not_adj_inl_inl (x y : Fin 5) : ¬ K5s.Adj (Sum.inl x) (Sum.inl y) := fun h => h

theorem not_adj_inr_inr (e e' : (⊤ : SimpleGraph (Fin 5)).edgeSet) : ¬ K5s.Adj (Sum.inr e) (Sum.inr e') :=
  fun h => h

theorem exists_third : ∀ x y : Fin 5, ∃ z, z ≠ x ∧ z ≠ y := by
  decide

theorem exists_two_others : ∀ x : Fin 5, ∃ z₁ z₂, z₁ ≠ x ∧ z₂ ≠ x ∧ z₁ ≠ z₂ := by
  decide

/-- Every vertex of the subdivided `K_5` has two distinct neighbours. -/
theorem two_nbrs (u : Fin 5 ⊕ (⊤ : SimpleGraph (Fin 5)).edgeSet) :
    ∃ a₁ a₂, K5s.Adj u a₁ ∧ K5s.Adj u a₂ ∧ a₁ ≠ a₂ := by
  rcases u with x | ⟨e, he⟩
  · obtain ⟨z₁, z₂, h₁, h₂, h₁₂⟩ := exists_two_others x
    refine ⟨Sum.inr ⟨s(x, z₁), (SimpleGraph.mem_edgeSet ⊤).2 h₁.symm⟩,
      Sum.inr ⟨s(x, z₂), (SimpleGraph.mem_edgeSet ⊤).2 h₂.symm⟩, Sym2.mem_mk_left x z₁, Sym2.mem_mk_left x z₂, ?_⟩
    intro h
    exact h₁₂ (Sym2.congr_right.1 (congrArg Subtype.val (Sum.inr_injective h)))
  · induction e using Sym2.ind with
    | h x y =>
      have hxy : x ≠ y := (SimpleGraph.mem_edgeSet ⊤).1 he
      exact ⟨Sum.inl x, Sum.inl y, Sym2.mem_mk_left x y, Sym2.mem_mk_right x y,
        fun h => hxy (Sum.inl_injective h)⟩

/-- No vertex `c ≠ u` of the subdivided `K_5` is adjacent to all neighbours of `u`. -/
theorem no_dominator (u c : Fin 5 ⊕ (⊤ : SimpleGraph (Fin 5)).edgeSet) (hcu : c ≠ u) :
    ∃ a, K5s.Adj u a ∧ ¬ K5s.Adj c a := by
  rcases u with x | ⟨e, he⟩
  · rcases c with y | e'
    · have hyx : y ≠ x := fun h => hcu (by rw [h])
      obtain ⟨z, hzx, hzy⟩ := exists_third x y
      refine ⟨Sum.inr ⟨s(x, z), (SimpleGraph.mem_edgeSet ⊤).2 hzx.symm⟩, Sym2.mem_mk_left x z, fun h => ?_⟩
      have h' : y ∈ s(x, z) := h
      rcases Sym2.mem_iff.1 h' with h | h
      · exact hyx h
      · exact hzy h.symm
    · obtain ⟨z, hzx, -⟩ := exists_third x x
      exact ⟨Sum.inr ⟨s(x, z), (SimpleGraph.mem_edgeSet ⊤).2 hzx.symm⟩, Sym2.mem_mk_left x z, not_adj_inr_inr _ _⟩
  · induction e using Sym2.ind with
    | h x y =>
      have hxy : x ≠ y := (SimpleGraph.mem_edgeSet ⊤).1 he
      rcases c with z | ⟨e', he'⟩
      · exact ⟨Sum.inl x, Sym2.mem_mk_left x y, not_adj_inl_inl _ _⟩
      · by_cases hx : x ∈ e'
        · refine ⟨Sum.inl y, Sym2.mem_mk_right x y, fun hy => hcu ?_⟩
          have he'xy : e' = s(x, y) := (Sym2.mem_and_mem_iff hxy).1 ⟨hx, hy⟩
          subst he'xy
          rfl
        · exact ⟨Sum.inl x, Sym2.mem_mk_left x y, hx⟩

/-! ### Embeddings with no edge leaving the image -/

section Closed

variable {α β γ : Type} {A : SimpleGraph α} {B : SimpleGraph β} {S : SimpleGraph γ}

/-- No edge of `A` leaves the image of `f`. -/
def Closed (f : S ↪g A) : Prop := ∀ a y, A.Adj (f a) y → y ∈ Set.range f

theorem closed_sumInl (f : S ↪g A) (hf : Closed f) :
    Closed (f.trans SimpleGraph.Embedding.sumInl : S ↪g A ⊕g B) := by
  intro a y h
  rcases y with y | y
  · obtain ⟨b, rfl⟩ := hf a y h
    exact ⟨b, rfl⟩
  · exact (Bool.false_ne_true h).elim

theorem closed_sumInr : Closed (SimpleGraph.Embedding.sumInr : B ↪g A ⊕g B) := by
  intro b y h
  rcases y with y | y
  · exact (Bool.false_ne_true h).elim
  · exact ⟨y, rfl⟩

end Closed

/-! ### The two results of the earlier proof route (not in v3.90) -/

theorem intro_K5sub_component_not_semiFalse_proved {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    (f : subdivision (⊤ : SimpleGraph (Fin 5)) ↪g G) (hcomp : ∀ a y, G.Adj (f a) y → y ∈ Set.range f) :
    ¬ IsSemiFalse G := by
  rintro ⟨ρ, hρ⟩
  -- the vertex `u` of the component added last
  obtain ⟨u, -, hu⟩ := Finset.exists_max_image Finset.univ (fun a => ρ (f a))
    (Finset.univ_nonempty_iff.2 ⟨Sum.inl 0⟩)
  have hlt : ∀ a, K5s.Adj u a → ρ (f a) < ρ (f u) := fun a ha =>
    lt_of_le_of_ne (hu a (Finset.mem_univ _)) fun h => ha.ne (f.injective (ρ.injective h)).symm
  have hadj : ∀ a, K5s.Adj u a → G.Adj (f u) (f a) := fun a ha => f.map_adj_iff.2 ha
  obtain ⟨a₁, a₂, h₁, h₂, h₁₂⟩ := two_nbrs u
  rcases hρ (f u) with h | ⟨w, -, -, hw⟩ | ⟨v, hv, hvw⟩
  · -- `u` has an earlier neighbour
    exact h (f a₁) (hadj a₁ h₁) (hlt a₁ h₁)
  · -- `u` has two earlier neighbours
    have e₁ := hw (f a₁) (hadj a₁ h₁) (hlt a₁ h₁)
    have e₂ := hw (f a₂) (hadj a₂ h₂) (hlt a₂ h₂)
    exact h₁₂ (f.injective (e₁.trans e₂.symm))
  · -- an earlier `v` adjacent to all neighbours of `u` lies in the component, and is not `u`
    obtain ⟨c, rfl⟩ := hcomp a₁ v ((hvw (f a₁) (hadj a₁ h₁) (hlt a₁ h₁)).symm)
    have hcu : c ≠ u := by
      rintro rfl
      exact lt_irrefl _ hv
    obtain ⟨a, ha, hca⟩ := no_dominator u c hcu
    exact hca (f.map_adj_iff.1 (hvw (f a) (hadj a ha) (hlt a ha)))

open UnionNoClass in
open Classical in
theorem intro_union_in_no_class_v170_proved {n : ℕ} (T : SimpleGraph (Fin n)) (hT : T.IsTree)
    (hgT : grundyNumber T = 4) :
    let X := (completeBipartiteGraph (Fin 2) (Fin 7) ⊕g subdivision (⊤ : SimpleGraph (Fin 5))) ⊕g T
    ((completeBipartiteGraph (Fin 2) (Fin 7)).maxDegree = 7 ∧
      (2 * (completeBipartiteGraph (Fin 2) (Fin 7)).edgeFinset.card : ℝ) / 9 = 28 / 9 ∧
      4 ≤ treewidth (subdivision (⊤ : SimpleGraph (Fin 5)))) ∧
    (X.IsBipartite ∧ IsDegenerate X 2 ∧ 2 < treewidth X ∧ 3 < X.maxDegree ∧ ¬ IsSemiFalse X ∧
      3 < grundyNumber X ∧ 3 < mad X) ∧
    ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W), G.IsBipartite → IsDegenerate G 2 →
      (X ⊕g G).IsBipartite ∧ IsDegenerate (X ⊕g G) 2 ∧ 2 < treewidth (X ⊕g G) ∧ 3 < (X ⊕g G).maxDegree ∧
        ¬ IsSemiFalse (X ⊕g G) ∧ 3 < grundyNumber (X ⊕g G) ∧ 3 < mad (X ⊕g G) := by
  intro X
  have H := intro_union_in_no_class_proved T hT hgT
  have eK : completeBipartiteGraph (Fin 2) (Fin 7) ↪g X :=
    SimpleGraph.Embedding.sumInl.trans SimpleGraph.Embedding.sumInl
  obtain ⟨eS, hS⟩ : ∃ eS : subdivision (⊤ : SimpleGraph (Fin 5)) ↪g X, Closed eS :=
    ⟨SimpleGraph.Embedding.sumInr.trans SimpleGraph.Embedding.sumInl, closed_sumInl _ closed_sumInr⟩
  have hbip : X.IsBipartite :=
    SimpleGraph.colorable_sum.2 ⟨SimpleGraph.colorable_sum.2 ⟨Classes.K2m_isBipartite,
      Subdivision.isBipartite _⟩, hT.isBipartite⟩
  have hdeg : IsDegenerate X 2 :=
    isDegenerate_sum (isDegenerate_sum (Examples.K2m_isDegenerate 7) (Subdivision.isDegenerate _))
      (Examples.isDegenerate_mono T (by norm_num) (Examples.tree_isDegenerate hT))
  have hgr : 4 ≤ grundyNumber X := hgT ▸ grundy_le_sum_right
  have P := props X eK eS hbip hdeg hgr
  refine ⟨⟨H.1.1, H.1.2.1, H.1.2.2.1⟩,
    ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.1, intro_K5sub_component_not_semiFalse_proved X eS hS, P.2.2.2.2.2⟩, ?_⟩
  intro W _ _ G hG hGd
  have P' := props (X ⊕g G) (eK.trans SimpleGraph.Embedding.sumInl) (eS.trans SimpleGraph.Embedding.sumInl)
    (SimpleGraph.colorable_sum.2 ⟨hbip, hG⟩) (isDegenerate_sum hdeg hGd) (hgr.trans grundy_le_sum_left)
  exact ⟨P'.1, P'.2.1, P'.2.2.1, P'.2.2.2.1,
    intro_K5sub_component_not_semiFalse_proved (X ⊕g G) (eS.trans SimpleGraph.Embedding.sumInl)
      (closed_sumInl eS hS), P'.2.2.2.2.2⟩

end SemiFalse

end Cereceda
