/-
LeeDiam/Sec1/Main.lean — the main results of Section 1 assembled; the Z^2 picture; between 2 and w(P).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Vertices
import LeeDiam.Defs.Walks
import LeeDiam.Defs.Band
import LeeDiam.Defs.Pn
import LeeDiam.Cited.Lee26
import LeeDiam.Sec1.VertexFinite
import LeeDiam.Sec1.Z2
import LeeDiam.Sec1.Bounds
import LeeDiam.Sec2.Walks
import LeeDiam.Sec3.Band
import LeeDiam.Sec4.Chain
import LeeDiam.Sec5.Upper
import LeeDiam.Sec6.Structure
import LeeDiam.Sec6.Order
import LeeDiam.Sec6.Chain

namespace LeeDiam

open Finset

/-! ### The band: its size and its two diameters as numbers -/

theorem S1.band_card (k : ℕ) : Fintype.card (Band k) = 3 * k := by
  show Fintype.card (Fin k × Fin 3) = 3 * k
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]

/-- `diam C(B_k)` is a natural number `d` with `4 d ≤ 3 (k + 1)` (Theorem 4.1). -/
theorem S1.band_chain_nat (k : ℕ) (hk : 1 ≤ k) : ∃ d : ℕ, chainDiam (Band k) = d ∧ 4 * d ≤ 3 * (k + 1) := by
  have h := thm_4_1_proved k hk
  have hne : chainDiam (Band k) ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) h
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.1 hne
  refine ⟨d, hd.symm, ?_⟩
  rw [← hd] at h
  have hdm : d ≤ 3 * (k + 1) / 4 := ENat.natCast_le_natCast.1 h
  omega

/-- Theorem 1.3 (consequence): `⌈(k - 3)/4⌉ ≤ diam O(B_k) - diam C(B_k)`. -/
theorem S1.band_gap (k : ℕ) (hk : 1 ≤ k) : ∃ dO dC : ℕ, orderDiam (Band k) = dO ∧ chainDiam (Band k) = dC ∧
    ⌈((k : ℝ) - 3) / 4⌉ ≤ (dO : ℤ) - dC := by
  obtain ⟨d, hd, h4⟩ := S1.band_chain_nat k hk
  refine ⟨k, d, thm_3_3_proved k hk, hd, ?_⟩
  rw [Int.ceil_le]
  have h4' : (4 * d : ℝ) ≤ 3 * (k + 1) := by exact_mod_cast h4
  push_cast
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  linarith

theorem sec1_between_two_and_width_proved (P : Type) [Fintype P] [PartialOrder P] (_hP : IsConnPoset P)
    (hnc : ¬ IsChain (· ≤ ·) (Set.univ : Set P)) :
    2 ≤ orderDiam P ∧ orderDiam P ≤ width P ∧ 2 ≤ chainDiam P ∧ chainDiam P ≤ width P ∧
      orderDiam P ≤ chainDiam P + (width P - 2 : ℕ) ∧ chainDiam P ≤ orderDiam P + (width P - 2 : ℕ) := by
  obtain ⟨p, q, hpq, hqp⟩ : ∃ p q : P, ¬ p ≤ q ∧ ¬ q ≤ p := by
    by_contra hcon
    push Not at hcon
    refine hnc fun x _ y _ _ => ?_
    by_cases hxy : x ≤ y
    · exact Or.inl hxy
    · exact Or.inr (hcon x y hxy)
  have h2O := S1.two_le_orderDiam hpq hqp
  have h2C := S1.two_le_chainDiam hpq hqp
  have hOw := (prop_2_3_proved P).2.2.2.1
  have hCw := (prop_2_3_proved P).2.2.2.2
  have hw2 : 2 ≤ width P := by exact_mod_cast h2O.trans hOw
  have hw : ((width P : ℕ) : ℕ∞) = 2 + ((width P - 2 : ℕ) : ℕ∞) := by
    norm_cast
    omega
  refine ⟨h2O, hOw, h2C, hCw, ?_, ?_⟩
  · calc orderDiam P ≤ width P := hOw
      _ = 2 + ((width P - 2 : ℕ) : ℕ∞) := hw
      _ ≤ chainDiam P + (width P - 2 : ℕ) := add_le_add h2C le_rfl
  · calc chainDiam P ≤ width P := hCw
      _ = 2 + ((width P - 2 : ℕ) : ℕ∞) := hw
      _ ≤ orderDiam P + (width P - 2 : ℕ) := add_le_add h2O le_rfl

theorem lee_conjecture_fails_proved :
    ¬ LeeConjecture ∧
    (∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (dO dC : ℕ),
      IsConnPoset P ∧ orderDiam P = dO ∧ chainDiam P = dC ∧ dC + 1 < dO) ∧
    (∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (dO dC : ℕ),
      IsConnPoset P ∧ orderDiam P = dO ∧ chainDiam P = dC ∧ dO + 1 < dC) := by
  obtain ⟨d, hd, h4⟩ := S1.band_chain_nat 8 (by norm_num)
  have hB8 : orderDiam (Band 8) = ((8 : ℕ) : ℕ∞) := thm_3_3_proved 8 (by norm_num)
  have hcB := (lem_3_1_consequences_proved 8).2.2.1 (by norm_num)
  refine ⟨fun hLee => ?_, ⟨Band 8, inferInstance, inferInstance, 8, d, hcB, hB8, hd, by omega⟩,
    ⟨Pn 4, inferInstance, inferInstance, 2, 4, lem_6_2_v_proved 4,
      by simpa using thm_6_7_proved 4 (by norm_num), by simpa using (thm_6_13_proved 4 le_rfl).2, by norm_num⟩⟩
  have h := (hLee (Band 8) hcB).1
  rw [hB8, hd] at h
  have h8 : 8 ≤ d + 1 := by exact_mod_cast h
  omega

theorem band_Z2_picture_proved (k : ℕ) :
    ∃ f : Band k ↪o ℤ × ℤ, ∀ i : Fin k,
      f (Band.a i) = ((i : ℤ) + 1, -((i : ℤ) + 1)) ∧ f (Band.b i) = ((i : ℤ) + 1, -(i : ℤ)) ∧
      f (Band.c i) = ((i : ℤ) + 2, -(i : ℤ)) ∧
      (f (Band.a i)).1 + (f (Band.a i)).2 = 0 ∧ (f (Band.b i)).1 + (f (Band.b i)).2 = 1 ∧
      (f (Band.c i)).1 + (f (Band.c i)).2 = 2 ∧
      ((f (Band.a i)).1 - (f (Band.a i)).2, (f (Band.a i)).1 + (f (Band.a i)).2) = (2 * ((i : ℤ) + 1), 0) ∧
      ((f (Band.b i)).1 - (f (Band.b i)).2, (f (Band.b i)).1 + (f (Band.b i)).2) = (2 * ((i : ℤ) + 1) - 1, 1) ∧
      ((f (Band.c i)).1 - (f (Band.c i)).2, (f (Band.c i)).1 + (f (Band.c i)).2) = (2 * ((i : ℤ) + 1), 2) := by
  obtain ⟨f, hf⟩ := S1.band_Z2 k
  refine ⟨f, fun i => ?_⟩
  obtain ⟨ha, hb, hc, hsa, hsb, hsc⟩ := hf i
  refine ⟨ha, hb, hc, hsa, hsb, hsc, ?_, ?_, ?_⟩
  · rw [ha]
    exact Prod.ext (by dsimp only; ring) (by dsimp only; ring)
  · rw [hb]
    exact Prod.ext (by dsimp only; ring) (by dsimp only; ring)
  · rw [hc]
    exact Prod.ext (by dsimp only; ring) (by dsimp only; ring)

theorem sec1_vertices_finite_proved (P : Type) [Fintype P] [PartialOrder P] :
    Finite {v : P → ℝ // HibiLi.IsFace (orderPolytope P) {v}} ∧
      Finite {v : P → ℝ // HibiLi.IsFace (chainPolytope P) {v}} := by
  exact polytope_vertices_finite P

theorem thm_1_3_proved (k : ℕ) (hk : 1 ≤ k) :
    IsConnPoset (Band k) ∧ Fintype.card (Band k) = 3 * k ∧ orderDiam (Band k) = k ∧
      chainDiam (Band k) ≤ ((3 * (k + 1) / 4 : ℕ) : ℕ∞) :=
  ⟨(lem_3_1_consequences_proved k).2.2.1 hk, S1.band_card k, thm_3_3_proved k hk, thm_4_1_proved k hk⟩

theorem thm_1_3_consequence_proved :
    (∀ k : ℕ, 1 ≤ k → ∃ dO dC : ℕ, orderDiam (Band k) = dO ∧ chainDiam (Band k) = dC ∧
      ⌈((k : ℝ) - 3) / 4⌉ ≤ (dO : ℤ) - dC) ∧
    (∀ M : ℕ, ∃ k, 1 ≤ k ∧ IsConnPoset (Band k) ∧
      ∃ dO dC : ℕ, orderDiam (Band k) = dO ∧ chainDiam (Band k) = dC ∧ dC + M ≤ dO) ∧
    (Fintype.card (Band 8) = 24 ∧ IsConnPoset (Band 8) ∧
      ∃ dO dC : ℕ, orderDiam (Band 8) = dO ∧ chainDiam (Band 8) = dC ∧ dC + 2 ≤ dO) := by
  refine ⟨S1.band_gap, fun M => ?_, ?_⟩
  · obtain ⟨d, hd, h4⟩ := S1.band_chain_nat (4 * M + 3) (by omega)
    exact ⟨4 * M + 3, by omega, (lem_3_1_consequences_proved _).2.2.1 (by omega), 4 * M + 3, d,
      thm_3_3_proved _ (by omega), hd, by omega⟩
  · obtain ⟨d, hd, h4⟩ := S1.band_chain_nat 8 (by norm_num)
    exact ⟨(S1.band_card 8).trans (by norm_num), (lem_3_1_consequences_proved 8).2.2.1 (by norm_num), 8, d,
      thm_3_3_proved 8 (by norm_num), hd, by omega⟩

theorem sec1_no_constant_proved :
    ∀ C : ℕ, ∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (dO dC : ℕ),
      IsConnPoset P ∧ orderDiam P = dO ∧ chainDiam P = dC ∧ dC + C < dO := by
  intro C
  obtain ⟨k, -, hconn, dO, dC, hO, hC, hle⟩ := thm_1_3_consequence_proved.2.1 (C + 1)
  exact ⟨Band k, inferInstance, inferInstance, dO, dC, hconn, hO, hC, by omega⟩

theorem thm_1_4_proved :
    (∀ n : ℕ, 4 ≤ n → IsConnPoset (Pn n) ∧ Fintype.card (Pn n) = 2 * n ^ 2 + 5 * n + 1 ∧
      orderDiam (Pn n) = 2 ∧ chainDiam (Pn n) = 4) ∧
    Fintype.card (Pn 4) = 53 ∧ chainDiam (Pn 4) = orderDiam (Pn 4) + 2 := by
  refine ⟨fun n hn => ⟨lem_6_2_v_proved n, def_6_1_count_proved n, thm_6_7_proved n (by omega),
    (thm_6_13_proved n hn).2⟩, (def_6_1_count_proved 4).trans (by norm_num), ?_⟩
  rw [thm_6_7_proved 4 (by norm_num), (thm_6_13_proved 4 le_rfl).2]
  norm_num

theorem sec1_linear_width_proved :
    ∀ k : ℕ, 1 ≤ k → width (Band k) = k ∧ ∃ dO dC : ℕ, orderDiam (Band k) = dO ∧ chainDiam (Band k) = dC ∧
      ⌈((k : ℝ) - 3) / 4⌉ ≤ (dO : ℤ) - dC :=
  fun k hk => ⟨(lem_3_1_consequences_proved k).2.2.2, S1.band_gap k hk⟩

theorem sec1_largest_difference_proved :
    (∀ (P : Type) [Fintype P] [PartialOrder P], orderDiam P = 2 → chainDiam P ≤ orderDiam P + 2) ∧
    ∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P), IsConnPoset P ∧ orderDiam P = 2 ∧ chainDiam P = orderDiam P + 2 := by
  refine ⟨fun P _ _ h => ?_, ⟨Pn 4, inferInstance, inferInstance, lem_6_2_v_proved 4,
    thm_6_7_proved 4 (by norm_num), ?_⟩⟩
  · rw [h]
    exact (thm_1_5_proved P h.le).trans (by norm_num)
  · rw [thm_6_7_proved 4 (by norm_num), (thm_6_13_proved 4 le_rfl).2]
    norm_num

end LeeDiam
