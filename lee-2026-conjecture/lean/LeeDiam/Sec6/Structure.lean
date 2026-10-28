/-
LeeDiam/Sec6/Structure.lean — Section 6.1 of paper 004 (short v1.50, sec_reverse.tex l. 33-106): the poset P_n, its
size, its level function, its partition, the involution σ, the antichains A, B, U, M_A, M_B, Lemma 6.2, and Z_A, Z_B.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Vertices
import LeeDiam.Defs.Walks
import LeeDiam.Defs.Pn
import LeeDiam.Defs.PnSets
import LeeDiam.Sec4.BandOrder
import LeeDiam.Bridge.Graphs
import LeeDiam.Sec6.PnOrder
import LeeDiam.Sec6.Sets


namespace LeeDiam

open PnSets PnOrder

namespace S6

variable {n : ℕ}

/-- `P_n` as a sum of its ten kinds of elements. -/
def toSum : PnElem n → Fin n ⊕ Fin n ⊕ Pair n ⊕ Pair n ⊕ Fin n ⊕ Fin n ⊕ Unit ⊕ Fin n ⊕ Fin n ⊕ (Fin n × Fin n)
  | .a i => .inl i
  | .b j => .inr (.inl j)
  | .m E => .inr (.inr (.inl E))
  | .m' E => .inr (.inr (.inr (.inl E)))
  | .y i => .inr (.inr (.inr (.inr (.inl i))))
  | .y' j => .inr (.inr (.inr (.inr (.inr (.inl j)))))
  | .h => .inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))
  | .w i => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))
  | .w' j => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl j))))))))
  | .t i j => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (i, j)))))))))

def ofSum : Fin n ⊕ Fin n ⊕ Pair n ⊕ Pair n ⊕ Fin n ⊕ Fin n ⊕ Unit ⊕ Fin n ⊕ Fin n ⊕ (Fin n × Fin n) → PnElem n
  | .inl i => .a i
  | .inr (.inl j) => .b j
  | .inr (.inr (.inl E)) => .m E
  | .inr (.inr (.inr (.inl E))) => .m' E
  | .inr (.inr (.inr (.inr (.inl i)))) => .y i
  | .inr (.inr (.inr (.inr (.inr (.inl j))))) => .y' j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))) => .h
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))) => .w i
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl j)))))))) => .w' j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (i, j))))))))) => .t i j

def equivSum : PnElem n ≃ Fin n ⊕ Fin n ⊕ Pair n ⊕ Pair n ⊕ Fin n ⊕ Fin n ⊕ Unit ⊕ Fin n ⊕ Fin n ⊕ (Fin n × Fin n) where
  toFun := toSum
  invFun := ofSum
  left_inv x := by cases x <;> rfl
  right_inv s := by rcases s with i | j | E | E | i | j | u | i | j | ⟨i, j⟩ <;> rfl

theorem sigma_sigma (x : Pn n) : sigma n (sigma n x) = x := by cases x <;> rfl

theorem sigma_injective : Function.Injective (sigma n) :=
  Function.LeftInverse.injective (g := sigma n) sigma_sigma

theorem rel_sigma {x z : Pn n} (hr : PnElem.Rel x z) : PnElem.Rel (sigma n x) (sigma n z) := by
  cases hr <;> simp only [sigma] <;> constructor <;> assumption

theorem le_sigma {x z : Pn n} (hle : x ≤ z) : sigma n x ≤ sigma n z :=
  Relation.ReflTransGen.lift (sigma n) (fun _ _ hr => rel_sigma hr) _ _ hle

theorem le_sigma_iff {x z : Pn n} : x ≤ z ↔ sigma n x ≤ sigma n z := by
  refine ⟨le_sigma, fun hle => ?_⟩
  have h2 := le_sigma hle
  rwa [sigma_sigma, sigma_sigma] at h2

theorem lt_sigma_iff {x z : Pn n} : x < z ↔ sigma n x < sigma n z := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, ← le_sigma_iff, sigma_injective.ne_iff]

theorem comp_sigma_iff (x z : Pn n) : Comp (sigma n x) (sigma n z) ↔ Comp x z := by
  unfold Comp
  rw [← lt_sigma_iff, ← lt_sigma_iff]

theorem sigma_image_sigma (S : Set (Pn n)) : sigma n '' (sigma n '' S) = S := by
  rw [Set.image_image]
  simp [sigma_sigma]

theorem isIdeal_sigma {I : Set (Pn n)} (hI : IsIdeal I) : IsIdeal (sigma n '' I) := by
  rintro x z hzx ⟨u, hu, rfl⟩
  refine ⟨sigma n z, hI ?_ hu, sigma_sigma z⟩
  have h2 := le_sigma hzx
  rwa [sigma_sigma] at h2

theorem isAntichainSet_sigma {X : Set (Pn n)} (hX : IsAntichainSet X) : IsAntichainSet (sigma n '' X) :=
  (S4.isAntichainSet_image_iff (sigma n) comp_sigma_iff X).2 hX

/-- `σ` induces an automorphism of the graph of ideals. -/
def idealAut : idealGraph (Pn n) ≃g idealGraph (Pn n) where
  toFun I := ⟨sigma n '' I.1, isIdeal_sigma I.2⟩
  invFun I := ⟨sigma n '' I.1, isIdeal_sigma I.2⟩
  left_inv I := Subtype.ext (sigma_image_sigma I.1)
  right_inv I := Subtype.ext (sigma_image_sigma I.1)
  map_rel_iff' := by
    intro I J
    show ((sigma n '' I.1 ⊆ sigma n '' J.1 ∧ IsConnSet (sigma n '' J.1 \ sigma n '' I.1)) ∨
        (sigma n '' J.1 ⊆ sigma n '' I.1 ∧ IsConnSet (sigma n '' I.1 \ sigma n '' J.1))) ↔
        ((I.1 ⊆ J.1 ∧ IsConnSet (J.1 \ I.1)) ∨ (J.1 ⊆ I.1 ∧ IsConnSet (I.1 \ J.1)))
    rw [Set.image_subset_image_iff sigma_injective, Set.image_subset_image_iff sigma_injective,
      ← Set.image_sdiff sigma_injective, ← Set.image_sdiff sigma_injective,
      S4.isConnSet_image_iff (sigma n) sigma_injective comp_sigma_iff,
      S4.isConnSet_image_iff (sigma n) sigma_injective comp_sigma_iff]

/-- `σ` induces an automorphism of the graph of antichains. -/
def antichainAut : antichainGraph (Pn n) ≃g antichainGraph (Pn n) where
  toFun X := ⟨sigma n '' X.1, isAntichainSet_sigma X.2⟩
  invFun X := ⟨sigma n '' X.1, isAntichainSet_sigma X.2⟩
  left_inv X := Subtype.ext (sigma_image_sigma X.1)
  right_inv X := Subtype.ext (sigma_image_sigma X.1)
  map_rel_iff' := by
    intro X Y
    show IsConnSet (symmDiff (sigma n '' X.1) (sigma n '' Y.1)) ↔ IsConnSet (symmDiff X.1 Y.1)
    rw [← Set.image_symmDiff sigma_injective, S4.isConnSet_image_iff (sigma n) sigma_injective comp_sigma_iff]

end S6

theorem def_6_1_count_proved (n : ℕ) : Fintype.card (Pn n) = 2 * n ^ 2 + 5 * n + 1 := by
  rw [Fintype.card_congr S6.equivSum]
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, Fintype.card_prod, Fintype.card_finset_len]
  have hC := Nat.mul_div_cancel' (even_iff_two_dvd.1 (Nat.even_mul_pred_self n))
  rw [← Nat.choose_two_right] at hC
  rcases n with _ | k
  · simp
  · simp only [Nat.add_sub_cancel] at hC
    nlinarith [hC]

theorem def_6_1_rank_proved (n : ℕ) :
    ∀ x z : Pn n, PnElem.Rel x z → PnElem.level z = PnElem.level x + 1 := by
  intro x z hr
  cases hr <;> rfl

theorem def_6_1_partition_proved (n : ℕ) :
    lamA n ∪ lamB n ∪ {PnElem.h} ∪ ups n ∪ tops n = Set.univ ∧ Disjoint (lamA n) (lamB n) ∧
      Disjoint (lamA n ∪ lamB n) {PnElem.h} ∧ Disjoint (lamA n ∪ lamB n ∪ {PnElem.h}) (ups n) ∧
      Disjoint (lamA n ∪ lamB n ∪ {PnElem.h} ∪ ups n) (tops n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext x
    cases x <;> simp [lamA, lamB, ups, tops, pairMinA, pairMinB, lowA, lowB, tgtA, tgtB, upA, upB, -Subtype.exists]
  all_goals
    rw [Set.disjoint_left]
    intro x hx hx'
    cases x <;> simp [lamA, lamB, ups, tops, pairMinA, pairMinB, lowA, lowB, tgtA, tgtB, upA, upB] at hx hx'

-- sec6_sigma_proved is in Sec6/SigmaGraph.lean (its graph automorphisms come from the coordinate permutation `x ↦ x ∘ σ`).

theorem sec6_antichains_proved (n : ℕ) :
    IsAntichainSet (tgtA n) ∧ IsAntichainSet (tgtB n) ∧ IsAntichainSet (tgts n) ∧ IsAntichainSet (pairMinA n) ∧
      IsAntichainSet (pairMinB n) := by
  refine ⟨isAntichainSet_of_level _ 2 ?_, isAntichainSet_of_level _ 2 ?_, isAntichainSet_of_level _ 2 ?_,
    isAntichainSet_of_level _ 0 ?_, isAntichainSet_of_level _ 0 ?_⟩
  · rintro x ⟨i, rfl⟩; rfl
  · rintro x ⟨i, rfl⟩; rfl
  · rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> rfl
  · rintro x ⟨E, rfl⟩; rfl
  · rintro x ⟨E, rfl⟩; rfl

theorem lem_6_2_i_proved (n : ℕ) (i : Fin n) :
    (∀ x : Pn n, x < PnElem.a i ↔ x = PnElem.y i ∨ ∃ E : Pair n, i ∈ E.1 ∧ x = PnElem.m E) ∧
    (∀ x : Pn n, x < PnElem.a i → x ≤ PnElem.y i) ∧
    (∀ x : Pn n, PnElem.a i < x ↔ x = PnElem.w i ∨ ∃ j, x = PnElem.t i j) ∧
    (∀ x : Pn n, PnElem.a i < x → PnElem.w i ≤ x) ∧
    (∀ x : Pn n, x < PnElem.b i ↔ x = PnElem.y' i ∨ ∃ E : Pair n, i ∈ E.1 ∧ x = PnElem.m' E) ∧
    (∀ x : Pn n, x < PnElem.b i → x ≤ PnElem.y' i) ∧
    (∀ x : Pn n, PnElem.b i < x ↔ x = PnElem.w' i ∨ ∃ j, x = PnElem.t j i) ∧
    (∀ x : Pn n, PnElem.b i < x → PnElem.w' i ≤ x) := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun x => ?_, fun x hx => ?_, fun x => ?_, fun x hx => ?_, fun x => ?_,
    fun x hx => ?_⟩
  all_goals (try rw [lt_iff_ple] at hx)
  all_goals (try rw [le_iff_ple])
  all_goals (try rw [lt_iff_ple])
  all_goals cases x <;> simp_all [ple, eq_comm]

theorem lem_6_2_ii_proved (n : ℕ) :
    {x : Pn n | x ≤ PnElem.h} = qSet n ∪ {PnElem.h} ∧ {x : Pn n | PnElem.h ≤ x} = {PnElem.h} ∪ ups n ∪ tops n ∧
    (∀ x : Pn n, x ∉ tgts n ∪ {PnElem.h} → Comp x PnElem.h) ∧ (∀ u ∈ tgts n, ¬ Comp u (PnElem.h : Pn n)) ∧
    (∀ q ∈ qSet n, ∀ z ∈ ups n ∪ tops n, q < z) := by
  refine ⟨?_, ?_, fun x hx => ?_, ?_, ?_⟩
  · ext x
    cases x <;> simp [le_iff_ple, ple, qSet, pairMinA, pairMinB, lowA, lowB, -Subtype.exists]
  · ext x
    cases x <;> simp [le_iff_ple, ple, ups, tops, upA, upB]
  · rw [comp_iff_ple]
    cases x <;> simp [ple, tgts, tgtA, tgtB] at hx ⊢
  · rintro u (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> simp [comp_iff_ple, ple]
  · rintro q (((⟨E, rfl⟩ | ⟨E, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) z ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, l, rfl⟩) <;>
      simp [lt_iff_ple, ple]

theorem lem_6_2_iii_proved (n : ℕ) : ∀ x ∈ lamA n, ∀ z ∈ lamB n, ¬ Comp x z := by
  rintro x ((⟨E, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) z ((⟨F, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) <;> simp [comp_iff_ple, ple]

theorem lem_6_2_iv_proved (n : ℕ) :
    (∀ z ∈ upA n ∪ tops n, ∃! i : Fin n, PnElem.a i < z) ∧ (∀ i, (PnElem.a i : Pn n) < PnElem.w i) ∧
    (∀ i j, (PnElem.a i : Pn n) < PnElem.t i j) ∧ (∀ z ∈ upA n, ∀ j : Fin n, ¬ (PnElem.b j : Pn n) < z) ∧
    (∀ z ∈ upB n ∪ tops n, ∃! j : Fin n, PnElem.b j < z) ∧ (∀ j, (PnElem.b j : Pn n) < PnElem.w' j) ∧
    (∀ i j, (PnElem.b j : Pn n) < PnElem.t i j) ∧ (∀ z ∈ upB n, ∀ i : Fin n, ¬ (PnElem.a i : Pn n) < z) ∧
    IsAntichainSet (ups n) ∧ IsAntichainSet (tops n) := by
  refine ⟨?_, fun i => ?_, fun i j => ?_, ?_, ?_, fun j => ?_, fun i j => ?_, ?_, isAntichainSet_of_level _ 3 ?_,
    isAntichainSet_of_level _ 4 ?_⟩
  · rintro z (⟨k, rfl⟩ | ⟨k, l, rfl⟩) <;> exact ⟨k, by simp [lt_iff_ple, ple], fun j hj => by simpa [lt_iff_ple, ple] using hj⟩
  · simp [lt_iff_ple, ple]
  · simp [lt_iff_ple, ple]
  · rintro z ⟨k, rfl⟩ j
    simp [lt_iff_ple, ple]
  · rintro z (⟨k, rfl⟩ | ⟨k, l, rfl⟩)
    · exact ⟨k, by simp [lt_iff_ple, ple], fun j hj => by simpa [lt_iff_ple, ple] using hj⟩
    · exact ⟨l, by simp [lt_iff_ple, ple], fun j hj => by simpa [lt_iff_ple, ple] using hj⟩
  · simp [lt_iff_ple, ple]
  · simp [lt_iff_ple, ple]
  · rintro z ⟨k, rfl⟩ i
    simp [lt_iff_ple, ple]
  · rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> rfl
  · rintro x ⟨i, j, rfl⟩; rfl

theorem lem_6_2_v_proved (n : ℕ) : IsConnPoset (Pn n) := by
  unfold IsConnPoset
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨PnElem.h, fun x => ?_⟩
  have adj : ∀ u v : Pn n, Comp u v → (compGraph (Pn n)).Reachable u v :=
    fun u v huv => SimpleGraph.Adj.reachable (G := compGraph (Pn n)) huv
  cases x with
  | a i => exact (adj _ (PnElem.y i) (by simp [comp_iff_ple, ple])).trans (adj _ _ (by simp [comp_iff_ple, ple]))
  | b j => exact (adj _ (PnElem.y' j) (by simp [comp_iff_ple, ple])).trans (adj _ _ (by simp [comp_iff_ple, ple]))
  | h => exact SimpleGraph.Reachable.refl _
  | _ => exact adj _ _ (by simp [comp_iff_ple, ple])

theorem sec6_ZA_proved (n : ℕ) :
    {x : Pn n | ∃ u ∈ tgtA n, x ≤ u} = lamA n ∧ {x : Pn n | ∃ u ∈ tgtA n, u ≤ x} = tgtA n ∪ upA n ∪ tops n ∧
    zA n = lamB n ∪ {PnElem.h} ∪ upB n ∧ zB n = lamA n ∪ {PnElem.h} ∪ upA n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨u, ⟨i, rfl⟩, hle⟩
      rw [le_iff_ple] at hle
      cases x <;> simp [ple] at hle <;> simp [lamA, pairMinA, lowA, tgtA, -Subtype.exists]
    · rintro ((⟨E, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
      · obtain ⟨i, hi⟩ := pair_nonempty E
        exact ⟨PnElem.a i, ⟨i, rfl⟩, by simpa [le_iff_ple, ple] using hi⟩
      · exact ⟨PnElem.a i, ⟨i, rfl⟩, by simp [le_iff_ple, ple]⟩
      · exact ⟨PnElem.a i, ⟨i, rfl⟩, le_rfl⟩
  · ext x
    constructor
    · rintro ⟨u, ⟨i, rfl⟩, hle⟩
      rw [le_iff_ple] at hle
      cases x <;> simp [ple] at hle <;> simp [tgtA, upA, tops]
    · rintro ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, j, rfl⟩)
      · exact ⟨PnElem.a i, ⟨i, rfl⟩, le_rfl⟩
      · exact ⟨PnElem.a i, ⟨i, rfl⟩, by simp [le_iff_ple, ple]⟩
      · exact ⟨PnElem.a i, ⟨i, rfl⟩, by simp [le_iff_ple, ple]⟩
  · ext x
    constructor
    · rintro ⟨hxA, hx⟩
      cases x with
      | a i => exact absurd ⟨i, rfl⟩ hxA
      | m E =>
        obtain ⟨i, hi⟩ := pair_nonempty E
        exact absurd (by simpa [comp_iff_ple, ple] using hi) (hx (PnElem.a i) ⟨i, rfl⟩)
      | y i => exact absurd (by simp [comp_iff_ple, ple]) (hx (PnElem.a i) ⟨i, rfl⟩)
      | w i => exact absurd (by simp [comp_iff_ple, ple]) (hx (PnElem.a i) ⟨i, rfl⟩)
      | t i j => exact absurd (by simp [comp_iff_ple, ple]) (hx (PnElem.a i) ⟨i, rfl⟩)
      | _ => simp [lamB, pairMinB, lowB, tgtB, upB, -Subtype.exists]
    · rintro ((((⟨E, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) | rfl) | ⟨j, rfl⟩) <;>
        exact ⟨fun ⟨i, hi⟩ => (by cases hi), fun u ⟨i, hu⟩ => by subst hu; simp [comp_iff_ple, ple]⟩
  · ext x
    constructor
    · rintro ⟨hxB, hx⟩
      cases x with
      | b j => exact absurd ⟨j, rfl⟩ hxB
      | m' E =>
        obtain ⟨j, hj⟩ := pair_nonempty E
        exact absurd (by simpa [comp_iff_ple, ple] using hj) (hx (PnElem.b j) ⟨j, rfl⟩)
      | y' j => exact absurd (by simp [comp_iff_ple, ple]) (hx (PnElem.b j) ⟨j, rfl⟩)
      | w' j => exact absurd (by simp [comp_iff_ple, ple]) (hx (PnElem.b j) ⟨j, rfl⟩)
      | t i j => exact absurd (by simp [comp_iff_ple, ple]) (hx (PnElem.b j) ⟨j, rfl⟩)
      | _ => simp [lamA, pairMinA, lowA, tgtA, upA, -Subtype.exists]
    · rintro ((((⟨E, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | rfl) | ⟨i, rfl⟩) <;>
        exact ⟨fun ⟨j, hj⟩ => (by cases hj), fun u ⟨j, hu⟩ => by subst hu; simp [comp_iff_ple, ple]⟩

theorem sec6_l85_proved (n : ℕ) (i : Fin n) :
    {x : Pn n | x < PnElem.y i} = {x | ∃ E : Pair n, i ∈ E.1 ∧ x = PnElem.m E} ∧
    {x : Pn n | x < PnElem.y i}.ncard = n - 1 :=
  S6.l85 n i

theorem sec6_updown_proved (n : ℕ) (i j : Fin n) :
    {x : Pn n | PnElem.y i ≤ x} = {PnElem.y i, PnElem.a i} ∪ {x | PnElem.h ≤ x} ∧
    {x : Pn n | x ≤ PnElem.w i} = {PnElem.w i, PnElem.a i, PnElem.h} ∪ qSet n ∧
    {x : Pn n | x ≤ PnElem.t i j} =
      {PnElem.t i j, PnElem.w i, PnElem.w' j, PnElem.a i, PnElem.b j, PnElem.h} ∪ qSet n :=
  S6.updown n i j

end LeeDiam
