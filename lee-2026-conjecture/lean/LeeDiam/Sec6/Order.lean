/-
LeeDiam/Sec6/Order.lean — Section 6.2 of paper 004 (short v1.50, sec_reverse.tex l. 110-189): diam O(P_n) = 2
(Lemmas 6.3, 6.4, 6.5, Proposition 6.6, Theorem 6.7).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Vertices
import LeeDiam.Defs.Walks
import LeeDiam.Defs.Pn
import LeeDiam.Defs.PnSets
import LeeDiam.Sec6.PnOrder
import LeeDiam.Sec4.Comps
import LeeDiam.Bridge.Graphs

namespace LeeDiam

open PnSets

/-! ## Helpers: targets, connectors and the hub -/

namespace S6Ord

open PnOrder

variable {n : ℕ}

theorem lo_lt {u : Pn n} (hu : u ∈ tgts n) : lo n u < u := by
  rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> simp [lo, lt_iff_ple, ple]

theorem lt_up {u : Pn n} (hu : u ∈ tgts n) : u < up n u := by
  rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> simp [up, lt_iff_ple, ple]

theorem lo_lt_h {u : Pn n} (hu : u ∈ tgts n) : lo n u < PnElem.h := by
  rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> simp [lo, lt_iff_ple, ple]

theorem h_lt_up {u : Pn n} (hu : u ∈ tgts n) : (PnElem.h : Pn n) < up n u := by
  rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> simp [up, lt_iff_ple, ple]

theorem lo_mem_q {u : Pn n} (hu : u ∈ tgts n) : lo n u ∈ qSet n := by
  rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> simp [lo, qSet, pairMinA, pairMinB, lowA, lowB]

theorem up_mem_ups {u : Pn n} (hu : u ∈ tgts n) : up n u ∈ ups n := by
  rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> simp [up, ups, upA, upB]

theorem up_not_mem {u : Pn n} (hu : u ∈ tgts n) : up n u ∉ qSet n ∪ tgts n := by
  rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> simp [up, qSet, tgts, tgtA, tgtB, pairMinA, pairMinB, lowA, lowB]

/-- Lemma 6.2 (i): an element below a target lies below its lower connector. -/
theorem le_lo_of_lt {u x : Pn n} (hu : u ∈ tgts n) (hx : x < u) : x ≤ lo n u := by
  rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> cases x <;> simp_all [lo, lt_iff_ple, le_iff_ple, ple]

/-- Lemma 6.2 (i): an element above a target lies above its upper connector. -/
theorem up_le_of_lt {u x : Pn n} (hu : u ∈ tgts n) (hx : u < x) : up n u ≤ x := by
  rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> cases x <;> simp_all [up, lt_iff_ple, le_iff_ple, ple]

/-- Lemma 6.2 (ii): every element other than the targets and `h` is comparable to `h`. -/
theorem comp_h {x : Pn n} (hx : x ∉ tgts n) (hxh : x ≠ PnElem.h) : Comp x PnElem.h := by
  cases x <;> simp_all [Comp, tgts, tgtA, tgtB, lt_iff_ple, ple]

theorem q_le_h {x : Pn n} (hx : x ∈ qSet n) : x ≤ PnElem.h := by
  rcases hx with ((⟨E, rfl⟩ | ⟨E, rfl⟩) | ⟨i, rfl⟩) | ⟨j, rfl⟩ <;> simp [le_iff_ple, ple]

/-- An ideal that contains `h` contains `Q` (Lemma 6.4 (i)). -/
theorem q_sub {I : Set (Pn n)} (hI : IsIdeal I) (hh : (PnElem.h : Pn n) ∈ I) : qSet n ⊆ I :=
  fun _ hx => hI (q_le_h hx) hh

theorem h_le_of_not_mem {x : Pn n} (hx : x ∉ qSet n ∪ tgts n) : (PnElem.h : Pn n) ≤ x := by
  cases x <;> simp_all [qSet, tgts, tgtA, tgtB, pairMinA, pairMinB, lowA, lowB, le_iff_ple, ple, -Subtype.exists]

/-- An ideal without `h` lies in `Q ∪ U` (Lemma 6.4 (i)). -/
theorem sub_q_tgts {J : Set (Pn n)} (hJ : IsIdeal J) (hh : (PnElem.h : Pn n) ∉ J) : J ⊆ qSet n ∪ tgts n := by
  intro x hx
  by_contra hxq
  exact hh (hJ (h_le_of_not_mem hxq) hx)

/-- Lemma 6.2 (iii): no element of `Λ_A` is comparable to an element of `Λ_B`. -/
theorem lam_no_comp {x z : Pn n} (hx : x ∈ lamA n) (hz : z ∈ lamB n) : ¬ Comp x z := by
  rcases hx with ((⟨E, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) <;> rcases hz with ((⟨F, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) <;>
    simp [Comp, lt_iff_ple, ple]

theorem q_tgts_sub_lam : qSet n ∪ tgts n ⊆ lamA n ∪ lamB n := by
  rintro x ((((⟨E, rfl⟩ | ⟨E, rfl⟩) | ⟨i, rfl⟩) | ⟨j, rfl⟩) | (⟨i, rfl⟩ | ⟨j, rfl⟩)) <;>
    simp [lamA, lamB, pairMinA, pairMinB, lowA, lowB, tgtA, tgtB, -Subtype.exists]

theorem w_lt_t (i j : Fin n) : (PnElem.w i : Pn n) < PnElem.t i j := by simp [lt_iff_ple, ple]

theorem w'_lt_t (i j : Fin n) : (PnElem.w' j : Pn n) < PnElem.t i j := by simp [lt_iff_ple, ple]

theorem up_not_mem_I {I J : Set (Pn n)} (hI : IsIdeal I) {u : Pn n} (hu : u ∈ tgts n)
    (h : u ∈ isoSet n I J ∨ u ∈ J \ I) : up n u ∉ I := by
  rcases h with h | h
  · exact h.2.2.2.2
  · exact fun hup => h.2 (hI (lt_up hu).le hup)

/-- **The connectivity lemma** behind Lemmas 6.3, 6.5 (iii) and Prop. 6.6: `I \ K` is connected if `h ∈ I \ K`, `Q ⊆ I`,
`K ⊆ Q ∪ U`, and every target `x ∈ I \ K` has `x^- ∉ K` or `x^+ ∈ I`. Every element of `I \ K` reaches `h`: directly if it
is not a target (Lemma 6.2 (ii)), and through `x^-` or `x^+` if it is. -/
theorem conn_diff {I K : Set (Pn n)} (hhI : (PnElem.h : Pn n) ∈ I) (hhK : (PnElem.h : Pn n) ∉ K)
    (hQ : qSet n ⊆ I) (hK : K ⊆ qSet n ∪ tgts n)
    (htgt : ∀ x ∈ tgts n, x ∈ I → x ∉ K → lo n x ∉ K ∨ up n x ∈ I) : IsConnSet (I \ K) := by
  refine S4.isConnSet_of_rtg (x0 := PnElem.h) ⟨hhI, hhK⟩ fun y hy => ?_
  by_cases hyT : y ∈ tgts n
  · rcases htgt y hyT hy.1 hy.2 with hlo | hup
    · have hc : lo n y ∈ I \ K := ⟨hQ (lo_mem_q hyT), hlo⟩
      exact (Relation.ReflTransGen.single ⟨⟨hhI, hhK⟩, hc, Or.inr (lo_lt_h hyT)⟩).tail
        ⟨hc, hy, Or.inl (lo_lt hyT)⟩
    · have hc : up n y ∈ I \ K := ⟨hup, fun hk => up_not_mem hyT (hK hk)⟩
      exact (Relation.ReflTransGen.single ⟨⟨hhI, hhK⟩, hc, Or.inl (h_lt_up hyT)⟩).tail
        ⟨hc, hy, Or.inr (lt_up hyT)⟩
  · by_cases hyh : y = PnElem.h
    · subst hyh
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨⟨hhI, hhK⟩, hy, S4.comp_symm (comp_h hyT hyh)⟩

/-- Lemma 6.4 (ii) for one side: the elements of `J` among the targets `tg k` and lower connectors `lw k` of one side lie
in one component of `J` (two of them share a pair minimum `pm E` below both), and that component stays in `Λ`. -/
theorem side_comp {J : Set (Pn n)} (hJ : IsIdeal J) (tg lw : Fin n → Pn n) (pm : Pair n → Pn n)
    (Λ Λ' : Set (Pn n)) (hlt : ∀ k, lw k < tg k) (hpm : ∀ (E : Pair n) k, k ∈ E.1 → pm E < lw k)
    (hΛ : ∀ x ∈ Λ, ∀ z ∈ Λ', ¬ Comp x z) (hsub : J ⊆ Λ ∪ Λ') (hS : ∀ k, tg k ∈ Λ ∧ lw k ∈ Λ)
    (hne : (J ∩ ({x | ∃ k, x = tg k} ∪ {x | ∃ k, x = lw k})).Nonempty) :
    ∃ K, IsComponent K J ∧ J ∩ ({x | ∃ k, x = tg k} ∪ {x | ∃ k, x = lw k}) ⊆ K ∧ K ⊆ Λ := by
  obtain ⟨z0, hz0J, hz0S⟩ := hne
  obtain ⟨K, hK, hz0K⟩ := S4.comp_exists hz0J
  have hidx : ∀ z ∈ ({x | ∃ k, x = tg k} ∪ {x | ∃ k, x = lw k} : Set (Pn n)), ∃ k, z = tg k ∨ z = lw k := by
    rintro z (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨k, Or.inl rfl⟩
    · exact ⟨k, Or.inr rfl⟩
  have hbelow : ∀ z k, (z = tg k ∨ z = lw k) → ∀ E : Pair n, k ∈ E.1 → pm E < z := by
    rintro z k (rfl | rfl) E hk
    · exact (hpm E k hk).trans (hlt k)
    · exact hpm E k hk
  have hsame : ∀ z z' k, (z = tg k ∨ z = lw k) → (z' = tg k ∨ z' = lw k) → z = z' ∨ Comp z z' := by
    rintro z z' k (rfl | rfl) (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (hlt k))
    · exact Or.inr (Or.inl (hlt k))
    · exact Or.inl rfl
  have hz0Λ : z0 ∈ Λ := by
    obtain ⟨k, hk | hk⟩ := hidx z0 hz0S
    · exact hk ▸ (hS k).1
    · exact hk ▸ (hS k).2
  refine ⟨K, hK, ?_, ?_⟩
  · rintro z ⟨hzJ, hzS⟩
    obtain ⟨k, hk⟩ := hidx z hzS
    obtain ⟨l, hl⟩ := hidx z0 hz0S
    by_cases hkl : k = l
    · subst hkl
      rcases hsame z0 z k hl hk with heq | hc
      · exact heq ▸ hz0K
      · exact S4.comp_closed hK hz0K hzJ hc
    · let E : Pair n := ⟨{k, l}, Finset.card_pair hkl⟩
      have hpmz := hbelow z k hk E (by simp [E])
      have hpmz0 := hbelow z0 l hl E (by simp [E])
      have hpmJ : pm E ∈ J := hJ hpmz.le hzJ
      have hpmK : pm E ∈ K := S4.comp_closed hK hz0K hpmJ (Or.inr hpmz0)
      exact S4.comp_closed hK hpmK hzJ (Or.inl hpmz)
  · intro x hxK
    by_contra hxΛ
    obtain ⟨u, huK, v, hvK, huΛ, hvΛ, huv⟩ := S4.isConnSet_cross hK.1 (· ∈ Λ) hz0K hxK hz0Λ hxΛ
    rcases hsub (hK.2.1 hvK) with hv | hv
    · exact hvΛ hv
    · exact hΛ u huΛ v hv huv

/-- Prop. 6.6 when every target of `Θ = Iso(I, J) ∪ (J \ I)` lies on one side `S` (`A` or `B`): `K = J \ J_1` is adjacent
to `J` and to `I`, where `J_1` is the component of `J` that contains `J ∩ (S ∪ Y_S)`; if that set is empty, `I` and `J`
are adjacent. -/
theorem mixed_side {I J : Set (Pn n)} (hm : IsMixed n I J) (tgS lwS lamS : Set (Pn n))
    (hS : ∀ x ∈ tgts n, x ∈ isoSet n I J ∨ x ∈ J \ I → x ∈ tgS) (hlo : ∀ x ∈ tgS, lo n x ∈ lwS)
    (hlamT : ∀ x ∈ lamS, x ∈ tgts n → x ∈ tgS)
    (hcomp : (J ∩ (tgS ∪ lwS)).Nonempty → ∃ K, IsComponent K J ∧ J ∩ (tgS ∪ lwS) ⊆ K ∧ K ⊆ lamS) :
    dO I J hm.1 hm.2.1 ≤ 2 := by
  have hI := hm.1
  have hJ := hm.2.1
  have hhI := hm.2.2.1
  have hhJ := hm.2.2.2
  have hQ := q_sub hI hhI
  have hJs := sub_q_tgts hJ hhJ
  have hJIT : J \ I ⊆ tgts n := fun x hx => (hJs hx.1).resolve_left (fun hq => hx.2 (hQ hq))
  by_cases hne : (J ∩ (tgS ∪ lwS)).Nonempty
  · obtain ⟨J1, hJ1, hJS, hJ1lam⟩ := hcomp hne
    have hKid : IsIdeal (J \ J1) := by
      intro z x hxz hz
      refine ⟨hJ hxz hz.1, fun hx1 => hz.2 ?_⟩
      rcases eq_or_lt_of_le hxz with rfl | hlt
      · exact hx1
      · exact S4.comp_closed hJ1 hx1 hz.1 (Or.inl hlt)
    have hKJ : J \ J1 ⊆ J := Set.sdiff_subset
    have hJK : J \ (J \ J1) = J1 := Set.sdiff_sdiff_cancel_left hJ1.2.1
    have hKI : J \ J1 ⊆ I := by
      intro x hx
      by_contra hxI
      exact hx.2 (hJS ⟨hx.1, Or.inl (hS x (hJIT ⟨hx.1, hxI⟩) (Or.inr ⟨hx.1, hxI⟩))⟩)
    have hconn : IsConnSet (I \ (J \ J1)) := by
      refine conn_diff hhI (fun hh => hhJ hh.1) hQ (hKJ.trans hJs) (fun x hxT hxI hxK => ?_)
      by_contra hcon
      rw [not_or, not_not] at hcon
      obtain ⟨hloK, hup⟩ := hcon
      have hxS : x ∈ tgS := by
        by_cases hxJ : x ∈ J
        · have hx1 : x ∈ J1 := by
            by_contra h
            exact hxK ⟨hxJ, h⟩
          exact hlamT x (hJ1lam hx1) hxT
        · exact hS x hxT (Or.inl ⟨hxT, hxI, hxJ, hloK.1, hup⟩)
      exact hloK.2 (hJS ⟨hloK.1, Or.inr (hlo x hxS)⟩)
    have hadj1 : dO I (J \ J1) hm.1 hKid ≤ 1 := by
      rw [dO_eq]
      exact (SimpleGraph.edist_eq_one_iff_adj.mpr (Or.inr ⟨hKI, hconn⟩)).le
    have hadj2 : dO (J \ J1) J hKid hm.2.1 ≤ 1 := by
      rw [dO_eq]
      exact (SimpleGraph.edist_eq_one_iff_adj.mpr (Or.inl ⟨hKJ, by rw [hJK]; exact hJ1.1⟩)).le
    calc dO I J hm.1 hm.2.1 ≤ dO I (J \ J1) hm.1 hKid + dO (J \ J1) J hKid hm.2.1 := by
          simp only [dO_eq]
          exact SimpleGraph.edist_triangle
      _ ≤ 1 + 1 := add_le_add hadj1 hadj2
      _ = 2 := one_add_one_eq_two
  · -- `Θ = ∅`: `J ⊆ I`, and `I \ J` is connected
    have hJI : J ⊆ I := by
      intro x hx
      by_contra hxI
      exact hne ⟨x, hx, Or.inl (hS x (hJIT ⟨hx, hxI⟩) (Or.inr ⟨hx, hxI⟩))⟩
    have hconn : IsConnSet (I \ J) := by
      refine conn_diff hhI hhJ hQ hJs (fun x hxT hxI hxJ => ?_)
      by_contra hcon
      rw [not_or, not_not] at hcon
      exact hne ⟨lo n x, hcon.1, Or.inr (hlo x (hS x hxT (Or.inl ⟨hxT, hxI, hxJ, hcon.1, hcon.2⟩)))⟩
    rw [dO_eq, SimpleGraph.edist_eq_one_iff_adj.mpr (Or.inr ⟨hJI, hconn⟩)]
    norm_num

end S6Ord

/-! ## The rows -/

theorem lem_6_3_proved (n : ℕ) (_hn : 2 ≤ n) :
    (∀ I : Set (Pn n), IsIdeal I → (PnElem.h : Pn n) ∈ I → IsConnSet I) ∧
    (∀ J : Set (Pn n), IsIdeal J → (PnElem.h : Pn n) ∉ J → IsConnSet Jᶜ ∧ {x : Pn n | PnElem.h ≤ x} ⊆ Jᶜ) := by
  refine ⟨fun I hI hh => ?_, fun J hJ hh => ⟨?_, fun x hx hxJ => hh (hJ hx hxJ)⟩⟩
  · have hc := S6Ord.conn_diff (K := ∅) hh (by simp) (S6Ord.q_sub hI hh) (Set.empty_subset _)
      (fun _ _ _ _ => Or.inl (by simp))
    simpa using hc
  · have hc := S6Ord.conn_diff (I := Set.univ) (K := J) (Set.mem_univ _) hh (fun _ _ => Set.mem_univ _)
      (S6Ord.sub_q_tgts hJ hh) (fun _ _ _ _ => Or.inr (Set.mem_univ _))
    rwa [← Set.compl_eq_univ_sdiff] at hc

theorem lem_6_4_i_proved (n : ℕ) (_hn : 2 ≤ n) (I J : Set (Pn n)) (hm : IsMixed n I J) :
    qSet n ⊆ I ∧ J ⊆ qSet n ∪ tgts n ∧ J \ I ⊆ tgts n := by
  have hQ := S6Ord.q_sub hm.1 hm.2.2.1
  have hJs := S6Ord.sub_q_tgts hm.2.1 hm.2.2.2
  exact ⟨hQ, hJs, fun x hx => (hJs hx.1).resolve_left (fun hq => hx.2 (hQ hq))⟩

theorem lem_6_4_ii_proved (n : ℕ) (_hn : 2 ≤ n) (I J : Set (Pn n)) (hm : IsMixed n I J) :
    ((J ∩ (tgtA n ∪ lowA n)).Nonempty →
      ∃ K, IsComponent K J ∧ J ∩ (tgtA n ∪ lowA n) ⊆ K ∧ K ⊆ lamA n) ∧
    ((J ∩ (tgtB n ∪ lowB n)).Nonempty →
      ∃ K, IsComponent K J ∧ J ∩ (tgtB n ∪ lowB n) ⊆ K ∧ K ⊆ lamB n) := by
  have hsub : J ⊆ lamA n ∪ lamB n := (S6Ord.sub_q_tgts hm.2.1 hm.2.2.2).trans S6Ord.q_tgts_sub_lam
  refine ⟨fun hne => S6Ord.side_comp hm.2.1 PnElem.a PnElem.y PnElem.m (lamA n) (lamB n) ?_ ?_
      (fun x hx z hz => S6Ord.lam_no_comp hx hz) hsub ?_ hne,
    fun hne => S6Ord.side_comp hm.2.1 PnElem.b PnElem.y' PnElem.m' (lamB n) (lamA n) ?_ ?_
      (fun x hx z hz hc => S6Ord.lam_no_comp hz hx (S4.comp_symm hc)) (by rw [Set.union_comm]; exact hsub) ?_ hne⟩
  · intro k
    simp [PnOrder.lt_iff_ple, PnOrder.ple]
  · intro E k hk
    simp [PnOrder.lt_iff_ple, PnOrder.ple, hk]
  · intro k
    exact ⟨Or.inr ⟨k, rfl⟩, Or.inl (Or.inr ⟨k, rfl⟩)⟩
  · intro k
    simp [PnOrder.lt_iff_ple, PnOrder.ple]
  · intro E k hk
    simp [PnOrder.lt_iff_ple, PnOrder.ple, hk]
  · intro k
    exact ⟨Or.inr ⟨k, rfl⟩, Or.inl (Or.inr ⟨k, rfl⟩)⟩

theorem lem_6_4_iii_proved (n : ℕ) (_hn : 2 ≤ n) (I J : Set (Pn n)) (hm : IsMixed n I J) :
    (∃ Γ, IsComponent Γ (I \ J) ∧ (PnElem.h : Pn n) ∈ Γ) ∧
    ∀ Γ, IsComponent Γ (I \ J) → (PnElem.h : Pn n) ∈ Γ →
      I \ J = Γ ∪ isoSet n I J ∧ ∀ u ∈ isoSet n I J, IsComponent {u} (I \ J) := by
  have hI := hm.1
  have hJ := hm.2.1
  have hQ := S6Ord.q_sub hI hm.2.2.1
  have hJs := S6Ord.sub_q_tgts hJ hm.2.2.2
  refine ⟨S4.comp_exists ⟨hm.2.2.1, hm.2.2.2⟩, fun Γ hΓ hhΓ => ⟨?_, fun u hu => ?_⟩⟩
  · ext x
    constructor
    · intro hx
      by_cases hxT : x ∈ tgts n
      · by_cases hlo : lo n x ∈ J
        · by_cases hup : up n x ∈ I
          · left
            have hupD : up n x ∈ I \ J := ⟨hup, fun h => S6Ord.up_not_mem hxT (hJs h)⟩
            have hupΓ := S4.comp_closed hΓ hhΓ hupD (Or.inl (S6Ord.h_lt_up hxT))
            exact S4.comp_closed hΓ hupΓ hx (Or.inr (S6Ord.lt_up hxT))
          · exact Or.inr ⟨hxT, hx.1, hx.2, hlo, hup⟩
        · left
          have hloD : lo n x ∈ I \ J := ⟨hQ (S6Ord.lo_mem_q hxT), hlo⟩
          have hloΓ := S4.comp_closed hΓ hhΓ hloD (Or.inr (S6Ord.lo_lt_h hxT))
          exact S4.comp_closed hΓ hloΓ hx (Or.inl (S6Ord.lo_lt hxT))
      · left
        by_cases hxh : x = PnElem.h
        · exact hxh ▸ hhΓ
        · exact S4.comp_closed hΓ hhΓ hx (S4.comp_symm (S6Ord.comp_h hxT hxh))
    · rintro (hx | hx)
      · exact hΓ.2.1 hx
      · exact ⟨hx.2.1, hx.2.2.1⟩
  · obtain ⟨huT, huI, huJ, hlo, hup⟩ := hu
    refine ⟨S4.isConnSet_singleton u, Set.singleton_subset_iff.2 ⟨huI, huJ⟩, fun C hC huC hCD => ?_⟩
    refine Set.Subset.antisymm (fun v hv => ?_) huC
    by_contra hvu
    obtain ⟨p, -, q, hq, hpu, -, hpq⟩ := S4.isConnSet_cross hC (· = u) (huC rfl) hv rfl hvu
    have hpu' : p = u := hpu
    rw [hpu'] at hpq
    have hqD := hCD hq
    rcases hpq with hlt | hlt
    · exact hup (hI (S6Ord.up_le_of_lt huT hlt) hqD.1)
    · exact hqD.2 (hJ (S6Ord.le_lo_of_lt huT hlt) hlo)

theorem lem_6_5_proved (n : ℕ) (_hn : 2 ≤ n) (I J : Set (Pn n)) (hm : IsMixed n I J) (i j : Fin n)
    (hwi : (PnElem.w i : Pn n) ∉ I) (hwj : (PnElem.w' j : Pn n) ∉ I) :
    (∃ Γ, IsComponent Γ Iᶜ ∧ (PnElem.w i : Pn n) ∈ Γ) ∧
    ∀ Γ, IsComponent Γ Iᶜ → (PnElem.w i : Pn n) ∈ Γ →
      (ups n \ I ⊆ Γ ∧ tgts n \ I ⊆ Γ) ∧
      (IsIdeal (I ∪ Γ) ∧ IsConnSet ((I ∪ Γ) \ I) ∧ J ⊂ I ∪ Γ) ∧
      IsConnSet ((I ∪ Γ) \ J) ∧
      (∃ hK : IsIdeal (I ∪ Γ), dO I (I ∪ Γ) hm.1 hK = 1 ∧ dO (I ∪ Γ) J hK hm.2.1 = 1) ∧
      dO I J hm.1 hm.2.1 ≤ 2 := by
  have hI := hm.1
  have hhI := hm.2.2.1
  have hhJ := hm.2.2.2
  have hQ := S6Ord.q_sub hI hhI
  have hJs := S6Ord.sub_q_tgts hm.2.1 hhJ
  refine ⟨S4.comp_exists hwi, fun Γ hΓ hwΓ => ?_⟩
  have htop : ∀ k l, (PnElem.w k : Pn n) ∉ I ∨ (PnElem.w' l : Pn n) ∉ I → (PnElem.t k l : Pn n) ∉ I := by
    rintro k l (hk | hl) ht
    · exact hk (hI (S6Ord.w_lt_t k l).le ht)
    · exact hl (hI (S6Ord.w'_lt_t k l).le ht)
  -- (i): `Γ` contains `W \ I` (paths through tops) and `U \ I`
  have hW : ups n \ I ⊆ Γ := by
    rintro x ⟨⟨k, rfl⟩ | ⟨l, rfl⟩, hx⟩
    · have h1 : (PnElem.t i j : Pn n) ∈ Γ :=
        S4.comp_closed hΓ hwΓ (htop i j (Or.inl hwi)) (Or.inl (S6Ord.w_lt_t i j))
      have h2 : (PnElem.w' j : Pn n) ∈ Γ := S4.comp_closed hΓ h1 hwj (Or.inr (S6Ord.w'_lt_t i j))
      have h3 : (PnElem.t k j : Pn n) ∈ Γ :=
        S4.comp_closed hΓ h2 (htop k j (Or.inr hwj)) (Or.inl (S6Ord.w'_lt_t k j))
      exact S4.comp_closed hΓ h3 hx (Or.inr (S6Ord.w_lt_t k j))
    · have h1 : (PnElem.t i l : Pn n) ∈ Γ :=
        S4.comp_closed hΓ hwΓ (htop i l (Or.inl hwi)) (Or.inl (S6Ord.w_lt_t i l))
      exact S4.comp_closed hΓ h1 hx (Or.inr (S6Ord.w'_lt_t i l))
  have hU : tgts n \ I ⊆ Γ := by
    rintro x ⟨hxT, hx⟩
    have hupI : up n x ∉ I := fun h => hx (hI (S6Ord.lt_up hxT).le h)
    have hupΓ := hW ⟨S6Ord.up_mem_ups hxT, hupI⟩
    exact S4.comp_closed hΓ hupΓ hx (Or.inr (S6Ord.lt_up hxT))
  -- (ii): `K = I ∪ Γ`
  have hKid : IsIdeal (I ∪ Γ) := by
    intro z x hxz hz
    rcases hz with hz | hz
    · exact Or.inl (hI hxz hz)
    · by_cases hxI : x ∈ I
      · exact Or.inl hxI
      · right
        rcases eq_or_lt_of_le hxz with rfl | hlt
        · exact hz
        · exact S4.comp_closed hΓ hz hxI (Or.inr hlt)
  have hdiffI : (I ∪ Γ) \ I = Γ := by
    ext x
    constructor
    · rintro ⟨hx | hx, hxI⟩
      · exact absurd hx hxI
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, hΓ.2.1 hx⟩
  have hJK : J ⊆ I ∪ Γ := by
    intro x hx
    rcases hJs hx with hq | ht
    · exact Or.inl (hQ hq)
    · by_cases hxI : x ∈ I
      · exact Or.inl hxI
      · exact Or.inr (hU ⟨ht, hxI⟩)
  have hssub : J ⊂ I ∪ Γ := ⟨hJK, fun h => hhJ (h (Or.inl hhI))⟩
  -- (iii): `K \ J` is connected
  have hconnJ : IsConnSet ((I ∪ Γ) \ J) := by
    refine S6Ord.conn_diff (Or.inl hhI) hhJ (hQ.trans Set.subset_union_left) hJs (fun x hx _ _ => Or.inr ?_)
    by_cases h : up n x ∈ I
    · exact Or.inl h
    · exact Or.inr (hW ⟨S6Ord.up_mem_ups hx, h⟩)
  have hadjI : dO I (I ∪ Γ) hm.1 hKid = 1 := by
    rw [dO_eq, SimpleGraph.edist_eq_one_iff_adj]
    exact Or.inl ⟨Set.subset_union_left, by rw [hdiffI]; exact hΓ.1⟩
  have hadjJ : dO (I ∪ Γ) J hKid hm.2.1 = 1 := by
    rw [dO_eq, SimpleGraph.edist_eq_one_iff_adj]
    exact Or.inr ⟨hJK, hconnJ⟩
  refine ⟨⟨hW, hU⟩, ⟨hKid, by rw [hdiffI]; exact hΓ.1, hssub⟩, hconnJ, ⟨hKid, hadjI, hadjJ⟩, ?_⟩
  calc dO I J hm.1 hm.2.1 ≤ dO I (I ∪ Γ) hm.1 hKid + dO (I ∪ Γ) J hKid hm.2.1 := by
        simp only [dO_eq]
        exact SimpleGraph.edist_triangle
    _ = 2 := by rw [hadjI, hadjJ, one_add_one_eq_two]

theorem prop_6_6_proved (n : ℕ) (hn : 2 ≤ n) (I J : Set (Pn n)) (hm : IsMixed n I J) : dO I J hm.1 hm.2.1 ≤ 2 := by
  by_cases hA : ∃ i, (PnElem.a i : Pn n) ∈ isoSet n I J ∨ (PnElem.a i : Pn n) ∈ J \ I
  · by_cases hB : ∃ j, (PnElem.b j : Pn n) ∈ isoSet n I J ∨ (PnElem.b j : Pn n) ∈ J \ I
    · obtain ⟨i, hi⟩ := hA
      obtain ⟨j, hj⟩ := hB
      have hwi : (PnElem.w i : Pn n) ∉ I := S6Ord.up_not_mem_I hm.1 (Or.inl ⟨i, rfl⟩) hi
      have hwj : (PnElem.w' j : Pn n) ∉ I := S6Ord.up_not_mem_I hm.1 (Or.inr ⟨j, rfl⟩) hj
      obtain ⟨⟨Γ, hΓ, hwΓ⟩, H⟩ := lem_6_5_proved n hn I J hm i j hwi hwj
      exact (H Γ hΓ hwΓ).2.2.2.2
    · refine S6Ord.mixed_side hm (tgtA n) (lowA n) (lamA n) ?_ ?_ ?_ (lem_6_4_ii_proved n hn I J hm).1
      · rintro x (hxA | ⟨j, rfl⟩) hx
        · exact hxA
        · exact absurd ⟨j, hx⟩ hB
      · rintro x ⟨i, rfl⟩
        exact ⟨i, rfl⟩
      · rintro x ((⟨E, rfl⟩ | ⟨i, rfl⟩) | hx) hxT
        · simp [tgts, tgtA, tgtB] at hxT
        · simp [tgts, tgtA, tgtB] at hxT
        · exact hx
  · refine S6Ord.mixed_side hm (tgtB n) (lowB n) (lamB n) ?_ ?_ ?_ (lem_6_4_ii_proved n hn I J hm).2
    · rintro x (⟨i, rfl⟩ | hxB) hx
      · exact absurd ⟨i, hx⟩ hA
      · exact hxB
    · rintro x ⟨j, rfl⟩
      exact ⟨j, rfl⟩
    · rintro x ((⟨E, rfl⟩ | ⟨j, rfl⟩) | hx) hxT
      · simp [tgts, tgtA, tgtB] at hxT
      · simp [tgts, tgtA, tgtB] at hxT
      · exact hx

theorem thm_6_7_proved (n : ℕ) (hn : 2 ≤ n) : orderDiam (Pn n) = 2 := by
  have h63 := lem_6_3_proved n hn
  apply le_antisymm
  · rw [orderDiam_le_iff]
    intro I J hI hJ
    by_cases hhI : (PnElem.h : Pn n) ∈ I <;> by_cases hhJ : (PnElem.h : Pn n) ∈ J
    · -- both contain `h`: both are adjacent to `∅`
      have hE : IsIdeal (∅ : Set (Pn n)) := isLowerSet_empty
      have a1 : dO I ∅ hI hE ≤ 1 := by
        rw [dO_eq]
        exact (SimpleGraph.edist_eq_one_iff_adj.mpr
          (Or.inr ⟨Set.empty_subset _, by simpa using h63.1 I hI hhI⟩)).le
      have a2 : dO ∅ J hE hJ ≤ 1 := by
        rw [dO_eq]
        exact (SimpleGraph.edist_eq_one_iff_adj.mpr
          (Or.inl ⟨Set.empty_subset _, by simpa using h63.1 J hJ hhJ⟩)).le
      calc dO I J hI hJ ≤ dO I ∅ hI hE + dO ∅ J hE hJ := by
            simp only [dO_eq]
            exact SimpleGraph.edist_triangle
        _ ≤ 1 + 1 := add_le_add a1 a2
        _ = 2 := one_add_one_eq_two
    · exact prop_6_6_proved n hn I J ⟨hI, hJ, hhI, hhJ⟩
    · rw [dO_eq, SimpleGraph.edist_comm, ← dO_eq]
      exact prop_6_6_proved n hn J I ⟨hJ, hI, hhJ, hhI⟩
    · -- neither contains `h`: both are adjacent to `P`
      have hU : IsIdeal (Set.univ : Set (Pn n)) := isLowerSet_univ
      have a1 : dO I Set.univ hI hU ≤ 1 := by
        rw [dO_eq]
        exact (SimpleGraph.edist_eq_one_iff_adj.mpr
          (Or.inl ⟨Set.subset_univ _, by rw [← Set.compl_eq_univ_sdiff]; exact (h63.2 I hI hhI).1⟩)).le
      have a2 : dO Set.univ J hU hJ ≤ 1 := by
        rw [dO_eq]
        exact (SimpleGraph.edist_eq_one_iff_adj.mpr
          (Or.inr ⟨Set.subset_univ _, by rw [← Set.compl_eq_univ_sdiff]; exact (h63.2 J hJ hhJ).1⟩)).le
      calc dO I J hI hJ ≤ dO I Set.univ hI hU + dO Set.univ J hU hJ := by
            simp only [dO_eq]
            exact SimpleGraph.edist_triangle
        _ ≤ 1 + 1 := add_le_add a1 a2
        _ = 2 := one_add_one_eq_two
  · -- the ideals `{m_E}` and `{m'_E}` are not nested
    have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := fun h => by simpa using congrArg Fin.val h
    let E : Pair n := ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair h01⟩
    have hmin : ∀ (z : Pn n) (x : Pn n), (z = PnElem.m E ∨ z = PnElem.m' E) → x ≤ z → x = z := by
      rintro z x (rfl | rfl) hxz <;> rw [PnOrder.le_iff_ple] at hxz <;> cases x <;> simp_all [PnOrder.ple]
    have hI : IsIdeal ({PnElem.m E} : Set (Pn n)) := by
      intro z x hxz hz
      rw [Set.mem_singleton_iff] at hz ⊢
      rw [hmin z x (Or.inl hz) hxz, hz]
    have hJ : IsIdeal ({PnElem.m' E} : Set (Pn n)) := by
      intro z x hxz hz
      rw [Set.mem_singleton_iff] at hz ⊢
      rw [hmin z x (Or.inr hz) hxz, hz]
    have hd : 2 ≤ dO {PnElem.m E} {PnElem.m' E} hI hJ := by
      rw [dO_eq]
      have h0 : (idealGraph (Pn n)).edist ⟨{PnElem.m E}, hI⟩ ⟨{PnElem.m' E}, hJ⟩ ≠ 0 := by
        rw [Ne, SimpleGraph.edist_eq_zero_iff]
        intro h
        have h' : ({PnElem.m E} : Set (Pn n)) = {PnElem.m' E} := congrArg Subtype.val h
        have hm : (PnElem.m E : Pn n) ∈ ({PnElem.m' E} : Set (Pn n)) := h' ▸ Set.mem_singleton _
        simp at hm
      have h1 : (idealGraph (Pn n)).edist ⟨{PnElem.m E}, hI⟩ ⟨{PnElem.m' E}, hJ⟩ ≠ 1 := by
        rw [Ne, SimpleGraph.edist_eq_one_iff_adj]
        rintro (⟨hsub, -⟩ | ⟨hsub, -⟩)
        · have hm := hsub (Set.mem_singleton (PnElem.m E : Pn n))
          simp at hm
        · have hm := hsub (Set.mem_singleton (PnElem.m' E : Pn n))
          simp at hm
      generalize (idealGraph (Pn n)).edist ⟨{PnElem.m E}, hI⟩ ⟨{PnElem.m' E}, hJ⟩ = x at h0 h1 ⊢
      induction x using ENat.recTopCoe with
      | top => exact le_top
      | coe k =>
        have hk0 : k ≠ 0 := by exact_mod_cast h0
        have hk1 : k ≠ 1 := by exact_mod_cast h1
        exact_mod_cast (show 2 ≤ k by omega)
    calc (2 : ℕ∞) ≤ dO {PnElem.m E} {PnElem.m' E} hI hJ := hd
      _ ≤ orderDiam (Pn n) := by
        rw [orderDiam_eq, dO_eq]
        exact SimpleGraph.edist_le_ediam

end LeeDiam
