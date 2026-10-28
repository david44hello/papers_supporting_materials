/-
LeeDiam/Sec3/Band.lean — Section 3: the band, Lemmas 3.1-3.2, Theorem 3.3.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Vertices
import LeeDiam.Defs.Walks
import LeeDiam.Defs.Band
import LeeDiam.Defs.Pn
import LeeDiam.Cited.Lee26
import LeeDiam.Sec4.BandOrder
import LeeDiam.Bridge.Graphs
import LeeDiam.Sec2.Walks

namespace LeeDiam

open Finset

/-! ## Helpers (namespace `S3`) -/

namespace S3

variable {k : ℕ}

/-- `a_1, …, a_k, …` are linked: `a_i < b_{i+1} > a_{i+1}`, so `a_0` reaches every `a_n`. -/
theorem reach_a (hk : 1 ≤ k) : ∀ n (hn : n < k),
    (compGraph (Band k)).Reachable (Band.a ⟨0, hk⟩) (Band.a ⟨n, hn⟩) := by
  intro n
  induction n with
  | zero => intro _; exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    intro hn
    have h1 : (compGraph (Band k)).Adj (Band.a ⟨n, by omega⟩) (Band.b ⟨n + 1, hn⟩) := by
      show Comp _ _
      rw [S4.comp_iff_val]
      simp
    have h2 : (compGraph (Band k)).Adj (Band.b ⟨n + 1, hn⟩) (Band.a ⟨n + 1, hn⟩) := by
      show Comp _ _
      rw [S4.comp_iff_val]
      simp
    exact (ih (by omega)).trans (h1.reachable.trans h2.reachable)

theorem band_conn (hk : 1 ≤ k) : IsConnPoset (Band k) := by
  unfold IsConnPoset
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨Band.a ⟨0, hk⟩, fun w => ?_⟩
  by_cases hw : w.2 = 0
  · have hwa : w = Band.a w.1 := Prod.ext rfl hw
    rw [hwa]
    exact reach_a hk _ w.1.isLt
  · have hadj : (compGraph (Band k)).Adj (Band.a w.1) w :=
      S4.comp_of_col rfl (fun h => hw (by rw [← h]; rfl))
    exact (reach_a hk _ w.1.isLt).trans hadj.reachable

theorem band_width : width (Band k) = k := by
  unfold width
  refine IsGreatest.csSup_eq ⟨⟨Finset.univ.image Band.a, ?_, ?_⟩, ?_⟩
  · apply S4.isAntichainSet_row 0
    intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨i, rfl⟩ := hx
    rfl
  · rw [Finset.card_image_of_injective _ (fun i j h => by simpa using congrArg Prod.fst h)]
    simp
  · rintro n ⟨A, hA, rfl⟩
    calc A.card ≤ (Finset.univ : Finset (Fin k)).card :=
          Finset.card_le_card_of_injOn (fun x => x.1) (by intro x _; exact Finset.mem_univ _)
            (by intro x hx y hy h; exact S4.antichain_col hA hx hy h)
      _ = k := by simp

/-- An interval-closed set of naturals has alternating sum `0` or `(-1)^(m+1)`, `m` its largest element. -/
theorem alt_sum_interval (S : Finset ℕ) (hS : ∀ a ∈ S, ∀ c ∈ S, ∀ n, a ≤ n → n ≤ c → n ∈ S) :
    (∑ n ∈ S, (-1 : ℤ) ^ (n + 1)) = 0 ∨
      ∃ m ∈ S, (∀ x ∈ S, x ≤ m) ∧ (∑ n ∈ S, (-1 : ℤ) ^ (n + 1)) = (-1) ^ (m + 1) := by
  revert hS
  induction S using Finset.induction_on_max with
  | empty => intro _; left; simp
  | insert a s has ih =>
    intro hS
    have hs : ∀ a' ∈ s, ∀ c ∈ s, ∀ n, a' ≤ n → n ≤ c → n ∈ s := by
      intro a' ha' c hc n h1 h2
      rcases Finset.mem_insert.1 (hS a' (Finset.mem_insert_of_mem ha') c (Finset.mem_insert_of_mem hc) n h1 h2)
        with rfl | h
      · exact absurd (has c hc) (by omega)
      · exact h
    have hnot : a ∉ s := fun h => lt_irrefl a (has a h)
    rw [Finset.sum_insert hnot]
    rcases ih hs with h0 | ⟨m, hm, hmax, hsum⟩
    · right
      refine ⟨a, Finset.mem_insert_self a s, fun x hx => ?_, by rw [h0, add_zero]⟩
      rcases Finset.mem_insert.1 hx with rfl | h
      · exact le_rfl
      · exact (has x h).le
    · left
      have hma : m + 1 = a := by
        have hlt := has m hm
        rcases Finset.mem_insert.1 (hS m (Finset.mem_insert_of_mem hm) a (Finset.mem_insert_self a s) (a - 1)
          (by omega) (by omega)) with h | h
        · omega
        · have := hmax _ h
          omega
      rw [hsum, ← hma]
      ring

theorem abs_le_one_of_alt {S : ℤ} (h : S = 0 ∨ ∃ m : ℕ, S = (-1) ^ (m + 1)) : |S| ≤ 1 := by
  rcases h with h | ⟨m, h⟩ <;> rw [h] <;> simp

/-- The alternating sum `Φ(S) = Σ_i [b_i ∈ S] (-1)^(i+1)` of v1.50 (0-based `i`). -/
noncomputable def phi (S : Set (Band k)) : ℤ :=
  open Classical in ∑ i : Fin k, if Band.b i ∈ S then (-1 : ℤ) ^ (i.val + 1) else 0

/-- The upper set of a row-0/row-1 description is an ideal: below a row-1 element there are only row-0 elements. -/
theorem rowIdeal (Q : Fin k → Prop) : IsIdeal {x : Band k | x.2 = 0 ∨ (x.2 = 1 ∧ Q x.1)} := by
  intro a b hba ha
  rw [S4.le_iff_bandLe] at hba
  rcases hba with rfl | ⟨hb, ha2, -⟩ | ⟨hb, ha2, -⟩ | ⟨hb, ha2, -⟩
  · exact ha
  · exact Or.inl (Fin.ext hb)
  · exfalso
    rcases ha with h | ⟨h, -⟩ <;> simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one] at h <;> omega
  · exact Or.inl (Fin.ext hb)

theorem rowMem (Q : Fin k → Prop) (i : Fin k) :
    Band.b i ∈ {x : Band k | x.2 = 0 ∨ (x.2 = 1 ∧ Q x.1)} ↔ Q i := by
  show (1 : Fin 3) = 0 ∨ ((1 : Fin 3) = 1 ∧ Q i) ↔ Q i
  exact ⟨fun h => h.elim (fun h => absurd h (by decide)) (fun h => h.2), fun h => Or.inr ⟨rfl, h⟩⟩

end S3

/-! ## The claims -/

theorem lem_3_1_pairs_proved (k : ℕ) (x y : Band k) :
    x < y ↔
      (x.2 = 0 ∧ y.2 = 1 ∧ (y.1 = x.1 ∨ y.1.val = x.1.val + 1)) ∨
      (x.2 = 1 ∧ y.2 = 2 ∧ (y.1 = x.1 ∨ y.1.val + 1 = x.1.val)) ∨
      (x.2 = 0 ∧ y.2 = 2 ∧ (y.1.val + 1 = x.1.val ∨ y.1 = x.1 ∨ y.1.val = x.1.val + 1)) := by
  rw [S4.lt_iff_val]
  simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]

theorem lem_3_1_consequences_proved (k : ℕ) :
    (∀ x y : Band k, x.1.val + 2 ≤ y.1.val → ¬ x ≤ y ∧ ¬ y ≤ x) ∧
    (∀ r : Fin 3, IsAntichainSet {x : Band k | x.2 = r}) ∧
    (1 ≤ k → IsConnPoset (Band k)) ∧ width (Band k) = k := by
  refine ⟨fun x y h => ?_, fun r => S4.isAntichainSet_row r _ (fun x hx => hx), S3.band_conn,
    S3.band_width⟩
  rw [S4.le_iff_bandLe, S4.le_iff_bandLe]
  unfold S4.bandLe
  rw [S4.band_ext_iff, S4.band_ext_iff]
  omega

theorem band_cross_proved (k : ℕ) (x y : Band k) (hxy : x.1 ≠ y.1) :
    (x < y ∨ y < x) ↔
      (y.1.val = x.1.val + 1 ∨ x.1.val = y.1.val + 1) ∧
      ((x.2 = 0 ∧ y.2 = 1 ∧ y.1.val = x.1.val + 1) ∨ (x.2 = 0 ∧ y.2 = 2 ∧ y.1.val = x.1.val + 1) ∨
       (x.2 = 0 ∧ y.2 = 2 ∧ x.1.val = y.1.val + 1) ∨ (x.2 = 1 ∧ y.2 = 2 ∧ x.1.val = y.1.val + 1) ∨
       (y.2 = 0 ∧ x.2 = 1 ∧ x.1.val = y.1.val + 1) ∨ (y.2 = 0 ∧ x.2 = 2 ∧ x.1.val = y.1.val + 1) ∨
       (y.2 = 0 ∧ x.2 = 2 ∧ y.1.val = x.1.val + 1) ∨ (y.2 = 1 ∧ x.2 = 2 ∧ y.1.val = x.1.val + 1)) := by
  rw [S4.lt_iff_val, S4.lt_iff_val]
  rw [Ne, Fin.ext_iff] at hxy
  simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
  have ha := x.2.isLt
  have hb := y.2.isLt
  generalize x.2.val = a at ha ⊢
  generalize y.2.val = b at hb ⊢
  generalize x.1.val = c at hxy ⊢
  generalize y.1.val = d at hxy ⊢
  interval_cases a <;> interval_cases b <;> simp <;> omega

theorem lem_3_2_proved (k : ℕ) (D : Set (Band k)) (hD : IsConnSet D) (hconv : IsConvexSet D) :
    ∀ i j l : Fin k, Band.b i ∈ D → Band.b j ∈ D → i ≤ l → l ≤ j → Band.b l ∈ D := by
  intro i j l hi hj hil hlj
  by_contra hl
  have hil' : i.val < l.val := by
    rcases lt_or_eq_of_le hil with h | h
    · exact h
    · exact absurd (h ▸ hi) hl
  have hlj' : l.val ≤ j.val := hlj
  obtain ⟨u, hu, v, hv, hQu, hQv, huv⟩ :=
    S4.isConnSet_cross hD (fun x : Band k => x.1.val < l.val) hi hj hil' (not_lt.2 hlj')
  rw [S4.comp_iff_val] at huv
  have hu2 := u.2.isLt
  have hv2 := v.2.isLt
  have hbl1 : (Band.b l).1.val = l.val := rfl
  have hbl2 : (Band.b l).2.val = 1 := rfl
  rcases huv with h | h | ⟨hrows, hc1, hc2⟩
  · omega
  · apply hl
    have hvb : v = Band.b l := by
      rw [S4.band_ext_iff]
      omega
    rw [← hvb]
    exact hv
  · rcases hrows with ⟨hu0, hv2'⟩ | ⟨hu2', hv0⟩
    · exact hl (hconv u (Band.b l) v (by rw [S4.lt_iff_val]; omega) (by rw [S4.lt_iff_val]; omega) hu hv)
    · exact hl (hconv v (Band.b l) u (by rw [S4.lt_iff_val]; omega) (by rw [S4.lt_iff_val]; omega) hv hu)

open Classical in
theorem thm_3_3_step_proved (k : ℕ) (I J : Set (Band k)) (hI : IsIdeal I) (hJ : IsIdeal J) (hIJ : I ⊆ J)
    (hconn : IsConnSet (J \ I)) :
    IsConvexSet (J \ I) ∧
      |(∑ i : Fin k, if Band.b i ∈ J then (-1 : ℤ) ^ (i.val + 1) else 0) -
        (∑ i : Fin k, if Band.b i ∈ I then (-1 : ℤ) ^ (i.val + 1) else 0)| ≤ 1 := by
  have hconv : IsConvexSet (J \ I) := by
    intro x y z hxy hyz hx hz
    exact ⟨hJ hyz.le hz.1, fun hy => hx.2 (hI hxy.le hy)⟩
  refine ⟨hconv, ?_⟩
  have hdiff : ∀ i : Fin k, ((if Band.b i ∈ J then (-1 : ℤ) ^ (i.val + 1) else 0) -
      (if Band.b i ∈ I then (-1 : ℤ) ^ (i.val + 1) else 0)) =
      if Band.b i ∈ J \ I then (-1 : ℤ) ^ (i.val + 1) else 0 := by
    intro i
    by_cases hbI : Band.b i ∈ I
    · have hbJ : Band.b i ∈ J := hIJ hbI
      simp [hbI, hbJ]
    · by_cases hbJ : Band.b i ∈ J <;> simp [hbI, hbJ]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun i _ => hdiff i), ← Finset.sum_filter]
  have hS : ∀ a ∈ (Finset.univ.filter (fun i : Fin k => Band.b i ∈ J \ I)).image Fin.val,
      ∀ c ∈ (Finset.univ.filter (fun i : Fin k => Band.b i ∈ J \ I)).image Fin.val, ∀ n, a ≤ n → n ≤ c →
        n ∈ (Finset.univ.filter (fun i : Fin k => Band.b i ∈ J \ I)).image Fin.val := by
    intro a ha c hc n h1 h2
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ha hc ⊢
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := hc
    have hjk := j.isLt
    exact ⟨⟨n, by omega⟩, lem_3_2_proved k (J \ I) hconn hconv i j ⟨n, by omega⟩ hi hj h1 h2, rfl⟩
  have key := S3.alt_sum_interval _ hS
  rw [Finset.sum_image (fun x _ y _ h => Fin.ext h)] at key
  apply S3.abs_le_one_of_alt
  rcases key with h | ⟨m, -, -, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨m, h⟩

/-- A step of the graph of ideals changes `Φ` by at most one. -/
theorem S3.adj_phi {k : ℕ} {I J : {K : Set (Band k) // IsIdeal K}} (h : (idealGraph (Band k)).Adj I J) :
    |S3.phi I.1 - S3.phi J.1| ≤ 1 := by
  rcases h with ⟨hIJ, hc⟩ | ⟨hJI, hc⟩
  · rw [abs_sub_comm]
    exact (thm_3_3_step_proved k I.1 J.1 I.2 J.2 hIJ hc).2
  · exact (thm_3_3_step_proved k J.1 I.1 J.2 I.2 hJI hc).2

/-- Along a path of ideals with `n + 1` entries, `Φ` changes by at most `n`. -/
theorem S3.phi_chain {k : ℕ} (L : List {K : Set (Band k) // IsIdeal K}) :
    ∀ A B : {K : Set (Band k) // IsIdeal K}, L.IsChain (idealGraph (Band k)).Adj → L.head? = some A →
      L.getLast? = some B → |S3.phi A.1 - S3.phi B.1| + 1 ≤ L.length := by
  induction L with
  | nil => intro A B _ h; simp at h
  | cons a t ih =>
    intro A B hch hA hB
    simp only [List.head?_cons, Option.some.injEq] at hA
    subst hA
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hB
      subst hB
      simp
    | cons b t' =>
      rw [List.isChain_cons_cons] at hch
      have h1 := ih b B hch.2 rfl (by simpa using hB)
      have h2 := S3.adj_phi hch.1
      have h3 := abs_sub_le (S3.phi a.1) (S3.phi b.1) (S3.phi B.1)
      simp only [List.length_cons] at h1 ⊢
      push_cast at h1 ⊢
      linarith

open Classical in
theorem thm_3_3_lipschitz_proved (k : ℕ) (I J : Set (Band k)) (hI : IsIdeal I) (hJ : IsIdeal J) :
    ((|(∑ i : Fin k, if Band.b i ∈ I then (-1 : ℤ) ^ (i.val + 1) else 0) -
        (∑ i : Fin k, if Band.b i ∈ J then (-1 : ℤ) ^ (i.val + 1) else 0)|).toNat : ℕ∞) ≤ dO I J hI hJ := by
  change ((|S3.phi I - S3.phi J|).toNat : ℕ∞) ≤ dO I J hI hJ
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
  rw [← hm] at hlt
  have hmn : m < (|S3.phi I - S3.phi J|).toNat := by exact_mod_cast hlt
  obtain ⟨L, hhead, hlast, hlen, hchain⟩ := (dO_le_iff I J hI hJ m).1 hm.symm.le
  have hL := S3.phi_chain L ⟨I, hI⟩ ⟨J, hJ⟩ hchain hhead hlast
  have hd : (((|S3.phi I - S3.phi J|).toNat : ℕ) : ℤ) = |S3.phi I - S3.phi J| :=
    Int.toNat_of_nonneg (abs_nonneg _)
  have hlen' : (L.length : ℤ) ≤ m + 1 := by exact_mod_cast hlen
  have hmn' : (m : ℤ) < ((|S3.phi I - S3.phi J|).toNat : ℕ) := by exact_mod_cast hmn
  linarith

open Classical in
theorem thm_3_3_far_pair_proved (k : ℕ) :
    ∃ (I0 I1 : Set (Band k)) (h0 : IsIdeal I0) (h1 : IsIdeal I1),
      I0 = {x | x.2 = 0 ∨ (x.2 = 1 ∧ Even (x.1.val + 1))} ∧ I1 = {x | x.2 = 0 ∨ (x.2 = 1 ∧ Odd (x.1.val + 1))} ∧
      (∑ i : Fin k, if Band.b i ∈ I0 then (-1 : ℤ) ^ (i.val + 1) else 0) -
        (∑ i : Fin k, if Band.b i ∈ I1 then (-1 : ℤ) ^ (i.val + 1) else 0) = k ∧
      (k : ℕ∞) ≤ dO I0 I1 h0 h1 := by
  refine ⟨{x | x.2 = 0 ∨ (x.2 = 1 ∧ Even (x.1.val + 1))}, {x | x.2 = 0 ∨ (x.2 = 1 ∧ Odd (x.1.val + 1))},
    S3.rowIdeal (fun i => Even (i.val + 1)), S3.rowIdeal (fun i => Odd (i.val + 1)), rfl, rfl, ?_⟩
  have hval : S3.phi {x : Band k | x.2 = 0 ∨ (x.2 = 1 ∧ Even (x.1.val + 1))} -
      S3.phi {x : Band k | x.2 = 0 ∨ (x.2 = 1 ∧ Odd (x.1.val + 1))} = k := by
    unfold S3.phi
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (show ∑ _i : Fin k, (1 : ℤ) = k by simp)
    have m0 : Band.b i ∈ {x : Band k | x.2 = 0 ∨ (x.2 = 1 ∧ Even (x.1.val + 1))} ↔ Even (i.val + 1) :=
      S3.rowMem (fun i => Even (i.val + 1)) i
    have m1 : Band.b i ∈ {x : Band k | x.2 = 0 ∨ (x.2 = 1 ∧ Odd (x.1.val + 1))} ↔ Odd (i.val + 1) :=
      S3.rowMem (fun i => Odd (i.val + 1)) i
    rcases Nat.even_or_odd (i.val + 1) with he | ho
    · rw [ite_eq_left (m0.2 he), ite_eq_right (fun h => (Nat.not_odd_iff_even.2 he) (m1.1 h)), he.neg_one_pow]
      norm_num
    · rw [ite_eq_right (fun h => (Nat.not_even_iff_odd.2 ho) (m0.1 h)), ite_eq_left (m1.2 ho), ho.neg_one_pow]
      norm_num
  refine ⟨hval, ?_⟩
  refine le_trans ?_ (thm_3_3_lipschitz_proved k _ _ _ _)
  change ((k : ℕ) : ℕ∞) ≤ ((|S3.phi _ - S3.phi _|).toNat : ℕ∞)
  rw [hval]
  simp

theorem thm_3_3_proved (k : ℕ) (_hk : 1 ≤ k) : orderDiam (Band k) = k := by
  obtain ⟨I0, I1, h0, h1, -, -, -, hfar⟩ := thm_3_3_far_pair_proved k
  apply le_antisymm
  · have hle := (prop_2_3_proved (Band k)).2.2.2.1
    rw [(lem_3_1_consequences_proved k).2.2.2] at hle
    exact hle
  · exact hfar.trans ((orderDiam_le_iff _).1 le_rfl I0 I1 h0 h1)

end LeeDiam

