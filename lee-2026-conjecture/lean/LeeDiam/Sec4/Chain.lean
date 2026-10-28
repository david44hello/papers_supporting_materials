/-
LeeDiam/Sec4/Chain.lean — Section 4 of paper 004: the chain polytope of the band, diam C(B_k) ≤ ⌊3(k+1)/4⌋. One
`X_proved` per Section 4 row of Statements.lean, from the helper modules LeeDiam/Sec4/*.lean (namespace S4).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Walks
import LeeDiam.Defs.Band
import LeeDiam.Defs.Chain
import LeeDiam.Sec4.Words
import LeeDiam.Sec4.WalkOps
import LeeDiam.Sec4.Merge
import LeeDiam.Sec4.Comb
import LeeDiam.Sec4.Tame
import LeeDiam.Sec4.Junction
import LeeDiam.Sec4.TableRows
import LeeDiam.Sec4.HalfJunction
import LeeDiam.Sec4.FullWord
import LeeDiam.Sec4.ChainWalks
import LeeDiam.Bridge.Graphs
import LeeDiam.Sec2.Walks

namespace LeeDiam

open Finset

open Band

theorem sec4_antichain_col_proved {k : ℕ} (X : Set (Band k)) (hX : IsAntichainSet X) (x y : Band k) (hx : x ∈ X) (hy : y ∈ X)
    (hxy : x.1 = y.1) : x = y :=
  S4.antichain_col hX hx hy hxy

theorem sec4_word_exists_proved {k : ℕ} (X : Set (Band k)) (hX : IsAntichainSet X) : ∃ w, X = ofWord w :=
  S4.word_exists X hX

theorem sec4_word_antichain_iff_proved {k : ℕ} (w : Fin k → Option (Fin 3)) :
    IsAntichainSet (ofWord w) ↔ ∀ i j : Fin k, j.val = i.val + 1 → ¬ BadPair (w i) (w j) :=
  S4.word_antichain_iff w

theorem sec4_run_form_proved {k : ℕ} (U : Set (Band k)) (hU : IsAntichainSet U) (s e : ℕ)
    (hrun : ∀ l : Fin k, s ≤ l.val → l.val ≤ e → ∃ x ∈ U, x.1 = l) :
    ∃ (i : ℕ) (r : Fin 3), r ≠ 1 ∧ ∀ x ∈ U, s ≤ x.1.val → x.1.val ≤ e →
      (x.2 = 1 ↔ x.1.val < s + i) ∧ (x.2 ≠ 1 → x.2 = r) :=
  S4.run_form U hU s e hrun

theorem sec4_P1_P2_proved {k : ℕ} (x y : Band k) :
    Comp x y ↔
      (x.2 = 1 ∧ y.2 ≠ 1 ∧ (y.1 = x.1 ∨ y.1.val + 1 = x.1.val)) ∨
      (y.2 = 1 ∧ x.2 ≠ 1 ∧ (x.1 = y.1 ∨ x.1.val + 1 = y.1.val)) ∨
      (((x.2 = 0 ∧ y.2 = 2) ∨ (x.2 = 2 ∧ y.2 = 0)) ∧ x.1.val ≤ y.1.val + 1 ∧ y.1.val ≤ x.1.val + 1) := by
  have := x.2.isLt
  have := y.2.isLt
  rw [S4.comp_iff_val]
  simp only [Fin.ext_iff, ne_eq, Fin.val_zero, Fin.val_one, Fin.val_two]

theorem sec4_rows_cols_proved {k : ℕ} (x y : Band k) : (x.2 = y.2 → ¬ Comp x y) ∧ (x.1 = y.1 → x ≠ y → Comp x y) :=
  ⟨fun h => S4.not_comp_of_row h, fun h hne => S4.comp_of_col h hne⟩

theorem sec4_translation_proved {k : ℕ} {k' : ℕ} (d : ℕ) (hd : k + d ≤ k') :
    (∀ x y : Band k, x ≤ y ↔ colShift d hd x ≤ colShift d hd y) ∧
    (∀ X : Set (Band k), IsAntichainSet X ↔ IsAntichainSet (colShift d hd '' X)) ∧
    (∀ D : Set (Band k), IsConnSet D ↔ IsConnSet (colShift d hd '' D)) ∧
    (∀ W : List (Set (Band k)), IsWalk W → IsWalk (W.map (colShift d hd '' ·))) :=
  S4.translation d hd

theorem lem_4_2_proved {k : ℕ} (F : Set (Band k)) (hF : F.Nonempty) :
    IsConnSet F ↔
      (∀ x ∈ F, ∀ y ∈ F, ∀ l : Fin k, x.1 ≤ l → l ≤ y.1 → ∃ z ∈ F, z.1 = l) ∧
      ∀ x ∈ F, ∀ y ∈ F, y.1.val = x.1.val + 1 →
        ∃ x' ∈ F, ∃ y' ∈ F, x'.1 = x.1 ∧ y'.1 = y.1 ∧ Comp x' y' :=
  S4.col_conn F hF

theorem sec4_sigma_proved {k : ℕ} :
    (∀ x y : Band k, x ≤ y ↔ sigmaAC y ≤ sigmaAC x) ∧ (∀ x y : Band k, Comp x y ↔ Comp (sigmaAC x) (sigmaAC y)) ∧
    (∀ W : List (Set (Band k)), IsWalk W → IsWalk (W.map (sigmaAC '' ·))) ∧
    (∀ w : Fin k → Option (Fin 3), sigmaAC '' ofWord w = ofWord (fun i => (w i).map Fin.rev)) ∧
    (∀ X : Set (Band k), (∀ x ∈ X, x.2 = 1) → sigmaAC '' X = X) :=
  S4.sigma_props

theorem sec4_trace_example_proved {k : ℕ} (e : Fin k) :
    outerTrace [{b e}, {c e}, {a e}, ∅] e = [none, some (c e), some (a e), none] :=
  S4.trace_example e

theorem sec4_reverse_split_proved {P : Type} [PartialOrder P] (W : List (Set P)) (A B : Set P)
    (hW : IsWalkFromTo W A B) : IsWalkFromTo W.reverse B A :=
  S4.isWalkFromTo_reverse hW

theorem lem_4_3_proved {k : ℕ} {r M : ℕ} (D : Fin r → Set (Band k)) (hD : Pairwise fun t t' => Disjoint (D t) (D t'))
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
        outerTrace ((List.range (M + 1)).map (mergedState W step)) e = outerTrace (W t) e :=
  S4.merge D hD W hW hWD step hmono hne hanti hconn

theorem lem_4_3_sequential_proved {k : ℕ} (W₁ W₂ : List (Set (Band k))) (A₁ B₁ A₂ B₂ : Set (Band k))
    (h₁ : IsWalkFromTo W₁ A₁ B₁) (h₂ : IsWalkFromTo W₂ A₂ B₂)
    (hfar : ∀ X ∈ W₁, ∀ Y ∈ W₂, ∀ x ∈ X, ∀ y ∈ Y, x.1.val + 2 ≤ y.1.val ∨ y.1.val + 2 ≤ x.1.val) :
    IsWalkFromTo (W₁.map (· ∪ A₂) ++ W₂.tail.map (B₁ ∪ ·)) (A₁ ∪ A₂) (B₁ ∪ B₂) ∧
      (W₁.map (· ∪ A₂) ++ W₂.tail.map (B₁ ∪ ·)).length - 1 = (W₁.length - 1) + (W₂.length - 1) :=
  S4.walk_sequential W₁ W₂ A₁ B₁ A₂ B₂ h₁ h₂ hfar

theorem lem_4_4_i_proved {k : ℕ} (W : List (Set (Band k))) (hW : IsWalk W) (y : Band k) (hy : ∀ X ∈ W, y ∉ X)
    (_h0 : ∀ z ∈ W.headD ∅, ¬ Comp y z) (μ : ℕ) (_hμ : μ < W.length) (hμy : ∃ z ∈ W.getD μ ∅, Comp y z)
    (hmin : ∀ t < μ, ∀ z ∈ W.getD t ∅, ¬ Comp y z) :
    IsWalk (W.mapIdx fun t X => if t < μ then insert y X else X) ∧
      (W.mapIdx fun t X => if t < μ then insert y X else X).length = W.length :=
  S4.ride_prefix W hW y hy μ hμy hmin

theorem lem_4_4_ii_proved {k : ℕ} (W : List (Set (Band k))) (hW : IsWalk W) (y : Band k) (hy : ∀ X ∈ W, y ∉ X)
    (_hn : ∀ z ∈ W.getLastD ∅, ¬ Comp y z) (ν : ℕ) (hν1 : 1 ≤ ν) (_hνn : ν < W.length)
    (hνy : ∃ z ∈ W.getD (ν - 1) ∅, Comp y z) (hmax : ∀ t, ν ≤ t → ∀ z ∈ W.getD t ∅, ¬ Comp y z) :
    IsWalk (W.mapIdx fun t X => if ν ≤ t then insert y X else X) ∧
      (W.mapIdx fun t X => if ν ≤ t then insert y X else X).length = W.length :=
  S4.ride_suffix W hW y hy ν hν1 hνy hmax

theorem lem_4_5_proved {k : ℕ} (s e : ℕ) (hse : s ≤ e) (hek : e < k) (par : ℕ) (hpar : par = 0 ∨ (par = 1 ∧ s + 1 ≤ e))
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
            i₁ < t ∧ t ≤ L₁.length + i₂) :=
  S4.comb s e hse hek par hpar A B hAB L₁ L₂ hL₁ hL₁c hL₂ hL₂c

theorem lem_4_5_count_proved {k : ℕ} (s e : ℕ) (hse : s ≤ e) (hek : e < k) :
    (helperSet 1 s e : Set (Band k)).ncard = (e - s + 1) / 2 ∧
      (helperSet 0 s e : Set (Band k)).ncard = (e - s + 2) / 2 := by
  rw [S4.helper_count 1 s e le_rfl hse hek, S4.helper_count 0 s e (Nat.zero_le 1) hse hek]
  omega

theorem cor_4_6_proved {k : ℕ} (r : Fin 3) (hr : r ≠ 1) (s e : ℕ) (hse : s ≤ e) (hek : e < k)
    (A B : Set (Band k)) (hAB : IsSplit A B (rowSeg r s e)) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 = (e - s + 1) / 2 + 1 ∧
      (∀ X ∈ W, ∀ x ∈ X, x.2 ≠ 1 ∧ s ≤ x.1.val ∧ x.1.val ≤ e) ∧
      (∀ X ∈ W, ∀ x ∈ X, x.1.val = s → x.2 = r) :=
  S4.comb_cor r hr s e hse hek A B hAB

theorem def_4_7_arrive_depart_proved {k : ℕ} (W : List (Set (Band k))) (i : Fin k) (h : Band k) (hT : IsTameAt W i h) :
    ∃ μ ν : ℕ, 1 ≤ μ ∧ μ < ν ∧ ν ≤ W.length - 1 ∧ ∀ t < W.length, (h ∈ W.getD t ∅ ↔ μ ≤ t ∧ t < ν) :=
  S4.tame_arrive_depart W i h hT

theorem sec4_tame_symm_proved {k : ℕ} (W : List (Set (Band k))) (hW : IsWalk W) (i : Fin k) (h : Band k) (hT : IsTameAt W i h) :
    IsTameAt W.reverse i h ∧ IsTameAt (W.map (sigmaAC '' ·)) i (sigmaAC h) ∧
      ∀ A B : Set (Band k), IsWalkFromTo W A B → (∀ x ∈ A ∪ B, x.2 = 1) →
        IsWalkFromTo (W.map (sigmaAC '' ·)) A B :=
  S4.tame_symm W hW i h hT

theorem lem_4_8_one_proved {k : ℕ} (hk : 1 ≤ k) (A B : Set (Band k)) (hAB : IsSplit A B {b ⟨0, hk⟩}) :
    ∃ W h, IsWalkFromTo W A B ∧ W.length - 1 = 2 ∧ IsTameAt W ⟨0, hk⟩ h ∧ ∀ X ∈ W, ∀ x ∈ X, x.1.val = 0 :=
  S4.tame_base_one hk A B hAB

theorem lem_4_8_two_proved {k : ℕ} (hk : 2 ≤ k) (A B : Set (Band k)) (hAB : IsSplit A B {b ⟨0, by omega⟩, b ⟨1, hk⟩}) :
    ∃ W h, IsWalkFromTo W A B ∧ W.length - 1 = 3 ∧ IsTameAt W ⟨1, hk⟩ h ∧ ∀ X ∈ W, ∀ x ∈ X, x.1.val ≤ 1 :=
  S4.tame_base_two hk A B hAB

theorem lem_4_9_proved {k : ℕ} (i : ℕ) (hi : i + 2 < k) (W : List (Set (Band k))) (A' B' : Set (Band k)) (h : Band k)
    (hW : IsWalkFromTo W A' B') (hT : IsTameAt W ⟨i, by omega⟩ h) (hmid : ∀ x ∈ A' ∪ B', x.2 = 1)
    (A'' B'' : Set (Band k)) (hAB : IsSplit A'' B'' {b ⟨i + 1, by omega⟩, b ⟨i + 2, hi⟩}) :
    ∃ W' h', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + 1 ∧
      IsTameAt W' ⟨i + 2, hi⟩ h' :=
  S4.tame_ext i hi W A' B' h hW hT hmid A'' B'' hAB

theorem cor_4_10_proved {k : ℕ} (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) (r : Fin 3) (hr : r ≠ 1)
    (A B : Set (Band k)) (hAB : IsSplit A B {x | x.2 = 1 ∧ x.1.val < i}) :
    ∃ W h, IsWalkFromTo W A B ∧ W.length - 1 = i / 2 + 2 ∧ IsTameAt W ⟨i - 1, by omega⟩ h ∧ h.2 = r ∧
      ∀ X ∈ W, ∀ x ∈ X, x.1.val < i :=
  S4.tame_cor i hi hik r hr A B hAB

theorem lem_4_11_proved {k : ℕ} (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hL : i + j ≤ k) (r : Fin 3) (hr : r ≠ 1)
    (W : List (Set (Band k))) (A' B' : Set (Band k)) (hW : IsWalkFromTo W A' B') (hmid : ∀ x ∈ A' ∪ B', x.2 = 1)
    (hcols : ∀ X ∈ W, ∀ x ∈ X, x.1.val < i)
    (hc : ∃ X ∈ W, ((⟨i - 1, by omega⟩ : Fin k), Fin.rev r) ∈ X)
    (A'' B'' : Set (Band k)) (hAB : IsSplit A'' B'' (rowSeg r i (i + j - 1))) :
    ∃ W', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + j / 2 ∧
      ∀ X ∈ W', ∀ x ∈ X, x.1.val < i + j :=
  S4.junction i j hi hj hL r hr W A' B' hW hmid hcols hc A'' B'' hAB

theorem lem_4_12_proved {k : ℕ} (i j : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hL : i + j ≤ k) (r : Fin 3) (hr : r ≠ 1)
    (W : List (Set (Band k))) (A' B' : Set (Band k)) (h : Band k) (hW : IsWalkFromTo W A' B')
    (hT : IsTameAt W ⟨i - 2, by omega⟩ h) (hmid : ∀ x ∈ A' ∪ B', x.2 = 1)
    (A'' B'' : Set (Band k)) (hAB : IsSplit A'' B'' (insert (b ⟨i - 1, by omega⟩) (rowSeg r i (i + j - 1)))) :
    ∃ W', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + (j + 1) / 2 ∧
      ∀ X ∈ W', ∀ x ∈ X, x.1.val < i + j :=
  S4.half_junction i j hi hj hL r hr W A' B' h hW hT hmid A'' B'' hAB

theorem prop_4_13_proved (L : ℕ) (hL : 2 ≤ L) (U : Set (Band L)) (hU : IsAntichainSet U)
    (hfull : ∀ l : Fin L, ∃ x ∈ U, x.1 = l) (i : ℕ) (hi : ∀ x ∈ U, x.2 = 1 ↔ x.1.val < i)
    (A B : Set (Band L)) (hAB : IsSplit A B U) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 ≤ (if 1 ≤ i then (L + 1) / 2 + 1 else L / 2 + 1) :=
  S4.full_word L hL U hU hfull i hi A B hAB

theorem lem_4_14_proved :
    (∀ p q : ℕ, 3 * (p + 1) / 4 + 3 * (q + 1) / 4 ≤ 3 * (p + q + 1 + 1) / 4) ∧
      (∀ k : ℕ, 2 ≤ k → (k + 1) / 2 + 1 ≤ 3 * (k + 1) / 4) ∧ 3 * (0 + 1) / 4 = 0 ∧ 3 * (1 + 1) / 4 = 1 :=
  ⟨fun p q => by omega, fun k hk => by
    rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h | h | h | h <;> omega,
    by norm_num, by norm_num⟩

theorem thm_4_1_walks_proved (k : ℕ) (A B U : Set (Band k)) (hAB : IsSplit A B U) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 ≤ 3 * (k + 1) / 4 :=
  S4.chain_walks k U A B hAB

/-- Theorem 4.1 from its walks: by Lemma 2.4 the chain distance is attained at a split, and a split of `U` has a walk
of length at most `⌊3(k+1)/4⌋` (`thm_4_1_walks`). (The bound holds for every `k`.) -/
theorem thm_4_1_proved (k : ℕ) (_hk : 1 ≤ k) : chainDiam (Band k) ≤ ((3 * (k + 1) / 4 : ℕ) : ℕ∞) := by
  rw [chainDiam_le_iff]
  intro X Y hX hY
  obtain ⟨A, B, hA, hB, -, -, hsplit, hle⟩ := (lem_2_4_proved (Band k)).1 X Y hX hY
  obtain ⟨W, hW, hlen⟩ := thm_4_1_walks_proved k A B (A ∪ B) hsplit
  exact hle.trans ((sec2_walk_dist_proved W A B hA hB hW).trans (by exact_mod_cast hlen))

theorem sec4_overview_fullword_proved {k : ℕ} (hk : 2 ≤ k) (U : Set (Band k)) (hU : IsAntichainSet U)
    (hfull : ∀ l : Fin k, ∃ x ∈ U, x.1 = l) (A B : Set (Band k)) (hAB : IsSplit A B U) :
    ∃ W, IsWalkFromTo W A B ∧ W.length - 1 ≤ (k + 1) / 2 + 1 :=
  S4.overview_fullword hk U hU hfull A B hAB

theorem table_2_line1_proved {k : ℕ} (hk : 1 ≤ k) :
    IsWalk [{Band.b ⟨0, hk⟩}, {Band.c ⟨0, hk⟩}, (∅ : Set (Band k))] ∧
    outerTrace [{Band.b ⟨0, hk⟩}, {Band.c ⟨0, hk⟩}, (∅ : Set (Band k))] ⟨0, hk⟩ =
      [none, some (Band.c ⟨0, hk⟩), none] :=
  S4.table_2_line1 hk

theorem table_2_lines23_proved {k : ℕ} (hk : 2 ≤ k) :
    IsWalk [∅, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨0, by omega⟩, Band.b ⟨1, hk⟩} : Set (Band k))] ∧
    outerTrace [∅, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨0, by omega⟩, Band.b ⟨1, hk⟩} : Set (Band k))] ⟨1, hk⟩ = [none, some (Band.c ⟨1, hk⟩), none] ∧
    IsWalk [{Band.b ⟨0, by omega⟩}, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨1, hk⟩} : Set (Band k))] ∧
    outerTrace [{Band.b ⟨0, by omega⟩}, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨1, hk⟩} : Set (Band k))] ⟨1, hk⟩ = [none, some (Band.c ⟨1, hk⟩), none] ∧
    Band.a ⟨0, by omega⟩ < (Band.c ⟨1, hk⟩ : Band k) ∧ Band.b ⟨1, hk⟩ < (Band.c ⟨0, by omega⟩ : Band k) :=
  S4.table_2_lines23 hk

theorem lem_4_9_V_proved {k : ℕ} (q r : Fin k) (hqr : r.val = q.val + 1) :
    IsWalk [∅, {Band.a q}, {Band.c q, Band.c r}, ({Band.b q, Band.b r} : Set (Band k))] ∧
    IsWalk [{Band.b r}, {Band.a q, Band.a r}, {Band.c q}, ({Band.b q} : Set (Band k))] ∧
    Band.a q < Band.c q ∧ Band.a q < Band.c r ∧ Band.b q < Band.c q ∧ Band.b r < Band.c q ∧
    Band.b r < Band.c r ∧ Band.a q < Band.b r ∧ Band.a r < Band.b r ∧ Band.a r < Band.c q :=
  S4.lem_4_9_V q r hqr

theorem lem_4_12_columns_proved {k : ℕ} (e : Fin k) :
    IsWalk [{Band.b e}, {Band.c e}, {Band.a e}, (∅ : Set (Band k))] ∧
    IsWalk [∅, {Band.c e}, {Band.a e}, ({Band.b e} : Set (Band k))] :=
  S4.lem_4_12_columns e

end LeeDiam
