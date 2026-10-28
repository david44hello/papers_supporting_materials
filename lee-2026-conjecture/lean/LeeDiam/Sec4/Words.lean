/-
LeeDiam/Sec4/Words.lean — Section 4.1 of paper 004 (short v0.60, sec_chain.tex l. 12-31): words, runs, (P1)-(P2),
translations, Lemma 4.2 (connected sets by columns), σ, and outer traces.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Chain
import LeeDiam.Sec4.BandOrder
import LeeDiam.Sec4.Trace

namespace LeeDiam.S4

open Band

variable {k : ℕ}

/-! ### Words (l. 13) -/

theorem badPair_some_iff (r s : Fin 3) :
    BadPair (some r) (some s) ↔ (r.val = 0 ∧ s.val ≠ 0) ∨ (r.val = 2 ∧ s.val ≠ 2) := by
  fin_cases r <;> fin_cases s <;> simp [BadPair]

theorem not_badPair_none_left (v : Option (Fin 3)) : ¬ BadPair none v := by
  cases v <;> simp [BadPair]

theorem not_badPair_none_right (u : Option (Fin 3)) : ¬ BadPair u none := by
  rcases u with _ | r
  · simp [BadPair]
  · fin_cases r <;> simp [BadPair]

theorem word_exists (X : Set (Band k)) (hX : IsAntichainSet X) : ∃ w, X = ofWord w := by
  classical
  refine ⟨fun i => if h : ∃ x ∈ X, x.1 = i then some (Classical.choose h).2 else none, ?_⟩
  ext x
  simp only [ofWord, Set.mem_ofPred_eq]
  constructor
  · intro hx
    have h : ∃ y ∈ X, y.1 = x.1 := ⟨x, hx, rfl⟩
    rw [dite_eq_left h]
    obtain ⟨hy, hyx⟩ := Classical.choose_spec h
    rw [antichain_col hX hy hx hyx]
  · intro hw
    split_ifs at hw with h
    · obtain ⟨hy, hyx⟩ := Classical.choose_spec h
      have h2 : (Classical.choose h).2 = x.2 := Option.some_inj.1 hw
      have hcx : Classical.choose h = x := Prod.ext hyx h2
      rw [← hcx]
      exact hy

theorem word_antichain_iff (w : Fin k → Option (Fin 3)) :
    IsAntichainSet (ofWord w) ↔ ∀ i j : Fin k, j.val = i.val + 1 → ¬ BadPair (w i) (w j) := by
  constructor
  · intro hX i j hij hbad
    rw [isAntichainSet_iff_comp] at hX
    rcases hi : w i with _ | r
    · rw [hi] at hbad
      exact not_badPair_none_left _ hbad
    rcases hj : w j with _ | s
    · rw [hj] at hbad
      exact not_badPair_none_right _ hbad
    rw [hi, hj, badPair_some_iff] at hbad
    let x : Band k := (i, r)
    let y : Band k := (j, s)
    have hx : x ∈ ofWord w := hi
    have hy : y ∈ ofWord w := hj
    apply hX x hx y hy
    rw [comp_iff_val]
    have hx1 : x.1.val = i.val := rfl
    have hx2 : x.2.val = r.val := rfl
    have hy1 : y.1.val = j.val := rfl
    have hy2 : y.2.val = s.val := rfl
    have := r.isLt
    have := s.isLt
    omega
  · intro h
    rw [isAntichainSet_iff_comp]
    intro x hx y hy hc
    simp only [ofWord, Set.mem_ofPred_eq] at hx hy
    have key : ∀ u v : Band k, w u.1 = some u.2 → w v.1 = some v.2 → v.1.val = u.1.val + 1 →
        ¬ ((u.2.val = 0 ∧ v.2.val ≠ 0) ∨ (u.2.val = 2 ∧ v.2.val ≠ 2)) := by
      intro u v hu hv huv hb
      apply h u.1 v.1 huv
      rw [hu, hv, badPair_some_iff]
      exact hb
    rw [comp_iff_val] at hc
    have := x.2.isLt
    have := y.2.isLt
    by_cases hcol : x.1 = y.1
    · rw [hcol, hy] at hx
      have hrow := Option.some_inj.1 hx
      rw [Fin.ext_iff] at hrow hcol
      omega
    · rw [Fin.ext_iff] at hcol
      have k1 := key x y hx hy
      have k2 := key y x hy hx
      omega

/-! ### Runs (l. 13) -/

theorem run_form (U : Set (Band k)) (hU : IsAntichainSet U) (s e : ℕ)
    (hrun : ∀ l : Fin k, s ≤ l.val → l.val ≤ e → ∃ x ∈ U, x.1 = l) :
    ∃ (i : ℕ) (r : Fin 3), r ≠ 1 ∧ ∀ x ∈ U, s ≤ x.1.val → x.1.val ≤ e →
      (x.2 = 1 ↔ x.1.val < s + i) ∧ (x.2 ≠ 1 → x.2 = r) := by
  classical
  have hex : ∃ n, e < s + n ∨ ∃ x ∈ U, x.1.val = s + n ∧ x.2 ≠ 1 := ⟨e + 1, Or.inl (by omega)⟩
  have hi := Nat.find_spec hex
  have hmin' : ∀ m, m < Nat.find hex → ¬ (e < s + m ∨ ∃ x ∈ U, x.1.val = s + m ∧ x.2 ≠ 1) :=
    fun m hm => Nat.find_min hex hm
  generalize Nat.find hex = i at hi hmin'
  have hmin : ∀ x ∈ U, s ≤ x.1.val → x.1.val < s + i → x.2 = 1 := by
    intro x hx hs hlt
    by_contra hne
    exact hmin' (x.1.val - s) (by omega) (Or.inr ⟨x, hx, by omega, hne⟩)
  rcases hi with hi | ⟨x0, hx0, hx0c, hx0r⟩
  · refine ⟨i, 0, by decide, fun x hx hs he => ?_⟩
    have hb := hmin x hx hs (by omega)
    exact ⟨⟨fun _ => by omega, fun _ => hb⟩, fun h => absurd hb h⟩
  · have hr : x0.2.val ≠ 1 := fun h => hx0r (Fin.ext h)
    have claim : ∀ d, ∀ x ∈ U, x.1.val = s + i + d → x.1.val ≤ e → x.2 = x0.2 := by
      intro d
      induction d with
      | zero =>
        intro x hx hxc _
        rw [antichain_col hU hx hx0 (Fin.ext (by omega))]
      | succ d ih =>
        intro x hx hxc hxe
        have hxk := x.1.isLt
        obtain ⟨y, hy, hyc⟩ := hrun ⟨s + i + d, by omega⟩ (show s ≤ s + i + d by omega)
          (show s + i + d ≤ e by omega)
        have hyc' : y.1.val = s + i + d := by rw [hyc]
        have hyr := ih y hy hyc' (by omega)
        rw [antichain_next_row hU hx hy (by omega) (by rw [hyr]; exact hr), hyr]
    refine ⟨i, x0.2, hx0r, fun x hx hs he => ?_⟩
    by_cases hlt : x.1.val < s + i
    · have hb := hmin x hx hs hlt
      exact ⟨⟨fun _ => hlt, fun _ => hb⟩, fun h => absurd hb h⟩
    · have hxr := claim (x.1.val - (s + i)) x hx (by omega) he
      refine ⟨⟨fun h => ?_, fun h => absurd h hlt⟩, fun _ => hxr⟩
      exact absurd (hxr.symm.trans h) hx0r

/-! ### Translations (l. 20) -/

theorem colShift_fst_val {k' : ℕ} (d : ℕ) (hd : k + d ≤ k') (x : Band k) :
    (colShift d hd x).1.val = x.1.val + d := rfl

theorem colShift_snd {k' : ℕ} (d : ℕ) (hd : k + d ≤ k') (x : Band k) : (colShift d hd x).2 = x.2 := rfl

theorem colShift_injective {k' : ℕ} (d : ℕ) (hd : k + d ≤ k') : Function.Injective (colShift d hd) := by
  intro x y h
  rw [band_ext_iff] at h ⊢
  rw [colShift_fst_val, colShift_fst_val, colShift_snd, colShift_snd] at h
  omega

theorem colShift_le_iff {k' : ℕ} (d : ℕ) (hd : k + d ≤ k') (x y : Band k) :
    x ≤ y ↔ colShift d hd x ≤ colShift d hd y := by
  rw [le_iff_bandLe, le_iff_bandLe]
  unfold bandLe
  simp only [band_ext_iff, colShift_fst_val, colShift_snd]
  omega

theorem colShift_comp_iff {k' : ℕ} (d : ℕ) (hd : k + d ≤ k') (x y : Band k) :
    Comp (colShift d hd x) (colShift d hd y) ↔ Comp x y := by
  rw [comp_iff_val, comp_iff_val]
  simp only [colShift_fst_val, colShift_snd]
  omega

theorem translation {k' : ℕ} (d : ℕ) (hd : k + d ≤ k') :
    (∀ x y : Band k, x ≤ y ↔ colShift d hd x ≤ colShift d hd y) ∧
    (∀ X : Set (Band k), IsAntichainSet X ↔ IsAntichainSet (colShift d hd '' X)) ∧
    (∀ D : Set (Band k), IsConnSet D ↔ IsConnSet (colShift d hd '' D)) ∧
    (∀ W : List (Set (Band k)), IsWalk W → IsWalk (W.map (colShift d hd '' ·))) :=
  ⟨colShift_le_iff d hd, fun X => (isAntichainSet_image_iff _ (colShift_comp_iff d hd) X).symm,
    fun D => (isConnSet_image_iff _ (colShift_injective d hd) (colShift_comp_iff d hd) D).symm,
    fun W hW => isWalk_map _ (colShift_injective d hd) (colShift_comp_iff d hd) W hW⟩

/-! ### Lemma 4.2 (l. 22-26): connected sets by columns -/

theorem col_conn (F : Set (Band k)) (hF : F.Nonempty) :
    IsConnSet F ↔
      (∀ x ∈ F, ∀ y ∈ F, ∀ l : Fin k, x.1 ≤ l → l ≤ y.1 → ∃ z ∈ F, z.1 = l) ∧
      ∀ x ∈ F, ∀ y ∈ F, y.1.val = x.1.val + 1 →
        ∃ x' ∈ F, ∃ y' ∈ F, x'.1 = x.1 ∧ y'.1 = y.1 ∧ Comp x' y' := by
  constructor
  · intro hc
    refine ⟨?_, ?_⟩
    · intro x hx y hy l hxl hly
      by_contra hno
      have hno' : ∀ z ∈ F, z.1 ≠ l := fun z hz hzl => hno ⟨z, hz, hzl⟩
      have hxl' : x.1 < l := lt_of_le_of_ne hxl (hno' x hx)
      obtain ⟨u, hu, v, hv, hQu, hQv, huv⟩ :=
        isConnSet_cross hc (fun z => z.1 < l) hx hy hxl' (not_lt.2 hly)
      have h1 : u.1.val < l.val := hQu
      have h2 : ¬ v.1.val < l.val := hQv
      have h3 := comp_cols huv
      exact hno' v hv (Fin.ext (by omega))
    · intro x hx y hy hxy
      obtain ⟨u, hu, v, hv, hQu, hQv, huv⟩ :=
        isConnSet_cross hc (fun z => z.1.val ≤ x.1.val) hx hy (le_refl x.1.val)
          (show ¬ y.1.val ≤ x.1.val by omega)
      have h1 : u.1.val ≤ x.1.val := hQu
      have h2 : ¬ v.1.val ≤ x.1.val := hQv
      have h3 := comp_cols huv
      exact ⟨u, hu, v, hv, Fin.ext (by omega), Fin.ext (by omega), huv⟩
  · rintro ⟨hint, hnb⟩
    obtain ⟨x0, hx0⟩ := hF
    let R := fun u v : Band k => u ∈ F ∧ v ∈ F ∧ Comp u v
    have hsymm : ∀ u v, Relation.ReflTransGen R u v → Relation.ReflTransGen R v u := by
      intro u v h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hpq ih => exact Relation.ReflTransGen.head ⟨hpq.2.1, hpq.1, comp_symm hpq.2.2⟩ ih
    have hcol : ∀ u ∈ F, ∀ v ∈ F, u.1 = v.1 → Relation.ReflTransGen R u v := by
      intro u hu v hv huv
      by_cases h : u = v
      · rw [h]
      · exact Relation.ReflTransGen.single ⟨hu, hv, comp_of_col huv h⟩
    have hstep : ∀ n, ∀ u ∈ F, ∀ v ∈ F, v.1.val = u.1.val + n → Relation.ReflTransGen R u v := by
      intro n
      induction n with
      | zero => intro u hu v hv h; exact hcol u hu v hv (Fin.ext (by omega))
      | succ n ih =>
        intro u hu v hv h
        have hvk := v.1.isLt
        obtain ⟨z, hz, hzl⟩ := hint u hu v hv ⟨u.1.val + 1, by omega⟩
          (show u.1.val ≤ u.1.val + 1 by omega) (show u.1.val + 1 ≤ v.1.val by omega)
        have hz1 : z.1.val = u.1.val + 1 := by rw [hzl]
        obtain ⟨x', hx', y', hy', hx'1, hy'1, hc⟩ := hnb u hu z hz hz1
        have hy'v : v.1.val = y'.1.val + n := by rw [hy'1]; omega
        exact (hcol u hu x' hx' hx'1.symm).trans
          (Relation.ReflTransGen.head ⟨hx', hy', hc⟩ (ih y' hy' v hv hy'v))
    refine isConnSet_of_rtg hx0 (fun y hy => ?_)
    by_cases h : x0.1.val ≤ y.1.val
    · exact hstep (y.1.val - x0.1.val) x0 hx0 y hy (by omega)
    · exact hsymm _ _ (hstep (x0.1.val - y.1.val) y hy x0 hx0 (by omega))

/-! ### σ (l. 29) -/

theorem sigma_sigma (x : Band k) : sigmaAC (sigmaAC x) = x := Prod.ext rfl (Fin.rev_rev _)

theorem sigma_injective : Function.Injective (sigmaAC (k := k)) := by
  intro x y h
  rw [← sigma_sigma x, h, sigma_sigma]

theorem sigma_fst (x : Band k) : (sigmaAC x).1 = x.1 := rfl

theorem sigma_snd_val (x : Band k) : (sigmaAC x).2.val = 2 - x.2.val := by
  show (Fin.rev x.2).val = 2 - x.2.val
  rw [Fin.val_rev]
  omega

theorem sigma_mid {x : Band k} (h : x.2 = 1) : sigmaAC x = x := by
  refine Prod.ext ?_ ?_
  · rfl
  show Fin.rev x.2 = x.2
  rw [h]
  decide

theorem sigma_le_iff (x y : Band k) : x ≤ y ↔ sigmaAC y ≤ sigmaAC x := by
  rw [le_iff_bandLe, le_iff_bandLe]
  unfold bandLe
  simp only [band_ext_iff, sigma_snd_val, sigma_fst]
  have := x.2.isLt
  have := y.2.isLt
  omega

theorem sigma_comp_iff (x y : Band k) : Comp (sigmaAC x) (sigmaAC y) ↔ Comp x y := by
  rw [comp_iff_val, comp_iff_val]
  simp only [sigma_snd_val, sigma_fst]
  have := x.2.isLt
  have := y.2.isLt
  omega

theorem sigma_mem_image_iff {X : Set (Band k)} {x : Band k} : x ∈ sigmaAC '' X ↔ sigmaAC x ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [sigma_sigma]
  · intro h
    exact ⟨sigmaAC x, h, sigma_sigma x⟩

theorem sigma_image_mid {X : Set (Band k)} (hX : ∀ x ∈ X, x.2 = 1) : sigmaAC '' X = X := by
  ext x
  rw [sigma_mem_image_iff]
  constructor
  · intro h
    have hm : (sigmaAC x).2 = 1 := hX _ h
    have hv : x.2.val = 1 := by
      have h1 := sigma_snd_val x
      rw [hm, Fin.val_one] at h1
      have h3 := x.2.isLt
      omega
    have hx : x.2 = 1 := Fin.ext hv
    rwa [sigma_mid hx] at h
  · intro h
    rwa [sigma_mid (hX x h)]

theorem sigma_props :
    (∀ x y : Band k, x ≤ y ↔ sigmaAC y ≤ sigmaAC x) ∧ (∀ x y : Band k, Comp x y ↔ Comp (sigmaAC x) (sigmaAC y)) ∧
    (∀ W : List (Set (Band k)), IsWalk W → IsWalk (W.map (sigmaAC '' ·))) ∧
    (∀ w : Fin k → Option (Fin 3), sigmaAC '' ofWord w = ofWord (fun i => (w i).map Fin.rev)) ∧
    (∀ X : Set (Band k), (∀ x ∈ X, x.2 = 1) → sigmaAC '' X = X) := by
  refine ⟨sigma_le_iff, fun x y => (sigma_comp_iff x y).symm,
    fun W hW => isWalk_map _ sigma_injective sigma_comp_iff W hW, fun w => ?_, fun X hX => sigma_image_mid hX⟩
  ext x
  rw [sigma_mem_image_iff]
  simp only [ofWord, Set.mem_ofPred_eq, sigma_fst]
  show w x.1 = some (Fin.rev x.2) ↔ (w x.1).map Fin.rev = some x.2
  rcases w x.1 with _ | r
  · simp
  · show some r = some (Fin.rev x.2) ↔ some (Fin.rev r) = some x.2
    rw [Option.some_inj, Option.some_inj]
    constructor
    · intro h; rw [h, Fin.rev_rev]
    · intro h; rw [← h, Fin.rev_rev]

/-! ### Outer traces (l. 31) -/

theorem outerAt_of_a_mem {X : Set (Band k)} {e : Fin k} (h : a e ∈ X) : outerAt X e = some (a e) := by
  unfold outerAt
  rw [ite_eq_left h]

theorem outerAt_of_c_mem {X : Set (Band k)} {e : Fin k} (ha : a e ∉ X) (h : c e ∈ X) :
    outerAt X e = some (c e) := by
  unfold outerAt
  rw [ite_eq_right ha, ite_eq_left h]

theorem outerAt_none {X : Set (Band k)} {e : Fin k} (ha : a e ∉ X) (hc : c e ∉ X) : outerAt X e = none := by
  unfold outerAt
  rw [ite_eq_right ha, ite_eq_right hc]

theorem a_ne_b (i j : Fin k) : a i ≠ b j := band_ne_of_row (by simp)
theorem a_ne_c (i j : Fin k) : a i ≠ c j := band_ne_of_row (by simp)
theorem b_ne_c (i j : Fin k) : b i ≠ c j := band_ne_of_row (by simp)

theorem trace_example (e : Fin k) :
    outerTrace [{b e}, {c e}, {a e}, ∅] e = [none, some (c e), some (a e), none] := by
  unfold outerTrace
  simp only [List.map_cons, List.map_nil]
  have h1 : outerAt ({b e} : Set (Band k)) e = none :=
    outerAt_none (by simpa using a_ne_b e e) (by simpa using (b_ne_c e e).symm)
  have h2 : outerAt ({c e} : Set (Band k)) e = some (c e) :=
    outerAt_of_c_mem (by simpa using a_ne_c e e) (Set.mem_singleton _)
  have h3 : outerAt ({a e} : Set (Band k)) e = some (a e) := outerAt_of_a_mem (Set.mem_singleton _)
  have h4 : outerAt (∅ : Set (Band k)) e = none := outerAt_none (by simp) (by simp)
  rw [h1, h2, h3, h4]
  exact List.destutter_of_isChain _ _ (by simp [(a_ne_c e e).symm])

end LeeDiam.S4
