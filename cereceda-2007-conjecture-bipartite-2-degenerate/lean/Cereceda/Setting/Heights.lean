/-
Cereceda/Setting/Heights.lean — heights on trees (before Lemma 2.4) and Lemma 2.4 (one tree).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Basic

namespace Cereceda

open Finset

namespace Heights

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ### Residues as integer congruences -/

lemma intCast_eq_res_iff (z : ℤ) (y : Fin 4) : ((z : ℤ) : ZMod 3) = res y ↔ (3 : ℤ) ∣ z - y.val := by
  unfold res
  rw [← Int.cast_natCast, ZMod.intCast_eq_intCast_iff_dvd_sub, ← dvd_neg, neg_sub]
  norm_num

lemma abs_sub_eq_one (a b : ℤ) : |a - b| = 1 ↔ a = b + 1 ∨ b = a + 1 := by
  rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
  omega

/-- A height in integer form: `3 ∣ h v - c v` and adjacent heights differ by one. -/
def IsHt (H : SimpleGraph W) (c : W → Fin 4) (h : W → ℤ) : Prop :=
  (∀ v, (3 : ℤ) ∣ h v - (c v).val) ∧ ∀ u v, H.Adj u v → h u = h v + 1 ∨ h v = h u + 1

omit [Fintype W] [DecidableEq W] in
lemma isHeight_iff (H : SimpleGraph W) (c : W → Fin 4) (h : W → ℤ) : IsHeight H c h ↔ IsHt H c h := by
  unfold IsHeight IsHt
  simp only [intCast_eq_res_iff, abs_sub_eq_one]

lemma val_pos {y : Fin 4} (hy : y ≠ 0) : 0 < y.val := by
  revert y; decide

lemma mem123_iff (y : Fin 4) : y ∈ ({1, 2, 3} : Finset (Fin 4)) ↔ 0 < y.val := by
  revert y; decide

/-- Colours in `{1,2,3}` are determined by their residue. -/
lemma eq_of_dvd {y y' : Fin 4} (hy : 0 < y.val) (hy' : 0 < y'.val) (h : (3 : ℤ) ∣ (y.val : ℤ) - y'.val) :
    y = y' := by
  have := y.isLt; have := y'.isLt
  exact Fin.ext (by omega)

/-- Every residue is the residue of a colour in `{1,2,3}`. -/
lemma exists_col (z : ℤ) : ∃ y : Fin 4, 0 < y.val ∧ (3 : ℤ) ∣ z - y.val := by
  have : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
  rcases this with h | h | h
  · exact ⟨⟨3, by omega⟩, by simp, by simp; omega⟩
  · exact ⟨⟨1, by omega⟩, by simp, by simp; omega⟩
  · exact ⟨⟨2, by omega⟩, by simp, by simp; omega⟩

/-! ### Existence of heights on a tree (sum of signed steps along the path from a root) -/

/-- The signed step from colour `a` to colour `b`: `+1` if `b ≡ a + 1 (mod 3)`, else `-1`. -/
def eps (a b : Fin 4) : ℤ := if (3 : ℤ) ∣ (b.val : ℤ) - a.val - 1 then 1 else -1

lemma eps_spec {a b : Fin 4} (ha : 0 < a.val) (hb : 0 < b.val) (hab : a ≠ b) :
    (3 : ℤ) ∣ (b.val : ℤ) - a.val - eps a b := by
  have := a.isLt; have := b.isLt
  have : a.val ≠ b.val := fun h => hab (Fin.ext h)
  unfold eps; split_ifs with h <;> omega

lemma eps_cases (a b : Fin 4) : eps a b = 1 ∨ eps a b = -1 := by
  unfold eps; split_ifs <;> simp

/-- The sum of the signed steps along the darts of a walk. -/
def wsum (T : SimpleGraph W) (c : W → Fin 4) {u v : W} (p : T.Walk u v) : ℤ :=
  (p.darts.map fun d => eps (c d.fst) (c d.snd)).sum

omit [Fintype W] [DecidableEq W] in
lemma wsum_concat (T : SimpleGraph W) (c : W → Fin 4) {u v w : W} (p : T.Walk u v) (hvw : T.Adj v w) :
    wsum T c (p.concat hvw) = wsum T c p + eps (c v) (c w) := by
  simp [wsum, SimpleGraph.Walk.darts_concat]

omit [Fintype W] [DecidableEq W] in
lemma wsum_dvd (T : SimpleGraph W) (c : W → Fin 4) (hc : IsProperFn T c) (h0 : ∀ v, c v ≠ 0) {u v : W}
    (p : T.Walk u v) : (3 : ℤ) ∣ wsum T c p - ((c v).val - (c u).val) := by
  induction p with
  | nil => simp [wsum]
  | cons hadj p ih =>
    simp only [wsum, SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons] at ih ⊢
    have := eps_spec (val_pos (h0 _)) (val_pos (h0 _)) (hc _ _ hadj)
    omega

omit [Fintype W] in
/-- On an edge `u v` of a tree, the path from the root to one end is the path to the other end plus the edge. -/
lemma path_adj (T : SimpleGraph W) (hT : T.IsAcyclic) {r : W} (pth : ∀ v, T.Walk r v)
    (hpth : ∀ v, (pth v).IsPath) {u v : W} (huv : T.Adj u v) :
    pth v = (pth u).concat huv ∨ pth u = (pth v).concat huv.symm := by
  by_cases hu : u ∈ (pth v).support
  · exact Or.inl (hT.path_concat (hpth u) (hpth v) huv hu)
  · have hv := hT.mem_support_of_ne_mem_support_of_adj_of_isPath (hpth u) (hpth v) huv hu
    exact Or.inr (hT.path_concat (hpth v) (hpth u) huv.symm hv)

/-! ### Uniqueness of heights on a connected graph -/

omit [Fintype W] [DecidableEq W] in
lemma diff_adj {H : SimpleGraph W} {c : W → Fin 4} {h h' : W → ℤ} (hh : IsHt H c h) (hh' : IsHt H c h')
    {u v : W} (huv : H.Adj u v) : h' u - h u = h' v - h v := by
  have h1 := hh.1 u; have h2 := hh'.1 u; have h3 := hh.1 v; have h4 := hh'.1 v
  rcases hh.2 u v huv with h5 | h5 <;> rcases hh'.2 u v huv with h6 | h6 <;> omega

omit [Fintype W] [DecidableEq W] in
lemma diff_walk {H : SimpleGraph W} {c : W → Fin 4} {h h' : W → ℤ} (hh : IsHt H c h) (hh' : IsHt H c h')
    {u v : W} (p : H.Walk u v) : h' u - h u = h' v - h v := by
  induction p with
  | nil => rfl
  | cons hadj p ih => exact (diff_adj hh hh' hadj).trans ih

/-! ### Lemma 2.4 on an arbitrary graph `H` with lists `A ⊆ {1,2,3}` -/

/-- The hypotheses of Lemma 2.4, in integer form, on a graph `H` with lists `A`. `big`: at every vertex either the
list contains `{1,2,3}`, or `|E v| ≤ 2`. -/
structure Setup (H : SimpleGraph W) (A : W → Finset (Fin 4)) (c c' : W → Fin 4) (h E : W → ℤ) : Prop where
  cA : ∀ v, c v ∈ A v
  c'A : ∀ v, c' v ∈ A v
  hh : IsHt H c h
  hE : ∀ v, Even (E v)
  hhE : IsHt H c' (h + E)
  big : ∀ v, (∀ y : Fin 4, 0 < y.val → y ∈ A v) ∨ (-2 ≤ E v ∧ E v ≤ 2)

variable {H : SimpleGraph W} {A : W → Finset (Fin 4)}

omit [Fintype W] in
lemma update_add (h E : W → ℤ) (v : W) (d : ℤ) :
    Function.update h v (h v + 2 * d) + Function.update E v (E v - 2 * d) = h + E := by
  funext w
  simp only [Pi.add_apply, Function.update_apply]
  split_ifs with hw
  · subst hw; ring
  · rfl

omit [Fintype W] in
/-- The colouring after the move is in the lists. -/
lemma step_cA {c : W → Fin 4} (hcA : ∀ v, c v ∈ A v) {v : W} {y : Fin 4} (hy : y ∈ A v) :
    ∀ w, Function.update c v y w ∈ A w := by
  intro w
  rw [Function.update_apply]
  split_ifs with hw
  · subst hw; exact hy
  · exact hcA w

omit [Fintype W] in
/-- The colouring after the move has the height `h + 2d[v]`. -/
lemma step_hh {c : W → Fin 4} {h : W → ℤ} (hh : IsHt H c h) {v : W} {d : ℤ} (hd : d = 1 ∨ d = -1)
    (hnb : ∀ u, H.Adj v u → h u = h v + d) {y : Fin 4} (hy : (3 : ℤ) ∣ h v + 2 * d - y.val) :
    IsHt H (Function.update c v y) (Function.update h v (h v + 2 * d)) := by
  refine ⟨fun w => ?_, fun a b hab => ?_⟩
  · simp only [Function.update_apply]
    split_ifs with hw
    · subst hw; exact hy
    · exact hh.1 w
  · simp only [Function.update_apply]
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) (H.ne_of_adj hab)
    · subst ha; have := hnb b hab; rcases hd with rfl | rfl <;> omega
    · subst hb; have := hnb a hab.symm; rcases hd with rfl | rfl <;> omega
    · exact hh.2 a b hab

omit [Fintype W] in
/-- One move: recolour `v` (all of whose neighbours have height `h v + d`, and `E v` has the sign of `d`) to the
colour of residue `h v + 2d`. -/
lemma step (hA : ∀ v y, y ∈ A v → 0 < y.val) {c c' : W → Fin 4} {h E : W → ℤ} (S : Setup H A c c' h E)
    (v : W) (d : ℤ) (hd : d = 1 ∨ d = -1) (hdE : 0 < d * E v) (hnb : ∀ u, H.Adj v u → h u = h v + d) :
    ∃ y, LegalMove H A c (v, y) ∧
      Setup H A (Function.update c v y) c' (Function.update h v (h v + 2 * d))
        (Function.update E v (E v - 2 * d)) := by
  obtain ⟨y, hy0, hy⟩ := exists_col (h v + 2 * d)
  have hv := S.hh.1 v
  obtain ⟨k, hk⟩ := S.hE v
  have hyA : y ∈ A v := by
    rcases S.big v with hall | hle
    · exact hall y hy0
    · have h' := S.hhE.1 v
      simp only [Pi.add_apply] at h'
      have : y = c' v := eq_of_dvd hy0 (hA v _ (S.c'A v)) (by rcases hd with rfl | rfl <;> omega)
      rw [this]; exact S.c'A v
  refine ⟨y, ?_, ?_⟩
  · simp only [LegalMove]
    refine ⟨fun hyc => ?_, hyA, fun u hu hcu => ?_⟩
    · subst hyc; rcases hd with rfl | rfl <;> omega
    · have h1 := S.hh.1 u; have h2 := hnb u hu
      rw [hcu] at h1; rcases hd with rfl | rfl <;> omega
  · refine ⟨step_cA S.cA hyA, S.c'A, step_hh S.hh hd hnb hy, fun w => ?_, ?_, fun w => ?_⟩
    · rw [Function.update_apply]
      split_ifs
      · exact (S.hE v).sub (even_two_mul d)
      · exact S.hE w
    · rw [update_add]; exact S.hhE
    · rw [Function.update_apply]
      split_ifs with hw
      · subst hw
        rcases S.big w with hall | hle
        · exact Or.inl hall
        · right; rcases hd with rfl | rfl <;> omega
      · exact S.big w

lemma sum_update_natAbs (E : W → ℤ) (v : W) (e : ℤ) :
    ∑ w, (Function.update E v e w).natAbs + (E v).natAbs = ∑ w, (E w).natAbs + e.natAbs := by
  rw [Fintype.sum_eq_add_sum_compl v, Fintype.sum_eq_add_sum_compl v (fun w => (E w).natAbs)]
  simp only [Function.update_self]
  rw [Finset.sum_congr rfl (fun w hw => by rw [Function.update_of_ne (by simpa using hw)])]
  ring

omit [DecidableEq W] in
/-- If `E` has a positive value, a vertex with `E v > 0` and `h v` least has all neighbours at height `h v + 1`. -/
lemma exists_pos_min {c c' : W → Fin 4} {h E : W → ℤ} (S : Setup H A c c' h E) (hpos : ∃ v, 0 < E v) :
    ∃ v, 0 < E v ∧ ∀ u, H.Adj v u → h u = h v + 1 := by
  obtain ⟨v, hvs, hmin⟩ := (univ.filter (fun w => 0 < E w)).exists_min_image h (by
    obtain ⟨w, hw⟩ := hpos; exact ⟨w, by simpa using hw⟩)
  simp only [mem_filter, mem_univ, true_and] at hvs hmin
  refine ⟨v, hvs, fun u hu => ?_⟩
  obtain ⟨k, hk⟩ := S.hE v
  have h2 := S.hhE.2 v u hu
  simp only [Pi.add_apply] at h2
  rcases S.hh.2 v u hu with h1 | h1
  · exfalso
    have := hmin u (by omega)
    omega
  · omega

omit [DecidableEq W] in
/-- Symmetric: a vertex with `E v < 0` and `h v` largest has all neighbours at height `h v - 1`. -/
lemma exists_neg_max {c c' : W → Fin 4} {h E : W → ℤ} (S : Setup H A c c' h E) (hneg : ∃ v, E v < 0) :
    ∃ v, E v < 0 ∧ ∀ u, H.Adj v u → h u = h v + -1 := by
  obtain ⟨v, hvs, hmax⟩ := (univ.filter (fun w => E w < 0)).exists_max_image h (by
    obtain ⟨w, hw⟩ := hneg; exact ⟨w, by simpa using hw⟩)
  simp only [mem_filter, mem_univ, true_and] at hvs hmax
  refine ⟨v, hvs, fun u hu => ?_⟩
  obtain ⟨k, hk⟩ := S.hE v
  have h2 := S.hhE.2 v u hu
  simp only [Pi.add_apply] at h2
  rcases S.hh.2 v u hu with h1 | h1
  · omega
  · exfalso
    have := hmax u (by omega)
    omega

/-- The conclusion of Lemma 2.4 for the sum `n = ∑ |E v|`. -/
def Concl (H : SimpleGraph W) (A : W → Finset (Fin 4)) (c c' : W → Fin 4) (E : W → ℤ) (n : ℕ) : Prop :=
  ∃ ms, IsSeq H A c ms c' ∧ 2 * ms.length = n ∧ ∀ v, 2 * movesOf ms v = (E v).natAbs

/-- The induction step: one move at `v`, then the induction hypothesis. -/
lemma induct_step (hA : ∀ v y, y ∈ A v → 0 < y.val) {n : ℕ}
    (ih : ∀ m < n, ∀ c c' h E, Setup H A c c' h E → ∑ v, (E v).natAbs = m → Concl H A c c' E m)
    {c c' : W → Fin 4} {h E : W → ℤ} (S : Setup H A c c' h E) (hn : ∑ v, (E v).natAbs = n)
    (v : W) (d : ℤ) (hd : d = 1 ∨ d = -1) (hdE : 0 < d * E v) (hnb : ∀ u, H.Adj v u → h u = h v + d) :
    Concl H A c c' E n := by
  obtain ⟨y, hlegal, S'⟩ := step hA S v d hd hdE hnb
  have hsum := sum_update_natAbs E v (E v - 2 * d)
  obtain ⟨k, hk⟩ := S.hE v
  have habs : (E v - 2 * d).natAbs + 2 = (E v).natAbs := by rcases hd with rfl | rfl <;> omega
  obtain ⟨ms, hseq, hlen, hmov⟩ := ih _ (by omega) _ _ _ _ S' rfl
  refine ⟨(v, y) :: ms, ⟨hlegal, hseq⟩, ?_, fun w => ?_⟩
  · simp only [List.length_cons]; omega
  · have := hmov w
    simp only [movesOf, List.countP_cons] at this ⊢
    by_cases hw : w = v
    · subst hw
      simp only [Function.update_self] at this
      simp only [decide_true, ↓reduceIte]
      omega
    · rw [Function.update_of_ne hw] at this
      simp only [Ne.symm hw, decide_false, Bool.false_eq_true, ↓reduceIte]
      omega

/-- Lemma 2.4 on any graph: induction on `∑ |E|`. -/
theorem main (hA : ∀ v y, y ∈ A v → 0 < y.val) (n : ℕ) :
    ∀ c c' h E, Setup H A c c' h E → ∑ v, (E v).natAbs = n → Concl H A c c' E n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c c' h E S hn
  by_cases hpos : ∃ v, 0 < E v
  · obtain ⟨v, hv, hnb⟩ := exists_pos_min S hpos
    exact induct_step hA ih S hn v 1 (Or.inl rfl) (by omega) hnb
  by_cases hneg : ∃ v, E v < 0
  · obtain ⟨v, hv, hnb⟩ := exists_neg_max S hneg
    exact induct_step hA ih S hn v (-1) (Or.inr rfl) (by omega) hnb
  simp only [not_exists, not_lt] at hpos hneg
  have hE0 : ∀ v, E v = 0 := fun v => le_antisymm (hpos v) (hneg v)
  have hcc : c' = c := by
    funext w
    have h1 := S.hh.1 w; have h2 := S.hhE.1 w
    simp only [Pi.add_apply, hE0, add_zero] at h2
    exact eq_of_dvd (hA w _ (S.c'A w)) (hA w _ (S.cA w)) (by omega)
  refine ⟨[], hcc, ?_, fun v => ?_⟩
  · simp [← hn, hE0]
  · simp [movesOf, hE0]

end Heights

open Heights

theorem height_exists_proved {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) (hT : T.IsTree)
    (c : W → Fin 4) (hc : IsProperFn T c) (h0 : ∀ v, c v ≠ 0) : ∃ h, IsHeight T c h := by
  obtain ⟨r⟩ := hT.connected.nonempty
  choose pth hpth using fun v => (hT.existsUnique_path r v).exists
  refine ⟨fun v => (c r).val + wsum T c (pth v), (isHeight_iff T c _).mpr ⟨fun v => ?_, fun u v huv => ?_⟩⟩
  · have := wsum_dvd T c hc h0 (pth v)
    beta_reduce
    omega
  · rcases path_adj T hT.isAcyclic pth hpth huv with e | e
    · simp only [e, wsum_concat]
      rcases eps_cases (c u) (c v) with h1 | h1 <;> omega
    · simp only [e, wsum_concat]
      rcases eps_cases (c v) (c u) with h1 | h1 <;> omega

theorem height_unique_proved {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) (hT : T.Connected)
    (c : W → Fin 4) (h h' : W → ℤ) (hh : IsHeight T c h) (hh' : IsHeight T c h') :
    ∃ k : ℤ, ∀ v, h' v = h v + 3 * k := by
  rw [isHeight_iff] at hh hh'
  obtain ⟨v₀⟩ := hT.nonempty
  have h1 := hh.1 v₀; have h2 := hh'.1 v₀
  obtain ⟨k, hk⟩ : (3 : ℤ) ∣ h' v₀ - h v₀ := by
    have := dvd_sub h2 h1; rwa [sub_sub_sub_cancel_right] at this
  refine ⟨k, fun v => ?_⟩
  obtain ⟨p⟩ := hT.preconnected v₀ v
  have := diff_walk hh hh' p
  omega

theorem lem_2_4_proved {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) (hT : T.IsTree) (r : W)
    (P : Finset (Fin 4)) (hP : P ⊆ {1, 2, 3}) (c c' : W → Fin 4) (hc : IsProperFn T c) (hc' : IsProperFn T c')
    (hcA : ∀ v, c v ∈ treeLists r P v) (hc'A : ∀ v, c' v ∈ treeLists r P v)
    (h E : W → ℤ) (hh : IsHeight T c h) (hE : ∀ v, Even (E v)) (hhE : IsHeight T c' (h + E))
    (hr : P.card ≤ 2 → |E r| ≤ 2) :
    ∃ ms, IsSeq T (treeLists r P) c ms c' ∧ 2 * ms.length = ∑ v, (E v).natAbs ∧
      ∀ v, 2 * movesOf ms v = (E v).natAbs := by
  -- the argument needs neither the tree structure nor properness of `c, c'` (the heights are given)
  have hA : ∀ v y, y ∈ treeLists r P v → 0 < y.val := by
    intro v y hy
    unfold treeLists at hy
    split_ifs at hy
    · exact (mem123_iff y).mp (hP hy)
    · exact (mem123_iff y).mp hy
  have big : ∀ v, (∀ y : Fin 4, 0 < y.val → y ∈ treeLists r P v) ∨ (-2 ≤ E v ∧ E v ≤ 2) := by
    intro v
    unfold treeLists
    split_ifs with hv
    · subst hv
      by_cases hcard : P.card ≤ 2
      · exact Or.inr (abs_le.mp (hr hcard))
      · have hP3 : P = {1, 2, 3} :=
          Finset.eq_of_subset_of_card_le hP (by rw [show ({1, 2, 3} : Finset (Fin 4)).card = 3 from rfl]; omega)
        exact Or.inl fun y hy => hP3 ▸ (mem123_iff y).mpr hy
    · exact Or.inl fun y hy => (mem123_iff y).mpr hy
  exact main hA _ c c' h E ⟨hcA, hc'A, (isHeight_iff T c h).mp hh, hE, (isHeight_iff T c' _).mp hhE, big⟩ rfl

end Cereceda
