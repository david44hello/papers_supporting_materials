/-
Cereceda/LB/PathCore.lean — path-level cores of Lemmas 4.2 (lem:h1), 4.3 (lem:flat), 4.7 (lem:flat4) and of the
first case of Proposition 4.1 of the paper (short version; Section 4). Imports Mathlib only; no paper definitions.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Encoding-free form. A path v_1 … v_n is read 0-based (position i is v_{i+1}). `col i : ZMod 3` is the residue of the
colour of position i (in a plain colouring the path uses only 0, 1, 2, so residue = colour). A height `h : ℕ → ℤ` moves
by ±1 at every step, in step with the colour (paper: s_i = col(v_{i+1}) - col(v_i) ∈ {+1, -1} mod 3, h(i+1) - h(i) = s_i).
"A can move to c" = no position of one class has colour c (the class of a vertex's path neighbours).
-/
import Mathlib

namespace Cereceda.PathAux

/-- `h` is a height of the path colouring `col` on positions `0 … n-1`: each step is `+1` or `-1`, in both. -/
def StepHeight (n : ℕ) (col : ℕ → ZMod 3) (h : ℕ → ℤ) : Prop :=
  ∀ i, i + 1 < n → (h (i + 1) = h i + 1 ∧ col (i + 1) = col i + 1) ∨
    (h (i + 1) = h i - 1 ∧ col (i + 1) = col i - 1)

variable {n : ℕ} {col : ℕ → ZMod 3} {h : ℕ → ℤ}

/-- Over `d` steps: the colour moves by the height change (mod 3), the height moves by at most `d`, with the
parity of `d`. -/
theorem span (hs : StepHeight n col h) :
    ∀ d i, i + d < n → col (i + d) = col i + ((h (i + d) - h i : ℤ) : ZMod 3) ∧
      |h (i + d) - h i| ≤ d ∧ (h (i + d) - h i + d) % 2 = 0 := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
    intro i hid
    obtain ⟨hc, hb, hp⟩ := ih i (by omega)
    have hb' := abs_le.mp hb
    rw [← add_assoc]
    rcases hs (i + d) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [h2, h1, hc]; push_cast; ring
      · rw [h1, abs_le]; push_cast; constructor <;> linarith
      · rw [h1]; push_cast; omega
    · refine ⟨?_, ?_, ?_⟩
      · rw [h2, h1, hc]; push_cast; ring
      · rw [h1, abs_le]; push_cast; constructor <;> linarith
      · rw [h1]; push_cast; omega

/-- One step moves the height by at most `1`. -/
theorem step_le (hs : StepHeight n col h) (i : ℕ) (hi : i + 1 < n) : |h (i + 1) - h i| ≤ 1 := by
  have := (span hs 1 i hi).2.1
  simpa using this

/-! ### Lemma 4.3 core: one missing colour on a parity class -/

/-- Finite check behind Lemma 4.3: two positions apart, both ends avoid `c`; then
`h + 2·[col = c - 1]` is the same at both ends (`D` = height change). -/
theorem phi_step_fin (a c : ZMod 3) (D : ℤ) (hD : D = -2 ∨ D = 0 ∨ D = 2) (ha : a ≠ c)
    (hb : a + (D : ZMod 3) ≠ c) :
    D + (if a + (D : ZMod 3) = c - 1 then 2 else 0) = (if a = c - 1 then 2 else 0) := by
  rcases hD with rfl | rfl | rfl <;> revert a c <;> decide

/-- Two positions apart, both avoiding `c`: `h + 2·[col = c - 1]` does not change. -/
theorem phi_invariant (hs : StepHeight n col h) (c : ZMod 3) (i : ℕ) (hi : i + 2 < n)
    (hci : col i ≠ c) (hci2 : col (i + 2) ≠ c) :
    h (i + 2) + (if col (i + 2) = c - 1 then 2 else 0) = h i + (if col i = c - 1 then 2 else 0) := by
  obtain ⟨hcol, hb, hp⟩ := span hs 2 i hi
  have hb' := abs_le.mp hb
  have hD : h (i + 2) - h i = -2 ∨ h (i + 2) - h i = 0 ∨ h (i + 2) - h i = 2 := by
    push_cast at hb' hp; omega
  have key := phi_step_fin (col i) c (h (i + 2) - h i) hD hci (by rw [← hcol]; exact hci2)
  rw [hcol]
  linarith

/-- On a parity class `p` (positions `p, p+2, p+4, …`) avoiding `c`, the height stays within `2` of `h p`. -/
theorem class_close (hs : StepHeight n col h) (c : ZMod 3) (p : ℕ) (hp : p < 2)
    (hc : ∀ j, j < n → j % 2 = p → col j ≠ c) :
    ∀ k, p + 2 * k < n → |h (p + 2 * k) - h p| ≤ 2 := by
  have inv : ∀ k, p + 2 * k < n →
      h (p + 2 * k) + (if col (p + 2 * k) = c - 1 then 2 else 0) =
        h p + (if col p = c - 1 then 2 else 0) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have e : p + 2 * (k + 1) = p + 2 * k + 2 := by ring
      rw [e]
      have h1 := ih (by omega)
      have h2 := phi_invariant hs c (p + 2 * k) (by omega) (hc _ (by omega) (by omega))
        (hc _ (by omega) (by omega))
      linarith
  intro k hk
  have e := inv k hk
  rw [abs_le]
  split_ifs at e <;> constructor <;> linarith

/-- Lemma 4.3 core for the vertex `a` (joined to the paper's odd path vertices = 0-based even positions):
if the even positions avoid a colour `c`, then `|h (n-1) - h 0| ≤ 3`. -/
theorem flat_even (hs : StepHeight n col h) (c : ZMod 3)
    (hc : ∀ j, j < n → j % 2 = 0 → col j ≠ c) : |h (n - 1) - h 0| ≤ 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have cc := class_close hs c 0 (by norm_num) hc
  rcases Nat.even_or_odd (n - 1) with ⟨r, hr⟩ | ⟨r, hr⟩
  · have e1 := cc r (by omega)
    rw [show 0 + 2 * r = n - 1 by omega] at e1
    linarith
  · have e1 := abs_le.mp (cc r (by omega))
    have e2 := abs_le.mp (step_le hs (0 + 2 * r) (by omega))
    rw [show 0 + 2 * r + 1 = n - 1 by omega] at e2
    rw [abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

/-- Lemma 4.3 core for the vertex `b` (joined to the paper's even path vertices = 0-based odd positions):
if the odd positions avoid a colour `c`, then `|h (n-1) - h 0| ≤ 4`. -/
theorem flat_odd (hs : StepHeight n col h) (c : ZMod 3)
    (hc : ∀ j, j < n → j % 2 = 1 → col j ≠ c) : |h (n - 1) - h 0| ≤ 4 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [show n - 1 = 0 by omega]; simp
  have cc := class_close hs c 1 (by norm_num) hc
  have e0 := abs_le.mp (step_le hs 0 (by omega))
  rw [show 0 + 1 = 1 by rfl] at e0
  rcases Nat.even_or_odd (n - 1) with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- n - 1 = 2r even, r ≥ 1: last odd position is 2r - 1 = 1 + 2(r-1)
    have e1 := abs_le.mp (cc (r - 1) (by omega))
    have e2 := abs_le.mp (step_le hs (1 + 2 * (r - 1)) (by omega))
    rw [show 1 + 2 * (r - 1) + 1 = n - 1 by omega] at e2
    rw [abs_le]
    constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2]
  · have e1 := abs_le.mp (cc r (by omega))
    rw [show 1 + 2 * r = n - 1 by omega] at e1
    rw [abs_le]
    constructor <;> linarith [e0.1, e0.2, e1.1, e1.2]

/-! ### Lemma 4.7 core: one missing colour on a residue class mod 4 -/

/-- Finite check behind Lemma 4.7: four positions apart, both ends avoid `c`; `D` = height change. With
`c₂ = c - 1`, `c₁ = c + 1`: `D ≤ 3 + [end = c₂] - [start = c₂]` and `D ≥ -3 - [end = c₁] + [start = c₁]`. -/
theorem psi_step_fin (a c : ZMod 3) (D : ℤ) (hD : D = -4 ∨ D = -2 ∨ D = 0 ∨ D = 2 ∨ D = 4) (ha : a ≠ c)
    (hb : a + (D : ZMod 3) ≠ c) :
    D ≤ 3 + (if a + (D : ZMod 3) = c - 1 then 1 else 0) - (if a = c - 1 then 1 else 0) ∧
      -3 - (if a + (D : ZMod 3) = c + 1 then 1 else 0) + (if a = c + 1 then 1 else 0) ≤ D := by
  rcases hD with rfl | rfl | rfl | rfl | rfl <;> revert a c <;> decide

/-- Four positions apart, both avoiding `c`: the two potentials of the paper's alternation argument. -/
theorem psi_invariant (hs : StepHeight n col h) (c : ZMod 3) (i : ℕ) (hi : i + 4 < n)
    (hci : col i ≠ c) (hci4 : col (i + 4) ≠ c) :
    h (i + 4) - h i ≤ 3 + (if col (i + 4) = c - 1 then 1 else 0) - (if col i = c - 1 then 1 else 0) ∧
      -3 - (if col (i + 4) = c + 1 then 1 else 0) + (if col i = c + 1 then 1 else 0) ≤ h (i + 4) - h i := by
  obtain ⟨hcol, hb, hp⟩ := span hs 4 i hi
  have hb' := abs_le.mp hb
  have hD : h (i + 4) - h i = -4 ∨ h (i + 4) - h i = -2 ∨ h (i + 4) - h i = 0 ∨
      h (i + 4) - h i = 2 ∨ h (i + 4) - h i = 4 := by
    push_cast at hb' hp; omega
  have key := psi_step_fin (col i) c (h (i + 4) - h i) hD hci (by rw [← hcol]; exact hci4)
  rw [hcol]
  exact key

/-- On a residue class `ρ` mod 4 avoiding `c`, `|h (ρ + 4k) - h ρ| ≤ 3k + 1`. -/
theorem class4_close (hs : StepHeight n col h) (c : ZMod 3) (ρ : ℕ) (hρ : ρ < 4)
    (hc : ∀ j, j < n → j % 4 = ρ → col j ≠ c) :
    ∀ k, ρ + 4 * k < n → |h (ρ + 4 * k) - h ρ| ≤ 3 * k + 1 := by
  have inv : ∀ k, ρ + 4 * k < n →
      h (ρ + 4 * k) - h ρ ≤ 3 * k + (if col (ρ + 4 * k) = c - 1 then 1 else 0) - (if col ρ = c - 1 then 1 else 0) ∧
        -3 * k - (if col (ρ + 4 * k) = c + 1 then 1 else 0) + (if col ρ = c + 1 then 1 else 0) ≤
          h (ρ + 4 * k) - h ρ := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have e : ρ + 4 * (k + 1) = ρ + 4 * k + 4 := by ring
      rw [e]
      obtain ⟨u1, l1⟩ := ih (by omega)
      obtain ⟨u2, l2⟩ := psi_invariant hs c (ρ + 4 * k) (by omega) (hc _ (by omega) (by omega))
        (hc _ (by omega) (by omega))
      push_cast
      constructor <;> linarith
  intro k hk
  obtain ⟨u, l⟩ := inv k hk
  rw [abs_le]
  constructor
  · split_ifs at l <;> linarith
  · split_ifs at u <;> linarith

/-- Lemma 4.7 core (integer form): if one residue class mod 4 avoids a colour `c`, then
`4 |h (n-1) - h 0| ≤ 3 (n - 1) + 28`, i.e. `|W| ≤ 3(n-1)/4 + 7`. -/
theorem flat4_int (hs : StepHeight n col h) (c : ZMod 3) (ρ : ℕ) (hρ : ρ < 4)
    (hc : ∀ j, j < n → j % 4 = ρ → col j ≠ c) :
    4 * |h (n - 1) - h 0| ≤ 3 * ((n : ℤ) - 1) + 28 := by
  rcases Nat.lt_or_ge n 5 with hn | hn
  · -- short path: |W| ≤ n - 1 ≤ 3
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    have e := (span hs (n - 1) 0 (by omega)).2.1
    rw [show 0 + (n - 1) = n - 1 by omega] at e
    have hcast : (((n - 1 : ℕ)) : ℤ) = (n : ℤ) - 1 := by omega
    rw [hcast] at e
    have hn' : (n : ℤ) ≤ 4 := by exact_mod_cast (show n ≤ 4 by omega)
    have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn0
    linarith
  · set k := (n - 1 - ρ) / 4 with hk
    have hk1 : ρ + 4 * k ≤ n - 1 := by omega
    have hk2 : n - 1 - (ρ + 4 * k) ≤ 3 := by omega
    have mid := abs_le.mp (class4_close hs c ρ hρ hc k (by omega))
    have head := (span hs ρ 0 (by omega)).2.1
    rw [show 0 + ρ = ρ by omega] at head
    have head' := abs_le.mp head
    have tail := (span hs (n - 1 - (ρ + 4 * k)) (ρ + 4 * k) (by omega)).2.1
    rw [show ρ + 4 * k + (n - 1 - (ρ + 4 * k)) = n - 1 by omega] at tail
    have tail' := abs_le.mp tail
    have hρ' : (ρ : ℤ) ≤ 3 := by exact_mod_cast (show ρ ≤ 3 by omega)
    have ht' : ((n - 1 - (ρ + 4 * k) : ℕ) : ℤ) ≤ 3 := by exact_mod_cast hk2
    have h4k : 4 * (k : ℤ) ≤ (n : ℤ) - 1 := by
      have : 4 * k ≤ n - 1 := by omega
      have hcast : (((n - 1 : ℕ)) : ℤ) = (n : ℤ) - 1 := by omega
      rw [← hcast]; exact_mod_cast this
    have hW : |h (n - 1) - h 0| ≤ 3 * k + 7 := by
      rw [abs_le]
      constructor <;> linarith [mid.1, mid.2, head'.1, head'.2, tail'.1, tail'.2]
    linarith

/-- Lemma 4.7 core, the paper's form `|W| ≤ 3(n-1)/4 + 7` (real). -/
theorem flat4 (hs : StepHeight n col h) (c : ZMod 3) (ρ : ℕ) (hρ : ρ < 4)
    (hc : ∀ j, j < n → j % 4 = ρ → col j ≠ c) :
    ((|h (n - 1) - h 0| : ℤ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4 + 7 := by
  have e := flat4_int hs c ρ hρ hc
  have e' : ((4 * |h (n - 1) - h 0| : ℤ) : ℝ) ≤ ((3 * ((n : ℤ) - 1) + 28 : ℤ) : ℝ) := by exact_mod_cast e
  push_cast at e' ⊢
  linarith

/-! ### Lemma 4.2 core: a move of one path vertex changes one height value by exactly 2 -/

/-- `StepHeight` only needs checking at the steps touching the changed position `i`. -/
theorem stepHeight_of_local (hs : StepHeight n col h) {col' : ℕ → ZMod 3} {h' : ℕ → ℤ} (i : ℕ)
    (hc : ∀ j, j ≠ i → col' j = col j) (hh : ∀ j, j ≠ i → h' j = h j)
    (hleft : 0 < i → i < n → (h' i = h' (i - 1) + 1 ∧ col' i = col' (i - 1) + 1) ∨
      (h' i = h' (i - 1) - 1 ∧ col' i = col' (i - 1) - 1))
    (hright : i + 1 < n → (h' (i + 1) = h' i + 1 ∧ col' (i + 1) = col' i + 1) ∨
      (h' (i + 1) = h' i - 1 ∧ col' (i + 1) = col' i - 1)) :
    StepHeight n col' h' := by
  intro j hj
  by_cases hji : j = i
  · subst hji; exact hright hj
  by_cases hj1 : j + 1 = i
  · have e : j = i - 1 := by omega
    have := hleft (by omega) (by omega)
    rw [← hj1] at this
    simpa [e, hj1] using this
  rw [hc j hji, hc (j + 1) hj1, hh j hji, hh (j + 1) hj1]
  exact hs j hj

/-- Finite check: a third colour. -/
theorem third_fin : ∀ a b : ZMod 3, b ≠ a → b ≠ a + 1 → b = a - 1 := by decide

theorem third_fin' : ∀ a b : ZMod 3, b ≠ a → b ≠ a - 1 → b = a + 1 := by decide

theorem fin_up_up : ∀ a : ZMod 3, a - 1 ≠ a - 1 - 1 + 1 → False := by decide

/-- Lemma 4.2 core. Let the path colouring `col'` differ from `col` only at position `i`, with a new colour that
differs from the old one and from the colours of the path neighbours of `i`. Then some height `h'` of `col'` agrees
with `h` off `i` and differs from it at `i` by exactly `2`. -/
theorem move_height (hs : StepHeight n col h) (col' : ℕ → ZMod 3) (i : ℕ) (hi : i < n)
    (hsame : ∀ j, j ≠ i → col' j = col j) (hne : col' i ≠ col i)
    (hl : 0 < i → col' i ≠ col (i - 1)) (hr : i + 1 < n → col' i ≠ col (i + 1)) :
    ∃ h' : ℕ → ℤ, StepHeight n col' h' ∧ (∀ j, j ≠ i → h' j = h j) ∧ |h' i - h i| = 2 := by
  -- the new value: v = h i + 2 or h i - 2, chosen from the right step if it exists, else from the left step
  have key : ∃ v : ℤ, |v - h i| = 2 ∧
      (0 < i → (v = h (i - 1) + 1 ∧ col' i = col (i - 1) + 1) ∨ (v = h (i - 1) - 1 ∧ col' i = col (i - 1) - 1)) ∧
      (i + 1 < n → (h (i + 1) = v + 1 ∧ col (i + 1) = col' i + 1) ∨
        (h (i + 1) = v - 1 ∧ col (i + 1) = col' i - 1)) := by
    by_cases hR : i + 1 < n
    · rcases hs i hR with ⟨h1, c1⟩ | ⟨h1, c1⟩
      · -- step up at i: col' i = col i - 1, v = h i + 2
        have hc' : col' i = col i - 1 := third_fin _ _ hne (by rw [← c1]; exact hr hR)
        refine ⟨h i + 2, by norm_num, fun hi0 => ?_, fun _ => Or.inr ⟨by linarith, by rw [c1, hc']; ring_nf; reduce_mod_char⟩⟩
        rcases hs (i - 1) (by omega) with ⟨h2, c2⟩ | ⟨h2, c2⟩
        · rw [show i - 1 + 1 = i by omega] at h2 c2
          exact absurd (by rw [hc', c2]; ring) (hl hi0)
        · rw [show i - 1 + 1 = i by omega] at h2 c2
          exact Or.inl ⟨by linarith, by rw [hc', c2]; ring_nf; reduce_mod_char⟩
      · -- step down at i: col' i = col i + 1, v = h i - 2
        have hc' : col' i = col i + 1 := third_fin' _ _ hne (by rw [← c1]; exact hr hR)
        refine ⟨h i - 2, by norm_num, fun hi0 => ?_, fun _ => Or.inl ⟨by linarith, by rw [c1, hc']; ring_nf; reduce_mod_char⟩⟩
        rcases hs (i - 1) (by omega) with ⟨h2, c2⟩ | ⟨h2, c2⟩
        · rw [show i - 1 + 1 = i by omega] at h2 c2
          exact Or.inr ⟨by linarith, by rw [hc', c2]; ring_nf; reduce_mod_char⟩
        · rw [show i - 1 + 1 = i by omega] at h2 c2
          exact absurd (by rw [hc', c2]; ring) (hl hi0)
    · by_cases hL : 0 < i
      · rcases hs (i - 1) (by omega) with ⟨h2, c2⟩ | ⟨h2, c2⟩
        · rw [show i - 1 + 1 = i by omega] at h2 c2
          -- col (i-1) = col i - 1, so col' i = col i + 1 = col (i-1) - 1, v = h i - 2
          have hc' : col' i = col i + 1 := third_fin' _ _ hne (by
            intro e; apply hl hL; rw [e, c2]; ring)
          refine ⟨h i - 2, by norm_num, fun _ => Or.inr ⟨by linarith, by rw [hc', c2]; ring_nf; reduce_mod_char⟩,
            fun h' => absurd h' hR⟩
        · rw [show i - 1 + 1 = i by omega] at h2 c2
          have hc' : col' i = col i - 1 := third_fin _ _ hne (by
            intro e; apply hl hL; rw [e, c2]; ring)
          refine ⟨h i + 2, by norm_num, fun _ => Or.inl ⟨by linarith, by rw [hc', c2]; ring_nf; reduce_mod_char⟩,
            fun h' => absurd h' hR⟩
      · exact ⟨h i + 2, by norm_num, fun h' => absurd h' hL, fun h' => absurd h' hR⟩
  obtain ⟨v, hv, hvl, hvr⟩ := key
  refine ⟨fun j => if j = i then v else h j, ?_, fun j hj => by simp [hj], by simpa using hv⟩
  refine stepHeight_of_local hs i hsame (fun j hj => by simp [hj]) (fun hi0 _ => ?_) (fun hR => ?_)
  · have e1 : i - 1 ≠ i := by omega
    simp only [e1, ↓reduceIte, hsame (i - 1) e1]
    exact hvl hi0
  · have e1 : i + 1 ≠ i := by omega
    simp only [e1, ↓reduceIte, hsame (i + 1) e1]
    exact hvr hR

/-- A change of one value by `2` changes `∑_{j<n} |h j - r j|` by at most `2` (paper, proof of Prop. 4.1, v3.90 l. 647: "each move
changes `∑_i |h_j(i) - h_0(i)|` by at most `2`"). -/
theorem l1_step (r h h' : ℕ → ℤ) (i : ℕ) (hh : ∀ j, j ≠ i → h' j = h j) (hv : |h' i - h i| = 2) :
    ∑ j ∈ Finset.range n, |h' j - r j| ≤ ∑ j ∈ Finset.range n, |h j - r j| + 2 := by
  have hterm : ∀ j ∈ Finset.range n, |h' j - r j| ≤ |h j - r j| + (if j = i then 2 else 0) := by
    intro j _
    by_cases hj : j = i
    · subst hj
      simp only
      calc |h' j - r j| = |(h' j - h j) + (h j - r j)| := by ring_nf
        _ ≤ |h' j - h j| + |h j - r j| := abs_add_le _ _
        _ = |h j - r j| + 2 := by rw [hv]; ring
    · simp [hj, hh j hj]
  calc ∑ j ∈ Finset.range n, |h' j - r j|
      ≤ ∑ j ∈ Finset.range n, (|h j - r j| + (if j = i then 2 else 0)) := Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.range n, |h j - r j| + ∑ j ∈ Finset.range n, (if j = i then (2 : ℤ) else 0) :=
        Finset.sum_add_distrib
    _ ≤ ∑ j ∈ Finset.range n, |h j - r j| + 2 := by
        rw [Finset.sum_ite_eq']
        split_ifs <;> linarith

/-! ### Proposition 4.1, case "a and b never move": full reversal of the height -/

/-- The pairs `{k, n - 1 - k}`, `k < M`, `2M ≤ n`, are disjoint and lie below `n`. -/
theorem pairs_le_sum (f : ℕ → ℤ) (M : ℕ) (h2M : 2 * M ≤ n) :
    ∑ k ∈ Finset.range M, (|f k| + |f (n - 1 - k)|) ≤ ∑ i ∈ Finset.range n, |f i| := by
  have hB : ∑ i ∈ (Finset.range M).image (fun k => n - 1 - k), |f i| =
      ∑ k ∈ Finset.range M, |f (n - 1 - k)| := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    have hx' : x < M := by simpa using hx
    have hy' : y < M := by simpa using hy
    have hxy' : n - 1 - x = n - 1 - y := hxy
    omega
  have hdisj : Disjoint (Finset.range M) ((Finset.range M).image (fun k => n - 1 - k)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image, Finset.mem_range] at ha hb
    obtain ⟨y, hy, hxy⟩ := hb
    omega
  have hsub : Finset.range M ∪ (Finset.range M).image (fun k => n - 1 - k) ⊆ Finset.range n := by
    intro a ha
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range] at ha ⊢
    rcases ha with hx | ⟨y, hy, rfl⟩ <;> omega
  rw [Finset.sum_add_distrib, ← hB, ← Finset.sum_union hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => abs_nonneg (f i))

/-- `∑_{k < M} (2(N - 1) - 4k) = 2M(N - 1) - 2M(M - 1)`. -/
theorem sum_lin (N : ℤ) : ∀ M : ℕ,
    ∑ k ∈ Finset.range M, (2 * (N - 1) - 4 * (k : ℤ)) = 2 * M * (N - 1) - 2 * M * (M - 1) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Proposition 4.1, first case ("If `a` and `b` never move"): `h` has all steps `+1`, `g` all steps `-1`; then
`∑_{i<n} |g i - h i| ≥ (n² - 1)/2`, here as `n² - 1 ≤ 2 ∑ |g - h|` (paper: `∑|f| ≥ 2⌊n/2⌋(n - ⌊n/2⌋) ≥ (n²-1)/2`). -/
theorem full_reversal (h g : ℕ → ℤ)
    (hh : ∀ i, i + 1 < n → h (i + 1) - h i = 1) (hg : ∀ i, i + 1 < n → g (i + 1) - g i = -1) :
    (n : ℤ) ^ 2 - 1 ≤ 2 * ∑ i ∈ Finset.range n, |g i - h i| := by
  have hf : ∀ i, i < n → g i - h i = (g 0 - h 0) - 2 * (i : ℤ) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have e1 := ih (by omega)
      have e2 := hh i hi
      have e3 := hg i hi
      push_cast
      linarith
  set m := n / 2 with hm
  have h2m : 2 * m ≤ n := by omega
  have hpairs := pairs_le_sum (fun i => g i - h i) m h2m
  have hlow : ∑ k ∈ Finset.range m, (2 * ((n : ℤ) - 1) - 4 * (k : ℤ)) ≤
      ∑ k ∈ Finset.range m, (|g k - h k| + |g (n - 1 - k) - h (n - 1 - k)|) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_range] at hk
    have e1 := hf k (by omega)
    have e2 := hf (n - 1 - k) (by omega)
    have hcast : ((n - 1 - k : ℕ) : ℤ) = (n : ℤ) - 1 - k := by omega
    rw [hcast] at e2
    linarith [le_abs_self (g k - h k), neg_abs_le (g (n - 1 - k) - h (n - 1 - k))]
  rw [sum_lin] at hlow
  have hsum := hlow.trans hpairs
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hmr : m = r := by omega
    rw [hmr] at hsum
    have hn : (n : ℤ) = 2 * r := by exact_mod_cast (show n = 2 * r by omega)
    rw [hn] at hsum ⊢
    nlinarith
  · have hmr : m = r := by omega
    rw [hmr] at hsum
    have hn : (n : ℤ) = 2 * r + 1 := by exact_mod_cast hr
    rw [hn] at hsum ⊢
    nlinarith

end Cereceda.PathAux
