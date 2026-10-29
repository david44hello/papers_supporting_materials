/-
Cereceda/LB/Cost.lean — Lemma 4.4 (lem:cost) of the paper "The Cereceda (2007) conjecture holds for bipartite
2-degenerate graphs", short v3.90 l. 630-642 (statement l. 630-633, proof l. 635-642).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper, verbatim (v3.90 l. 630-633; Lean's `g` is the paper's `h'`, Lean's `n` is the paper's `\ell`):
  Let $h, h' \colon \{1,\dots,\ell\} \to \mathbb{Z}$ be functions whose steps $h(i+1) - h(i)$ and $h'(i+1) - h'(i)$ are
  all $\pm 1$, every step of $h$ being $+1$. Let a real number $q \ge 0$ satisfy $h'(\ell) - h'(1) \le (\ell-1) - q$
  and $q/4 + 1 \le \ell/2$. Then $\sum_i |h'(i) - h(i)| \ge q^2/8$. The same holds with all signs reversed (all steps
  of $h$ equal to $-1$ and $h'(\ell) - h'(1) \ge -(\ell-1) + q$).

Encoding: 0-based, position i (0 ≤ i < n) is the paper's index i+1; the step at i is the value at i+1 minus
the value at i, for i + 1 < n. `q` is real (the paper uses q = (ℓ-29)/4 in Proposition 4.6, v3.90 l. 706).
Proof = the paper's: f = g - h falls by at most 2 per step and by at least q in total; the pairs {k, n-1-k}, k ≤ m with
m = ⌊q/4⌋, are disjoint and carry |f| ≥ q - 4k each; ∑_{k ≤ m} (q - 4k) = (m+1)(q - 2m) ≥ q²/8.
-/
import Mathlib

namespace Cereceda.CostAux

open Finset

/-- Telescoping: if every step of `h` below `n` is `+1`, then `h (i + d) - h i = d` while `i + d < n`. -/
theorem steps_plus_one {n : ℕ} {h : ℕ → ℤ}
    (hh : ∀ i, i + 1 < n → h (i + 1) - h i = 1) :
    ∀ d i, i + d < n → h (i + d) - h i = d := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
    intro i hid
    have h1 := ih i (by omega)
    have h2 := hh (i + d) (by omega)
    rw [← add_assoc]
    push_cast
    linarith

/-- Telescoping: if `f` falls by at most `2` per step below `n`, it falls by at most `2 d` over `d` steps. -/
theorem fall_le {n : ℕ} {f : ℕ → ℤ} (hf : ∀ i, i + 1 < n → f i - f (i + 1) ≤ 2) :
    ∀ d i, i + d < n → f i - f (i + d) ≤ 2 * d := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
    intro i hid
    have h1 := ih i (by omega)
    have h2 := hf (i + d) (by omega)
    rw [← add_assoc]
    push_cast
    linarith

/-- `∑_{k < M} (q - 4k) = M q - 2 M (M - 1)`. -/
theorem sum_arith (q : ℝ) : ∀ M : ℕ, ∑ k ∈ range M, (q - 4 * (k : ℝ)) = M * q - 2 * M * (M - 1) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The pair bound: for `k ≤ m` with `2 (m + 1) ≤ n`, `|f k| + |f (n - 1 - k)| ≥ q - 4k`
(paper: `|f(i)| + |f(i')| ≥ q - 4(i-1)` with `i = k + 1`, `i' = n + 1 - i`). -/
theorem pair_bound {n m : ℕ} {f : ℕ → ℤ} {q : ℝ}
    (hf : ∀ i, i + 1 < n → f i - f (i + 1) ≤ 2)
    (hfall : q ≤ ((f 0 - f (n - 1) : ℤ) : ℝ)) (h2m : 2 * (m + 1) ≤ n) :
    ∀ k ∈ range (m + 1), q - 4 * (k : ℝ) ≤ (((|f k| + |f (n - 1 - k)|) : ℤ) : ℝ) := by
  intro k hk
  rw [Finset.mem_range] at hk
  have hA := fall_le hf k 0 (by omega)
  have hB := fall_le hf k (n - 1 - k) (by omega)
  rw [show 0 + k = k by omega] at hA
  rw [show n - 1 - k + k = n - 1 by omega] at hB
  have habs : f k - f (n - 1 - k) ≤ |f k| + |f (n - 1 - k)| := by
    linarith [le_abs_self (f k), neg_abs_le (f (n - 1 - k))]
  have hZ : f 0 - f (n - 1) - 4 * (k : ℤ) ≤ |f k| + |f (n - 1 - k)| := by linarith
  have hR : (((f 0 - f (n - 1) - 4 * (k : ℤ)) : ℤ) : ℝ) ≤ (((|f k| + |f (n - 1 - k)|) : ℤ) : ℝ) := by
    exact_mod_cast hZ
  push_cast at hR hfall ⊢
  linarith

/-- The pairs `{k, n - 1 - k}`, `k ≤ m`, are disjoint and lie below `n`, so their sum is at most the full sum. -/
theorem pairs_le_sum {n m : ℕ} (f : ℕ → ℤ) (h2m : 2 * (m + 1) ≤ n) :
    ∑ k ∈ range (m + 1), (|f k| + |f (n - 1 - k)|) ≤ ∑ i ∈ range n, |f i| := by
  have hB : ∑ i ∈ (range (m + 1)).image (fun k => n - 1 - k), |f i| =
      ∑ k ∈ range (m + 1), |f (n - 1 - k)| := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    have hx' : x < m + 1 := by simpa using hx
    have hy' : y < m + 1 := by simpa using hy
    have hxy' : n - 1 - x = n - 1 - y := hxy
    omega
  have hdisj : Disjoint (range (m + 1)) ((range (m + 1)).image (fun k => n - 1 - k)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image, Finset.mem_range] at ha hb
    obtain ⟨y, hy, hxy⟩ := hb
    omega
  have hsub : range (m + 1) ∪ (range (m + 1)).image (fun k => n - 1 - k) ⊆ range n := by
    intro a ha
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range] at ha ⊢
    rcases ha with hx | ⟨y, hy, rfl⟩ <;> omega
  rw [Finset.sum_add_distrib, ← hB, ← Finset.sum_union hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => abs_nonneg (f i))

/-- General form: `f` falls by at most `2` per step below `n` and by at least `q` from `0` to `n - 1`;
then `∑_{i < n} |f i| ≥ q² / 8` (with `q ≥ 0`, `q / 4 + 1 ≤ n / 2`). -/
theorem cost_of_fall {n : ℕ} {f : ℕ → ℤ} {q : ℝ}
    (hf : ∀ i, i + 1 < n → f i - f (i + 1) ≤ 2)
    (hq : 0 ≤ q) (hfall : q ≤ ((f 0 - f (n - 1) : ℤ) : ℝ)) (hqn : q / 4 + 1 ≤ (n : ℝ) / 2) :
    q ^ 2 / 8 ≤ ∑ i ∈ range n, ((|f i| : ℤ) : ℝ) := by
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℕ, (m : ℝ) ≤ q / 4 ∧ q / 4 < m + 1 :=
    ⟨⌊q / 4⌋₊, Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
  have h2m : 2 * (m + 1) ≤ n := by
    have : ((2 * (m + 1) : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  have hlow := Finset.sum_le_sum (pair_bound hf hfall h2m)
  rw [sum_arith] at hlow
  have hsumR : ((∑ k ∈ range (m + 1), (|f k| + |f (n - 1 - k)|) : ℤ) : ℝ) ≤
      ((∑ i ∈ range n, |f i| : ℤ) : ℝ) := by
    exact_mod_cast pairs_le_sum f h2m
  simp only [Int.cast_sum] at hsumR
  refine le_trans ?_ (hlow.trans hsumR)
  have hr0 : 0 ≤ q - 4 * m := by linarith
  have hr8 : 0 ≤ 8 - (q - 4 * m) := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  push_cast
  nlinarith [mul_nonneg hr0 hr8]

end Cereceda.CostAux

namespace Cereceda

open Finset

/-- **Lemma 4.4 (lem:cost)**, first part (v3.90 l. 630-632), 0-based. -/
theorem cost_proved (n : ℕ) (h g : ℕ → ℤ) (q : ℝ)
    (hh : ∀ i, i + 1 < n → h (i + 1) - h i = 1)
    (hg : ∀ i, i + 1 < n → g (i + 1) - g i = 1 ∨ g (i + 1) - g i = -1)
    (hq : 0 ≤ q)
    (hgq : ((g (n - 1) - g 0 : ℤ) : ℝ) ≤ ((n : ℝ) - 1) - q)
    (hqn : q / 4 + 1 ≤ (n : ℝ) / 2) :
    q ^ 2 / 8 ≤ ∑ i ∈ Finset.range n, ((|g i - h i| : ℤ) : ℝ) := by
  have hn : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hH := CostAux.steps_plus_one hh (n - 1) 0 (by omega)
  rw [show 0 + (n - 1) = n - 1 by omega] at hH
  have hf : ∀ i, i + 1 < n → (g i - h i) - (g (i + 1) - h (i + 1)) ≤ 2 := by
    intro i hin
    have h1 := hh i hin
    rcases hg i hin with h2 | h2 <;> linarith
  have hfall : q ≤ (((g 0 - h 0) - (g (n - 1) - h (n - 1)) : ℤ) : ℝ) := by
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have key : (g 0 - h 0) - (g (n - 1) - h (n - 1)) = ((n : ℤ) - 1) - (g (n - 1) - g 0) := by linarith
    rw [key]
    push_cast at hgq ⊢
    linarith
  exact CostAux.cost_of_fall (f := fun i => g i - h i) hf hq hfall hqn

/-- **Lemma 4.4 (lem:cost)**, mirror form (v3.90 l. 632-633: "The same holds with all signs reversed"), 0-based. -/
theorem cost_mirror_proved (n : ℕ) (h g : ℕ → ℤ) (q : ℝ)
    (hh : ∀ i, i + 1 < n → h (i + 1) - h i = -1)
    (hg : ∀ i, i + 1 < n → g (i + 1) - g i = 1 ∨ g (i + 1) - g i = -1)
    (hq : 0 ≤ q)
    (hgq : -((n : ℝ) - 1) + q ≤ ((g (n - 1) - g 0 : ℤ) : ℝ))
    (hqn : q / 4 + 1 ≤ (n : ℝ) / 2) :
    q ^ 2 / 8 ≤ ∑ i ∈ Finset.range n, ((|g i - h i| : ℤ) : ℝ) := by
  have hh' : ∀ i, i + 1 < n → -h (i + 1) - -h i = 1 := by
    intro i hin
    have := hh i hin
    linarith
  have hg' : ∀ i, i + 1 < n → -g (i + 1) - -g i = 1 ∨ -g (i + 1) - -g i = -1 := by
    intro i hin
    rcases hg i hin with h2 | h2
    · right; linarith
    · left; linarith
  have hgq' : ((-g (n - 1) - -g 0 : ℤ) : ℝ) ≤ ((n : ℝ) - 1) - q := by
    push_cast at hgq ⊢
    linarith
  have hsum : ∑ i ∈ Finset.range n, ((|g i - h i| : ℤ) : ℝ) =
      ∑ i ∈ Finset.range n, ((|-g i - -h i| : ℤ) : ℝ) :=
    Finset.sum_congr rfl (fun i _ => by rw [show -g i - -h i = -(g i - h i) by ring, abs_neg])
  rw [hsum]
  exact cost_proved n (fun i => -h i) (fun i => -g i) q hh' hg' hq hgq' hqn

end Cereceda
