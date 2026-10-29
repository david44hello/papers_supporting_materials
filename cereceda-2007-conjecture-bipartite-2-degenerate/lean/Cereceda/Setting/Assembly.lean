/-
Cereceda/Setting/Assembly.lean — Theorem 1.2, the class form of the conjecture, and the open-problem reductions,
each proved from the TYPES of the statements it uses (hypotheses), so Statements.lean instantiates them.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Basic
import Cereceda.Defs.Instance

namespace Cereceda

open Finset

namespace Assembly

/-- The type of `sec2_order_iff_degenerate`. -/
def OrderIffType : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ),
    (∃ ρ : V ≃ Fin (Fintype.card V), IsDegOrder G d ρ) ↔ IsDegenerate G d

/-- The type of `lem_2_5`. -/
def SweepType : Prop :=
  ∀ (𝒞 : InstanceClass) (lam : ℝ), 2 ≤ lam →
    (∀ (W : Type) [Fintype W] [DecidableEq W] (I : Instance W), 𝒞 W I.toSkeleton → I.g = 0 →
      ∀ α β : W → Fin 4, I.IsGreedy I.x α → I.IsGreedy I.g β →
        ∃ ms, I.IsSeq α ms β ∧ (ms.length : ℝ) ≤ lam * Fintype.card W) →
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (ρ : V ≃ Fin n)
      (hρ : IsDegOrder G 2 ρ), (∀ w, 𝒞 (ConeV G ρ w) (coneSkeleton G ρ hρ w)) →
    (recolGraph G 4).ediam ≠ ⊤ ∧
      ((recolGraph G 4).diam : ℝ) ≤ 2 * lam * ∑ w, ((cone G ρ w).card : ℝ) ∧
      2 * lam * ∑ w, ((cone G ρ w).card : ℝ) ≤ lam * n * (n + 1)

/-- The type of `thm_3_1`. -/
def BipInstType : Prop :=
  ∀ {W : Type} [Fintype W] [DecidableEq W] (I : Instance W), I.NoRoots → I.graph.IsBipartite →
    ∀ α β : W → Fin 4, I.IsGreedy I.x α → I.IsGreedy I.g β →
      ∃ ms, I.IsSeq α ms β ∧ movesOf ms I.sink = 1 ∧ (∀ v, v ≠ I.sink → movesOf ms v ≤ 2) ∧
        ms.length ≤ 2 * Fintype.card W - 1

/-- The type of `thm_1_2_cones`. -/
def ConesType : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], G.IsBipartite →
    ∀ {n : ℕ} (ρ : V ≃ Fin n) (hρ : IsDegOrder G 2 ρ) (w : V),
      (coneSkeleton G ρ hρ w).graph.IsBipartite ∧ (coneSkeleton G ρ hρ w).NoRoots

/-- From the sweep's real bound to an `ediam` bound by a natural number. -/
theorem ediam_le_of_sweep {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (N : ℕ)
    (hne : (recolGraph G 4).ediam ≠ ⊤) (hle : ((recolGraph G 4).diam : ℝ) ≤ N) :
    (recolGraph G 4).ediam ≤ (N : ℕ∞) := by
  have hcast : ((recolGraph G 4).diam : ℕ∞) = (recolGraph G 4).ediam :=
    SimpleGraph.natCast_diam_eq_ediam_iff.mpr hne
  rw [← hcast]
  exact_mod_cast (by exact_mod_cast hle : (recolGraph G 4).diam ≤ N)

/-- The sweep with an arbitrary class and `λ`, plus the degeneracy order: `ediam ≤ ⌈λ⌉₊ n(n+1)`. -/
theorem ediam_le_of_class (hord : OrderIffType) (hsweep : SweepType) (𝒞 : InstanceClass) (lam : ℝ) (hlam : 2 ≤ lam)
    (hlin : ∀ (W : Type) [Fintype W] [DecidableEq W] (I : Instance W), 𝒞 W I.toSkeleton → I.g = 0 →
      ∀ α β : W → Fin 4, I.IsGreedy I.x α → I.IsGreedy I.g β →
        ∃ ms, I.IsSeq α ms β ∧ (ms.length : ℝ) ≤ lam * Fintype.card W)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : IsDegenerate G 2)
    (hcones : ∀ {n : ℕ} (ρ : V ≃ Fin n) (hρ : IsDegOrder G 2 ρ) (w : V), 𝒞 (ConeV G ρ w) (coneSkeleton G ρ hρ w)) :
    (recolGraph G 4).ediam ≤ ((⌈lam⌉₊ * Fintype.card V * (Fintype.card V + 1) : ℕ) : ℕ∞) := by
  obtain ⟨ρ, hρ⟩ := (hord G 2).mpr hdeg
  obtain ⟨hne, hdiam, hsum⟩ := hsweep 𝒞 lam hlam hlin G ρ hρ (hcones ρ hρ)
  refine ediam_le_of_sweep G _ hne ?_
  have hceil : lam ≤ (⌈lam⌉₊ : ℝ) := Nat.le_ceil lam
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) * (Fintype.card V + 1) := by positivity
  push_cast
  calc ((recolGraph G 4).diam : ℝ) ≤ lam * (Fintype.card V) * (Fintype.card V + 1) := hdiam.trans hsum
    _ = lam * ((Fintype.card V : ℝ) * (Fintype.card V + 1)) := by ring
    _ ≤ (⌈lam⌉₊ : ℝ) * ((Fintype.card V : ℝ) * (Fintype.card V + 1)) := mul_le_mul_of_nonneg_right hceil hn
    _ = (⌈lam⌉₊ : ℝ) * (Fintype.card V) * (Fintype.card V + 1) := by ring

/-- The length of a list of moves is the sum over the vertices of their numbers of moves. -/
theorem length_eq_sum_movesOf {W : Type} [Fintype W] [DecidableEq W] (ms : List (W × Fin 4)) :
    ms.length = ∑ v, movesOf ms v := by
  induction ms with
  | nil => simp [movesOf]
  | cons m ms ih =>
    simp only [movesOf, List.countP_cons, List.length_cons] at ih ⊢
    rw [Finset.sum_add_distrib, ← ih]
    simp [Finset.sum_ite_eq]

theorem nat_bound_sq (C n : ℕ) : C * n * (n + 1) ≤ 2 * C * n ^ 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · nlinarith [Nat.mul_le_mul_left (C * n) (show n + 1 ≤ 2 * n by omega)]

end Assembly

open Cereceda.Assembly

theorem thm_1_2_of (hord : OrderIffType) (hsweep : SweepType) (h31 : BipInstType) (hc : ConesType)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) (hdeg : IsDegenerate G 2) :
    (recolGraph G 4).ediam ≤ ((2 * Fintype.card V * (Fintype.card V + 1) : ℕ) : ℕ∞) := by
  have h := ediam_le_of_class hord hsweep (fun W _ _ S => S.NoRoots ∧ S.graph.IsBipartite) 2 le_rfl
    (by
      intro W _ _ I hI _ α β hα hβ
      obtain ⟨ms, hms, -, -, hlen⟩ := h31 I hI.1 hI.2 α β hα hβ
      refine ⟨ms, hms, ?_⟩
      have : ms.length ≤ 2 * Fintype.card W := hlen.trans (Nat.sub_le _ _)
      exact_mod_cast this)
    G hdeg (fun ρ hρ w => ⟨(hc G hbip ρ hρ w).2, (hc G hbip ρ hρ w).1⟩)
  simpa using h

theorem cereceda_bipartite_two_degenerate_of (h12 : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.IsBipartite → IsDegenerate G 2 →
      (recolGraph G 4).ediam ≤ ((2 * Fintype.card V * (Fintype.card V + 1) : ℕ) : ℕ∞)) :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsBipartite → IsDegenerate G 2 → (recolGraph G 4).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞) := by
  refine ⟨4, fun V _ _ G _ hbip hdeg => (h12 G hbip hdeg).trans ?_⟩
  have := nat_bound_sq 2 (Fintype.card V)
  exact_mod_cast (by omega : 2 * Fintype.card V * (Fintype.card V + 1) ≤ 4 * Fintype.card V ^ 2)

theorem open_1_reduction_of (hord : OrderIffType) (hsweep : SweepType) (lam : ℝ)
    (hlin : ∀ (W : Type) [Fintype W] [DecidableEq W] (I : Instance W), I.g = 0 →
      ∀ α β : W → Fin 4, I.IsGreedy I.x α → I.IsGreedy I.g β →
        ∃ ms, I.IsSeq α ms β ∧ (ms.length : ℝ) ≤ lam * Fintype.card W) :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsDegenerate G 2 → (recolGraph G 4).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞) := by
  refine ⟨2 * ⌈max lam 2⌉₊, fun V _ _ G _ hdeg => ?_⟩
  have h := ediam_le_of_class hord hsweep (fun _ _ _ _ => True) (max lam 2) (le_max_right _ _)
    (by
      intro W _ _ I _ hg α β hα hβ
      obtain ⟨ms, hms, hlen⟩ := hlin W I hg α β hα hβ
      refine ⟨ms, hms, hlen.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    G hdeg (fun _ _ _ => trivial)
  refine h.trans ?_
  have := nat_bound_sq ⌈max lam 2⌉₊ (Fintype.card V)
  exact_mod_cast this

theorem open_1_per_vertex_of (hred : ∀ lam : ℝ,
      (∀ (W : Type) [Fintype W] [DecidableEq W] (I : Instance W), I.g = 0 →
        ∀ α β : W → Fin 4, I.IsGreedy I.x α → I.IsGreedy I.g β →
          ∃ ms, I.IsSeq α ms β ∧ (ms.length : ℝ) ≤ lam * Fintype.card W) →
      ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        IsDegenerate G 2 → (recolGraph G 4).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞))
    (K : ℕ)
    (hK : ∀ (W : Type) [Fintype W] [DecidableEq W] (I : Instance W), I.g = 0 →
      ∀ α β : W → Fin 4, I.IsGreedy I.x α → I.IsGreedy I.g β →
        ∃ ms, I.IsSeq α ms β ∧ ∀ v, movesOf ms v ≤ K) :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsDegenerate G 2 → (recolGraph G 4).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞) := by
  refine hred K (fun W _ _ I hg α β hα hβ => ?_)
  obtain ⟨ms, hms, hmv⟩ := hK W I hg α β hα hβ
  refine ⟨ms, hms, ?_⟩
  have hlen : ms.length = ∑ v, movesOf ms v := length_eq_sum_movesOf ms
  have : ms.length ≤ K * Fintype.card W := by
    rw [hlen]
    calc ∑ v, movesOf ms v ≤ ∑ _v : W, K := Finset.sum_le_sum (fun v _ => hmv v)
      _ = K * Fintype.card W := by simp [mul_comm]
  exact_mod_cast this

end Cereceda
