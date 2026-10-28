/-
EulerFlow/IntFlow/ChainLift.lean — paper 002, Lemma 7.4, abstract and Section 7 opening ("the same residues modulo
k"): two integer lifts of `f` are joined by a PATH of integer lifts of `f` (`lem_8_4_fibre`), and a `{1,-1,2,-2}`-chain
of `ℤ_k`-flows becomes a walk in `𝓕(G, k)` in which every flow of the chain, in order, is replaced by a non-empty path of
its integer lifts; the walk is a path when the chain is (`sec7_chain_lift`).
Helpers live in namespace `EulerFlow.Sec8`.
-/
import EulerFlow.IntFlow.Transfer
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace EulerFlow

namespace Sec8

open Finset MGraph

variable {V E : Type} {G : MGraph V E} [Fintype E] [DecidableEq E] [DecidableEq V]

/-! ### Lemma 7.4 inside the fibre -/

/-- One cycle `Q` of the decomposition of `(F' - F)/k` moves the lift `F` to the lift `F + k χ_Q` of the same `f`;
it is adjacent to `F` and differs from `F'` on fewer edges. -/
lemma fibre_step [Fintype V] {k : ℕ} (hk : 2 ≤ k) {f : E → ZMod k} {F F' : E → ℤ}
    (hF : G.IsIntLift k f F) (hF' : G.IsIntLift k f F') (hne : F ≠ F') :
    ∃ F₁ : E → ℤ, ∃ hF₁ : G.IsIntLift k f F₁, (G.kFlowGraph k).Adj ⟨F, hF.1⟩ ⟨F₁, hF₁.1⟩ ∧
      (univ.filter fun e => F₁ e ≠ F' e).card < (univ.filter fun e => F e ≠ F' e).card := by
  have hf := isNZFlow_of_lift hk hF
  have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  -- `h = (F' - F)/k`, a `{-1,0,1}`-valued integer flow (as in `lem_8_4_proved`)
  set h : E → ℤ := fun e => if F' e = F e then 0 else if F' e = F e + k then 1 else -1 with hh
  have hFF : ∀ e, F' e = F e + h e * k := by
    intro e
    have h1 := (sec8_rf_proved k hk G f hf).2 F hF e
    have h2 := (sec8_rf_proved k hk G f hf).2 F' hF' e
    simp only [hh]
    split_ifs with ha hb <;> omega
  have hval : ∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1 := by
    intro e; simp only [hh]; split_ifs <;> simp
  have hcirc : G.IsFlow h := by
    apply isFlow_of_mul h k hkz
    have : (fun e => (k : ℤ) * h e) = fun e => F' e - F e := by
      funext e; rw [hFF e]; ring
    rw [this]
    exact IsFlow.sub hF'.1.1 hF.1.1
  obtain ⟨Qs, -, hsign, hsum, -⟩ := circ_decomp h hval hcirc
  -- `Qs` is not empty, since `h ≠ 0`
  obtain ⟨e₀, he₀⟩ := Function.ne_iff.1 hne
  obtain ⟨Q, Qs', rfl⟩ : ∃ Q Qs', Qs = Q :: Qs' := by
    cases Qs with
    | nil =>
      exfalso
      have h0 : h e₀ = 0 := by rw [← hsum e₀]; rfl
      exact he₀ (by rw [hFF e₀, h0]; ring)
    | cons Q Qs' => exact ⟨Q, Qs', rfl⟩
  have hQ : ∀ e, Q.chi e ≠ 0 → Q.chi e = h e := hsign Q List.mem_cons_self
  obtain ⟨F₁, hF₁def⟩ : ∃ F₁ : E → ℤ, F₁ = F + fun e => Q.chi e • (k : ℤ) := ⟨_, rfl⟩
  -- on every edge `F₁` is `F` (off `Q`) or `F'` (on `Q`)
  have hon : ∀ e, Q.chi e ≠ 0 → F₁ e = F' e := by
    intro e he
    simp only [hF₁def, Pi.add_apply, smul_eq_mul]
    rw [hQ e he, hFF e]
  have hoff : ∀ e, Q.chi e = 0 → F₁ e = F e := by
    intro e he
    simp only [hF₁def, Pi.add_apply, he, zero_smul, add_zero]
  have hcase : ∀ e, F₁ e = F e ∨ F₁ e = F' e := by
    intro e
    by_cases he : Q.chi e = 0
    · exact Or.inl (hoff e he)
    · exact Or.inr (hon e he)
  have hF₁ : G.IsIntLift k f F₁ := by
    refine ⟨⟨?_, fun e => ?_⟩, fun e => ?_⟩
    · rw [hF₁def]
      exact IsFlow.add hF.1.1 (IsFlow.zsmul_const Q.isFlow_chi (k : ℤ))
    · rcases hcase e with h1 | h1 <;> rw [h1]
      · exact hF.1.2 e
      · exact hF'.1.2 e
    · rcases hcase e with h1 | h1 <;> rw [h1]
      · exact hF.2 e
      · exact hF'.2 e
  -- an edge of `Q`, where `F₁ = F' ≠ F`
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ Q.ne_nil
  have hchi : Q.chi d.1 ≠ 0 := by rw [Q.chi_of_mem hd]; exact dartSign_ne_zero _
  have hdF : F d.1 ≠ F' d.1 := by
    intro hEq
    have h0 : h d.1 * k = 0 := by linear_combination -(hEq + hFF d.1)
    exact hchi ((hQ d.1 hchi).trans ((mul_eq_zero.1 h0).resolve_right hkz))
  have hd1 : F₁ d.1 = F' d.1 := hon d.1 hchi
  refine ⟨F₁, hF₁, ?_, ?_⟩
  · rw [kFlowGraph, stepGraph, SimpleGraph.fromRel_adj]
    refine ⟨fun hEq => hdF ?_, Or.inl ⟨Q, (k : ℤ), hkz, hkz, hF₁def⟩⟩
    rw [Subtype.mk.injEq] at hEq
    rw [hEq, hd1]
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨d.1, by simpa using hdF, by simp [hd1]⟩
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      rcases hcase e with h1 | h1
      · rwa [h1] at he
      · exact absurd h1 he

/-- Any two integer lifts of `f` are joined in `𝓕(G, k)` by a walk all of whose `k`-flows are integer lifts of `f`. -/
lemma fibre_walk [Fintype V] (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (f : E → ZMod k) (F F' : E → ℤ)
    (hF : G.IsIntLift k f F) (hF' : G.IsIntLift k f F') :
    ∃ W : (G.kFlowGraph k).Walk ⟨F, hF.1⟩ ⟨F', hF'.1⟩, ∀ X ∈ W.support, G.IsIntLift k f X.1 := by
  suffices key : ∀ n, ∀ F : E → ℤ, ∀ hF : G.IsIntLift k f F, (univ.filter fun e => F e ≠ F' e).card = n →
      ∃ W : (G.kFlowGraph k).Walk ⟨F, hF.1⟩ ⟨F', hF'.1⟩, ∀ X ∈ W.support, G.IsIntLift k f X.1 from
    key _ F hF rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F hF hn
    by_cases hne : F = F'
    · subst hne
      refine ⟨SimpleGraph.Walk.nil, fun X hX => ?_⟩
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hX
      rw [hX]
      exact hF
    · obtain ⟨F₁, hF₁, hadj, hlt⟩ := fibre_step hk hF hF' hne
      obtain ⟨W, hW⟩ := ih (univ.filter fun e => F₁ e ≠ F' e).card (by omega) F₁ hF₁ rfl
      refine ⟨SimpleGraph.Walk.cons hadj W, fun X hX => ?_⟩
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hX
      rcases hX with rfl | hX
      · exact hF
      · exact hW X hX

/-- `lem_8_4_fibre` (Lemma 7.4): any two integer lifts of `f` are joined in `𝓕(G, k)` by a path all of whose
`k`-flows are integer lifts of `f` (the walk of `fibre_walk`, with its loops removed by `Walk.bypass`). -/
theorem lem_8_4_fibre_proved [Fintype V] (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (f : E → ZMod k) (F F' : E → ℤ)
    (hF : G.IsIntLift k f F) (hF' : G.IsIntLift k f F') :
    ∃ W : (G.kFlowGraph k).Walk ⟨F, hF.1⟩ ⟨F', hF'.1⟩, W.IsPath ∧ ∀ X ∈ W.support, G.IsIntLift k f X.1 := by
  classical
  obtain ⟨W, hW⟩ := fibre_walk k hk G f F F' hF hF'
  exact ⟨W.bypass, W.bypass_isPath, fun X hX => hW X (W.support_bypass_subset_support hX)⟩

/-! ### The chain of `k`-flows keeps the residues -/

/-- `lift_step_pos` with the relation of the two lifts: one step `b = a + t χ_Q`, `t ∈ {1, 2}`, has integer lifts
`F_a`, `F_b = F_a + t χ_Q`. -/
lemma lift_step_rel_pos [Fintype V] {k : ℕ} (hk : 3 ≤ k) (Q : G.DirCycle) (a b : E → ZMod k)
    (ha : G.IsNZFlow a) (hb : G.IsNZFlow b) (t : ℕ) (ht : t = 1 ∨ t = 2)
    (hab : b = a + fun e => Q.chi e • (t : ZMod k)) :
    ∃ Fa Fb : E → ℤ, G.IsIntLift k a Fa ∧ G.IsIntLift k b Fb ∧
      ∃ l : ℤ, l ≠ 0 ∧ Fb = Fa + fun e => Q.chi e • l := by
  rcases ht with rfl | rfl
  · obtain ⟨Fa, hFa⟩ := lem_8_3_proved k (by omega) G a ha
    have hb' : G.IsNZFlow (a + fun e => Q.chi e • (1 : ZMod k)) := by simpa [hab] using hb
    have hFb := lem_8_5_proved k (by omega) G Q a ha hb' Fa hFa
    have hFb' : G.IsIntLift k b (Fa + fun e => Q.chi e • (1 : ℤ)) := by simpa [hab] using hFb
    exact ⟨Fa, _, hFa, hFb', 1, one_ne_zero, rfl⟩
  · have hb' : G.IsNZFlow (a + fun e => Q.chi e • (2 : ZMod k)) := by simpa [hab] using hb
    obtain ⟨Fa, hFa, hFb⟩ := lem_8_6_proved k hk G Q a ha hb'
    have hFb' : G.IsIntLift k b (Fa + fun e => Q.chi e • (2 : ℤ)) := by simpa [hab] using hFb
    exact ⟨Fa, _, hFa, hFb', 2, two_ne_zero, rfl⟩

/-- `lift_step` with the relation of the two lifts: one step `b = a + t χ_Q`, `t ∈ {1, -1, 2, -2}`, has integer lifts
`F_a`, `F_b` that differ by `l χ_Q`, `l ≠ 0`. -/
lemma lift_step_rel [Fintype V] {k : ℕ} (hk : 3 ≤ k) (Q : G.DirCycle) (a b : E → ZMod k) (ha : G.IsNZFlow a)
    (hb : G.IsNZFlow b) (t : ZMod k) (ht : t ∈ Tcyc k) (hab : b = a + fun e => Q.chi e • t) :
    ∃ Fa Fb : E → ℤ, G.IsIntLift k a Fa ∧ G.IsIntLift k b Fb ∧
      ∃ l : ℤ, l ≠ 0 ∧ (Fb = Fa + (fun e => Q.chi e • l) ∨ Fa = Fb + fun e => Q.chi e • l) := by
  simp only [Tcyc, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · obtain ⟨Fa, Fb, hFa, hFb, l, hl, h⟩ := lift_step_rel_pos hk Q a b ha hb 1 (Or.inl rfl) (by simpa using hab)
    exact ⟨Fa, Fb, hFa, hFb, l, hl, Or.inl h⟩
  · -- `a = b + χ_Q`: the value-1 step from the other end
    obtain ⟨Fb, Fa, hFb, hFa, l, hl, h⟩ := lift_step_rel_pos hk Q b a hb ha 1 (Or.inl rfl)
      (by rw [hab]; funext e; simp)
    exact ⟨Fa, Fb, hFa, hFb, l, hl, Or.inr h⟩
  · obtain ⟨Fa, Fb, hFa, hFb, l, hl, h⟩ := lift_step_rel_pos hk Q a b ha hb 2 (Or.inr rfl) (by simpa using hab)
    exact ⟨Fa, Fb, hFa, hFb, l, hl, Or.inl h⟩
  · obtain ⟨Fb, Fa, hFb, hFa, l, hl, h⟩ := lift_step_rel_pos hk Q b a hb ha 2 (Or.inr rfl)
      (by rw [hab]; funext e; simp)
    exact ⟨Fa, Fb, hFa, hFb, l, hl, Or.inr h⟩

omit [DecidableEq E] in
/-- An integer flow lifts at most one `ℤ_k`-flow: a lift determines its residues. -/
lemma residues_eq_of_lift {k : ℕ} {f g : E → ZMod k} {F : E → ℤ} (hf : G.IsIntLift k f F)
    (hg : G.IsIntLift k g F) : f = g := by
  funext e
  rw [← hf.2 e, ← hg.2 e]

/-- Lifts of two DIFFERENT `ℤ_k`-flows that differ by `l χ_Q`, `l ≠ 0`, are adjacent in `𝓕(G, k)`. -/
lemma adj_of_lifts {k : ℕ} {a b : E → ZMod k} (hab : a ≠ b) (Q : G.DirCycle) {Fa Fb : E → ℤ}
    (hFa : G.IsIntLift k a Fa) (hFb : G.IsIntLift k b Fb) (l : ℤ) (hl : l ≠ 0)
    (h : Fb = Fa + (fun e => Q.chi e • l) ∨ Fa = Fb + fun e => Q.chi e • l) :
    (G.kFlowGraph k).Adj ⟨Fa, hFa.1⟩ ⟨Fb, hFb.1⟩ := by
  rw [kFlowGraph, stepGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun hEq => hab ?_, ?_⟩
  · rw [Subtype.mk.injEq] at hEq
    rw [hEq] at hFa
    exact residues_eq_of_lift hFa hFb
  · rcases h with h | h
    · exact Or.inl ⟨Q, l, hl, hl, h⟩
    · exact Or.inr ⟨Q, l, hl, hl, h⟩

/-- `sec7_chain_lift`, by induction on the chain `w` as in `lifts_joined_of_walk`: a fibre path from the given lift of
the first flow to a lift of the first step, the step's edge, then the walk of the rest of the chain. -/
lemma chain_lift_aux [Fintype V] {k : ℕ} (hk : 3 ≤ k) {a b : {f : E → ZMod k // G.IsNZFlow f}}
    (w : (G.tStepGraph (Tcyc k)).Walk a b) :
    ∀ (Fa Fb : E → ℤ) (hFa : G.IsIntLift k a.1 Fa) (hFb : G.IsIntLift k b.1 Fb),
    ∃ (W : (G.kFlowGraph k).Walk ⟨Fa, hFa.1⟩ ⟨Fb, hFb.1⟩) (φ : ℕ → ℕ),
      φ 0 = 0 ∧ φ W.length = w.length ∧
      (∀ j < W.length, φ (j + 1) = φ j ∨ φ (j + 1) = φ j + 1) ∧
      (∀ j ≤ W.length, G.IsIntLift k (w.getVert (φ j)).1 (W.getVert j).1) ∧
      (∀ j₁ j₂, j₁ < j₂ → j₂ ≤ W.length → φ j₁ = φ j₂ → W.getVert j₁ ≠ W.getVert j₂) ∧
      (w.IsPath → W.IsPath) := by
  induction w with
  | nil =>
    intro Fa Fb hFa hFb
    obtain ⟨P, hP, hPl⟩ := lem_8_4_fibre_proved k (by omega) G _ Fa Fb hFa hFb
    refine ⟨P, fun _ => 0, rfl, rfl, fun _ _ => Or.inl rfl, fun j _ => ?_,
      fun j₁ j₂ hlt hle _ hEq => ?_, fun _ => hP⟩
    · -- `Walk.nil.getVert 0` is the vertex `a` itself
      exact hPl _ (P.getVert_mem_support j)
    · exact hlt.ne (hP.getVert_injOn (show j₁ ≤ P.length by omega) (show j₂ ≤ P.length from hle) hEq)
  | @cons a c b hadj w ih =>
    intro Fa Fb hFa hFb
    have hadj' : a ≠ c ∧ ((∃ Q : G.DirCycle, ∃ t ∈ Tcyc k, t ≠ 0 ∧ c.1 = a.1 + fun e => Q.chi e • t) ∨
        (∃ Q : G.DirCycle, ∃ t ∈ Tcyc k, t ≠ 0 ∧ a.1 = c.1 + fun e => Q.chi e • t)) := hadj
    have hac : a.1 ≠ c.1 := fun h => hadj'.1 (Subtype.ext h)
    -- lifts `G_a`, `G_c` of the two ends of the first step, adjacent in `𝓕(G, k)`
    obtain ⟨Ga, Gc, hGa, hGc, Q, l, hl, hrel⟩ : ∃ Ga Gc : E → ℤ, G.IsIntLift k a.1 Ga ∧ G.IsIntLift k c.1 Gc ∧
        ∃ Q : G.DirCycle, ∃ l : ℤ, l ≠ 0 ∧
          (Gc = Ga + (fun e => Q.chi e • l) ∨ Ga = Gc + fun e => Q.chi e • l) := by
      rcases hadj'.2 with ⟨Q, t, ht, _, h⟩ | ⟨Q, t, ht, _, h⟩
      · obtain ⟨Ga, Gc, hGa, hGc, l, hl, hr⟩ := lift_step_rel hk Q a.1 c.1 a.2 c.2 t ht h
        exact ⟨Ga, Gc, hGa, hGc, Q, l, hl, hr⟩
      · obtain ⟨Gc, Ga, hGc, hGa, l, hl, hr⟩ := lift_step_rel hk Q c.1 a.1 c.2 a.2 t ht h
        exact ⟨Ga, Gc, hGa, hGc, Q, l, hl, hr.symm⟩
    have hA := adj_of_lifts hac Q hGa hGc l hl hrel
    obtain ⟨P, hP, hPl⟩ := lem_8_4_fibre_proved k (by omega) G _ Fa Ga hFa hGa
    obtain ⟨W', φ', h0', hlen', hstep', hlift', hrun', hpath'⟩ := ih Gc Fb hGc hFb
    -- `W = P, then the edge G_a G_c, then W'`; `φ = 0` on `P`, then `φ' + 1`
    obtain ⟨W, hW⟩ : ∃ W : (G.kFlowGraph k).Walk ⟨Fa, hFa.1⟩ ⟨Fb, hFb.1⟩,
        W = P.append (SimpleGraph.Walk.cons hA W') := ⟨_, rfl⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℕ, ∀ j, φ j = if j ≤ P.length then 0 else φ' (j - P.length - 1) + 1 :=
      ⟨_, fun _ => rfl⟩
    have hWlen : W.length = P.length + (W'.length + 1) := by
      rw [hW, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
    have hWlo : ∀ j, j ≤ P.length → W.getVert j = P.getVert j := fun j hj => by
      rw [hW, SimpleGraph.Walk.getVert_append', ite_eq_left hj]
    have hWhi : ∀ j, P.length < j → W.getVert j = W'.getVert (j - P.length - 1) := fun j hj => by
      rw [hW, SimpleGraph.Walk.getVert_append', ite_eq_right (not_le.2 hj)]
      exact SimpleGraph.Walk.getVert_cons _ _ (by omega)
    have hφlo : ∀ j, j ≤ P.length → φ j = 0 := fun j hj => by rw [hφ, ite_eq_left hj]
    have hφhi : ∀ j, P.length < j → φ j = φ' (j - P.length - 1) + 1 := fun j hj => by
      rw [hφ, ite_eq_right (not_le.2 hj)]
    refine ⟨W, φ, hφlo 0 (Nat.zero_le _), ?_, ?_, ?_, ?_, ?_⟩
    · -- `φ` ends at the length of the chain
      rw [hWlen, hφhi (P.length + (W'.length + 1)) (by omega),
        show P.length + (W'.length + 1) - P.length - 1 = W'.length by omega, hlen', SimpleGraph.Walk.length_cons]
    · -- `φ` rises by `0` or `1`
      intro j hj
      rw [hWlen] at hj
      by_cases h1 : j + 1 ≤ P.length
      · left
        rw [hφlo (j + 1) h1, hφlo j (by omega)]
      · by_cases h2 : j ≤ P.length
        · right
          rw [hφhi (j + 1) (by omega), hφlo j h2, show j + 1 - P.length - 1 = 0 by omega, h0']
        · rw [hφhi (j + 1) (by omega), hφhi j (by omega),
            show j + 1 - P.length - 1 = (j - P.length - 1) + 1 by omega]
          rcases hstep' (j - P.length - 1) (by omega) with h | h
          · left
            rw [h]
          · right
            rw [h]
    · -- the `j`-th `k`-flow of `W` lifts the `φ(j)`-th flow of the chain
      intro j hj
      rw [hWlen] at hj
      by_cases h : j ≤ P.length
      · rw [hφlo j h, hWlo j h, SimpleGraph.Walk.getVert_zero]
        exact hPl _ (P.getVert_mem_support j)
      · rw [hφhi j (by omega), hWhi j (by omega), SimpleGraph.Walk.getVert_cons_succ]
        exact hlift' _ (by omega)
    · -- no `k`-flow repeats inside a run
      intro j₁ j₂ hlt hle hφeq hEq
      rw [hWlen] at hle
      by_cases h2 : j₂ ≤ P.length
      · rw [hWlo j₁ (by omega), hWlo j₂ h2] at hEq
        exact hlt.ne (hP.getVert_injOn (show j₁ ≤ P.length by omega) (show j₂ ≤ P.length from h2) hEq)
      · by_cases h1 : j₁ ≤ P.length
        · rw [hφlo j₁ h1, hφhi j₂ (by omega)] at hφeq
          omega
        · rw [hφhi j₁ (by omega), hφhi j₂ (by omega)] at hφeq
          rw [hWhi j₁ (by omega), hWhi j₂ (by omega)] at hEq
          exact hrun' (j₁ - P.length - 1) (j₂ - P.length - 1) (by omega) (by omega)
            (Nat.add_right_cancel hφeq) hEq
    · -- `W` is a path when the chain is: the lifts of `a` (on `P`) are not lifts of the later flows
      intro hw
      rw [SimpleGraph.Walk.cons_isPath_iff] at hw
      obtain ⟨hw', ha⟩ := hw
      rw [hW, SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons,
        List.tail_cons, List.nodup_append]
      refine ⟨hP.support_nodup, (hpath' hw').support_nodup, fun X hX Y hY hXY => ?_⟩
      subst hXY
      obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hY
      have h2 := hlift' n hnle
      rw [hn] at h2
      apply ha
      rw [Subtype.ext (residues_eq_of_lift (hPl X hX) h2)]
      exact SimpleGraph.Walk.getVert_mem_support _ _

/-- `sec7_chain_lift` (Section 7 opening l.550-552, abstract l.44-45): a chain `w` of `ℤ_k`-flows with step values in
`{1,-1,2,-2}` becomes a walk `W` in `𝓕(G, k)` from any lift of its first flow to any lift of its last flow; the `j`-th
`k`-flow of `W` lifts the `φ(j)`-th flow of `w`, where `φ` runs from `0` to the length of `w` in steps of `0` or `1`;
no `k`-flow repeats inside a run, and `W` is a path when `w` is. -/
theorem sec7_chain_lift_proved [Fintype V] (k : ℕ) (hk : 3 ≤ k) (G : MGraph V E)
    {a b : {f : E → ZMod k // G.IsNZFlow f}} (w : (G.tStepGraph (Tcyc k)).Walk a b)
    (Fa Fb : E → ℤ) (hFa : G.IsIntLift k a.1 Fa) (hFb : G.IsIntLift k b.1 Fb) :
    ∃ (W : (G.kFlowGraph k).Walk ⟨Fa, hFa.1⟩ ⟨Fb, hFb.1⟩) (φ : ℕ → ℕ),
      φ 0 = 0 ∧ φ W.length = w.length ∧
      (∀ j < W.length, φ (j + 1) = φ j ∨ φ (j + 1) = φ j + 1) ∧
      (∀ j ≤ W.length, G.IsIntLift k (w.getVert (φ j)).1 (W.getVert j).1) ∧
      (∀ j₁ j₂, j₁ < j₂ → j₂ ≤ W.length → φ j₁ = φ j₂ → W.getVert j₁ ≠ W.getVert j₂) ∧
      (w.IsPath → W.IsPath) :=
  chain_lift_aux hk w Fa Fb hFa hFb

end Sec8

end EulerFlow
