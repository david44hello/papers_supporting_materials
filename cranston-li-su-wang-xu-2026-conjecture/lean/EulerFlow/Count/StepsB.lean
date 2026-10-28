/-
EulerFlow/Count/StepsB.lean — paper 002, Theorem 2.5, second part (tex l.549-556): for `|A| ≥ 4` and an even graph
with `M` edges, any two flows are joined by at most `16M³ + 12M² + M` steps.
Route = the paper's: count multi-steps along the proof of Theorem 2.3. A loop costs one more multi-step (Lemma 3.1).
Loopless graphs: induction on `Φ`; the blow-up `G⁺` keeps `2M + 3Φ` (three more edges, `Φ` two less), and a walk of
multi-steps of `G⁺` gives a walk of `G⁺/Δ ≅ G` that is not longer (Lemma 5.1); at `Φ = 0` Theorem 2.5 (a) counts
`B(M) = M² + 3M + 1`. As `Φ ≤ 2M`, every even graph needs at most `B(4M) = 16M² + 12M + 1` multi-steps, each at most
`M` steps.
-/
import EulerFlow.Count.StepsA
import EulerFlow.Reduction.Expand
import EulerFlow.Reduction.Triangle

namespace EulerFlow

namespace Count

open Finset MGraph

/-- A map that sends every edge to an edge or to a single vertex does not lengthen walks. -/
lemma walk_transport {α β : Type} {G₁ : SimpleGraph α} {G₂ : SimpleGraph β} (ψ : α → β)
    (hψ : ∀ a b, G₁.Adj a b → ψ a = ψ b ∨ G₂.Adj (ψ a) (ψ b)) {a b : α} (w : G₁.Walk a b) :
    ∃ w' : G₂.Walk (ψ a) (ψ b), w'.length ≤ w.length := by
  induction w with
  | nil => exact ⟨SimpleGraph.Walk.nil, le_refl _⟩
  | cons hadj w ih =>
    obtain ⟨w', hw'⟩ := ih
    rcases hψ _ _ hadj with h | h
    · rw [h]; exact ⟨w', by rw [SimpleGraph.Walk.length_cons]; omega⟩
    · exact ⟨SimpleGraph.Walk.cons h w', by simp only [SimpleGraph.Walk.length_cons]; omega⟩

section Blowup

variable {V E V₂ E₂ : Type} [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype E₂] [DecidableEq V₂]
  [DecidableEq E₂] {A : Type} [AddCommGroup A] {G : MGraph V E} {H : MGraph V₂ E₂}
  {x₁ x₂ x₃ : V} {d₁₂ d₂₃ d₃₁ : E}

/-- A map on `E(G)` read on `H ≅ G/Δ`: restrict to the edges outside `Δ`, then move along the isomorphism. -/
def pull {M : Type} (φ : EdgeIso (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}) H) (F : E → M) : E₂ → M :=
  fun e => F (φ.eE.symm e).1

omit [Fintype E] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂] in
lemma pull_eq {M : Type} (φ : EdgeIso (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}) H) (F : E → M) (g : E₂ → M)
    (hF : restrictTo {d₁₂, d₂₃, d₃₁} F = fun e => g (φ.eE e)) : pull φ F = g := by
  funext e
  have := congr_fun hF (φ.eE.symm e)
  simpa [restrictTo, pull] using this

lemma isIFlow_pull (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁)
    (φ : EdgeIso (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}) H) {M : Type} [AddCommGroup M] {I : Set M}
    {F : E → M} (hF : G.IsIFlow I F) : H.IsIFlow I (pull φ F) := by
  rw [φ.isIFlow_iff]
  convert isIFlow_restrictTo hΔ.mem hF using 1
  funext e
  simp [pull, restrictTo]

lemma isFlow_pull (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁)
    (φ : EdgeIso (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}) H) {M : Type} [AddCommGroup M]
    {F : E → M} (hF : G.IsFlow F) : H.IsFlow (pull φ F) := by
  rw [φ.isFlow_iff]
  convert isFlow_restrictTo hΔ.mem hF using 1
  funext e
  simp [pull, restrictTo]

/-- Lemma 5.1 (b) in `h`-form, read on `H`: a multi-step of `G` gives the identity or a multi-step of `H`. -/
lemma pull_circStep (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁)
    (φ : EdgeIso (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}) H) {F F' : E → A} (hstep : CircStep G F F') :
    pull φ F' = pull φ F ∨ CircStep H (pull φ F) (pull φ F') := by
  obtain ⟨t, ht, h, hval, hfl, -, heq⟩ := hstep
  have hpull : pull φ F' = pull φ F + fun e => pull φ h e • t := by
    rw [heq]; rfl
  by_cases h0 : ∃ e, pull φ h e ≠ 0
  · exact Or.inr ⟨t, ht, pull φ h, fun e => hval _, isFlow_pull hΔ φ hfl, h0, hpull⟩
  · left
    simp only [not_exists, not_not] at h0
    rw [hpull]
    funext e
    simp [h0 e]

/-- The pulled flow, as a vertex of the multi-step graph of `H`. -/
def pullNZ (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁)
    (φ : EdgeIso (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}) H) (F : {f : E → A // G.IsNZFlow f}) :
    {f : E₂ → A // H.IsNZFlow f} :=
  ⟨pull φ F.1, isIFlow_pull hΔ φ F.2⟩

lemma pull_adj (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁)
    (φ : EdgeIso (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}) H) (F F' : {f : E → A // G.IsNZFlow f})
    (hadj : (msGraph G A).Adj F F') :
    pullNZ hΔ φ F = pullNZ hΔ φ F' ∨ (msGraph H A).Adj (pullNZ hΔ φ F) (pullNZ hΔ φ F') := by
  by_cases heq : pullNZ hΔ φ F = pullNZ hΔ φ F'
  · exact Or.inl heq
  · right
    rw [msGraph, SimpleGraph.fromRel_adj] at hadj ⊢
    refine ⟨heq, ?_⟩
    rcases hadj.2 with h | h
    · rcases pull_circStep hΔ φ h with h' | h'
      · exact absurd (Subtype.ext h'.symm) heq
      · exact Or.inl h'
    · rcases pull_circStep hΔ φ h with h' | h'
      · exact absurd (Subtype.ext h') heq
      · exact Or.inr h'

end Blowup

variable {A : Type} [AddCommGroup A]

/-- The multi-step count of Theorem 2.3's induction on `Φ` (tex l.550-554): a loopless even graph with
`2M + 3Φ ≤ 2k` has any two flows joined by at most `k² + 3k + 1` multi-steps. -/
theorem ms_bound_loopless [Fintype A] (hA : 4 ≤ Fintype.card A) :
    ∀ n, ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      G.phi = n → G.Loopless → G.IsEven → ∀ k, 2 * Fintype.card E + 3 * G.phi ≤ 2 * k →
      ∀ f f' : {f : E → A // G.IsNZFlow f}, ∃ w : (msGraph G A).Walk f f', w.length ≤ k ^ 2 + 3 * k + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V E _ _ _ _ G hn hG hev k hk f f'
  -- `Φ = 0`: all degrees at most 4, Theorem 2.5 (a)
  by_cases hdeg : ∀ v, G.degree v ≤ 4
  · obtain ⟨w, hw⟩ := ms_bound G hev hdeg f f'
    refine ⟨w, hw.trans ?_⟩
    have : Fintype.card E ≤ k := by omega
    nlinarith
  simp only [not_forall, not_le] at hdeg
  obtain ⟨v, hv⟩ := hdeg
  have hv6 : 6 ≤ G.degree v := by obtain ⟨j, hj⟩ := hev v; omega
  obtain ⟨S₁, S₂, hΔ, hl, hev', hphi, ⟨φ⟩⟩ := exists_expand hG hev hv6
  -- lift both flows to `G⁺` (Lemma 5.1 (a))
  have hlift := (lem_5_1_a_proved hA (G.expandAt v S₁ S₂) (.inr 0) (.inr 1) (.inl v) (.inr 0) (.inr 1) (.inr 2)
    hΔ).2
  obtain ⟨F₁, hF₁, hr₁⟩ := hlift _ ((φ.isIFlow_iff f.1).1 f.2)
  obtain ⟨F₂, hF₂, hr₂⟩ := hlift _ ((φ.isIFlow_iff f'.1).1 f'.2)
  -- the induction hypothesis on `G⁺`: same `k`, since `2(M + 3) + 3(Φ - 2) = 2M + 3Φ`
  have hk' : 2 * Fintype.card (E ⊕ Fin 3) + 3 * (G.expandAt v S₁ S₂).phi ≤ 2 * k := by
    rw [Fintype.card_sum, Fintype.card_fin]; omega
  obtain ⟨W, hW⟩ := ih _ (by omega) _ _ (G.expandAt v S₁ S₂) rfl hl hev' k hk' ⟨F₁, hF₁⟩ ⟨F₂, hF₂⟩
  -- read the walk on `G ≅ G⁺/Δ` (Lemma 5.1 (b))
  obtain ⟨w, hw⟩ := walk_transport (pullNZ hΔ φ) (pull_adj hΔ φ) W
  have e₁ : pullNZ hΔ φ ⟨F₁, hF₁⟩ = f := Subtype.ext (pull_eq φ F₁ f.1 hr₁)
  have e₂ : pullNZ hΔ φ ⟨F₂, hF₂⟩ = f' := Subtype.ext (pull_eq φ F₂ f'.1 hr₂)
  exact ⟨w.copy e₁ e₂, by rw [SimpleGraph.Walk.length_copy]; omega⟩

/-- Every even graph with `M` edges has any two flows joined by at most `16M² + 12M + 1` multi-steps; loops first,
one multi-step each (Lemma 3.1, tex l.449). -/
theorem ms_bound_even [Fintype A] (hA : 4 ≤ Fintype.card A) :
    ∀ n, ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : MGraph V E),
      Fintype.card E = n → G.IsEven → ∀ f f' : {f : E → A // G.IsNZFlow f},
      ∃ w : (msGraph G A).Walk f f', w.length ≤ 16 * n ^ 2 + 12 * n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V E _ _ _ _ G hn hev f f'
  subst hn
  by_cases hloop : ∃ l, G.IsLoop l
  · obtain ⟨l, hl⟩ := hloop
    have hlt := card_deleteEdge_lt l
    obtain ⟨w₁, hw₁⟩ := ih _ hlt V _ (G.deleteEdge l) rfl (isEven_deleteEdge hl hev)
      ⟨fun x => f.1 x.1, isIFlow_restrict hl f.2⟩ ⟨fun x => f'.1 x.1, isIFlow_restrict hl f'.2⟩
    set φ := loopHom (A := A) hl (f.1 l) (f.2.2 l) with hφ
    have hstart : φ ⟨fun x => f.1 x.1, isIFlow_restrict hl f.2⟩ = f := Subtype.ext (extLoop_restrict f.1)
    -- the last multi-step changes the value on the loop
    have hoff : ∀ y, y ≠ l → extLoop l (fun x => f'.1 x.1) (f.1 l) y = f'.1 y := by
      intro y hy; simp [extLoop, hy]
    have hat : extLoop l (fun x => f'.1 x.1) (f.1 l) l = f.1 l := by simp [extLoop]
    obtain ⟨w₂, hw₂⟩ := msWalk_le_one G (φ ⟨fun x => f'.1 x.1, isIFlow_restrict hl f'.2⟩) f' (by
      by_cases hfl : f.1 l = f'.1 l
      · left
        show f'.1 = extLoop l (fun x => f'.1 x.1) (f.1 l)
        rw [hfl, extLoop_restrict]
      · right
        show CircStep G (extLoop l (fun x => f'.1 x.1) (f.1 l)) f'.1
        have := loop_circStep hl (extLoop l (fun x => f'.1 x.1) (f.1 l)) (f'.1 l) (by rw [hat]; exact Ne.symm hfl)
        convert this using 1
        funext y
        by_cases hy : y = l
        · subst hy; simp [hat]
        · simp [hy, hoff y hy])
    refine ⟨((w₁.map φ).copy hstart rfl).append w₂, ?_⟩
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
    have hm : Fintype.card {x : E // x ≠ l} + 1 ≤ Fintype.card E := hlt
    nlinarith
  -- loopless: the `Φ`-induction with `k = 4M`, as `Φ ≤ 2M`
  have hphi : G.phi ≤ 2 * Fintype.card E := by
    rw [← MGraph.Sec4.sum_degree (G := G)]
    exact Finset.sum_le_sum fun v _ => Nat.sub_le _ _
  obtain ⟨w, hw⟩ := ms_bound_loopless hA _ V E G rfl (fun e he => hloop ⟨e, he⟩) hev (4 * Fintype.card E)
    (by omega) f f'
  exact ⟨w, hw.trans (le_of_eq (by ring))⟩

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- `thm_2_5_b` (Theorem 2.5, second part, tex l.188-189, l.549-556). -/
theorem thm_2_5_b_proved (A : Type) [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A) (G : MGraph V E)
    (hev : G.IsEven) (f f' : {f : E → A // G.IsNZFlow f}) :
    ∃ w : (G.flowGraph A).Walk f f',
      w.length ≤ 16 * Fintype.card E ^ 3 + 12 * Fintype.card E ^ 2 + Fintype.card E := by
  obtain ⟨w, hw⟩ := ms_bound_even hA _ V E G rfl hev f f'
  obtain ⟨w', hw'⟩ := flowWalk_of_msWalk G w
  refine ⟨w', hw'.trans ?_⟩
  calc Fintype.card E * w.length ≤ Fintype.card E * (16 * Fintype.card E ^ 2 + 12 * Fintype.card E + 1) :=
        Nat.mul_le_mul_left _ hw
    _ = 16 * Fintype.card E ^ 3 + 12 * Fintype.card E ^ 2 + Fintype.card E := by ring

end Count

end EulerFlow
