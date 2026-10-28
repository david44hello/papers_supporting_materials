/-
EulerFlow/Reduction/Const.lean — Lemma 3.3 of paper 002 (constant flows, tex l.271-292): `a 𝟙_D` is a flow;
two of them are equal or one multi-step with the value `-2a` apart; `B(v; e, e')` contains one.
-/
import EulerFlow.Reduction.SplitLemma

namespace EulerFlow

open Finset

namespace MGraph

variable {V E : Type} {G : MGraph V E} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- `σ_D`: `-1` on the edges that `D` reverses, `1` on the others. -/
def orientSign (D : E → Bool) : E → ℤ := fun e => if D e then -1 else 1

omit [Fintype E] [DecidableEq E] in
theorem constFlow_eq_smul {A : Type} [AddCommGroup A] (a : A) (D : E → Bool) :
    constFlow a D = fun e => orientSign D e • a := by
  funext e; simp only [constFlow, orientSign]; split_ifs <;> simp

omit [DecidableEq E] in
theorem boundary_zsmul {A : Type} [AddCommGroup A] (h : E → ℤ) (t : A) (z : V) :
    G.boundary (fun e => h e • t) z = G.boundary h z • t := by
  simp only [boundary, Finset.sum_smul, sub_smul]

omit [DecidableEq E] in
theorem isFlow_zsmul {A : Type} [AddCommGroup A] {h : E → ℤ} (hh : G.IsFlow h) (t : A) :
    G.IsFlow (fun e => h e • t) := by
  rw [isFlow_iff_boundary] at *; intro z; rw [boundary_zsmul, hh, zero_smul]

omit [DecidableEq E] in
theorem boundary_sub {M : Type} [AddCommGroup M] (x y : E → M) (z : V) :
    G.boundary (x - y) z = G.boundary x z - G.boundary y z := by
  simp only [boundary, Pi.sub_apply, Finset.sum_sub_distrib]; abel

omit [DecidableEq E] in
/-- `a 𝟙_D` is an `I`-flow for an Eulerian orientation `D` and `a ∈ I`, `I = -I` (tex l.273). -/
theorem isIFlow_constFlow {A : Type} [AddCommGroup A] {I : Set A} (hI : ∀ y ∈ I, -y ∈ I) {D : E → Bool}
    (hD : G.IsEulerOrient D) {a : A} (ha : a ∈ I) : G.IsIFlow I (constFlow a D) := by
  refine ⟨?_, fun e => ?_⟩
  · rw [constFlow_eq_smul]; exact isFlow_zsmul ((isEulerOrient_iff D).1 hD) a
  · simp only [constFlow]; split_ifs
    · exact hI _ ha
    · exact ha

/-- The edges reversed between `D` and `D₂`, with the sign of `D`. -/
def reversedSign (D D₂ : E → Bool) : E → ℤ := fun e => if D e = D₂ e then 0 else orientSign D e

omit [Fintype E] [DecidableEq E] in
theorem reversedSign_mem (D D₂ : E → Bool) (e : E) :
    reversedSign D D₂ e = -1 ∨ reversedSign D D₂ e = 0 ∨ reversedSign D D₂ e = 1 := by
  simp only [reversedSign, orientSign]; split_ifs <;> simp

omit [DecidableEq E] in
/-- The arcs of `D` reversed in `D₂` carry an integer flow (tex l.282-283). -/
theorem isFlow_reversedSign {D D₂ : E → Bool} (hD : G.IsEulerOrient D) (hD₂ : G.IsEulerOrient D₂) :
    G.IsFlow (reversedSign D D₂) := by
  have h1 := (isFlow_iff_boundary G _).1 ((isEulerOrient_iff D).1 hD)
  have h2 := (isFlow_iff_boundary G _).1 ((isEulerOrient_iff D₂).1 hD₂)
  have htwo : (fun e => 2 * reversedSign D D₂ e) = orientSign D - orientSign D₂ := by
    funext e; simp only [reversedSign, orientSign, Pi.sub_apply]
    cases D e <;> cases D₂ e <;> simp
  rw [isFlow_iff_boundary]; intro z
  have := boundary_smul (G := G) (reversedSign D D₂) 2 z
  rw [htwo, boundary_sub] at this
  have h3 : G.boundary (orientSign D) z - G.boundary (orientSign D₂) z = 0 := by
    rw [show orientSign D = fun e => if D e then (-1 : ℤ) else 1 from rfl, h1 z,
      show orientSign D₂ = fun e => if D₂ e then (-1 : ℤ) else 1 from rfl, h2 z, sub_zero]
  omega

omit [Fintype E] [DecidableEq E] in
/-- `a 𝟙_{D₂} = a 𝟙_D - 2a (χ_{Q_1} + ⋯ + χ_{Q_r})` (tex l.284-285). -/
theorem constFlow_eq_add {A : Type} [AddCommGroup A] (a : A) (D D₂ : E → Bool) :
    constFlow a D₂ = constFlow a D + fun e => reversedSign D D₂ e • (-(2 • a)) := by
  funext e; simp only [constFlow, reversedSign, orientSign, Pi.add_apply]
  cases D e <;> cases D₂ e <;> simp [two_nsmul]

/-- Lemma 3.3 (a), general form. -/
theorem constFlow_eq_or_multiStep {A : Type} [AddCommGroup A] (a : A) {D D₂ : E → Bool}
    (hD : G.IsEulerOrient D) (hD₂ : G.IsEulerOrient D₂) :
    constFlow a D₂ = constFlow a D ∨ G.IsMultiStep (-(2 • a)) (constFlow a D) (constFlow a D₂) := by
  by_cases h2a : 2 • a = 0
  · left; rw [constFlow_eq_add a D D₂, h2a, neg_zero]; funext e; simp
  by_cases h0 : reversedSign D D₂ = 0
  · left; rw [constFlow_eq_add a D D₂, h0]; funext e; simp
  right
  obtain ⟨Qs, hpw, -, hsum, -⟩ := circ_decomp _ (reversedSign_mem D D₂) (isFlow_reversedSign hD hD₂)
  refine ⟨neg_ne_zero.2 h2a, Qs, ?_, hpw, ?_⟩
  · rintro rfl; apply h0; funext e; rw [← hsum e]; simp
  · rw [constFlow_eq_add a D D₂]; funext e; simp only [Pi.add_apply, hsum]

/-- A splitting off of an even graph is even (tex l.288: "`G'` is even"). -/
theorem isEven_splitOff [Fintype V] {v : V} {e e' : E} (hd : SplitData G v e e') (hev : G.IsEven) :
    (G.splitOff v e e').IsEven := by
  intro z
  have h := degree_splitOff hd z
  have hz := hev z
  rw [← h] at hz
  split_ifs at hz
  · exact (Nat.even_add.1 hz).2 (by decide)
  · simpa using hz

/-- Lemma 3.3 (b), general form: an Eulerian orientation `D` of `G` with `a 𝟙_D = L(a 𝟙_{D'})`, so that the ends
of `e, e'` at `v` are a balanced pair of `a 𝟙_D` (tex l.288-291). -/
theorem exists_eulerOrient_balanced [Fintype V] {v : V} {e e' : E} (hd : SplitData G v e e') (hev : G.IsEven)
    {A : Type} [AddCommGroup A] (a : A) :
    ∃ D : E → Bool, G.IsEulerOrient D ∧
      dirVal (constFlow a D) (G.endAt e v) + dirVal (constFlow a D) (G.endAt e' v) = 0 := by
  obtain ⟨D', hD'⟩ := exists_eulerOrient (isEven_splitOff hd hev)
  set σ := G.splitLift v e e' (orientSign D') with hσ
  have hσflow : G.IsFlow σ := (isFlow_splitLift_iff hd _).2 ((isEulerOrient_iff D').1 hD')
  have hσval : ∀ x, σ x ∈ ({y | y = 1 ∨ y = -1} : Set ℤ) := by
    refine splitLift_mem (fun y hy => ?_) _ (fun o => ?_)
    · simp only [Set.mem_ofPred_eq] at *; omega
    · simp only [orientSign, Set.mem_ofPred_eq]; split_ifs <;> simp
  let D : E → Bool := fun x => decide (σ x = -1)
  have hsign : orientSign D = σ := by
    funext x; simp only [orientSign, D]
    rcases hσval x with h | h <;> simp [h]
  refine ⟨D, (isEulerOrient_iff D).2 ?_, ?_⟩
  · exact (show (fun e => if D e then (-1 : ℤ) else 1) = σ from hsign) ▸ hσflow
  · have : constFlow a D = G.splitLift v e e' (constFlow a D') := by
      rw [constFlow_eq_smul, constFlow_eq_smul, splitLift_zsmul, hsign]
    rw [this]
    exact splitLift_balanced hd.ne hd.at₁ hd.nl₁ hd.at₂ hd.nl₂ _

end MGraph

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] in
omit [DecidableEq E] in
/-- Lemma 3.3, preamble (tex l.273), exactly the Statements type. -/
theorem lem_3_3_flow_proved {A : Type} [AddCommGroup A] (G : MGraph V E) (D : E → Bool) (hD : G.IsEulerOrient D)
    (a : A) (ha : a ≠ 0) : G.IsNZFlow (constFlow a D) :=
  isIFlow_constFlow nonzero_neg hD ha

omit [Fintype V] in
/-- Lemma 3.3 (a) (tex l.276-277), exactly the Statements type. -/
theorem lem_3_3_a_proved {A : Type} [AddCommGroup A] (G : MGraph V E) (a : A) (_ha : a ≠ 0) (D D₂ : E → Bool)
    (hD : G.IsEulerOrient D) (hD₂ : G.IsEulerOrient D₂) :
    constFlow a D₂ = constFlow a D ∨ G.IsMultiStep (-(2 • a)) (constFlow a D) (constFlow a D₂) :=
  constFlow_eq_or_multiStep a hD hD₂

/-- Lemma 3.3 (b) (tex l.278), exactly the Statements type. -/
theorem lem_3_3_b_proved {A : Type} [AddCommGroup A] (G : MGraph V E) (hev : G.IsEven) (hG : G.Loopless) (v : V)
    (e e' : E) (hne : e ≠ e') (he : G.IsAt e v) (he' : G.IsAt e' v) (a : A) (ha : a ≠ 0) :
    ∃ D : E → Bool, G.IsEulerOrient D ∧ G.InB v e e' (constFlow a D) := by
  obtain ⟨D, hD, hbal⟩ := exists_eulerOrient_balanced (SplitData.of hG hne he he') hev a
  exact ⟨D, hD, lem_3_3_flow_proved G D hD a ha, hbal⟩

end EulerFlow
