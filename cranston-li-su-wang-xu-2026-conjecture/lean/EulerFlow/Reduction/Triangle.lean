/-
EulerFlow/Reduction/Triangle.lean — Lemma 5.1 of paper 002 (contracting a triangle, tex l.415-446) and the
triangle computation of the introduction (a triangle is A-connected for |A| ≥ 4, tex l.110-111).
-/
import EulerFlow.Reduction.Paper3

namespace EulerFlow

open Finset

/-- `|A| ≥ 4` leaves a value outside any three (tex l.434). -/
theorem exists_ne_three {A : Type} [Fintype A] [DecidableEq A] (hA : 4 ≤ Fintype.card A) (a b c : A) :
    ∃ z : A, z ≠ a ∧ z ≠ b ∧ z ≠ c := by
  by_contra h
  push Not at h
  have hsub : (univ : Finset A) ⊆ {a, b, c} := by
    intro z _
    by_cases ha : z = a
    · simp [ha]
    by_cases hb : z = b
    · simp [hb]
    simp [h z ha hb]
  have := Finset.card_le_card hsub
  have h3 : ({a, b, c} : Finset A).card ≤ 3 := by
    refine (Finset.card_insert_le _ _).trans ?_
    exact Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp))
  rw [Finset.card_univ] at this
  omega

namespace MGraph

variable {V E : Type} {G : MGraph V E} [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Restriction to `E(G⁺) ∖ E(Δ)` keeps the flow condition (tex l.428-429) -/

section Restrict

variable {X : Finset V} {D : Finset E}

/-- A sum over the edges outside `D` of a map vanishing on `D` is the sum over all edges. -/
theorem sum_subtype_not_mem {M : Type} [AddCommMonoid M] (F : E → M) (hF : ∀ e ∈ D, F e = 0) :
    ∑ e : {e : E // e ∉ D}, F e.1 = ∑ e, F e := by
  rw [← Finset.sum_subtype (univ.filter (fun e => e ∉ D)) (p := fun e => e ∉ D) (by simp),
    ← Finset.sum_filter_add_sum_filter_not univ (fun e => e ∉ D)]
  have : ∑ e ∈ univ.filter (fun e => ¬(e ∉ D)), F e = 0 :=
    Finset.sum_eq_zero fun e he => hF e (by simpa using he)
  rw [this, add_zero]

omit [Fintype E] [DecidableEq E] in
theorem contract_src_some {e : {e : E // e ∉ D}} {y : {y : V // y ∉ X}} :
    (G.contract X D).src e = some y ↔ G.src e.1 = y.1 := by
  simp only [contract]
  split_ifs with h
  · simp only [false_iff]; intro h'; exact y.2 (h' ▸ h)
  · simp [Subtype.ext_iff]

omit [Fintype E] [DecidableEq E] in
theorem contract_tgt_some {e : {e : E // e ∉ D}} {y : {y : V // y ∉ X}} :
    (G.contract X D).tgt e = some y ↔ G.tgt e.1 = y.1 := by
  simp only [contract]
  split_ifs with h
  · simp only [false_iff]; intro h'; exact y.2 (h' ▸ h)
  · simp [Subtype.ext_iff]

omit [Fintype E] [DecidableEq E] in
theorem contract_src_none {e : {e : E // e ∉ D}} : (G.contract X D).src e = none ↔ G.src e.1 ∈ X := by
  simp only [contract]; split_ifs with h <;> simp [h]

omit [Fintype E] [DecidableEq E] in
theorem contract_tgt_none {e : {e : E // e ∉ D}} : (G.contract X D).tgt e = none ↔ G.tgt e.1 ∈ X := by
  simp only [contract]; split_ifs with h <;> simp [h]

variable (hDX : ∀ d ∈ D, G.src d ∈ X ∧ G.tgt d ∈ X)
include hDX

/-- At a vertex `y` outside `X`, the boundary of `p x` in `G⁺/Δ` is the boundary of `x` in `G⁺`. -/
theorem boundary_restrict_some {M : Type} [AddCommGroup M] (x : E → M) (y : {y : V // y ∉ X}) :
    (G.contract X D).boundary (restrictTo D x) (some y) = G.boundary x y.1 := by
  rw [boundary_eq_sum_bdryTerm, boundary_eq_sum_bdryTerm,
    ← sum_subtype_not_mem (G.bdryTerm x y.1) (fun d hd => ?_)]
  · refine Finset.sum_congr rfl fun e _ => ?_
    simp only [bdryTerm, restrictTo, contract_src_some, contract_tgt_some]
  · have h := hDX d hd
    have h1 : G.tgt d ≠ y.1 := fun h' => y.2 (h' ▸ h.2)
    have h2 : G.src d ≠ y.1 := fun h' => y.2 (h' ▸ h.1)
    simp [bdryTerm, h1, h2]

/-- At the new vertex, the boundary of `p x` is the sum of the boundaries of `x` at the vertices of `X`: the
edges of `Δ` cancel (tex l.428-429). -/
theorem boundary_restrict_none {M : Type} [AddCommGroup M] (x : E → M) :
    (G.contract X D).boundary (restrictTo D x) none = ∑ z ∈ X, G.boundary x z := by
  simp only [boundary_eq_sum_bdryTerm]
  rw [Finset.sum_comm, ← sum_subtype_not_mem (fun e => ∑ z ∈ X, G.bdryTerm x z e) (fun d hd => ?_)]
  · refine Finset.sum_congr rfl fun e _ => ?_
    simp only [bdryTerm, restrictTo, contract_src_none, contract_tgt_none, Finset.sum_sub_distrib,
      Finset.sum_ite_eq]
  · have h := hDX d hd
    simp only [bdryTerm, Finset.sum_sub_distrib, Finset.sum_ite_eq, h.1, h.2, ite_true, sub_self]

theorem isFlow_restrictTo {M : Type} [AddCommGroup M] {x : E → M} (hx : G.IsFlow x) :
    (G.contract X D).IsFlow (restrictTo D x) := by
  rw [isFlow_iff_boundary] at *
  intro w
  cases w with
  | none => rw [boundary_restrict_none hDX]; exact Finset.sum_eq_zero fun z _ => hx z
  | some y => rw [boundary_restrict_some hDX]; exact hx _

theorem isIFlow_restrictTo {M : Type} [AddCommGroup M] {I : Set M} {x : E → M} (hx : G.IsIFlow I x) :
    (G.contract X D).IsIFlow I (restrictTo D x) :=
  ⟨isFlow_restrictTo hDX hx.1, fun e => hx.2 e.1⟩

end Restrict

/-! ### Lifting a flow of `G⁺/Δ` (tex l.429-434) -/

section Lift

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem joins_cases {d : E} {a b c w : V} (h1 : G.Joins d a b) (h2 : G.Joins d c w) :
    (a = c ∧ b = w) ∨ (a = w ∧ b = c) := by
  unfold Joins at *; rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    subst h1 h1' <;> simp_all

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem joins_mem {d : E} {a b : V} (h : G.Joins d a b) : (G.src d = a ∨ G.src d = b) ∧ (G.tgt d = a ∨ G.tgt d = b) := by
  unfold Joins at h; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

/-- The value, in the reference direction of `d`, of the value `y` from `a` to the other end of `d`. -/
def triVal {A : Type} [AddCommGroup A] (G : MGraph V E) (d : E) (a : V) (y : A) : A := if G.src d = a then y else -y

theorem boundary_single {M : Type} [AddCommGroup M] (d : E) (y : M) (z : V) :
    G.boundary (Pi.single d y) z = (if G.tgt d = z then y else 0) - (if G.src d = z then y else 0) := by
  simp only [boundary, Finset.sum_pi_single', mem_filter, mem_univ, true_and]

/-- An edge `d` joining `a ≠ b`, with the value `y` from `a` to `b`, contributes `y` at `b` and `-y` at `a`. -/
theorem boundary_single_triVal {A : Type} [AddCommGroup A] {d : E} {a b : V} (hJ : G.Joins d a b) (hab : a ≠ b)
    (y : A) (z : V) :
    G.boundary (Pi.single d (G.triVal d a y)) z = (if b = z then y else 0) - (if a = z then y else 0) := by
  rw [boundary_single]
  unfold Joins at hJ
  rcases hJ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [triVal, h1, h2, ite_true]
  · have : G.src d ≠ a := fun h => hab (h1.symm.trans h).symm
    simp only [triVal, h1, h2, ite_eq_right (Ne.symm hab)]
    by_cases ha : a = z <;> by_cases hb : b = z <;> simp [ha, hb]

variable {A : Type} [AddCommGroup A] {x₁ x₂ x₃ : V} {d₁₂ d₂₃ d₃₁ : E}

omit [Fintype E] in
theorem IsIsolatedTriangle.mem (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁) :
    ∀ d ∈ ({d₁₂, d₂₃, d₃₁} : Finset E), G.src d ∈ ({x₁, x₂, x₃} : Finset V) ∧ G.tgt d ∈ ({x₁, x₂, x₃} : Finset V) := by
  intro d hd
  simp only [mem_insert, mem_singleton] at hd
  rcases hd with rfl | rfl | rfl
  · have := joins_mem hΔ.joins₁₂; simp only [mem_insert, mem_singleton]; tauto
  · have := joins_mem hΔ.joins₂₃; simp only [mem_insert, mem_singleton]; tauto
  · have := joins_mem hΔ.joins₃₁; simp only [mem_insert, mem_singleton]; tauto

omit [Fintype E] [DecidableEq E] in
theorem IsIsolatedTriangle.d_ne (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁) :
    d₁₂ ≠ d₂₃ ∧ d₂₃ ≠ d₃₁ ∧ d₃₁ ≠ d₁₂ := by
  have h1 := hΔ.x_ne₁₂; have h2 := hΔ.x_ne₂₃; have h3 := hΔ.x_ne₃₁
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · subst h; rcases joins_cases hΔ.joins₁₂ hΔ.joins₂₃ with ⟨a, b⟩ | ⟨a, b⟩ <;> simp_all
  · subst h; rcases joins_cases hΔ.joins₂₃ hΔ.joins₃₁ with ⟨a, b⟩ | ⟨a, b⟩ <;> simp_all
  · subst h; rcases joins_cases hΔ.joins₃₁ hΔ.joins₁₂ with ⟨a, b⟩ | ⟨a, b⟩ <;> simp_all

variable [Fintype A] [DecidableEq A]

/-- Lemma 5.1 (a), second half (tex l.429-434): every nowhere-zero flow of `G⁺/Δ` is `p f` for a nowhere-zero
flow `f` of `G⁺`: give `x₁x₂, x₂x₃, x₃x₁` the values `z, z + β₂, z - β₁` with `z ∉ {0, -β₂, β₁}`. -/
theorem exists_lift_contract (hA : 4 ≤ Fintype.card A) (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁)
    (h : {e : E // e ∉ ({d₁₂, d₂₃, d₃₁} : Finset E)} → A)
    (hh : (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).IsNZFlow h) :
    ∃ f : E → A, G.IsNZFlow f ∧ restrictTo {d₁₂, d₂₃, d₃₁} f = h := by
  have hDX := hΔ.mem
  obtain ⟨n12, n23, n31⟩ := hΔ.d_ne
  have m12 := hΔ.x_ne₁₂
  have m23 := hΔ.x_ne₂₃
  have m31 := hΔ.x_ne₃₁
  -- `h` extended by `0` on the edges of `Δ`
  let x₀ : E → A := fun e => if he : e ∈ ({d₁₂, d₂₃, d₃₁} : Finset E) then 0 else h ⟨e, he⟩
  have hx₀ : restrictTo ({d₁₂, d₂₃, d₃₁} : Finset E) x₀ = h := by
    funext e; simp only [restrictTo, x₀, dite_eq_right e.2]
  have hflow := (isFlow_iff_boundary _ _).1 hh.1
  -- `β_i` = the boundary of `x₀` at `x_i`; the three sum to `0` (tex l.430)
  have hβsum : G.boundary x₀ x₁ + G.boundary x₀ x₂ + G.boundary x₀ x₃ = 0 := by
    have := boundary_restrict_none hDX x₀
    rw [hx₀, hflow none, Finset.sum_insert (by simp [m12, m31.symm]), Finset.sum_insert (by simp [m23]),
      Finset.sum_singleton] at this
    rw [add_assoc]; exact this.symm
  have hβ₃ : G.boundary x₀ x₃ = -(G.boundary x₀ x₁ + G.boundary x₀ x₂) := eq_neg_of_add_eq_zero_right hβsum
  have hout : ∀ z, z ∉ ({x₁, x₂, x₃} : Finset V) → G.boundary x₀ z = 0 := by
    intro z hz
    have := boundary_restrict_some hDX x₀ ⟨z, hz⟩
    rw [hx₀, hflow] at this; exact this.symm
  obtain ⟨z₀, hz0, hz2, hz1⟩ := exists_ne_three hA 0 (-G.boundary x₀ x₂) (G.boundary x₀ x₁)
  -- the values of the triangle (tex l.431-434)
  let τ : E → A := Pi.single d₁₂ (G.triVal d₁₂ x₁ z₀) + Pi.single d₂₃ (G.triVal d₂₃ x₂ (z₀ + G.boundary x₀ x₂)) +
    Pi.single d₃₁ (G.triVal d₃₁ x₃ (z₀ - G.boundary x₀ x₁))
  have hτ : ∀ z, G.boundary τ z =
      ((if x₂ = z then z₀ else 0) - if x₁ = z then z₀ else 0) +
      ((if x₃ = z then z₀ + G.boundary x₀ x₂ else 0) - if x₂ = z then z₀ + G.boundary x₀ x₂ else 0) +
      ((if x₁ = z then z₀ - G.boundary x₀ x₁ else 0) - if x₃ = z then z₀ - G.boundary x₀ x₁ else 0) := by
    intro z
    simp only [τ, boundary_add, boundary_single_triVal hΔ.joins₁₂ m12, boundary_single_triVal hΔ.joins₂₃ m23,
      boundary_single_triVal hΔ.joins₃₁ m31]
  have hne : ∀ (d : E) (a : V) (y : A), y ≠ 0 → G.triVal d a y ≠ 0 := by
    intro d a y hy; unfold triVal; split_ifs <;> simpa using hy
  have hτoff : ∀ e, e ∉ ({d₁₂, d₂₃, d₃₁} : Finset E) → τ e = 0 := by
    intro e he
    have h1 : e ≠ d₁₂ := fun h' => he (by simp [h'])
    have h2 : e ≠ d₂₃ := fun h' => he (by simp [h'])
    have h3 : e ≠ d₃₁ := fun h' => he (by simp [h'])
    simp only [τ, Pi.add_apply, Pi.single_apply, h1, h2, h3, ite_false, add_zero]
  refine ⟨x₀ + τ, ⟨?_, fun e => ?_⟩, ?_⟩
  · -- the flow condition at every vertex (tex l.432-433)
    rw [isFlow_iff_boundary]
    intro z
    rw [boundary_add, hτ z]
    by_cases h1 : z = x₁
    · rw [h1]; simp only [m12.symm, m31, ite_true, ite_false, sub_zero, zero_sub]; abel
    by_cases h2 : z = x₂
    · rw [h2]; simp only [m12, m23.symm, ite_true, ite_false, sub_zero, zero_sub]; abel
    by_cases h3 : z = x₃
    · rw [h3, hβ₃]; simp only [m23, m31.symm, ite_true, ite_false, sub_zero, zero_sub]; abel
    have hz : z ∉ ({x₁, x₂, x₃} : Finset V) := by simp [h1, h2, h3]
    rw [hout z hz]
    simp [Ne.symm h1, Ne.symm h2, Ne.symm h3]
  · -- nowhere zero (tex l.434)
    by_cases he : e ∈ ({d₁₂, d₂₃, d₃₁} : Finset E)
    · have hx0 : x₀ e = 0 := by simp only [x₀, dite_eq_left he]
      rw [Pi.add_apply, hx0, zero_add]
      simp only [mem_insert, mem_singleton] at he
      rcases he with he | he | he <;> rw [he]
      · simp only [τ, Pi.add_apply, Pi.single_apply, n12, n31.symm, ite_true, ite_false, add_zero]
        exact hne _ _ _ hz0
      · simp only [τ, Pi.add_apply, Pi.single_apply, n12.symm, n23, ite_true, ite_false, add_zero, zero_add]
        exact hne _ _ _ (fun h' => hz2 (eq_neg_of_add_eq_zero_left h'))
      · simp only [τ, Pi.add_apply, Pi.single_apply, n31, n23.symm, ite_true, ite_false, zero_add]
        exact hne _ _ _ (fun h' => hz1 (sub_eq_zero.1 h'))
    · simp only [Pi.add_apply, hτoff e he, add_zero, x₀, dite_eq_right he]
      exact hh.2 ⟨e, he⟩
  · funext e
    simp only [restrictTo, Pi.add_apply, hτoff e.1 e.2, add_zero, x₀, dite_eq_right e.2]

end Lift

/-! ### Multi-steps and flow-connectedness pass to `G⁺/Δ` (tex l.436-445) -/

section Pass

variable {A : Type} [AddCommGroup A] {x₁ x₂ x₃ : V} {d₁₂ d₂₃ d₃₁ : E}

/-- Lemma 5.1 (b): a multi-step of `G⁺` with the value `t` restricts to the identity or to a multi-step of `G⁺/Δ`
with the value `t` (tex l.436-443). -/
theorem restrict_multiStep (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁) {t : A} {f₁ f₂ : E → A}
    (hstep : G.IsMultiStep t f₁ f₂) :
    restrictTo {d₁₂, d₂₃, d₃₁} f₂ = restrictTo {d₁₂, d₂₃, d₃₁} f₁ ∨
      (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).IsMultiStep t (restrictTo {d₁₂, d₂₃, d₃₁} f₁)
        (restrictTo {d₁₂, d₂₃, d₃₁} f₂) := by
  obtain ⟨ht, Qs, hne, hpw, hf⟩ := hstep
  let S := restrictTo ({d₁₂, d₂₃, d₃₁} : Finset E) (chiSum Qs)
  have hS : (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).IsFlow S := isFlow_restrictTo hΔ.mem (isFlow_chiSum Qs)
  have hSv : ∀ e, S e = -1 ∨ S e = 0 ∨ S e = 1 := fun e => sum_chi_mem Qs hpw e.1
  have heq : restrictTo ({d₁₂, d₂₃, d₃₁} : Finset E) f₂ = restrictTo {d₁₂, d₂₃, d₃₁} f₁ + fun e => S e • t := by
    rw [hf]; rfl
  by_cases hS0 : S = 0
  · left; rw [heq, hS0]; funext e; simp
  · right
    obtain ⟨Qs₂, hpw₂, -, hsum₂, -⟩ := circ_decomp S hSv hS
    refine ⟨ht, Qs₂, ?_, hpw₂, ?_⟩
    · rintro rfl; apply hS0; funext e; rw [← hsum₂ e]; simp
    · rw [heq]; funext e; simp only [Pi.add_apply, hsum₂]

variable [Fintype A] [DecidableEq A]

/-- Lemma 5.1, last sentence: if `G⁺` is `A`-flow-connected, so is `G⁺/Δ` (tex l.425, l.445). -/
theorem flowConnected_contract (hA : 4 ≤ Fintype.card A) (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁)
    (hconn : G.FlowConnected A) : (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).FlowConnected A := by
  intro h₁ h₂
  obtain ⟨f₁, hf₁, hr₁⟩ := exists_lift_contract hA hΔ h₁.1 h₁.2
  obtain ⟨f₂, hf₂, hr₂⟩ := exists_lift_contract hA hΔ h₂.1 h₂.2
  let φ : {f : E → A // G.IsIFlow ({x | x ≠ 0} : Set A) f} →
      {g // (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).IsIFlow ({x | x ≠ 0} : Set A) g} :=
    fun f => ⟨restrictTo {d₁₂, d₂₃, d₃₁} f.1, isIFlow_restrictTo hΔ.mem f.2⟩
  have key := reachable_transport (T := ({x | x ≠ 0} : Set A)) φ
    (fun f Q t hft => ⟨restrictTo {d₁₂, d₂₃, d₃₁} Q.chi, fun e => Q.chi_mem e.1,
      isFlow_restrictTo hΔ.mem Q.isFlow_chi, rfl⟩) (hconn ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩)
  have e₁ : φ ⟨f₁, hf₁⟩ = h₁ := Subtype.ext hr₁
  have e₂ : φ ⟨f₂, hf₂⟩ = h₂ := Subtype.ext hr₂
  rw [e₁, e₂] at key
  exact key

end Pass

end MGraph

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] in
/-- Lemma 5.1 (a) (tex l.421), exactly the Statements type. -/
theorem lem_5_1_a_proved {A : Type} [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A) (G : MGraph V E)
    (x₁ x₂ x₃ : V) (d₁₂ d₂₃ d₃₁ : E) (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁) :
    (∀ f : E → A, G.IsNZFlow f →
      (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).IsNZFlow (restrictTo {d₁₂, d₂₃, d₃₁} f)) ∧
    (∀ h, (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).IsNZFlow h →
      ∃ f : E → A, G.IsNZFlow f ∧ restrictTo {d₁₂, d₂₃, d₃₁} f = h) := by
  classical
  exact ⟨fun f hf => isIFlow_restrictTo hΔ.mem hf, fun h hh => exists_lift_contract hA hΔ h hh⟩

omit [Fintype V] in
/-- Lemma 5.1 (b) (tex l.422-424), exactly the Statements type. -/
theorem lem_5_1_b_proved {A : Type} [AddCommGroup A] [Fintype A] (_hA : 4 ≤ Fintype.card A) (G : MGraph V E)
    (x₁ x₂ x₃ : V) (d₁₂ d₂₃ d₃₁ : E) (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁) (t : A) (f₁ f₂ : E → A)
    (_h₁ : G.IsNZFlow f₁) (_h₂ : G.IsNZFlow f₂) (hstep : G.IsMultiStep t f₁ f₂) :
    restrictTo {d₁₂, d₂₃, d₃₁} f₂ = restrictTo {d₁₂, d₂₃, d₃₁} f₁ ∨
      (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).IsMultiStep t (restrictTo {d₁₂, d₂₃, d₃₁} f₁)
        (restrictTo {d₁₂, d₂₃, d₃₁} f₂) :=
  restrict_multiStep hΔ hstep

omit [Fintype V] in
/-- Lemma 5.1, last sentence (tex l.425), exactly the Statements type. -/
theorem lem_5_1_c_proved {A : Type} [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A) (G : MGraph V E)
    (x₁ x₂ x₃ : V) (d₁₂ d₂₃ d₃₁ : E) (hΔ : G.IsIsolatedTriangle x₁ x₂ x₃ d₁₂ d₂₃ d₃₁)
    (hconn : G.FlowConnected A) : (G.contract {x₁, x₂, x₃} {d₁₂, d₂₃, d₃₁}).FlowConnected A := by
  classical
  exact flowConnected_contract hA hΔ hconn

/-- Introduction (tex l.110-111): a triangle is `A`-connected for `|A| ≥ 4`: for every boundary `β` with sum `0`
there is a nowhere-zero map on the three edges with that boundary; exactly the Statements type. -/
theorem intro_triangle_A_connected_proved {A : Type} [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A)
    (β : Fin 3 → A) (hβ : ∑ v, β v = 0) :
    ∃ x : Fin 3 → A, (∀ e, x e ≠ 0) ∧ (cycleGraph 3).boundary x = β := by
  classical
  obtain ⟨z, hz0, hz1, hz2⟩ := exists_ne_three hA 0 (β 1) (-β 0)
  rw [Fin.sum_univ_three] at hβ
  refine ⟨![z, z - β 1, z + β 0], fun e => ?_, ?_⟩
  · fin_cases e
    · simpa using hz0
    · simpa [sub_eq_zero] using hz1
    · simpa [add_eq_zero_iff_eq_neg] using hz2
  · funext v
    fin_cases v <;> simp [boundary, cycleGraph, Finset.sum_filter, Fin.sum_univ_three]
    rw [eq_neg_of_add_eq_zero_right hβ]; abel

end EulerFlow
