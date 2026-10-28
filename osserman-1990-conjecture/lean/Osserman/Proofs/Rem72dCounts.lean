/-
Rem72dCounts.lean — multiplicities of Clifford forms, paper 013, Remark 7.2.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Rem72a
import Osserman.Proofs.ThmEProjection
import Osserman.Proofs.ThmESpectral
import Osserman.Proofs.HurwitzRadon

namespace Osserman.Proofs.Rem72d

open Osserman Matrix Osserman.Proofs.Spectral Osserman.Proofs.Rem72a
open Osserman.Proofs.ThmEProjection Osserman.Proofs.ThmESpectral

noncomputable def selectedSpan {ν : ℕ} (v : Fin ν → Vec 16) (p : Fin ν → Prop) :
    Submodule ℝ (Vec 16) := Submodule.span ℝ (Set.range fun a : {a : Fin ν // p a} => v a.1)

lemma selectedSpan_eq {ν : ℕ} (v : Fin ν → Vec 16) (p : Fin ν → Prop) :
    selectedSpan v p = Submodule.span ℝ (v '' {a | p a}) := by
  unfold selectedSpan
  apply congrArg (Submodule.span ℝ)
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

lemma selectedSpan_le {ν : ℕ} (v : Fin ν → Vec 16) (p : Fin ν → Prop) :
    selectedSpan v p ≤ frameSpan v := by
  rw [selectedSpan, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span (Set.mem_range_self a.1)

lemma selectedSpan_rank {ν : ℕ} (v : Fin ν → Vec 16) (p : Fin ν → Prop) [DecidablePred p]
    (hv : ∀ a b, v a ⬝ᵥ v b = if a = b then 1 else 0) :
    Module.finrank ℝ ↥(selectedSpan v p) = Fintype.card {a : Fin ν // p a} := by
  apply finrank_span_eq_card
  exact (span_independent v hv).comp (fun a : {a : Fin ν // p a} => a.1) Subtype.val_injective

lemma Wsub_rank {ν : ℕ} (J : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr J)
    (x : Vec 16) (hx : x ⬝ᵥ x = 1) : Module.finrank ℝ ↥(Wsub J x) = 15 - ν := by
  let v : Fin ν → Vec 16 := fun a => J a *ᵥ x
  obtain ⟨hv, hp⟩ := clifford_frame J hJ x hx
  have split : frameSpan v ⊔ Wsub J x = perp x := by
    apply le_antisymm
    · exact sup_le (span_le_perp v x hp) inf_le_left
    · intro y hy
      refine Submodule.mem_sup.mpr ⟨frameProj v *ᵥ y, projection_mem v y,
        y - frameProj v *ᵥ y, ?_, by abel⟩
      rw [mem_Wsub]
      exact ⟨(perp x).sub_mem hy ((span_le_perp v x hp) (projection_mem v y)),
        (mem_orth_frame v _).mp (projection_complement v hv y)⟩
  have disjoint : frameSpan v ⊓ Wsub J x = ⊥ := by
    apply eq_bot_iff.mpr
    intro y hy
    have orth : y ∈ orthSub (frameSpan v) :=
      (mem_orth_frame v y).mpr (mem_Wsub.mp hy.2).2
    exact dotProduct_self_eq_zero.mp (orth y hy.1)
  have dimensions := Submodule.finrank_sup_add_finrank_inf_eq (frameSpan v) (Wsub J x)
  have rank : Module.finrank ℝ ↥(frameSpan v) = ν := by
    change Module.finrank ℝ ↥(Submodule.span ℝ (Set.range v)) = ν
    simpa only [Fintype.card_fin] using finrank_span_eq_card (span_independent v hv)
  rw [split, disjoint, finrank_bot, add_zero, rank] at dimensions
  have total := finrank_perp hx
  omega

lemma clifford_multiplicity (R : CurvTensor 16) {ν : ℕ}
    (J : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr J)
    (l0 : ℝ) (η : Fin ν → ℝ)
    (hjac : ∀ x, R.jacobi x = l0 • Pi x + ∑ a, η a • jfam (J a) x)
    (x : Vec 16) (hx : x ⬝ᵥ x = 1) (ℓ : ℝ) :
    R.redMult x ℓ = Fintype.card {a : Fin ν // l0 + η a = ℓ} +
      (if ℓ = l0 then 15 - ν else 0) := by
  classical
  let v : Fin ν → Vec 16 := fun a => J a *ᵥ x
  have hv := (clifford_frame J hJ x hx).1
  have eig : Esp R x ℓ = selectedSpan v (fun a => l0 + η a = ℓ) ⊔
      (if ℓ = l0 then Wsub J x else ⊥) := by
    rw [selectedSpan_eq]
    exact eig_clifford hJ (hjac x) hx ℓ
  have disjoint : selectedSpan v (fun a => l0 + η a = ℓ) ⊓ Wsub J x = ⊥ := by
    apply eq_bot_iff.mpr
    intro y hy
    have orth : y ∈ orthSub (frameSpan v) :=
      (mem_orth_frame v y).mpr (mem_Wsub.mp hy.2).2
    exact dotProduct_self_eq_zero.mp (orth y (selectedSpan_le v _ hy.1))
  change Module.finrank ℝ ↥(Esp R x ℓ) = _
  rw [eig]
  split_ifs with equal
  · have dimensions := Submodule.finrank_sup_add_finrank_inf_eq
      (selectedSpan v (fun a => l0 + η a = ℓ)) (Wsub J x)
    rw [disjoint, finrank_bot, add_zero, selectedSpan_rank v _ hv, Wsub_rank J hJ x hx] at dimensions
    have subspace : (selectedSpan v (fun a => l0 + η a = ℓ) ⊔
        (if ℓ = l0 then Wsub J x else ⊥)) = selectedSpan v (fun a => l0 + η a = ℓ) ⊔ Wsub J x := by
      rw [ite_eq_left equal]
    exact (congrArg (fun S : Submodule ℝ (Vec 16) => Module.finrank ℝ ↥S) subspace).trans dimensions
  · have subspace : (selectedSpan v (fun a => l0 + η a = ℓ) ⊔
        (if ℓ = l0 then Wsub J x else ⊥)) = selectedSpan v (fun a => l0 + η a = ℓ) := by
      rw [ite_eq_right equal, sup_bot_eq]
    simp only [add_zero]
    exact (congrArg (fun S : Submodule ℝ (Vec 16) => Module.finrank ℝ ↥S) subspace).trans
      (selectedSpan_rank v (fun a => l0 + η a = ℓ) hv)

theorem rem_7_2_nu_le_7_proved (R' : CurvTensor 16) {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : IsCliffordStr Jα) (hν : ν ≤ 7) (l0 : ℝ) (μ : Fin ν → ℝ) (hμ : ∀ α, μ α ≠ 0)
    (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, μ α • jfam (Jα α) x) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 → R'.redMult x l0 = 15 - ν ∧ 8 ≤ R'.redMult x l0 ∧
      ∀ ℓ : ℝ, ℓ ≠ l0 → R'.redMult x ℓ < R'.redMult x l0 := by
  classical
  intro x hx
  have empty : IsEmpty {a : Fin ν // l0 + μ a = l0} :=
    ⟨fun a => hμ a.1 (by linarith [a.2])⟩
  have base := clifford_multiplicity R' Jα hJ l0 μ hjac x hx l0
  simp only [Fintype.card_of_isEmpty, ite_true, zero_add] at base
  refine ⟨base, by omega, fun ℓ different => ?_⟩
  have count := Fintype.card_subtype_le (fun a : Fin ν => l0 + μ a = ℓ)
  have other := clifford_multiplicity R' Jα hJ l0 μ hjac x hx ℓ
  simp only [ite_eq_right different, add_zero] at other
  simp only [Fintype.card_fin] at count
  omega

theorem rem_7_2_cl8_differs_proved (R' : CurvTensor 16) (μ κ : ℝ) (hκ : κ ≠ 0)
    (Jα : Fin 8 → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr Jα)
    (hjac : ∀ x, R'.jacobi x = μ • Pi x + κ • (Pi x - ∑ i, jfam (Jα i) x)) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 → R'.redMult x (μ + κ) = 7 ∧ R'.redMult x μ = 8 := by
  classical
  have form (x : Vec 16) : R'.jacobi x = (μ + κ) • Pi x + ∑ i, (-κ) • jfam (Jα i) x := by
    rw [hjac, add_smul, smul_sub, Finset.smul_sum]
    simp only [neg_smul, Finset.sum_neg_distrib]
    abel
  intro x hx
  have empty : IsEmpty {a : Fin 8 // μ + κ + -κ = μ + κ} :=
    ⟨fun a => hκ (by linarith [a.2])⟩
  have full : Fintype.card {a : Fin 8 // μ + κ + -κ = μ} = 8 := by
    simp
  have first := clifford_multiplicity R' Jα hJ (μ + κ) (fun _ => -κ) form x hx (μ + κ)
  have second := clifford_multiplicity R' Jα hJ (μ + κ) (fun _ => -κ) form x hx μ
  have different : μ ≠ μ + κ := by intro equal; apply hκ; linarith
  simpa only [Fintype.card_of_isEmpty, full, ite_true, ite_eq_right different, zero_add, add_zero,
    Nat.reduceSub] using And.intro first second

lemma pattern771_bound (R : CurvTensor 16) (hpat : HasPattern R ![7, 7, 1])
    (x : Vec 16) (hx : x ⬝ᵥ x = 1) (ℓ : ℝ) : R.redMult x ℓ ≤ 7 := by
  obtain ⟨ev, hev, hmult⟩ := hpat
  by_cases equal : ∃ i, ℓ = ev i
  · obtain ⟨i, rfl⟩ := equal
    rw [hmult x hx i]
    fin_cases i <;> norm_num
  · have different (i : Fin 3) : ℓ ≠ ev i := fun h => equal ⟨i, h⟩
    have zero : Esp R x ℓ = ⊥ := by
      apply eq_bot_iff.mpr
      intro y hy
      obtain ⟨y0, h0, y1, h1, y2, h2, sum⟩ :=
        three_decomp R ![7, 7, 1] (Or.inl rfl) ev hev x hx (hmult x hx) y hy.2
      have first := eig_dot_zero R x _ _ (different 0) y y0 hy h0
      have second := eig_dot_zero R x _ _ (different 1) y y1 hy h1
      have third := eig_dot_zero R x _ _ (different 2) y y2 hy h2
      apply dotProduct_self_eq_zero.mp
      calc
        y ⬝ᵥ y = y ⬝ᵥ (y0 + y1 + y2) := congrArg (fun z => y ⬝ᵥ z) sum
        _ = 0 := by rw [dotProduct_add, dotProduct_add, first, second, third]; ring
    change Module.finrank ℝ ↥(Esp R x ℓ) ≤ 7
    rw [zero, finrank_bot]
    omega

theorem rem_7_2_771_nu8_proved (R' : CurvTensor 16) (hpat : HasPattern R' ![7, 7, 1]) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr Jα) (l0 : ℝ) (η : Fin ν → ℝ)
    (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, η α • jfam (Jα α) x) :
    ν = 8 ∧ ∀ α, η α ≠ 0 := by
  classical
  let x : Vec 16 := Pi.single 0 1
  have hx : x ⬝ᵥ x = 1 := by simp [x, dotProduct, Pi.single_apply]
  have bound := pattern771_bound R' hpat x hx l0
  have formula := clifford_multiplicity R' Jα hJ l0 η hjac x hx l0
  simp only [ite_true] at formula
  have upper := Osserman.Proofs.HurwitzRadon.rem_7_2_nu_le_8_proved Jα hJ
  have dimension : ν = 8 := by omega
  refine ⟨dimension, fun α equal => ?_⟩
  have positive : 0 < Fintype.card {a : Fin ν // l0 + η a = l0} := by
    exact Fintype.card_pos_iff.mpr ⟨⟨α, by rw [equal, add_zero]⟩⟩
  omega

end Osserman.Proofs.Rem72d
