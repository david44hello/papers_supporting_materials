/-
CorD.lean — proofs of the six Corollary D rows of paper 013 (Osserman/Paper/Statements7.lean v0.71): cor_D (l.40),
hasPattern_osserman (l.55), hasPattern_of_literal (l.64), cor_D_87 (l.644), cor_D_771 (l.648), cor_D_cases (l.653).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Each `<row>_proved` has the row's type verbatim. The rows that use Theorem E (cor_D_771, cor_D_cases, cor_D) take its
exact type (Statements7.lean l.48-50) as the first premise `hE`, so a link is e.g. `cor_D_771_proved thm_E R h`.
Theorem C is used through `ThmC.thm_C_of_prop_5_2 Sec5c.prop_5_2_proved` (= Statements.lean's `thm_C`).
Cited: only `Osserman.Cited.andrejic_thm5` (in cor_D).
-/
import Osserman.Defs.ThreeRoot
import Osserman.Cited.Andrejic
import Osserman.Proofs.OssTop
import Osserman.Proofs.Spectral
import Osserman.Proofs.ThmC
import Osserman.Proofs.Sec5c

namespace Osserman.Proofs.CorD

open Osserman Osserman.Cited Matrix

/-! ### Independent subspaces: the dimension of a finite sup is the sum of the dimensions -/

lemma finrank_biSup_eq {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {ι : Type*}
    [DecidableEq ι] {W : ι → Submodule ℝ V} (hW : iSupIndep W) (s : Finset ι) :
    Module.finrank ℝ ↥(⨆ i ∈ s, W i) = ∑ i ∈ s, Module.finrank ℝ ↥(W i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    have hd : Disjoint (W a) (⨆ i ∈ s, W i) := by
      rw [← Finset.iSup_coe]
      exact hW.disjoint_biSup (by simpa using ha)
    have h := Submodule.finrank_sup_add_finrank_inf_eq (W a) (⨆ i ∈ s, W i)
    rw [hd.eq_bot, finrank_bot] at h
    omega

/-- At a unit `x`, if the distinct values `ev i` have reduced multiplicities `m i` with `∑ m i = n - 1`, every other
value has reduced multiplicity 0 (the reduced eigenspaces are independent inside `x^⊥`, of dimension `n - 1`). -/
lemma redMult_other {n k : ℕ} (R : CurvTensor n) {m : Fin k → ℕ} {ev : Fin k → ℝ} (hev : Function.Injective ev)
    (hsum : ∑ i, m i + 1 = n) {x : Vec n} (hx : x ⬝ᵥ x = 1) (hm : ∀ i, R.redMult x (ev i) = m i) {μ : ℝ}
    (hμ : ∀ i, μ ≠ ev i) : R.redMult x μ = 0 := by
  classical
  have hW : iSupIndep (Spectral.Esp R x) :=
    (Module.End.eigenspaces_iSupIndep (R.jacobiMap x)).mono fun _ => inf_le_left
  have hμs : μ ∉ Finset.univ.image ev := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun i hi => hμ i hi.symm
  have hle : (⨆ ν ∈ insert μ (Finset.univ.image ev), Spectral.Esp R x ν) ≤ perp x :=
    iSup₂_le fun _ _ => inf_le_right
  have h1 := Submodule.finrank_mono hle
  rw [finrank_biSup_eq hW, Finset.sum_insert hμs, Finset.sum_image (fun i _ j _ h => hev h)] at h1
  have h2 : ∑ i, Module.finrank ℝ ↥(Spectral.Esp R x (ev i)) = ∑ i, m i :=
    Finset.sum_congr rfl fun i _ => hm i
  have h3 : Module.finrank ℝ ↥(Spectral.Esp R x μ) = R.redMult x μ := rfl
  have hp := Spectral.finrank_perp hx
  omega

/-! ### The six rows -/

/-- Row `hasPattern_osserman` (Statements7.lean l.55). -/
theorem hasPattern_osserman_proved {n k : ℕ} (R : CurvTensor n) (m : Fin k → ℕ) (hsum : ∑ i, m i + 1 = n)
    (hR : HasPattern R m) :
    R.IsOsserman ∧ ∃ ev : Fin k → ℝ, Function.Injective ev ∧
      (∀ x : Vec n, x ⬝ᵥ x = 1 → ∀ i, R.redMult x (ev i) = m i) ∧
      ∀ x : Vec n, x ⬝ᵥ x = 1 → ∀ μ : ℝ, (∀ i, μ ≠ ev i) → R.redMult x μ = 0 := by
  obtain ⟨ev, hev, hm⟩ := hR
  have hzero : ∀ x : Vec n, x ⬝ᵥ x = 1 → ∀ μ : ℝ, (∀ i, μ ≠ ev i) → R.redMult x μ = 0 :=
    fun x hx μ hμ => redMult_other R hev hsum hx (hm x hx) hμ
  refine ⟨fun x y hx hy μ => ?_, ev, hev, hm, hzero⟩
  by_cases h : ∃ i, μ = ev i
  · obtain ⟨i, rfl⟩ := h
    rw [hm x hx i, hm y hy i]
  · have h' : ∀ i, μ ≠ ev i := fun i hi => h ⟨i, hi⟩
    rw [hzero x hx μ h', hzero y hy μ h']

/-- Row `hasPattern_of_literal` (Statements7.lean l.64). -/
theorem hasPattern_of_literal_proved {k : ℕ} (R : CurvTensor 16) (hO : R.IsOssermanSet) (m : Fin k → ℕ)
    (ev : Fin k → ℝ) (hev : Function.Injective ev) (x₀ : Vec 16) (hx₀ : x₀ ⬝ᵥ x₀ = 1)
    (h₀ : ∀ i, R.redMult x₀ (ev i) = m i) : HasPattern R m := by
  have hO' := (OssTop.isOsserman_iff_set_proved R).mpr hO
  exact ⟨ev, hev, fun x hx i => by rw [hO' x x₀ hx hx₀, h₀ i]⟩

/-- Row `cor_D_87` (Statements7.lean l.636): Theorem C on the pattern `(8,7)`. -/
theorem cor_D_87_proved (R : CurvTensor 16) (h : HasPattern R ![8, 7]) : R.IsClifford ∨ IsCayleyType R := by
  obtain ⟨ev, hev, hm⟩ := h
  have h2 : ∃ μ₁ μ₂ : ℝ, μ₁ ≠ μ₂ ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ₁ = 8 ∧ R.redMult x μ₂ = 7 :=
    ⟨ev 0, ev 1, fun h01 => absurd (hev h01) (by decide), fun x hx => ⟨hm x hx 0, hm x hx 1⟩⟩
  obtain ⟨μ, κ, -, -, A, -, hcase⟩ := ThmC.thm_C_of_prop_5_2 Sec5c.prop_5_2_proved R h2
  rcases hcase with ⟨-, hC⟩ | ⟨-, hC⟩ | ⟨-, T, hT, hR⟩
  · exact Or.inl hC
  · exact Or.inl hC
  · exact Or.inr ⟨μ - κ / 3, κ / 3, T, hT, hR⟩

/-- Row `cor_D_771` (Statements7.lean l.640): Theorem E (premise `hE`) on the pattern `(7,7,1)`. -/
theorem cor_D_771_proved
    (hE : ∀ R : CurvTensor 16,
      (HasPattern R ![7, 7, 1] ∨ HasPattern R ![8, 6, 1] ∨ HasPattern R ![8, 5, 2] ∨ HasPattern R ![7, 6, 2]) →
      R.IsClifford)
    (R : CurvTensor 16) (h : HasPattern R ![7, 7, 1]) : R.IsClifford :=
  hE R (Or.inl h)

/-- Row `cor_D_cases` (Statements7.lean l.645). -/
theorem cor_D_cases_proved
    (hE : ∀ R : CurvTensor 16,
      (HasPattern R ![7, 7, 1] ∨ HasPattern R ![8, 6, 1] ∨ HasPattern R ![8, 5, 2] ∨ HasPattern R ![7, 6, 2]) →
      R.IsClifford)
    (R : CurvTensor 16)
    (h : R.IsClifford ∨ HasPattern R ![8, 7] ∨ HasPattern R ![7, 7, 1]) : R.IsClifford ∨ IsCayleyType R := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact cor_D_87_proved R h
  · exact Or.inl (cor_D_771_proved hE R h)

/-- Row `cor_D` (Statements7.lean l.40): Andrejić's theorem leaves Clifford, `(8,7)` or `(7,7,1)`. -/
theorem cor_D_proved
    (hE : ∀ R : CurvTensor 16,
      (HasPattern R ![7, 7, 1] ∨ HasPattern R ![8, 6, 1] ∨ HasPattern R ![8, 5, 2] ∨ HasPattern R ![7, 6, 2]) →
      R.IsClifford)
    (R : CurvTensor 16) (hO : R.IsOsserman) (hJP : IsJacobiProportional R) :
    R.IsClifford ∨ IsCayleyType R := by
  by_cases hC : R.IsClifford
  · exact Or.inl hC
  · exact cor_D_cases_proved hE R (Or.inr (andrejic_thm5 R hO hJP hC))

end Osserman.Proofs.CorD
