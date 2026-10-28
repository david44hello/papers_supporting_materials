/-
ThmECayley.lean — excluding the Cayley alternative in Theorem E, paper 013, lines 767–771.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Lemma71Geometry
import Osserman.Proofs.CayleyIdentify
import Osserman.Proofs.Lemma71Blocks
import Osserman.Proofs.ThmC
import Osserman.Proofs.Sec5c

namespace Osserman.Proofs.ThmECayley

open Osserman Matrix Osserman.Proofs.Threshold Osserman.Proofs.Curv
open Osserman.Proofs.Spectral Osserman.Proofs.CayleyJacobi
open Osserman.Proofs.Lemma71Geometry Osserman.Proofs.CayleyIdentify

lemma Acay_smul (t : ℝ) (x : Vec 16) : Acay stdSys (t • x) = (t * t) • Acay stdSys x := by
  obtain ⟨R, roots, am⟩ := cayley_normalized
  rw [← am]
  exact Amat_smul R 1 3 t x

lemma range_smul_matrix (M : Matrix (Fin 16) (Fin 16) ℝ) (t : ℝ) (ht : t ≠ 0) :
    LinearMap.range (Matrix.toLin' (t • M)) = LinearMap.range (Matrix.toLin' M) := by
  ext y
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨t • z, by simpa only [Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.mulVec_smul] using hz⟩
  · rintro ⟨z, hz⟩
    refine ⟨t⁻¹ • z, ?_⟩
    change (t • M) *ᵥ (t⁻¹ • z) = y
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ ht, one_smul]
    exact hz

lemma L_smul (t : ℝ) (ht : t ≠ 0) (x : Vec 16) : Lstd (t • x) = Lstd x := by
  unfold Lstd
  rw [Acay_smul, range_smul_matrix _ _ (mul_ne_zero ht ht),
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ht)]

lemma N_smul (t : ℝ) (ht : t ≠ 0) (x : Vec 16) : Nstd (t • x) = Nstd x := by
  unfold Nstd
  rw [L_smul t ht]

lemma perp_smul (t : ℝ) (ht : t ≠ 0) (x : Vec 16) : perp (t • x) = perp x := by
  ext y
  change (t • x) ⬝ᵥ y = 0 ↔ x ⬝ᵥ y = 0
  rw [smul_dotProduct, smul_eq_mul, mul_eq_zero]
  simp only [ht, false_or]

lemma E_smul (t : ℝ) (ht : t ≠ 0) (x : Vec 16) : Estd (t • x) = Estd x := by
  unfold Estd
  rw [L_smul t ht, perp_smul t ht]

theorem thm_E_conj_standard_proved (T J : Matrix (Fin 16) (Fin 16) ℝ)
    (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ) :
    ((∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x ∈ (Nstd (T *ᵥ x)).comap (Matrix.toLin' T)) →
        ∀ z : Vec 16, z ≠ 0 → (T * J * Tᵀ) *ᵥ z ∈ Nstd z) ∧
      ((∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x ∈ (Estd (T *ᵥ x)).comap (Matrix.toLin' T)) →
        ∀ z : Vec 16, z ≠ 0 → (T * J * Tᵀ) *ᵥ z ∈ Estd z) := by
  have tt : T * Tᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).mp hT
  have unit (u : Vec 16) (hu : u ⬝ᵥ u = 1) : (Tᵀ *ᵥ u) ⬝ᵥ (Tᵀ *ᵥ u) = 1 := by
    rw [orthogonal_dot Tᵀ (by simpa using tt), hu]
  have restore (u : Vec 16) : T *ᵥ (Tᵀ *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, tt, Matrix.one_mulVec]
  constructor
  · intro field z hz
    obtain ⟨s, u, hu, equal⟩ := exists_unit_scale z
    have snonzero : s ≠ 0 := by intro zero; apply hz; rw [equal, zero, zero_smul]
    have member := field (Tᵀ *ᵥ u) (unit u hu)
    change T *ᵥ (J *ᵥ (Tᵀ *ᵥ u)) ∈ Nstd (T *ᵥ (Tᵀ *ᵥ u)) at member
    rw [restore, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at member
    rw [equal, N_smul s snonzero, Matrix.mulVec_smul]
    exact (Nstd u).smul_mem s member
  · intro field z hz
    obtain ⟨s, u, hu, equal⟩ := exists_unit_scale z
    have snonzero : s ≠ 0 := by intro zero; apply hz; rw [equal, zero, zero_smul]
    have member := field (Tᵀ *ᵥ u) (unit u hu)
    change T *ᵥ (J *ᵥ (Tᵀ *ᵥ u)) ∈ Estd (T *ᵥ (Tᵀ *ᵥ u)) at member
    rw [restore, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at member
    rw [equal, E_smul s snonzero, Matrix.mulVec_smul]
    exact (Estd u).smul_mem s member

lemma A_perp_action (x y : Vec 16) (hx : x ⬝ᵥ x = 1) (hy : x ⬝ᵥ y = 0) :
    Acay stdSys x *ᵥ y = (1 / 2 : ℝ) • (y + Hcomb stdSys (hvec stdSys x) *ᵥ y) := by
  simp only [Acay, hx, one_smul, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec, outer_mulVec_real, hy, zero_smul, sub_zero, Hcomb, hvec]

lemma mem_E_unit (x y : Vec 16) (hx : x ⬝ᵥ x = 1) :
    y ∈ Estd x ↔ x ⬝ᵥ y = 0 ∧ Acay stdSys x *ᵥ y = y := by
  have nonzero : x ≠ 0 := by intro zero; simp [zero] at hx
  have eigenspace := (sec7_L_eigenspace_proved x nonzero).2.1
  have w : (fun i => (x ⬝ᵥ (stdSys i *ᵥ x)) / (x ⬝ᵥ x)) = hvec stdSys x := by
    ext i; simp [hx, hvec]
  rw [w] at eigenspace
  change y ∈ Lstd x ∧ x ⬝ᵥ y = 0 ↔ _
  rw [eigenspace]
  constructor
  · intro h
    have eigen : Hcomb stdSys (hvec stdSys x) *ᵥ y = y := by
      simpa only [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, one_smul, Hcomb] using h.1
    refine ⟨h.2, ?_⟩
    rw [A_perp_action x y hx h.2, eigen]
    module
  · intro h
    refine ⟨?_, h.1⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change Hcomb stdSys (hvec stdSys x) *ᵥ y = (1 : ℝ) • y
    rw [one_smul]
    have action := h.2
    rw [A_perp_action x y hx h.1] at action
    ext i
    have entry := congrFun action i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at entry
    linarith

lemma mem_N_unit (x y : Vec 16) (hx : x ⬝ᵥ x = 1) :
    y ∈ Nstd x ↔ x ⬝ᵥ y = 0 ∧ Acay stdSys x *ᵥ y = 0 := by
  have nonzero : x ≠ 0 := by intro zero; simp [zero] at hx
  have eigenspace := negative_space x nonzero
  have w : (fun i => (x ⬝ᵥ (stdSys i *ᵥ x)) / (x ⬝ᵥ x)) = hvec stdSys x := by
    ext i; simp [hx, hvec]
  rw [w] at eigenspace
  constructor
  · intro h
    have orthogonal : x ⬝ᵥ y = 0 := h x (self_mem_L x)
    have eigen : Hcomb stdSys (hvec stdSys x) *ᵥ y = -y := by
      rw [eigenspace] at h
      simpa only [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, neg_one_smul, Hcomb] using h
    refine ⟨orthogonal, ?_⟩
    rw [A_perp_action x y hx orthogonal, eigen, add_neg_cancel, smul_zero]
  · intro h
    rw [eigenspace]
    apply Module.End.mem_eigenspace_iff.mpr
    change Hcomb stdSys (hvec stdSys x) *ᵥ y = (-1 : ℝ) • y
    rw [neg_one_smul]
    have action := h.2
    rw [A_perp_action x y hx h.1] at action
    ext i
    have entry := congrFun action i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.zero_apply, Pi.neg_apply, smul_eq_mul] at entry ⊢
    linarith

lemma transported_action (Rt : CurvTensor 16) (a b : ℝ)
    (T : Matrix (Fin 16) (Fin 16) ℝ) (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ)
    (hR : ∀ u v w, Rt.op u v w = a • R1fun u v w + b • pullbackFun T RCayFun u v w)
    (x y : Vec 16) (hx : x ⬝ᵥ x = 1) (hy : x ⬝ᵥ y = 0) :
    T *ᵥ Rt.op y x x = (a + b) • (T *ᵥ y) + (3 * b) • (Acay stdSys (T *ᵥ x) *ᵥ (T *ᵥ y)) := by
  have tt : T * Tᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).mp hT
  have t't : Tᵀ * T = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hT
  have htx : (T *ᵥ x) ⬝ᵥ (T *ᵥ x) = 1 := by rw [orthogonal_dot T t't, hx]
  have htxy : (T *ᵥ x) ⬝ᵥ (T *ᵥ y) = 0 := by rw [orthogonal_dot T t't, hy]
  rw [hR, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have round : R1fun y x x = y := by simp [R1fun, hx, dotProduct_comm y x, hy]
  rw [round, pullbackFun, Matrix.mulVec_mulVec, tt, Matrix.one_mulVec, RCay_jacobi]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add,
    Osserman.Pi, htx, Matrix.sub_mulVec, Matrix.one_mulVec, one_smul,
    outer_mulVec_real, htxy, zero_smul, sub_zero]
  module

theorem thm_E_cayley_eigendistributions_proved (Rt : CurvTensor 16) (a b : ℝ) (hb : b ≠ 0)
    (T : Matrix (Fin 16) (Fin 16) ℝ) (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ)
    (hR : ∀ u v w, Rt.op u v w = a • R1fun u v w + b • pullbackFun T RCayFun u v w) (x : Vec 16)
    (hx : x ⬝ᵥ x = 1) :
    Module.End.eigenspace (Rt.jacobiMap x) (a + b) ⊓ perp x = (Nstd (T *ᵥ x)).comap (Matrix.toLin' T) ∧
      Module.End.eigenspace (Rt.jacobiMap x) (a + 4 * b) ⊓ perp x = (Estd (T *ᵥ x)).comap (Matrix.toLin' T) := by
  have t't : Tᵀ * T = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hT
  have htx : (T *ᵥ x) ⬝ᵥ (T *ᵥ x) = 1 := by rw [orthogonal_dot T t't, hx]
  have injective : Function.Injective (fun y : Vec 16 => T *ᵥ y) := by
    intro u v equal
    have images := congrArg (fun z => Tᵀ *ᵥ z) equal
    simpa only [Matrix.mulVec_mulVec, t't, Matrix.one_mulVec] using images
  have nonzero : (3 : ℝ) * b ≠ 0 := mul_ne_zero (by norm_num) hb
  constructor
  · ext y
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
    change (Rt.op y x x = (a + b) • y ∧ x ⬝ᵥ y = 0) ↔ T *ᵥ y ∈ Nstd (T *ᵥ x)
    rw [mem_N_unit _ _ htx, orthogonal_dot T t't]
    constructor
    · intro h
      have action := transported_action Rt a b T hT hR x y hx h.2
      rw [h.1, Matrix.mulVec_smul] at action
      have zero : (3 * b) • (Acay stdSys (T *ᵥ x) *ᵥ (T *ᵥ y)) = 0 := by
        exact (add_left_cancel (by simpa only [add_zero] using action.symm))
      exact ⟨h.2, (smul_eq_zero.mp zero).resolve_left nonzero⟩
    · intro h
      refine ⟨?_, h.1⟩
      apply injective
      change T *ᵥ Rt.op y x x = T *ᵥ ((a + b) • y)
      rw [transported_action Rt a b T hT hR x y hx h.1, h.2, smul_zero, add_zero, Matrix.mulVec_smul]
  · ext y
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
    change (Rt.op y x x = (a + 4 * b) • y ∧ x ⬝ᵥ y = 0) ↔ T *ᵥ y ∈ Estd (T *ᵥ x)
    rw [mem_E_unit _ _ htx, orthogonal_dot T t't]
    constructor
    · intro h
      have action := transported_action Rt a b T hT hR x y hx h.2
      rw [h.1, Matrix.mulVec_smul] at action
      refine ⟨h.2, ?_⟩
      ext i
      have entry := congrFun action i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at entry
      have product : (3 * b) * ((Acay stdSys (T *ᵥ x) *ᵥ (T *ᵥ y)) i - (T *ᵥ y) i) = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left nonzero)
    · intro h
      refine ⟨?_, h.1⟩
      apply injective
      change T *ᵥ Rt.op y x x = T *ᵥ ((a + 4 * b) • y)
      rw [transported_action Rt a b T hT hR x y hx h.1, h.2, Matrix.mulVec_smul]
      module

lemma cayley_eigenvalue (Rt : CurvTensor 16) (a b μ : ℝ)
    (T : Matrix (Fin 16) (Fin 16) ℝ) (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ)
    (hR : ∀ u v w, Rt.op u v w = a • R1fun u v w + b • pullbackFun T RCayFun u v w)
    (x y : Vec 16) (hx : x ⬝ᵥ x = 1) (hy : x ⬝ᵥ y = 0) (hne : y ≠ 0)
    (eigen : Rt.op y x x = μ • y) : μ = a + b ∨ μ = a + 4 * b := by
  have t't : Tᵀ * T = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hT
  have htx : (T *ᵥ x) ⬝ᵥ (T *ᵥ x) = 1 := by rw [orthogonal_dot T t't, hx]
  let v := T *ᵥ y
  let A := Acay stdSys (T *ᵥ x)
  let c := 3 * b
  let d := μ - (a + b)
  have nonzero : v ≠ 0 := by
    intro zero
    apply hne
    have equal := congrArg (fun z => Tᵀ *ᵥ z) zero
    simpa only [v, Matrix.mulVec_mulVec, t't, Matrix.one_mulVec, Matrix.mulVec_zero] using equal
  have square : A * A = A := by
    simpa only [htx, one_smul] using (sec7_cayley_A_props_proved.2.2 (T *ᵥ x)).2.1
  have action := transported_action Rt a b T hT hR x y hx hy
  rw [eigen, Matrix.mulVec_smul] at action
  have key : c • (A *ᵥ v) = d • v := by
    calc
      c • (A *ᵥ v) = ((a + b) • v + c • (A *ᵥ v)) - (a + b) • v := by module
      _ = μ • v - (a + b) • v := by rw [← action]
      _ = d • v := by dsimp only [d]; module
  have keyA := congrArg (fun z => A *ᵥ z) key
  simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, square] at keyA
  have vector_zero : (d * (d - c)) • v = 0 := by
    calc
      _ = d • (d • v) - c • (d • v) := by module
      _ = d • (c • (A *ᵥ v)) - c • (c • (A *ᵥ v)) := by rw [← key]
      _ = c • (d • (A *ᵥ v) - c • (A *ᵥ v)) := by module
      _ = 0 := by rw [← keyA, sub_self, smul_zero]
  have scalar_zero : d * (d - c) = 0 := (smul_eq_zero.mp vector_zero).resolve_right nonzero
  rcases mul_eq_zero.mp scalar_zero with first | second
  · exact Or.inl (by dsimp only [d] at first; linarith)
  · exact Or.inr (by dsimp only [d, c] at second; linarith)

lemma eigenvalue_of_positive (Rt : CurvTensor 16) (a b μ : ℝ)
    (T : Matrix (Fin 16) (Fin 16) ℝ) (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ)
    (hR : ∀ u v w, Rt.op u v w = a • R1fun u v w + b • pullbackFun T RCayFun u v w)
    (x : Vec 16) (hx : x ⬝ᵥ x = 1) (positive : 0 < Rt.redMult x μ) :
    μ = a + b ∨ μ = a + 4 * b := by
  change 0 < Module.finrank ℝ ↥(Esp Rt x μ) at positive
  obtain ⟨y, nonzero⟩ := Module.finrank_pos_iff_exists_ne_zero.mp positive
  have ynonzero : (y : Vec 16) ≠ 0 := by intro zero; exact nonzero (Subtype.ext zero)
  have member := mem_Esp.mp y.property
  exact cayley_eigenvalue Rt a b μ T hT hR x y hx member.2 ynonzero member.1

lemma conjugated_zero (T J : Matrix (Fin 16) (Fin 16) ℝ)
    (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ) (zero : T * J * Tᵀ = 0) : J = 0 := by
  have t't : Tᵀ * T = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hT
  calc
    J = (Tᵀ * T) * J * (Tᵀ * T) := by rw [t't]; simp
    _ = Tᵀ * (T * J * Tᵀ) * T := by noncomm_ring
    _ = 0 := by rw [zero]; simp

theorem thm_E_no_cayley_proved (Rt : CurvTensor 16) (μ₀ μ₁ : ℝ) (hne : μ₀ ≠ μ₁) (a b : ℕ)
    (hab : (a = 7 ∧ b = 8) ∨ (a = 8 ∧ b = 7))
    (hpat : ∀ x : Vec 16, x ⬝ᵥ x = 1 → Rt.redMult x μ₀ = a ∧ Rt.redMult x μ₁ = b)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJ0 : J ≠ 0)
    (hfield : ∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x ∈ Module.End.eigenspace (Rt.jacobiMap x) μ₁) :
    ¬ IsCayleyType Rt := by
  rintro ⟨α, β, T, hT, representation⟩
  let x0 : Vec 16 := Pi.single 0 1
  have unit : x0 ⬝ᵥ x0 = 1 := by simp [x0]
  have apos : 0 < a := by rcases hab with h | h <;> omega
  have bpos : 0 < b := by rcases hab with h | h <;> omega
  have pos0 : 0 < Rt.redMult x0 μ₀ := by rw [(hpat x0 unit).1]; exact apos
  have pos1 : 0 < Rt.redMult x0 μ₁ := by rw [(hpat x0 unit).2]; exact bpos
  have candidate0 := eigenvalue_of_positive Rt α β μ₀ T hT representation x0 unit pos0
  have candidate1 := eigenvalue_of_positive Rt α β μ₁ T hT representation x0 unit pos1
  have βnonzero : β ≠ 0 := by
    intro zero
    have first : μ₀ = α := by rcases candidate0 with h | h <;> simpa only [zero, add_zero, mul_zero] using h
    have second : μ₁ = α := by rcases candidate1 with h | h <;> simpa only [zero, add_zero, mul_zero] using h
    exact hne (first.trans second.symm)
  have perpendicular (x : Vec 16) : x ⬝ᵥ (J *ᵥ x) = 0 := by
    have equal := Matrix.dotProduct_transpose_mulVec J x x
    rw [hJs, Matrix.neg_mulVec, dotProduct_neg] at equal
    linarith
  rcases candidate1 with first | second
  · have field : ∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x ∈ (Nstd (T *ᵥ x)).comap (Matrix.toLin' T) := by
      intro x hx
      rw [← (thm_E_cayley_eigendistributions_proved Rt α β βnonzero T hT representation x hx).1]
      refine ⟨?_, perpendicular x⟩
      apply Module.End.mem_eigenspace_iff.mpr
      have eigen := Module.End.mem_eigenspace_iff.mp (hfield x hx)
      rwa [first] at eigen
    have standard := (thm_E_conj_standard_proved T J hT).1 field
    have zero := Osserman.Proofs.Lemma71Blocks.lem_7_1_b_proved (T * J * Tᵀ) standard
    exact hJ0 (conjugated_zero T J hT zero)
  · have field : ∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x ∈ (Estd (T *ᵥ x)).comap (Matrix.toLin' T) := by
      intro x hx
      rw [← (thm_E_cayley_eigendistributions_proved Rt α β βnonzero T hT representation x hx).2]
      refine ⟨?_, perpendicular x⟩
      apply Module.End.mem_eigenspace_iff.mpr
      have eigen := Module.End.mem_eigenspace_iff.mp (hfield x hx)
      rwa [second] at eigen
    have standard := (thm_E_conj_standard_proved T J hT).2 field
    have zero := Osserman.Proofs.Lemma71Blocks.lem_7_1_a_proved (T * J * Tᵀ) standard
    exact hJ0 (conjugated_zero T J hT zero)

theorem thm_E_tilde_clifford_proved (Rt : CurvTensor 16) (μ₀ μ₁ : ℝ) (hne : μ₀ ≠ μ₁) (a b : ℕ)
    (hab : (a = 7 ∧ b = 8) ∨ (a = 8 ∧ b = 7))
    (hpat : ∀ x : Vec 16, x ⬝ᵥ x = 1 → Rt.redMult x μ₀ = a ∧ Rt.redMult x μ₁ = b)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJ0 : J ≠ 0)
    (hfield : ∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x ∈ Module.End.eigenspace (Rt.jacobiMap x) μ₁) :
    Rt.IsClifford := by
  have hypothesis : ∃ μ₁' μ₂' : ℝ, μ₁' ≠ μ₂' ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 → Rt.redMult x μ₁' = 8 ∧ Rt.redMult x μ₂' = 7 := by
    rcases hab with h | h
    · exact ⟨μ₁, μ₀, Ne.symm hne, fun x hx => by simpa only [h.1, h.2] using (hpat x hx).symm⟩
    · exact ⟨μ₀, μ₁, hne, fun x hx => by simpa only [h.1, h.2] using hpat x hx⟩
  obtain ⟨μ, κ, _, _, A, _, cases⟩ := Osserman.Proofs.ThmC.thm_C_of_prop_5_2
    Osserman.Proofs.Sec5c.prop_5_2_proved Rt hypothesis
  rcases cases with cl7 | cl8 | cayley
  · exact cl7.2
  · exact cl8.2
  · obtain ⟨form, T, hT, representation⟩ := cayley
    exact (thm_E_no_cayley_proved Rt μ₀ μ₁ hne a b hab hpat J hJs hJ0 hfield
      ⟨μ - κ / 3, κ / 3, T, hT, representation⟩).elim

end Osserman.Proofs.ThmECayley


